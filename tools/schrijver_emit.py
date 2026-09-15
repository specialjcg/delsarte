#!/usr/bin/env python3
"""Emit Schrijver's program and its exact certificate in the format of
`Delsarte/SDP/Sparse.lean`.

Outside the trust base, like `schrijver_cert.py` which it calls. What it writes
is checked by the Lean kernel; before writing, the same integer check is replayed
here so that a mismatch is caught without a Lean build.

Integer encoding (see `Sparse.lean`):

* variable u has scale m u, the multinomial of its orbit; block and row
  coefficients are stored multiplied by m u, the objective too;
* Gram vectors over V, weights over W, multipliers over T = W V^2;
* only the rows carrying a multiplier are emitted, renumbered in order.

Usage:

    schrijver_emit.py n d OUT.lean [--cache FILE]
"""

from fractions import Fraction as Q
from math import floor, gcd, lcm
from pathlib import Path
import pickle
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import schrijver_cert as SC  # noqa: E402
import schrijver_sdp as S  # noqa: E402


def as_int(x):
    assert x.denominator == 1, x
    return x.numerator


def scales(P):
    m = [0] * len(P.keys)
    for (a, b, c), u in P.keys.items():
        t = (a + b - c) // 2
        m[u] = S.mult(P.n, a, b, t)
    return m


def encode(P, grams, mu):
    nv = len(P.keys)
    m = scales(P)
    obj = [as_int(P.obj.get(u, Q(0)) * m[u]) for u in range(nv)]
    base = [sorted((p, q, as_int(c)) for (p, q), c in F0.items() if c != 0)
            for F0, _ in P.blocks]
    by_var = [[] for _ in range(nv)]
    for b, (_, F) in enumerate(P.blocks):
        for u, M in F.items():
            for (p, q), c in M.items():
                if c != 0:
                    by_var[u].append((b, p, q, as_int(c * m[u])))
    used = sorted(l for l, x in mu.items() if x > 0)
    renum = {l: r for r, l in enumerate(used)}
    row_base = [as_int(P.rows[l][1]) for l in used]
    row_by_var = [[] for _ in range(nv)]
    for l in used:
        for u, c in P.rows[l][0].items():
            row_by_var[u].append((renum[l], as_int(c * m[u])))
    data = dict(scale=m, obj=obj, base=base, byVar=by_var, rowBase=row_base,
                rowByVar=row_by_var)

    V = lcm(*(x.denominator for g in grams for x in g.v))
    Dd = lcm(*(g.d.denominator for g in grams))
    Dm = lcm(*(mu[l].denominator for l in used))
    W = lcm(Dd, Dm // gcd(Dm, V * V))
    T = W * V * V
    assert T % Dm == 0
    blocks = [[] for _ in P.blocks]
    for g in grams:
        blocks[g.b].append((as_int(g.d * W), [as_int(x * V) for x in g.v]))
    cert = dict(V=V, W=W, grams=blocks, mu=[as_int(mu[l] * T) for l in used])
    return data, cert


def get(L, i, default):
    return L[i] if 0 <= i < len(L) else default


def gram_num(cert, b, p, q):
    return sum(w * get(v, p, 0) * get(v, q, 0) for w, v in get(cert["grams"], b, []))


def check(data, cert):
    """The Lean `Data.check`, line for line. Returns (ok, bnum, T)."""
    T = cert["W"] * cert["V"] ** 2
    ok = cert["V"] > 0 and cert["W"] > 0
    for u in range(len(data["scale"])):
        c = T * data["obj"][u]
        c += sum(x * gram_num(cert, b, p, q) for b, p, q, x in data["byVar"][u])
        c += sum(get(cert["mu"], l, 0) * a for l, a in data["rowByVar"][u])
        ok &= c == 0
    bnum = sum(x * gram_num(cert, b, p, q)
               for b in range(len(cert["grams"])) for p, q, x in get(data["base"], b, []))
    bnum += sum(cert["mu"][l] * get(data["rowBase"], l, 0) for l in range(len(cert["mu"])))
    return ok, bnum, T


def lean_list(xs, fmt, per_line=8, indent="    "):
    items = [fmt(x) for x in xs]
    if not items:
        return "[]"
    lines = [", ".join(items[i:i + per_line]) for i in range(0, len(items), per_line)]
    return "[" + (",\n" + indent).join(lines) + "]"


def tup(x):
    return "(" + ", ".join(str(v) for v in x) + ")"


def nested(xss, fmt, per_line):
    return "[" + ",\n    ".join(lean_list(xs, fmt, per_line, "     ") for xs in xss) + "]"


def zig(c):
    """Zigzag encoding, inverse of `Sparse.unzig`."""
    return 2 * c if c >= 0 else -2 * c - 1


def flat(xs):
    """Tuples with a signed last component, flattened for `Sparse.decode2/3/4`."""
    return [v for x in xs for v in (*x[:-1], zig(x[-1]))]


def pieces(name, xss, typ, fmt, per_line, wrap=""):
    """One small definition per inner list, and the list of their names.

    A single literal of fifteen thousand tuples does not elaborate (measured:
    over sixteen minutes, then a heartbeat timeout), and small definitions of
    tuples still time out; flat lists of naturals, decoded by `wrap`, do not."""
    out, names = [], []
    for i, xs in enumerate(xss):
        names.append(f"{name}{i}")
        body = lean_list(xs, fmt, per_line, "   " + " " * len(wrap))
        out.append(f"noncomputable def {name}{i} : {typ} :=\n  {wrap}{body}\n")
    return "\n".join(out), lean_list(names, str, 6, "    ")


def write_lean(path, n, d, data, cert, bound):
    gram = lambda g: ("(" + str(g[0]) + ",\n    decodeZ "
                      + lean_list([zig(x) for x in g[1]], str, 5, "             ") + ")")
    base_defs, base = pieces("base", [flat(x) for x in data["base"]],
                             "List (ℕ × ℕ × ℤ)", str, 12, "decode3 ")
    var_defs, by_var = pieces("byVar", [flat(x) for x in data["byVar"]],
                              "List (ℕ × ℕ × ℕ × ℤ)", str, 12, "decode4 ")
    row_defs, row_by_var = pieces("rowByVar", [flat(x) for x in data["rowByVar"]],
                                  "List (ℕ × ℤ)", str, 12, "decode2 ")
    gram_defs, grams = pieces("grams", cert["grams"], "List (ℕ × List ℤ)", gram, 1)
    chunks = [cert["mu"][i:i + 50] for i in range(0, len(cert["mu"]), 50)]
    mu_defs, _ = pieces("mu", chunks, "List ℕ", str, 1)
    mu = " ++ ".join(f"mu{i}" for i in range(len(chunks))) or "[]"
    # One kernel `decide` per range of about a thousand entries: a single one over
    # every variable exhausted 31 GB (measured), a range costs about 400 MB.
    nnz = [len(a) + len(b) for a, b in zip(data["byVar"], data["rowByVar"])]
    cuts, acc = [0], 0
    for u, k in enumerate(nnz):
        acc += k
        if acc >= 1000 and u + 1 < len(nnz):
            cuts.append(u + 1)
            acc = 0
    cuts.append(len(nnz))
    ranges = "\n".join(
        f"theorem range{r} : data.checkRange cert {lo} {hi - lo} = true := by\n"
        f"  decide +kernel\n"
        for r, (lo, hi) in enumerate(zip(cuts, cuts[1:])))
    cases = "".join(
        f"  by_cases h{r} : u < {hi}\n"
        f"  · exact Data.coeff_eq_zero_of_checkRange range{r} (by omega) (by omega)\n"
        for r, hi in enumerate(cuts[1:-1]))
    cases += (f"  exact Data.coeff_eq_zero_of_checkRange range{len(cuts) - 2}"
              f" (by omega) (by omega)\n")
    out = f"""/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.SDP.Sparse

/-!
# Schrijver's program for `A({n},{d})` and its certificate — generated data

Written by `tools/schrijver_emit.py {n} {d}`. Do not edit by hand. The generator
is outside the trust base: these lists mean nothing until the kernel checks them.
Certified value of the objective: {float(bound):.9f}.
-/

namespace Delsarte.SDP.Schrijver{n}_{d}

open Delsarte.SDP.Sparse

{base_defs}
{var_defs}
{row_defs}
{gram_defs}
{mu_defs}
/-- The program, integer encoded. -/
noncomputable def data : Data where
  scale := {lean_list(data["scale"], str, 6, "    ")}
  obj := decodeZ {lean_list([zig(x) for x in data["obj"]], str, 6, "            ")}
  base := {base}
  byVar := {by_var}
  rowBase := decodeZ {lean_list([zig(x) for x in data["rowBase"]], str, 20, "            ")}
  rowByVar := {row_by_var}

/-- The certificate. -/
noncomputable def cert : Cert where
  V := {cert["V"]}
  W := {cert["W"]}
  grams := {grams}
  mu := {mu}

/-! ## Kernel check, by ranges of variables

One `decide +kernel` per range of about a thousand entries, see `Data.checkRange`.
Generated like the data; what is proved here does not depend on the generator. -/

{ranges}
theorem nv_data : data.nv = {len(nnz)} := by decide +kernel

/-- The certificate checks. -/
theorem check_data : data.check cert = true := by
  refine Data.check_of_coeff (by decide +kernel) (by decide +kernel) fun u hu => ?_
  rw [nv_data] at hu
{cases}
end Delsarte.SDP.Schrijver{n}_{d}
"""
    Path(path).write_text(out)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    n, d, out = int(args[0]), int(args[1]), args[2]
    cache = sys.argv[sys.argv.index("--cache") + 1] if "--cache" in sys.argv else None
    if cache and Path(cache).exists():
        P = SC.Program(n, d)
        grams, mu = pickle.loads(Path(cache).read_bytes())
    else:
        P, grams, mu = SC.certify(n, d)
        if cache:
            Path(cache).write_bytes(pickle.dumps((grams, mu)))
    ok, bound = SC.check(P, grams, mu)
    assert ok, "certificate does not check in Fraction"
    data, cert = encode(P, grams, mu)
    ok, bnum, T = check(data, cert)
    assert ok, "integer encoding does not check"
    assert Q(bnum, T) + 1 == bound, (Q(bnum, T) + 1, bound)
    nnz = sum(map(len, data["byVar"]))
    print(f"A({n},{d}): vars {len(data['scale'])}, block nnz {nnz}, rows {len(cert['mu'])}, "
          f"V 2^{cert['V'].bit_length() - 1}, W 2^{cert['W'].bit_length() - 1}, "
          f"bound 1 + bnum/T = {float(bound):.9f} -> A <= {floor(bound)}")

    # Negative control: one weight numerator off by one must fail the check.
    b = next(i for i, g in enumerate(cert["grams"]) if g)
    bad = dict(cert, grams=[list(g) for g in cert["grams"]])
    w, v = bad["grams"][b][0]
    bad["grams"][b][0] = (w + 1, v)
    assert not check(data, bad)[0], "a tampered weight was accepted"
    print("  [ok] weight numerator + 1 rejected")
    write_lean(out, n, d, data, cert, bound)
    print(f"  wrote {out}")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact rational solver for the Delsarte linear program, binary case.

This is a *source of candidates*, never an authority.  Nothing it prints is
trusted: the dual vector it produces is re-verified inside Lean by
`Delsarte.Certificate.DualCert`, and the bound is re-derived there from the
weak duality theorem.  Consequently this file is deliberately outside the trust
base, and its language is irrelevant.

Primal LP, in the shape `max c x  s.t.  A x <= b, x >= 0`:

    variables   a_i,  d <= i <= n          (the distance distribution)
    constraints -sum_i K_k(i) a_i <= K_k(0),   1 <= k <= n
    objective   max sum_i a_i

`b_k = K_k(0) = C(n,k) > 0`, so the origin is feasible and no phase one is
needed.  The dual optimal `y` is read off the objective row under the slack
columns, and satisfies exactly what `DualCert` checks:

    y_k >= 0                        for 1 <= k <= n
    -sum_k y_k K_k(i) >= 1          for d <= i <= n

with resulting bound `A(n,2,d) <= 1 + sum_k y_k K_k(0)`.

Everything is `fractions.Fraction`; there is no floating point anywhere.
"""

from math import lcm
from fractions import Fraction
import sys


def krawtchouk_table(n, q, kmax):
    """K[k][i] for 0 <= k <= kmax, 0 <= i <= n, by the three-term recurrence.

    Mirrors `Delsarte.krawtchoukRec`: no binomial coefficient is ever computed.
    """
    K = [[Fraction(0)] * (n + 1) for _ in range(kmax + 1)]
    for i in range(n + 1):
        K[0][i] = Fraction(1)
        if kmax >= 1:
            K[1][i] = Fraction((q - 1) * (n - i) - i)
    for k in range(kmax - 1):
        for i in range(n + 1):
            lead = Fraction((q - 1) * (n - i) - i - (q - 2) * (k + 1))
            K[k + 2][i] = (lead * K[k + 1][i] - Fraction(q - 1) * (n - k) * K[k][i]) / (k + 2)
    return K


def simplex(A, b, c):
    """max c x subject to A x <= b, x >= 0, with b >= 0.

    Returns (optimum, x, y) with y the dual optimal.  Bland's rule, so no
    cycling; exact arithmetic, so no tolerance.
    """
    m, nv = len(A), len(A[0])
    # tableau: nv structural + m slack + rhs
    T = [[Fraction(0)] * (nv + m + 1) for _ in range(m + 1)]
    for r in range(m):
        for j in range(nv):
            T[r][j] = Fraction(A[r][j])
        T[r][nv + r] = Fraction(1)
        T[r][-1] = Fraction(b[r])
    for j in range(nv):
        T[m][j] = -Fraction(c[j])
    basis = [nv + r for r in range(m)]

    while True:
        piv_col = None
        for j in range(nv + m):
            if T[m][j] < 0:
                piv_col = j          # Bland: first negative
                break
        if piv_col is None:
            break
        piv_row, best = None, None
        for r in range(m):
            if T[r][piv_col] > 0:
                ratio = T[r][-1] / T[r][piv_col]
                if best is None or ratio < best or (ratio == best and basis[r] < basis[piv_row]):
                    best, piv_row = ratio, r
        if piv_row is None:
            raise RuntimeError("unbounded primal: the LP was set up wrong")
        p = T[piv_row][piv_col]
        T[piv_row] = [v / p for v in T[piv_row]]
        for r in range(m + 1):
            if r != piv_row and T[r][piv_col] != 0:
                f = T[r][piv_col]
                T[r] = [a - f * bb for a, bb in zip(T[r], T[piv_row])]
        basis[piv_row] = piv_col

    x = [Fraction(0)] * nv
    for r in range(m):
        if basis[r] < nv:
            x[basis[r]] = T[r][-1]
    y = [T[m][nv + r] for r in range(m)]
    return T[m][-1], x, y


def solve(n, d, q=2):
    K = krawtchouk_table(n, q, n)
    dists = list(range(d, n + 1))
    A = [[-K[k][i] for i in dists] for k in range(1, n + 1)]
    b = [K[k][0] for k in range(1, n + 1)]
    c = [Fraction(1)] * len(dists)
    opt, x, y = simplex(A, b, c)
    return K, dists, opt, x, y


def check(n, d, K, y, q=2):
    """Re-verify a candidate `y` from scratch. Returns (ok, bound, slacks)."""
    ok = all(v >= 0 for v in y)
    slacks = []
    for i in range(d, n + 1):
        s = -sum(y[k - 1] * K[k][i] for k in range(1, n + 1))
        slacks.append(s)
        if s < 1:
            ok = False
    bound = 1 + sum(y[k - 1] * K[k][0] for k in range(1, n + 1))
    return ok, bound, slacks


def round_certificate(n, d, K, y, den, q=2):
    """Round `y` down to multiples of 1/den, then repair feasibility.

    Rounding down keeps `y >= 0` but can break `slack >= 1`.  The deficit is
    repaired by scaling the whole vector up by the smallest multiple of 1/den
    that restores every constraint.  A scaled certificate is still a
    certificate: both the constraints and the objective are homogeneous of
    degree one in `y`, apart from the constant 1 in the bound.
    """
    yr = [Fraction(int(v * den), den) for v in y]
    if all(v == 0 for v in yr):
        return None
    _, _, slacks = check(n, d, K, yr, q)
    worst = min(slacks)
    if worst <= 0:
        return None
    scale = Fraction(1)
    if worst < 1:
        scale = Fraction(1) / worst
        # round the scale up to a multiple of 1/den so denominators stay small
        scale = Fraction(-((-scale * den).__floor__()), den)
    yr = [v * scale for v in yr]
    ok, bound, slacks = check(n, d, K, yr, q)
    return (yr, ok, bound, slacks) if ok else None


def report(n, d, q=2):
    K, dists, opt, x, y = solve(n, d, q)
    ok, bound, slacks = check(n, d, K, y, q)
    print(f"=== A({n},{q},{d}) ===")
    print(f"  LP optimum          : {1 + opt}  (~{float(1 + opt):.6f})")
    print(f"  dual re-verified    : {ok}, bound {bound} (~{float(bound):.6f})")
    print(f"  floor of the bound  : {bound.__floor__()}")
    dens = sorted({v.denominator for v in y})
    print(f"  y denominators      : {dens[:8]}{' ...' if len(dens) > 8 else ''}")
    print(f"  y support           : {[k + 1 for k, v in enumerate(y) if v != 0]}")
    for den in (1, 2, 4, 8, 16, 32, 64, 128, 256, 1024, 4096):
        r = round_certificate(n, d, K, y, den, q)
        if r is None:
            continue
        yr, okr, br, _ = r
        if br < bound.__floor__() + 1:
            print(f"  rounded 1/{den:<5} -> bound {br} (~{float(br):.6f})"
                  f"  denominators {sorted({v.denominator for v in yr})}")
            print(f"    y = {[str(v) for v in yr]}")
            break
    else:
        print("  no rounding at these denominators keeps the bound below the next integer")
    return y, bound



def emit_lean_lt(n, d, q=2):
    """Print the Lean declarations for one certificate, rounded down.

    Same as `emit_lean`, but the bound check is strict: `bound < B + 1` with
    `B = floor(bound)`.  That is what `A_le_of_intCertLt` needs, and it removes
    `emit_lean`'s requirement that the linear program's optimum be an integer.
    The extra step is the integrality of `A n q d`, not linear programming.
    """
    K, dists, opt, x, y = solve(n, d, q)
    ok, bound, slacks = check(n, d, K, y, q)
    assert ok, "the candidate failed its own re-verification"
    B = bound.__floor__()
    name = f"cert{n}_{d}"
    den = lcm(*[v.denominator for v in y])
    p = [0] + [int(v * den) for v in y]
    assert all(v >= 0 for v in p), "a scaled coefficient came out negative"
    for i in range(d, n + 1):
        slack = -sum(p[k] * K[k][i] for k in range(n + 1))
        assert den <= slack, f"the scaled certificate fails at distance {i}"
    lhs = den + sum(p[k] * K[k][0] for k in range(n + 1))
    assert lhs < (B + 1) * den, "the scaled certificate misses its own floor"
    rats = ", ".join(f"`y {k} = {y[k-1]}`" for k in range(1, n + 1) if y[k - 1] != 0)
    lines = []
    lines.append(f"/-- Certificate for `n = {n}`, `d = {d}`, scaled by its common denominator")
    lines.append(f"`{den}`. Index `0` is unused. Linear-programming optimum `{bound}`. -/")
    lines.append(f"def {name}Int : List ℤ :=")
    lines.append("  " + wrap_ints(p))
    lines.append("")
    lines.append(f"/-- The common denominator of `{name}`. -/")
    lines.append(f"def {name}Den : ℤ := {den}")
    lines.append("")
    lines.extend(wrap_doc(f"The same certificate as rationals: {rats}. Derived from the "
                          "integer form, so the two cannot drift apart."))
    lines.append(f"def {name} : ℕ → ℚ := ratOfInt {name}Int {name}Den")
    lines.append("")
    lines.append(f"-- {n - d + 1} dual constraints, each a sum of {n} integer products")
    check_line = f"theorem intCheck_{name} : intCheck {n} {d} {name}Int {name}Den = true := by decide"
    if len(check_line) <= 100:
        lines.append(check_line)
    else:
        lines.append(check_line[: -len(" decide")])
        lines.append("  decide")
    lines.append("")
    lines.append(f"theorem dualCert_{name} : DualCert {n} 2 {d} {name} :=")
    lines.append(f"  dualCert_of_intCheck intCheck_{name}")
    lines.append("")
    lines.append(f"theorem A_{n}_{q}_{d}_le : A {n} {q} {d} ≤ {B} :=")
    lines.append(f"  A_le_of_intCertLt (p := {name}Int) (D := {name}Den) (by norm_num) "
                 f"intCheck_{name}")
    lines.append("    (by decide)")
    lines.append("")
    lines.append(f"#guard dualCheck {n} {q} {d} {name}")
    lines.append(f"#guard bound {n} {q} {name} == {bound}")
    print("\n".join(lines))
    print()

if __name__ == "__main__":
    if len(sys.argv) >= 3:
        # usage: delsarte_lp.py n d [q]   (q defaults to 2)
        q = int(sys.argv[3]) if len(sys.argv) >= 4 else 2
        report(int(sys.argv[1]), int(sys.argv[2]), q)
    else:
        for n, d in ((5, 3), (17, 8), (23, 7), (24, 10), (13, 5)):
            report(n, d)
            print()


def wrap_ints(nums, width=96, indent="   "):
    """Format a list of integers as Lean source, wrapped to `width` columns."""
    out, line = [], "["
    for i, x in enumerate(nums):
        piece = str(x) + (", " if i < len(nums) - 1 else "]")
        if len(line) + len(piece) > width:
            out.append(line.rstrip())
            line = indent + piece
        else:
            line += piece
    out.append(line)
    return "\n".join(out)


def wrap_doc(text, width=95):
    """Wrap one docstring into Lean `/-- ... -/` lines."""
    words, lines, cur = text.split(), [], "/--"
    for w in words:
        if len(cur) + 1 + len(w) > width:
            lines.append(cur)
            cur = w
        else:
            cur = cur + " " + w
    lines.append(cur + " -/")
    return lines


def emit_lean(n, d, q=2):
    """Print the Lean declarations and the .cert body for one certificate.

    Transcribing a dozen certificates by hand is a good way to introduce a typo
    that no theorem would catch, since a wrong `y` simply fails to be feasible --
    or worse, is feasible and proves a different bound.  So the text is generated
    here and re-checked by Lean; `Delsarte/Certificate/Files.lean` then pins the
    `.cert` file to the Lean definition.
    """
    K, dists, opt, x, y = solve(n, d, q)
    ok, bound, slacks = check(n, d, K, y, q)
    assert ok, "the candidate failed its own re-verification"
    assert bound.denominator == 1, f"bound {bound} is not an integer"
    name = f"cert{n}_{d}"
    den = lcm(*[v.denominator for v in y])
    p = [0] + [int(v * den) for v in y]
    assert all(v >= 0 for v in p), "a scaled coefficient came out negative"
    for i in range(d, n + 1):
        slack = -sum(p[k] * K[k][i] for k in range(n + 1))
        assert den <= slack, f"the scaled certificate fails at distance {i}"
    rats = ", ".join(f"`y {k} = {y[k-1]}`" for k in range(1, n + 1) if y[k - 1] != 0)
    lines = []
    lines.append(f"/-- Certificate for `n = {n}`, `d = {d}`, scaled by its common denominator")
    lines.append(f"`{den}`. Index `0` is unused. -/")
    lines.append(f"def {name}Int : List ℤ :=")
    lines.append("  " + wrap_ints(p))
    lines.append("")
    lines.append(f"/-- The common denominator of `{name}`. -/")
    lines.append(f"def {name}Den : ℤ := {den}")
    lines.append("")
    lines.extend(wrap_doc(f"The same certificate as rationals: {rats}. Derived from the "
                          "integer form, so the two cannot drift apart."))
    lines.append(f"def {name} : ℕ → ℚ := ratOfInt {name}Int {name}Den")
    lines.append("")
    lines.append(f"-- {n - d + 1} dual constraints, each a sum of {n} integer products")
    check_line = f"theorem intCheck_{name} : intCheck {n} {d} {name}Int {name}Den = true := by decide"
    if len(check_line) <= 100:
        lines.append(check_line)
    else:
        lines.append(check_line[: -len(" decide")])
        lines.append("  decide")
    lines.append("")
    lines.append(f"theorem dualCert_{name} : DualCert {n} 2 {d} {name} :=")
    lines.append(f"  dualCert_of_intCheck intCheck_{name}")
    lines.append("")
    lines.append(f"theorem A_{n}_{q}_{d}_le : A {n} {q} {d} ≤ {bound} :=")
    lines.append(f"  A_le_of_intCert (p := {name}Int) (D := {name}Den) (by norm_num) "
                 f"intCheck_{name}")
    lines.append("    (by decide)")
    lines.append("")
    lines.append(f"#guard dualCheck {n} {q} {d} {name}")
    lines.append(f"#guard bound {n} {q} {name} == {bound}")
    print("\n".join(lines))
    print()
    cert = [f"n {n}", f"q {q}", f"d {d}", "y " + " ".join(str(v) for v in y)]
    print("-- .cert body:")
    print("\n".join("-- " + l for l in cert))
    print()

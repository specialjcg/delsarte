#!/usr/bin/env python3
"""Replay the averaging identity that §3 of `THEOREM1.md` needs, without `M̃`.

`Delsarte/Hamming/THEOREM1.md` §6 names the `Sₙ`-invariance of

    M̃ = (1/n!) · Σ_σ P_σ M P_σᵀ

as unproved, and §3 consumes that invariance to write `u_iᵀ M̃ u_j` as
`Σ_t x^t_{i,j} · (Σ_{|v|=i,|w|=j,|v∧w|=t} c(v) c(w))`.  Invariance of a matrix
under a group is the expensive object; the identity below avoids naming it by
averaging the *vector* instead:

    Σ_σ (P_σ u_i)ᵀ M (P_σ u_j)
      = Σ_{v,w} c(v) c(w) · ( Σ_σ M[σv, σw] )
      = Σ_t ( Σ_σ M over the orbit (i,j,t) ) · gram(i, j, t)
      = n! · Σ_t x^t_{i,j} · 2^k · beta^t_{i,j,k} .

`Σ_σ M[σv,σw]` is constant on the orbit of `(|v|,|w|,|v∧w|)` by plain
relabelling, and equals `n!` times the orbit average `x^t_{i,j}` by definition of
that average.  Nothing here asks a matrix to be invariant.  The left side is
nonnegative term by term -- each term is `aᵀ M a` at `a = P_σ u_j` -- which is
`sum_smul_quadForm_nonneg` in `Delsarte/Hamming/Positivity.lean` with every
weight 1, and the inner sum is `gram_eq_pow_mul_beta` in
`Delsarte/Hamming/Terwilliger.lean`.  Both are already proved in Lean.  This
script is the numerical evidence that the two fit together; it is a check, not a
derivation, and Theorem 1 stays unproved.

Standard library only, exact arithmetic on Python ints and `Fraction`, and no
cvxpy: it runs in CI beside `check_beta.py`, whose `beta()` it imports rather
than copying.  `x^t_{i,j}` is likewise *measured* off `M`, summed over the orbit
and divided by the imported `mult()`, never evaluated from a closed form -- a
check that computed both sides from formulas would compare a formula with
itself.

`n!` permutations are enumerated in full, so `n <= 8`.  `n = 8` alone costs 37 of
the 44 seconds a full sweep takes, twelve times the two sibling checks put
together, and it exercises no `k` and no shape that `n = 7` does not: `(8, 2)` is
`(7, 2)` on a wider cube.  It is therefore behind `--full` and CI runs without it.
That is a statement about cost, not about confidence -- it passes.

Three guards, because a checker that never rejects has proved nothing:

  1. A non-disjoint pairing must break the identity.  `c(v)` is built from
     disjoint pairs and §4 splits the coordinates on exactly that hypothesis, so
     dropping it must be visible.
  2. Negating `beta` must break it.  Otherwise the right side is not being read.
  3. Live counts.  A case where both sides vanish proves nothing, so the pass
     requires the identity to have been nonzero somewhere.

Exit status is 1 if any case disagrees, if either negative control fails to
fire, or if no case was live.
"""

from fractions import Fraction
from itertools import combinations, permutations
from math import factorial
from pathlib import Path
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from schrijver_algebra import beta, mult, realisable  # noqa: E402

def weight(v):
    return bin(v).count("1")


def coeff(v, pairs):
    """`c(v) = prod_l ([a_l in v] - [b_l in v])`, as a bitmask predicate."""
    p = 1
    for a, b in pairs:
        p *= ((v >> a) & 1) - ((v >> b) & 1)
        if p == 0:
            return 0
    return p


def matrix(n, S):
    """`M[v,w] = |{z in S : z^v in S, z^w in S}|`, the (19) matrix of §1."""
    words = range(1 << n)
    return {(v, w): sum(1 for z in S if (z ^ v) in S and (z ^ w) in S)
            for v in words for w in words}


def orbit_average(n, M, i, j, t):
    """`x^t_{i,j}` measured off `M`: the orbit sum over the orbit size.

    The orbit size is the imported `mult()`, which is what the program's
    normalization is defined by; it is not recomputed here.
    """
    tot = sum(M[(v, w)] for v in range(1 << n) for w in range(1 << n)
              if weight(v) == i and weight(w) == j and weight(v & w) == t)
    m = mult(n, i, j, t)
    return Fraction(tot, m) if m else Fraction(0)


def permuted(v, perm, n):
    out = 0
    for c in range(n):
        if (v >> c) & 1:
            out |= 1 << perm[c]
    return out


def left(n, M, pairs, i, j):
    """`Σ_σ (P_σ u_i)ᵀ M (P_σ u_j)`, by enumerating all `n!` permutations."""
    ui = [(v, coeff(v, pairs)) for v in range(1 << n)
          if weight(v) == i and coeff(v, pairs)]
    uj = [(w, coeff(w, pairs)) for w in range(1 << n)
          if weight(w) == j and coeff(w, pairs)]
    tot = 0
    for perm in permutations(range(n)):
        pv = [(permuted(v, perm, n), c) for v, c in ui]
        pw = [(permuted(w, perm, n), c) for w, c in uj]
        tot += sum(cv * cw * M[(a, b)] for a, cv in pv for b, cw in pw)
    return Fraction(tot)


def right(n, M, k, i, j, sign=+1):
    """`n! · Σ_t x^t_{i,j} · 2^k · beta^t_{i,j,k}`, the §3 shape."""
    tot = Fraction(0)
    for t in range(n + 1):
        if not realisable(n, i, j, t):
            continue
        x = orbit_average(n, M, i, j, t)
        tot += x * (2 ** k) * sign * beta(n, i, j, k, t)
    return factorial(n) * tot


def pairs_of(k):
    return [(2 * l, 2 * l + 1) for l in range(k)]


def draw(n, seed, complement):
    """A random code, or its complement: §1 sums over an arbitrary set."""
    rng = random.Random(seed)
    C = {w for w in range(1 << n) if rng.random() < 0.5}
    return [w for w in range(1 << n) if (w in C) != complement]


def run(n, k, seed, complement, pairs=None, sign=+1):
    """Return (agree, disagree, live) over the block's index range."""
    pairs = pairs_of(k) if pairs is None else pairs
    M = matrix(n, draw(n, seed, complement))
    agree = disagree = live = 0
    for i in range(k, n - k + 1):
        for j in range(k, n - k + 1):
            lhs = left(n, M, pairs, i, j)
            rhs = right(n, M, k, i, j, sign=sign)
            if lhs == rhs:
                agree += 1
            else:
                disagree += 1
            if lhs != 0:
                live += 1
    return agree, disagree, live


CASES = [(6, 2, 7, False), (6, 2, 11, True), (6, 1, 3, False), (6, 1, 5, True),
         (7, 2, 13, False), (7, 3, 2, False)]

#: `n = 8` is 37 of the 44 seconds and adds no shape; `--full` only.
SLOW_CASES = [(8, 2, 17, False)]


def check_identity(full=False):
    ok, total_live = True, 0
    for n, k, seed, comp in CASES + (SLOW_CASES if full else []):
        agree, disagree, live = run(n, k, seed, comp)
        tag = "complement" if comp else "code      "
        line(disagree == 0, f"n={n} k={k} S={tag} seed={seed:<3} "
                            f"{agree} agree, {disagree} differ, {live} live")
        ok &= disagree == 0
        total_live += live
    if total_live == 0:
        line(False, "every case was two zeros agreeing")
        ok = False
    line(ok, f"identity holds on every case, {total_live} live")
    return ok


def check_controls():
    # A pairing sharing a coordinate: §4 splits on disjointness, so it must show.
    _, disagree, _ = run(6, 2, 7, False, pairs=[(0, 1), (1, 2)])
    line(disagree > 0, f"negative control: non-disjoint pairing rejected "
                       f"({disagree} mismatches)")
    # Negating beta: the right side must actually be read.
    _, neg, _ = run(6, 2, 7, False, sign=-1)
    line(neg > 0, f"negative control: negated beta rejected ({neg} mismatches)")
    return disagree > 0 and neg > 0


def line(ok, text):
    print(f"[{'ok' if ok else 'FAIL'}] {text}")


def main():
    full = "--full" in sys.argv
    ok = check_identity(full)
    ok &= check_controls()
    if not full:
        print("[skip] n=8 (37s, no new shape); rerun with --full")
    print("orbit: all passed" if ok else "orbit: FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

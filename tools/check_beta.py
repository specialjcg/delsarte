#!/usr/bin/env python3
"""Replay the two identities Schrijver's Theorem 1 rests on.

Imports the same `beta()` that `schrijver_sdp.py` measures with and that
`schrijver_cert.py` writes certificates from, so a drift between the formula and
the shipped data shows up here.  That is the whole reason this file does not
carry its own copy of it -- except for (7), which it must, since (7) is what
`beta()` is being compared against.

Standard library only, and no cvxpy: it runs in CI beside
`crosscheck_brouwer.py`.

What is checked, and nothing beyond it:

  (a) `beta()` computes (7) exactly, as Python ints, for every (n, i, j, k, t)
      with n <= 24.  That covers every size the repository uses: n = 19 for the
      shipped certificate, n = 22 for the controls, n = 24 for the largest table
      row.  It is a check, not a proof; the identity (7) = (7') is not derived.

  (b) The Gram identity

          sum_{|v|=i, |w|=j, |v^w|=t} c(v) c(w) = 2^k beta^t_{i,j,k},
          c(v) = prod_l ([a_l in v] - [b_l in v])

      over k disjoint pairs, by brute force over all 2^n subsets.  This is the
      step that makes the blocks' positivity a sum of squares, so it is the step
      a Lean proof would have to reproduce.  Brute force stops where enumeration
      does, at n = 10 here; nothing says it holds beyond.

  (c) Negative controls, without which (b) means little.  A different disjoint
      pairing must give the same constant -- the identity cannot depend on which
      coordinates are picked.  A *symmetric* coefficient, `+` where c has `-`,
      must fail; if it passed, the test would be matching anything put in front
      of it.
"""

from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from schrijver_algebra import beta, realisable  # noqa: E402

NMAX_CLOSED = 24
NMAX_GRAM = 10


def C(a, b):
    return comb(a, b) if 0 <= b <= a else 0


def schrijver_7(n, i, j, k, t):
    """Equation (7) verbatim.  The one copy of a formula this file is allowed."""
    return sum((1 if (u - t) % 2 == 0 else -1) * C(u, t) * C(n - 2 * k, u - k)
               * C(n - k - u, i - u) * C(n - k - u, j - u)
               for u in range(n + 1))


def sizes(n):
    for k in range(n // 2 + 1):
        for i in range(k, n - k + 1):
            for j in range(k, n - k + 1):
                for t in range(n + 1):
                    if realisable(n, i, j, t):
                        yield k, i, j, t


def check_closed():
    bad = tot = 0
    for n in range(1, NMAX_CLOSED + 1):
        for k, i, j, t in sizes(n):
            tot += 1
            b = beta(n, i, j, k, t)
            if not isinstance(b, int) or b != schrijver_7(n, i, j, k, t):
                bad += 1
    line(bad == 0, f"beta is (7), in ints, n <= {NMAX_CLOSED}: "
                   f"{tot} triples, {bad} differ")
    return bad == 0


def coeff(v, pairs, sign):
    p = 1
    for a, b in pairs:
        p *= (1 if a in v else 0) + sign * (1 if b in v else 0)
        if p == 0:
            return 0
    return p


def ratio(n, pairs, sign=-1):
    """The constant r with beta = r * (Gram sum), or None if there is none."""
    k = len(pairs)
    by = {}
    for i in range(n + 1):
        acc = []
        for s in combinations(range(n), i):
            v = frozenset(s)
            c = coeff(v, pairs, sign)
            if c:
                acc.append((v, c))
        by[i] = acc

    found = set()
    for i in range(k, n - k + 1):
        for j in range(k, n - k + 1):
            bucket = {}
            for v, cv in by[i]:
                for w, cw in by[j]:
                    s = len(v & w)
                    bucket[s] = bucket.get(s, 0) + cv * cw
            for t in range(n + 1):
                if not realisable(n, i, j, t):
                    continue
                b, g = beta(n, i, j, k, t), bucket.get(t, 0)
                if b == 0 and g == 0:
                    continue
                if b == 0 or g == 0:
                    return None
                found.add(Fraction(b, g))
    return found.pop() if len(found) == 1 else None


def pairs_of(k):
    return [(2 * l, 2 * l + 1) for l in range(k)]


def check_gram():
    good = True
    for n in range(4, NMAX_GRAM + 1):
        for k in range(n // 2 + 1):
            want = Fraction(1, 2 ** k)
            got = ratio(n, pairs_of(k))
            good &= got == want
            if got != want:
                line(False, f"Gram n={n} k={k}: beta / sum = {got}, want {want}")
    line(good, f"Gram identity, constant 2^-k, 4 <= n <= {NMAX_GRAM}, every k")
    return good


def check_controls():
    # Another disjoint pairing: the constant must not move.
    same = ratio(8, [(0, 5), (2, 7)]) == Fraction(1, 4)
    line(same, "negative control: a different pairing gives the same constant")
    # `+` where the coefficient has `-`: must not reproduce beta.
    broken = ratio(8, pairs_of(2), sign=+1) is None
    line(broken, "negative control: a symmetric coefficient is rejected")
    return same and broken


def line(ok, text):
    print(f"[{'ok' if ok else 'FAIL'}] {text}")


def main():
    ok = check_closed()
    ok &= check_gram()
    ok &= check_controls()
    print("beta: all passed" if ok else "beta: FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

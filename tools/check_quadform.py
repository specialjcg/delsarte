#!/usr/bin/env python3
"""Check the sum-of-squares identity behind Schrijver's blocks.

Section 1 of `Delsarte/Hamming/THEOREM1.md`, formalized in
`Delsarte/Hamming/Positivity.lean` as `quadForm_eq_sum_sq`:

    sum_{v,w} a_v a_w M_{v,w}  =  sum_{z in S} ( sum_v [z+v in C] a_v )^2,
    M_{v,w} = sum_{z in S} [z+v in C] [z+w in C].

Words are bitmasks, so addition on F_2^n is XOR.  Arithmetic is exact: the
weights are `Fraction`, never floats.  This is a check, not a derivation; the
proof for all `n` is the Lean one.

Two negative controls, because a checker that never rejects has proved nothing:

  1. Bumping one entry of `M` must break the identity.  The weights are drawn
     away from zero on purpose: the perturbation shifts the total by
     `a[v0] * a[w0]`, so a zero weight would let the control misfire silently.
  2. An arbitrary symmetric matrix must be able to drive the form negative.
     Otherwise nonnegativity would be vacuous rather than a consequence of the
     Gram structure.  Roughly half the draws should go negative; zero would mean
     the control is asleep.

A third guard counts how often the left side is nonzero, so that a pass cannot
be two zeros agreeing.

Exit status is 1 if any identity fails, if either negative control never fires,
or if the left side is always zero.
"""

import random
import sys
from fractions import Fraction

NONZERO = [x for x in range(-4, 5) if x != 0]


def run(n, trials, seed=0):
    """Return (agree, disagree, live, perturbation_caught, went_negative)."""
    rng = random.Random(seed)
    words = list(range(1 << n))
    agree = disagree = live = 0
    caught = negative = 0

    for _ in range(trials):
        C = {w for w in words if rng.random() < 0.5}
        S = [w for w in words if rng.random() < 0.5]
        a = {v: Fraction(rng.choice(NONZERO)) for v in words}

        M = {(v, w): sum(1 for z in S if (z ^ v) in C and (z ^ w) in C)
             for v in words for w in words}
        lhs = sum(a[v] * a[w] * M[(v, w)] for v in words for w in words)
        rhs = sum(sum((1 if (z ^ v) in C else 0) * a[v] for v in words) ** 2
                  for z in S)

        if lhs == rhs:
            agree += 1
        else:
            disagree += 1
        if lhs != 0:
            live += 1
        if rhs < 0:
            raise SystemExit("rhs negative: a sum of squares cannot be")

        v0, w0 = rng.choice(words), rng.choice(words)
        bad = dict(M)
        bad[(v0, w0)] += 1
        if sum(a[v] * a[w] * bad[(v, w)] for v in words for w in words) != rhs:
            caught += 1

        R = {}
        for v in words:
            for w in words:
                R[(v, w)] = R[(w, v)] if (w, v) in R else Fraction(rng.randint(-3, 3))
        if sum(a[v] * a[w] * R[(v, w)] for v in words for w in words) < 0:
            negative += 1

    return agree, disagree, live, caught, negative


def main():
    trials = 40
    ok = True
    for n in (2, 3, 4):
        agree, disagree, live, caught, negative = run(n, trials, seed=n)
        print(f"n={n}: agree={agree} disagree={disagree} live={live}/{trials} "
              f"perturbation_caught={caught}/{trials} "
              f"arbitrary_M_negative={negative}/{trials}")
        if disagree:
            print(f"  [fail] identity broke on {disagree} draws")
            ok = False
        if caught != trials:
            print(f"  [fail] control 1 misfired {trials - caught} times")
            ok = False
        if negative == 0:
            print("  [fail] control 2 never drove the form negative")
            ok = False
        if live == 0:
            print("  [fail] the left side was always zero")
            ok = False
    print("controls: all passed" if ok else "controls: FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

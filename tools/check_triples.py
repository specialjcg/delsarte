#!/usr/bin/env python3
"""Replay the bridge of `Delsarte/Hamming/Orbit.lean` against bitmask arithmetic.

`lambdaT_eq_orbit_sum` says the triple count of `Delsarte/Hamming/Triples.lean`
is the sum of the matrix of (19) over an orbit:

    Σ_{(v,w) ∈ orbit(i,j,t)} gramMat C C v w = λ^t_{i,j}(C) .

That theorem holds for every `n` and needs no replay to be believed.  What it
does *not* do is pin down what `interDist` means, and that is what this script is
for.  Both sides of the identity are written with the same `interDist`, so
replacing that definition by any other function of three words leaves the theorem
true and its proof unchanged -- the fibration argument never looks inside it.  A
`interDist` that counted the wrong intersection would therefore prove the same
theorem about the wrong numbers, and nothing in Lean would notice.

So the check below does not replay the Lean proof.  It recomputes both sides from
an independent implementation, on plain machine integers, where the three
statistics are written the way Schrijver's paper writes them:

    |X △ Y| = popcount(X ^ Y),
    |X △ Z| = popcount(X ^ Z),
    |(X △ Y) ∩ (X △ Z)| = popcount((X ^ Y) & (X ^ Z)),

and the matrix is `M[v,w] = |{z ∈ C : z^v ∈ C, z^w ∈ C}|`.  Nothing is imported
from the Lean side and nothing from `schrijver_algebra.py`: an agreement between
two spellings of the same mistake is not evidence.  If the Lean `interDist` ever
drifts from `(X △ Y) ∩ (X △ Z)`, the two sides part company here.

This is cheap -- no permutations, unlike `tools/check_orbit.py`, which replays the
*averaging* identity of §2 and pays `n!` for it.  The largest case is the
even-weight code of length 6, which is the shape issue #44's reduction cares
about; the rest are random subsets and their complements, because §1 sums over an
arbitrary set and a code with structure could hide an error that a generic one
does not.

Two guards, because a checker that never rejects has proved nothing.  Both
corrupt the *orbit side only*.  Corrupting both sides at once would leave the
identity true and the guard silent, for the same reason the Lean theorem does not
pin the statistic down: the fibration never looks inside it.  A guard written the
obvious way -- one `overlap` argument threaded through both sides -- passes
vacuously, which is the trap this file exists to avoid falling into.

  1. Overlap by `|v ∨ w|` instead of `|v ∧ w|` on the orbit side must break the
     identity.  This is the way the statistic is most likely to be misread.
  2. An overlap blind to one coordinate must break it.  This is the failure mode
     `Orbit.lean` names for its own translation lemmas -- one that dropped a
     coordinate -- transposed to the statistic itself.

And a liveness requirement: a case where both sides vanish proves nothing, so the
pass demands that the counts were nonzero somewhere.

Exit status is 1 if any case disagrees, if either guard fails to fire, or if no
case was live.
"""

import random
import sys


def wt(v):
    return bin(v).count("1")


def triple_counts(C, overlap):
    """Every `λ^t_{i,j}` in one pass over `C³`, keyed by `(i, j, t)`."""
    out = {}
    for X in C:
        for Y in C:
            d1 = X ^ Y
            i = wt(d1)
            for Z in C:
                d2 = X ^ Z
                key = (i, wt(d2), wt(overlap(d1, d2)))
                out[key] = out.get(key, 0) + 1
    return out


def orbit_sums(n, C, overlap):
    """Every orbit sum of `M[v,w] = |{z ∈ C : z^v ∈ C, z^w ∈ C}|`, same keys."""
    S = set(C)
    out = {}
    for v in range(1 << n):
        iv = wt(v)
        for w in range(1 << n):
            m = sum(1 for z in S if (z ^ v) in S and (z ^ w) in S)
            if m:
                key = (iv, wt(w), wt(overlap(v, w)))
                out[key] = out.get(key, 0) + m
    return out


#: The intended statistic, and the two mistakes the guards substitute for it.
GOOD = lambda a, b: a & b                       # noqa: E731
UNION = lambda a, b: a | b                      # noqa: E731
BLIND = lambda a, b: (a & b) & ~1               # noqa: E731


def draw(n, seed, kind):
    """A random subset, its complement, or the even-weight code of length `n`."""
    if kind == "even":
        return [w for w in range(1 << n) if wt(w) % 2 == 0]
    rng = random.Random(seed)
    inside = {w for w in range(1 << n) if rng.random() < 0.5}
    return [w for w in range(1 << n) if (w in inside) != (kind == "complement")]


def run(n, seed, kind, orb_overlap=GOOD):
    """Return (agree, disagree, live) over every key either side produces.

    The triple side always uses the intended statistic; only the orbit side is
    ever corrupted, so that a guard compares two implementations rather than one
    implementation with itself.
    """
    C = draw(n, seed, kind)
    lam = triple_counts(C, GOOD)
    orb = orbit_sums(n, C, orb_overlap)
    agree = disagree = live = 0
    for key in set(lam) | set(orb):
        a, b = lam.get(key, 0), orb.get(key, 0)
        if a == b:
            agree += 1
        else:
            disagree += 1
        if a:
            live += 1
    return agree, disagree, live


CASES = [(3, 1, "random"), (4, 2, "random"), (4, 7, "complement"),
         (5, 3, "random"), (5, 11, "complement"), (6, 0, "even")]


def check_identity():
    ok, total_live = True, 0
    for n, seed, kind in CASES:
        agree, disagree, live = run(n, seed, kind)
        line(disagree == 0, f"n={n} C={kind:<10} seed={seed:<3} "
                            f"{agree} agree, {disagree} differ, {live} live")
        ok &= disagree == 0
        total_live += live
    if total_live == 0:
        line(False, "every case was two zeros agreeing")
        ok = False
    line(ok, f"lambdaT == orbit sum on every case, {total_live} live cells")
    return ok


def check_guards():
    _, union, _ = run(5, 3, "random", orb_overlap=UNION)
    line(union > 0, f"negative control: |v OR w| for |v AND w| rejected "
                    f"({union} mismatches)")
    _, blind, _ = run(5, 3, "random", orb_overlap=BLIND)
    line(blind > 0, f"negative control: overlap blind to one coordinate "
                    f"rejected ({blind} mismatches)")
    return union > 0 and blind > 0


def line(ok, text):
    print(f"[{'ok' if ok else 'FAIL'}] {text}")


def main():
    ok = check_identity()
    ok &= check_guards()
    print("triples: all passed" if ok else "triples: FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

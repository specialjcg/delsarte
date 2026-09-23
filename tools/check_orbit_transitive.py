#!/usr/bin/env python3
"""Check the half of orbit constancy that `Delsarte/Hamming/Orbit.lean` does not prove.

§6 of `Delsarte/Hamming/THEOREM1.md` needs `Σ_σ M[σv, σw]` to be constant on the
class of pairs with a given `(|v|, |w|, |v ∧ w|)`. That splits in two:

  * invariance under the action -- `orbitSum_permWord` in `Orbit.lean`, proved;
  * transitivity: the class *is* one orbit of `Sₙ`, so that invariance transfers
    from "same orbit" to "same statistics". Not proved anywhere.

Only the second is checked here, since the first is a reindexing of a sum over a
group and a numerical replay of it would test nothing. Two facts are measured:

    every statistic class is a single `Sₙ`-orbit,
    its size is  mult(n,i,j,t) = n! / ( t! (i-t)! (j-t)! (n-i-j+t)! ).

The second is what `Delsarte/Hamming/Terwilliger.lean` defines `mult` to be, by a
cardinality rather than by this formula; the formula is recomputed here from
factorials so that agreeing with it is evidence rather than a tautology. Nothing
is imported from the Lean side or from `schrijver_algebra.py`.

The guards weaken the *group* or the *partition*, never both, and never the thing
being compared against: a corruption applied to both sides at once would pass
vacuously. That trap is spelled out in `tools/check_triples.py`, which was written
after falling into it.
"""

from itertools import permutations
from math import factorial
import sys


def wt(v):
    return bin(v).count("1")


def permute(v, p, n):
    """Relabel the coordinates of the bitmask `v` along `p`."""
    out = 0
    for c in range(n):
        if (v >> c) & 1:
            out |= 1 << p[c]
    return out


STAT = lambda v, w: (wt(v), wt(w), wt(v & w))
BLIND = lambda v, w: (wt(v), wt(w))


def classes(n, stat):
    """Partition every pair of words by the statistic."""
    out = {}
    for v in range(1 << n):
        for w in range(1 << n):
            out.setdefault(stat(v, w), set()).add((v, w))
    return out


def group(n, kind):
    """All of `Sₙ`, or the cyclic shifts -- a proper subgroup for `n > 2`."""
    if kind == "sym":
        return list(permutations(range(n)))
    return [tuple((c + s) % n for c in range(n)) for s in range(n)]


def orbit_of(n, pair, G):
    v, w = pair
    return {(permute(v, p, n), permute(w, p, n)) for p in G}


def transitive(n, stat=STAT, kind="sym"):
    """Return (classes, how many are a single orbit) under the given group."""
    G = group(n, kind)
    cls = classes(n, stat)
    whole = 0
    for S in cls.values():
        rep = min(S)
        if orbit_of(n, rep, G) == S:
            whole += 1
    return len(cls), whole


def mult(n, i, j, t):
    """The four cells of a pair: `v∧w`, `v\\w`, `w\\v`, `(v∪w)ᶜ`."""
    cells = (t, i - t, j - t, n - i - j + t)
    if min(cells) < 0:
        return 0
    out = factorial(n)
    for c in cells:
        out //= factorial(c)
    return out


def sizes(n):
    """Return (classes, mismatches against the factorial formula)."""
    cls = classes(n, STAT)
    bad = [(k, len(S), mult(n, *k)) for k, S in cls.items() if len(S) != mult(n, *k)]
    return len(cls), bad


def line(ok, text):
    print(f"[{'ok' if ok else 'FAIL'}] {text}")
    return ok


def main():
    good = True
    total = 0

    for n in range(2, 7):
        cls, whole = transitive(n)
        total += cls
        good &= line(whole == cls,
                     f"n={n}: {whole}/{cls} statistic classes are a single Sn-orbit")

    for n in range(2, 7):
        cls, bad = sizes(n)
        good &= line(not bad, f"n={n}: {cls} class sizes match mult(n,i,j,t)"
                              + (f", {len(bad)} wrong: {bad[:3]}" if bad else ""))

    # Guard 1: a proper subgroup must fail to be transitive on the classes. If it
    # did not, the check above would be passing on something weaker than `Sₙ`.
    cls, whole = transitive(4, kind="cyclic")
    good &= line(whole < cls,
                 f"negative control: cyclic shifts on n=4 leave {cls - whole}"
                 f"/{cls} classes split")

    # Guard 2: forgetting the overlap must merge distinct orbits. If it did not,
    # the third statistic would be carrying no information.
    cls, whole = transitive(4, stat=BLIND)
    good &= line(whole < cls,
                 f"negative control: dropping |v AND w| on n=4 leaves {cls - whole}"
                 f"/{cls} classes split")

    good &= line(total > 0, f"{total} classes examined in all")

    print("orbit transitivity: " + ("all passed" if good else "FAILED"))
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())

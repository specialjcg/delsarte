"""Read the bounds on `A(n, q, d)` out of the Lean sources.

`tools/crosscheck_brouwer.py` used to carry its list of claims by hand. A hand
list is wrong in one direction that matters: it cannot report a bound the
repository proves and nobody transcribed, so the cross-check stayed silent about
exactly the cells where silence was worth something. The list is derived here
instead, from the statements themselves.

What counts as a claim, deliberately narrowly:

  * a `theorem` or `lemma` whose statement, before `:=`, is exactly
    `A n q d ≤ B` or `A n q d = B`, possibly with the cast `(A n q d : ℚ)`;
  * with **no binders** between the name and the `:`. A declaration that takes a
    hypothesis proves something conditional, and
    `Delsarte/SDP/Schrijver.lean`'s `A_19_6_le_of_relaxation` is precisely such a
    case: it is not a bound this repository has proved, and must not be reported
    as one.

Anything subtler than that shape is not recognised, on purpose -- a parser that
guesses would eventually promote a conditional statement to a claim, which is the
failure this file exists to prevent. `--check` prints what the old hand list and
this extraction disagree about.

Usage:

    lean_claims.py            list the claims, one per line
    lean_claims.py --python   emit them as a Python literal
    lean_claims.py --check    diff against a hand list on stdin, as a module
"""

from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCES = ROOT / "Delsarte"

# `A n q d ≤ B`, `A n q d = B`, or the same wrapped in a cast to ℚ.
BOUND = re.compile(
    r"\(?\s*A\s+(\d+)\s+(\d+)\s+(\d+)\s*(?::\s*ℚ\s*\))?\s*(≤|=)\s*(\d+)\s*$"
)

# The start of a declaration, at column zero only: an indented `theorem` is
# inside a proof, and a `have` is not a claim at all.
DECL = re.compile(r"^(?:theorem|lemma)\s+(\S+)\s*(.*)$")


def statement(lines, i):
    """Return the text of the declaration starting at `lines[i]`, up to `:=`.

    Statements wrap, so this joins continuation lines; it stops at `:=` or at the
    next declaration, whichever comes first.
    """
    out = []
    for line in lines[i:]:
        if out and re.match(r"^\S", line) and DECL.match(line) is None and ":=" not in line:
            break
        head, sep, _ = line.partition(":=")
        out.append(head)
        if sep:
            break
    return " ".join(out)


def claims(root=SOURCES):
    """Return `(n, q, d, bound, where, kind)` for every unconditional bound."""
    found = []
    for path in sorted(root.rglob("*.lean")):
        lines = path.read_text().splitlines()
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if m is None:
                continue
            rest = statement(lines, i)[len("theorem"):].lstrip()
            name, sep, body = rest.partition(":")
            if not sep or name.strip() != m.group(1):
                # Binders sit between the name and the colon: conditional, skip.
                continue
            b = BOUND.match(body.strip())
            if b is None:
                continue
            n, q, d, rel, bound = b.groups()
            where = f"{path.relative_to(ROOT / 'Delsarte')}:{i + 1}"
            found.append((int(n), int(q), int(d), int(bound), where, rel))
    return found


def binary(root=SOURCES):
    """The binary claims, in the `(n, d, bound, where)` shape the cross-check wants."""
    return [(n, d, b, w) for n, q, d, b, w, _ in claims(root) if q == 2]


# The hand list exactly as it stood in `crosscheck_brouwer.py` before extraction
# replaced it, frozen here on purpose. Deriving the claims removes one failure --
# a proved bound nobody transcribed -- and introduces another: a parser that
# silently stops recognising a declaration would shrink the list, and every
# cross-check downstream would go on passing, quietly checking less. So the
# extraction has to keep reproducing these thirty-three cells. Entries are only
# ever added here when a bound is deliberately retired from the repository.
BASELINE = [
    (5, 3, 4), (5, 3, 6), (13, 5, 64), (8, 4, 16), (12, 6, 24), (14, 5, 128),
    (24, 8, 4096), (23, 7, 4096), (6, 3, 8), (10, 5, 12), (12, 5, 40), (15, 6, 128),
    (7, 4, 8), (11, 5, 24), (13, 3, 512), (15, 5, 256), (16, 4, 2048), (16, 6, 256),
    (16, 8, 32), (21, 7, 1024), (22, 7, 2048), (28, 12, 288), (18, 4, 6553),
    (23, 4, 174762), (26, 4, 1198372), (19, 4, 13106), (20, 4, 26212),
    (24, 4, 349524), (27, 4, 2396744), (28, 4, 4793488), (26, 5, 163840),
    (31, 3, 67108864), (32, 4, 67108864),
]

# Three statements whose shape the parser has to keep handling: a cast to ℚ, an
# equality rather than an inequality, and a non-binary alphabet. Each was a real
# near-miss while this file was written.
SHAPES = [(5, 2, 3, 6), (24, 2, 8, 4096), (11, 3, 5, 729)]


def check():
    """Check the extraction still covers the frozen baseline, and report what is new."""
    shapes = {(n, q, d, b) for n, q, d, b, _, _ in claims()}
    for want in SHAPES:
        if want not in shapes:
            print(f"  PARSER    A{want[:3]} <= {want[3]} is no longer recognised")
            return 1

    hand = set(BASELINE)
    auto = {(n, d, b) for n, d, b, _ in binary()}
    missing = sorted(hand - auto)
    extra = sorted(auto - hand)
    print(f"hand list: {len(hand)} cells   extracted: {len(auto)} cells")
    for n, d, b in missing:
        print(f"  MISSING   A({n},{d}) <= {b} is in the hand list, not extracted")
    for n, d, b in extra:
        print(f"  NEW       A({n},{d}) <= {b} is proved in Lean, absent from the hand list")
    ternary = [c for c in claims() if c[1] != 2]
    for n, q, d, b, w, _ in ternary:
        print(f"  NON BINARY A({n},{q},{d}) <= {b}  {w} -- outside Brouwer's binary table")
    return 1 if missing else 0


def main(argv):
    if "--check" in argv:
        return check()
    rows = claims()
    if "--python" in argv:
        print("CLAIMS = [")
        for n, d, b, w in binary():
            print(f"    ({n}, {d}, {b}, {w!r}),")
        print("]")
        return 0
    for n, q, d, b, w, rel in rows:
        print(f"A({n},{q},{d}) {rel} {b:<12} {w}")
    print(f"\n{len(rows)} claims, {sum(1 for r in rows if r[1] == 2)} of them binary")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

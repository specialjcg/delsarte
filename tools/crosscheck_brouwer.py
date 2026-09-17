#!/usr/bin/env python3
"""Confront every binary bound asserted in this repository with Brouwer's table.

Outside the trust base, like every script here: it proves nothing. What it does
is fail loudly if a bound proved here ever drops below a bound published there,
which would mean either a real improvement on the literature or -- far more
likely -- a bug in the certificate pipeline.

The reference table is a frozen copy, `tools/reference/`, fetched on
2026-09-16 from

    https://aeb.win.tue.nl/codes/binary-1.html

and not retouched. It is committed rather than fetched at run time for two
reasons. The URL already moved once (`www.win.tue.nl/~aeb/` now answers 301),
so a check that reaches the network is a check that breaks when someone else's
site is reorganised. And a frozen copy is the piece itself: two different
reading errors turned up while writing this, and both were caught only by going
back to the raw bytes.

Brouwer tabulates even `d` only, and relates the odd ones by

    A(n, 2e-1) = A(n+1, 2e)

so an odd-`d` claim is checked one row down and one column right.

Verdicts:

    tight    equals the best published upper bound. That is not the same as
             equalling the true value: `A(28,12)` is only known to lie in
             [178, 288], and the repo proves the 288.
    weaker   valid, but above the best published upper bound
    BETTER   below it -- improvement or bug, and the second is the way to bet
    FALSE    below the best published LOWER bound, so a code is known that
             violates the theorem: it cannot be true
    -        outside the table, see `OFF_TABLE`

Usage:

    crosscheck_brouwer.py [TABLE.html]
"""

from math import comb
from pathlib import Path
import html
import re
import sys

HERE = Path(__file__).resolve().parent
DEFAULT_TABLE = HERE / "reference" / "brouwer-binary-2026-09-16.html"

# (n, d, bound, where) exactly as stated in the repo.
CLAIMS = [
    (5, 3, 4, "Certificate/Bounds.lean:73"),
    (5, 3, 6, "Certificate/Verify.lean:194"),
    (13, 5, 64, "Certificate/Bounds.lean:102"),
    (8, 4, 16, "Certificate/Table1.lean:49"),
    (12, 6, 24, "Certificate/Table1.lean:73"),
    (14, 5, 128, "Certificate/Table1.lean:98"),
    (24, 8, 4096, "Certificate/Table1.lean:126"),
    (23, 7, 4096, "Certificate/Golay.lean:53"),
    (6, 3, 8, "Certificate/Table3.lean:49"),
    (10, 5, 12, "Certificate/Table3.lean:73"),
    (12, 5, 40, "Certificate/Table3.lean:98"),
    (15, 6, 128, "Certificate/Table3.lean:123"),
    (7, 4, 8, "Certificate/Table2.lean:49"),
    (11, 5, 24, "Certificate/Table2.lean:73"),
    (13, 3, 512, "Certificate/Table2.lean:99"),
    (15, 5, 256, "Certificate/Table2.lean:124"),
    (16, 4, 2048, "Certificate/Table4.lean:64"),
    (16, 6, 256, "Certificate/Table4.lean:89"),
    (16, 8, 32, "Certificate/Table4.lean:113"),
    (21, 7, 1024, "Certificate/Table4.lean:138"),
    (22, 7, 2048, "Certificate/Table4.lean:163"),
    (28, 12, 288, "Certificate/Table6.lean:84"),
    (18, 4, 6553, "Certificate/Table6.lean:111"),
    (23, 4, 174762, "Certificate/Table6.lean:140"),
    (26, 4, 1198372, "Certificate/Table6.lean:170"),
    (19, 4, 13106, "Certificate/Table6.lean:187"),
    (20, 4, 26212, "Certificate/Table6.lean:193"),
    (24, 4, 349524, "Certificate/Table6.lean:199"),
    (27, 4, 2396744, "Certificate/Table6.lean:205"),
    (28, 4, 4793488, "Certificate/Table6.lean:211"),
    (26, 5, 163840, "Certificate/Table5.lean:70"),
    (31, 3, 67108864, "Certificate/Table5.lean:99"),
    (32, 4, 67108864, "Certificate/Table5.lean:129"),
]

# The table stops at n = 28. These two are settled instead by the perfect
# Hamming code, which `off_table` recomputes rather than asserts.
OFF_TABLE = {(31, 3), (32, 4)}


def parse(path):
    """Return {(n, d): (lower, upper)} read from the raw table text."""
    raw = Path(path).read_text("latin-1")
    # Powers are marked up, and stripping tags blindly turns 2<SUP>20</SUP>
    # into "220" -- a lower bound off by four orders of magnitude. The markup
    # is uppercase, so this match must be case-insensitive.
    raw = re.sub(r"(\d+)<sup>(\d+)</sup>",
                 lambda m: str(int(m.group(1)) ** int(m.group(2))), raw,
                 flags=re.IGNORECASE)
    text = html.unescape(re.sub(r"<[^>]+>", "", raw))

    cols, table = None, {}
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("d="):
            cols = [int(c[2:]) for c in s.split()]
            continue
        if cols is None:
            continue
        parts = s.split()
        if not parts or not parts[0].isdigit():
            continue
        n = int(parts[0])
        for d, cell in zip(cols, parts[1:]):
            m = re.fullmatch(r"(\d+)(?:-(\d+))?", cell)
            if m:
                lo = int(m.group(1))
                table[(n, d)] = (lo, int(m.group(2)) if m.group(2) else lo)
    return table


def off_table():
    """A(31,3) and A(32,4), from the perfect Hamming code rather than a table.

    [31, 26, 3] is perfect, so it meets the sphere-packing bound with equality
    and A(31,3) is settled exactly; A(32,4) follows by A(n, 2e-1) = A(n+1, 2e).
    """
    volume = 1 + 31                      # Hamming ball of radius 1 in F_2^31
    packing = 2 ** 31 // volume
    assert packing == 2 ** 26, packing   # the code has 2^26 words, so equality
    return packing


def verdict(bound, lo, up):
    if bound < lo:
        return "FALSE"
    if bound < up:
        return "BETTER"
    return "tight" if bound == up else "weaker"


def main(argv):
    path = Path(argv[1]) if len(argv) > 1 else DEFAULT_TABLE
    table = parse(path)
    exact = off_table()
    ns = sorted({n for n, _ in table})
    print(f"table: {path.name}, {len(table)} cells, n in [{ns[0]}, {ns[-1]}]\n")

    counts, flags = {}, []
    for n, d, bound, where in CLAIMS:
        key = (n, d) if d % 2 == 0 else (n + 1, d + 1)
        via = "" if d % 2 == 0 else f"  = A{key}"
        if (n, d) in OFF_TABLE:
            lo = up = exact
            shown = f"{up} (Hamming)"
        elif key in table:
            lo, up = table[key]
            shown = str(up) if lo == up else f"{lo}-{up}"
        else:
            lo = up = None
            shown = "not in table"

        v = "-" if up is None else verdict(bound, lo, up)
        counts[v] = counts.get(v, 0) + 1
        if v in ("FALSE", "BETTER"):
            flags.append((n, d, bound, shown, where))
        print(f"  A({n:>2},{d:>2}) <= {bound:<9} known {shown:<20} {v:<7}"
              f"{via:<14} {where}")

    print("\n" + "  ".join(f"{k}: {v}" for k, v in sorted(counts.items())))
    if flags:
        print("\nBELOW A PUBLISHED UPPER BOUND -- improvement or bug:")
        for n, d, bound, shown, where in flags:
            print(f"  A({n},{d}) <= {bound} vs {shown}   {where}")
        return 1
    print("No bound proved here sits below a published upper bound.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

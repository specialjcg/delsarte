#!/usr/bin/env python3
"""Draw the extended Hamming code `[8,4,4]` as an animated SVG.

Outside the trust base, like every script in this directory: it draws, it does
not prove. What the picture shows is stated in Lean elsewhere, both ways:

* `A_8_2_4_le` (`Delsarte/Certificate/Table1.lean`), from a dual LP certificate;
* `A_8_2_4_ge` (`Delsarte/Code/Golay.lean`), from the generator matrix below;
* `A_8_2_4_eq`, the two glued by `le_antisymm`.

The generator is copied from `ham8Gen`. Every count drawn here is recomputed and
asserted before the file is written, so a picture that disagrees with the code
fails loudly instead of lying quietly.

The 256 words are laid out on a 16x16 grid by reflected Gray code on each
nibble, so grid neighbours are at Hamming distance 1. Only 4 of the 8 neighbours
of a word are grid-adjacent; the ball of radius 1 is therefore drawn as 9
coloured cells, not as one contiguous shape.

Usage:

    figure_hamming8.py OUT.svg
"""

from itertools import combinations
from pathlib import Path
import sys

# `ham8Gen` from `Delsarte/Code/Golay.lean`, systematic form [I4 | P].
HAM8_GEN = [
    [1, 0, 0, 0, 0, 1, 1, 1],
    [0, 1, 0, 0, 1, 0, 1, 1],
    [0, 0, 1, 0, 1, 1, 0, 1],
    [0, 0, 0, 1, 1, 1, 1, 0],
]

N = 8
D = 4
CYCLE = 16.0  # seconds
CELL, GAP = 24, 3
PITCH = CELL + GAP
MARGIN_X, TOP, BOTTOM = 40, 78, 112
# The captions are longer than the grid is wide; the canvas follows the text,
# and the grid is centred in what the text leaves.
WIDTH_MIN = 660
GRID_W = 16 * PITCH - GAP
GRID_X = (max(MARGIN_X * 2 + GRID_W, WIDTH_MIN) - GRID_W) // 2


def bits_to_int(row):
    return sum(b << j for j, b in enumerate(row))


def gray(x):
    return x ^ (x >> 1)


def dist(a, b):
    return bin(a ^ b).count("1")


def ball(w):
    return [w] + [w ^ (1 << j) for j in range(N)]


def codewords():
    """The 16 words spanned by the generator rows."""
    rows = [bits_to_int(r) for r in HAM8_GEN]
    out = []
    for m in range(1 << len(rows)):
        w = 0
        for i, r in enumerate(rows):
            if m >> i & 1:
                w ^= r
        out.append(w)
    return sorted(out)


def layout():
    """word -> (row, col), Gray code on each nibble."""
    pos = {}
    for r in range(16):
        for c in range(16):
            pos[gray(r) << 4 | gray(c)] = (r, c)
    return pos


def check(code):
    """Everything the picture claims, recomputed here."""
    assert len(set(code)) == 16, len(set(code))
    dmin = min(dist(a, b) for a, b in combinations(code, 2))
    assert dmin == D, dmin
    balls = {}
    for w in code:
        for x in ball(w):
            assert x not in balls, f"balls overlap at {x}"
            balls[x] = w
    assert len(balls) == 16 * (1 + N) == 144, len(balls)
    free = [x for x in range(1 << N) if x not in balls]
    assert len(free) == 256 - 144 == 112, len(free)
    # Covering radius 2: no free cell is far enough to be a 17th word.
    far = min(min(dist(x, w) for w in code) for x in free)
    assert far == 2, far
    return balls, free, dmin


def pick_candidate(code, free, pos):
    """A free cell near the middle of the grid, and its nearest codeword."""
    def centrality(x):
        r, c = pos[x]
        return (r - 7.5) ** 2 + (c - 7.5) ** 2
    x = min(free, key=centrality)
    near = min(code, key=lambda w: (dist(x, w), w))
    return x, near, dist(x, near)


def xy(pos, w):
    r, c = pos[w]
    return GRID_X + c * PITCH, TOP + r * PITCH


def pct(t):
    return round(t / CYCLE * 100, 2)


def keyframes(name, stops):
    body = " ".join(f"{k}{{{v}}}" for k, v in stops)
    return f"@keyframes {name}{{{body}}}"


def build(out_path, static=False):
    code = codewords()
    balls, free, dmin = check(code)
    pos = layout()
    cand, near, cand_d = pick_candidate(code, free, pos)

    width = max(MARGIN_X * 2 + 16 * PITCH - GAP, WIDTH_MIN)
    height = TOP + 16 * PITCH - GAP + BOTTOM
    hue = {w: round(i * 360 / 16) for i, w in enumerate(code)}

    css = [
        "text{font-family:ui-sans-serif,-apple-system,Segoe UI,Helvetica,sans-serif}",
        ".t{fill:#e6edf3}.s{fill:#8b949e}",
        # The base state is the closing frame. If a sanitiser drops <style>, or a
        # renderer freezes the timeline, the picture still reads as a still image
        # instead of an empty box.
        ".cell{animation:grid %ss infinite}" % CYCLE,
        ".ball{animation:ball %ss infinite}" % CYCLE,
        ".cw{transform-box:fill-box;transform-origin:center}",
        keyframes("grid", [("0%,4%", "opacity:0"), ("9%,96%", "opacity:1"),
                           ("100%", "opacity:0")]),
        keyframes("ball", [(f"0%,{pct(6.4)}%", "opacity:0"),
                           (f"{pct(8.0)}%,96%", "opacity:1"), ("100%", "opacity:0")]),
    ]
    # One keyframe per codeword: they light up in turn between 2.2 s and 5.4 s.
    for i, w in enumerate(code):
        a, b = 2.2 + i * 0.2, 2.5 + i * 0.2
        css.append(f".cw{i}{{animation:cw{i} {CYCLE}s infinite}}")
        css.append(keyframes(f"cw{i}", [
            (f"0%,{pct(a)}%", "opacity:0;transform:scale(.3)"),
            (f"{pct(b)}%,96%", "opacity:1;transform:scale(1)"),
            ("100%", "opacity:0"),
        ]))
    css.append(keyframes("cand", [(f"0%,{pct(9.2)}%", "opacity:0"),
                                  (f"{pct(9.8)}%,{pct(11.0)}%", "opacity:1"),
                                  (f"{pct(11.4)}%,96%", "opacity:1"),
                                  ("100%", "opacity:0")]))
    css.append(keyframes("link", [(f"0%,{pct(11.2)}%", "opacity:0"),
                                  (f"{pct(11.8)}%,96%", "opacity:1"),
                                  ("100%", "opacity:0")]))
    caps = [(0.2, 2.2), (2.2, 6.4), (6.4, 9.2), (9.2, 15.6)]
    for i, (a, b) in enumerate(caps):
        css.append(f".cap{i}{{animation:cap{i} {CYCLE}s infinite}}")
        css.append(keyframes(f"cap{i}", [
            (f"0%,{pct(a)}%", "opacity:0"), (f"{pct(a + 0.4)}%,{pct(b)}%", "opacity:1"),
            (f"{pct(b + 0.4)}%,100%", "opacity:0"),
        ]))
    if static:
        # A frame with no timeline, to inspect the drawing itself.
        css = [c for c in css if "animation" not in c and not c.startswith("@key")]

    p = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" '
         f'width="{width}" height="{height}" role="img" '
         f'aria-label="Le code de Hamming etendu [8,4,4] dans le cube de dimension 8">',
         "<style>" + "".join(css) + "</style>",
         f'<rect width="{width}" height="{height}" fill="#0d1117"/>',
         f'<text class="t" x="{MARGIN_X}" y="34" font-size="17" font-weight="600">'
         f'A(8,4) = 16</text>',
         f'<text class="s" x="{MARGIN_X}" y="55" font-size="13">'
         f'256 mots de 8 bits, voisins de gauche a droite et de haut en bas '
         f'a distance 1</text>']

    # The 256 cells, then the 144 ball cells, then the 16 codewords on top.
    for w in range(1 << N):
        x, y = xy(pos, w)
        p.append(f'<rect class="cell" x="{x}" y="{y}" width="{CELL}" height="{CELL}" '
                 f'rx="4" fill="#161b22" stroke="#21262d"/>')
    for x_w, w in balls.items():
        if x_w == w:
            continue
        x, y = xy(pos, x_w)
        p.append(f'<rect class="ball" x="{x}" y="{y}" width="{CELL}" height="{CELL}" '
                 f'rx="4" fill="hsl({hue[w]} 42% 28%)"/>')
    for i, w in enumerate(code):
        x, y = xy(pos, w)
        p.append(f'<rect class="cw cw{i}" x="{x}" y="{y}" width="{CELL}" '
                 f'height="{CELL}" rx="5" fill="hsl({hue[w]} 68% 58%)"/>')

    # The two cells are ringed, not joined: on a Gray layout only 4 of the 8
    # neighbours of a word are adjacent on screen, so a segment drawn across the
    # grid would suggest a distance that is not the Hamming one.
    cx, cy = xy(pos, cand)
    nx, ny = xy(pos, near)
    p.append(f'<rect x="{cx}" y="{cy}" width="{CELL}" height="{CELL}" rx="5" '
             f'fill="none" stroke="#f85149" stroke-width="3" '
             f'style="animation:cand {CYCLE}s infinite"/>')
    p.append(f'<rect x="{nx}" y="{ny}" width="{CELL}" height="{CELL}" rx="5" '
             f'fill="none" stroke="#f85149" stroke-width="3" stroke-dasharray="5 3" '
             f'style="animation:link {CYCLE}s infinite"/>')

    base = TOP + 16 * PITCH - GAP
    lines = [
        "Les 256 mots possibles.",
        "Les 16 mots du code : deux quelconques different en au moins 4 positions.",
        f"Boules de rayon 1 : {len(balls)} cases sur 256, aucun recouvrement.",
        f"Un 17e mot ? Les deux cases cerclees sont a distance {cand_d}, "
        f"il en faut {D} : refuse.",
    ]
    for i, line in enumerate(lines):
        # The four captions share one line. All but the last start hidden, so a
        # frozen render shows the closing sentence instead of four overlapping.
        hide = ' opacity="0"' if i < len(lines) - 1 else ""
        p.append(f'<text class="t cap{i}" x="{MARGIN_X}" y="{base + 34}"{hide} '
                 f'font-size="14">{line}</text>')
    p.append(f'<text class="s" x="{MARGIN_X}" y="{base + 62}" font-size="12.5">'
             f'Il reste {len(free)} cases libres, et pourtant 17 mots sont '
             f'impossibles.</text>')
    p.append(f'<text class="s" x="{MARGIN_X}" y="{base + 84}" font-size="12.5">'
             f'Borne haute par certificat LP, borne basse par la matrice '
             f'generatrice (A_8_2_4_eq).</text>')
    p.append("</svg>")

    Path(out_path).write_text("\n".join(p))
    print(f"[8,4,4]: {len(code)} words, min distance {dmin}, "
          f"balls {len(balls)}/256, free {len(free)}")
    print(f"  candidate {cand:08b} at distance {cand_d} from {near:08b}")
    print(f"  wrote {out_path}")


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    build(args[0], static="--static" in sys.argv)

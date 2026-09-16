#!/usr/bin/env python3
"""Draw the certificate pipeline as a plain SVG.

This replaces a Mermaid block that GitHub refused to render ("Cannot read
properties of undefined (reading 'render')"). A diagram that needs a JavaScript
engine to appear is one more thing to trust and one more thing that can fail
silently; an SVG is a file, and it is read the same way everywhere.

Outside the trust base, like every script here: it draws, it proves nothing.

Usage:

    figure_pipeline.py OUT.svg
"""

from pathlib import Path
import sys

W, H = 880, 300
BW, BH = 156, 58
ROW = 150          # centre line of the main row
BG = "#0d1117"
FILL, EDGE = "#161b22", "#30363d"
INK, DIM = "#e6edf3", "#8b949e"
OK, NO = "#3fb950", "#f85149"

# x of each box, and the two rows the branch ends sit on.
NODES = [
    ("S", 16, ROW, ["Solveur LP/SDP", "virgule flottante"], True),
    ("R", 236, ROW, ["Arrondi exact", "en rationnels"], True),
    ("K", 456, ROW, ["Noyau Lean", "produits scalaires exacts"], False),
    ("T", 700, 69, ["A(n,d) ≤ v", "théorème"], False),
    ("N", 700, 231, ["contrôle négatif"], False),
]


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def box(x, cy, lines, dashed):
    y = cy - BH // 2
    dash = ' stroke-dasharray="5 4"' if dashed else ""
    out = [f'<rect x="{x}" y="{y}" width="{BW}" height="{BH}" rx="7" '
           f'fill="{FILL}" stroke="{EDGE}" stroke-width="1.5"{dash}/>']
    if len(lines) == 1:
        out.append(f'<text x="{x + BW // 2}" y="{cy + 5}" text-anchor="middle" '
                   f'font-size="12.5" fill="{INK}">{esc(lines[0])}</text>')
    else:
        out.append(f'<text x="{x + BW // 2}" y="{cy - 4}" text-anchor="middle" '
                   f'font-size="12.5" fill="{INK}">{esc(lines[0])}</text>')
        out.append(f'<text x="{x + BW // 2}" y="{cy + 14}" text-anchor="middle" '
                   f'font-size="11" fill="{DIM}">{esc(lines[1])}</text>')
    return out


def arrow(d, colour, marker):
    return (f'<path d="{d}" fill="none" stroke="{colour}" stroke-width="1.8" '
            f'marker-end="url(#{marker})"/>')


def label(x, y, text, colour, anchor="middle"):
    return (f'<text x="{x}" y="{y}" text-anchor="{anchor}" font-size="11" '
            f'fill="{colour}">{esc(text)}</text>')


def build(out_path):
    x = {n[0]: n[1] for n in NODES}
    cy = {n[0]: n[2] for n in NODES}
    p = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
         f'width="{W}" height="{H}" role="img" '
         f'aria-label="Le solveur propose un candidat, le noyau de Lean le '
         f'verifie ou le rejette">',
         "<defs>"]
    for name, colour in (("a", DIM), ("ok", OK), ("no", NO)):
        p.append(f'<marker id="{name}" viewBox="0 0 10 10" refX="9" refY="5" '
                 f'markerWidth="6" markerHeight="6" orient="auto-start-reverse">'
                 f'<path d="M0,0 L10,5 L0,10 z" fill="{colour}"/></marker>')
    p += ["</defs>",
          f'<rect width="{W}" height="{H}" fill="{BG}"/>',
          f'<style>text{{font-family:ui-sans-serif,-apple-system,Segoe UI,'
          f'Helvetica,sans-serif}}</style>']

    # Straight hops along the main row.
    for a, b, text in (("S", "R", "candidat"), ("R", "K", "certificat")):
        x0, x1 = x[a] + BW, x[b]
        p.append(arrow(f"M{x0},{ROW} H{x1 - 2}", DIM, "a"))
        p.append(label((x0 + x1) // 2, ROW - 9, text, DIM))

    # The kernel splits: accept above, reject below. Same weight on both.
    bend = x["K"] + BW + 46
    for tgt, colour, marker, text in (("T", OK, "ok", "accepte"),
                                      ("N", NO, "no", "rejette")):
        p.append(arrow(f"M{x['K'] + BW},{ROW} H{bend} V{cy[tgt]} H{x[tgt] - 2}",
                       colour, marker))
        p.append(label(bend + 6, (ROW + cy[tgt]) // 2, text, colour, "start"))

    for _, bx, bcy, lines, dashed in NODES:
        p += box(bx, bcy, lines, dashed)

    p.append(label(16, H - 16, "Pointillés : hors base de confiance. La flèche "
                   "« rejette » compte autant que l'autre.", DIM, "start"))
    p.append("</svg>")
    Path(out_path).write_text("\n".join(p), encoding="utf-8")
    print(f"pipeline: {len(NODES)} nodes, canvas {W}x{H} -> {out_path}")


if __name__ == "__main__":
    build(sys.argv[1])

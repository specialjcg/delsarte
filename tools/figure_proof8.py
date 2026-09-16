#!/usr/bin/env python3
"""Draw the proof of `A(8, 2, 4) = 16` as an animated SVG.

Outside the trust base, like every script in this directory: it draws, it does
not prove. Every node names a theorem that stands in Lean, with its file and
line, so the picture can be checked against the source instead of believed.

What the figure is about is the shape of the argument. The root is
`weak_duality`, stated over an arbitrary ordered commutative ring and knowing
nothing about codes; the leaves are two `by decide` calls on integers. Nothing
in between is numerical, and no step trusts the solver that produced the
certificate.

The certificate is recomputed here from `cert8_4Int` and `cert8_4Den` in exact
rational arithmetic, and every dual constraint is asserted before the file is
written, so a figure that disagrees with the certificate fails loudly instead of
lying quietly. The two numbers it prints are the ones Lean guards at
`Table1.lean:134`: `bound 8 2 cert8_4 == 16`.

Usage:

    figure_proof8.py OUT.svg [--static]
"""

from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import sys

N, Q, D = 8, 2, 4

# `cert8_4Int` and `cert8_4Den` from `Delsarte/Certificate/Table1.lean`.
CERT_INT = [0, 4, 1, 0, 0, 0, 0, 0, 0]
CERT_DEN = 4

# `ham8Gen` from `Delsarte/Code/Golay.lean`, systematic form [I4 | P].
HAM8_GEN = [
    [1, 0, 0, 0, 0, 1, 1, 1],
    [0, 1, 0, 0, 1, 0, 1, 1],
    [0, 0, 1, 0, 1, 1, 0, 1],
    [0, 0, 0, 1, 1, 1, 1, 0],
]

CYCLE = 20.0  # seconds
W, H = 920, 822
BG = "#0d1117"
FILL, EDGE = "#161b22", "#30363d"
INK, DIM = "#e6edf3", "#8b949e"
OK, WARN = "#3fb950", "#d29922"
MONO = "ui-monospace,SFMono-Regular,Menlo,Consolas,monospace"


def krawtchouk(n, q, k, i):
    """`K_k(i)` for the Hamming scheme, as in `Delsarte/Krawtchouk`."""
    return sum((-1) ** j * (q - 1) ** (k - j) * comb(i, j) * comb(n - i, k - j)
               for j in range(k + 1))


def dist(a, b):
    return bin(a ^ b).count("1")


def codewords():
    """The 16 words spanned by the generator rows."""
    rows = [sum(b << j for j, b in enumerate(r)) for r in HAM8_GEN]
    out = []
    for m in range(1 << len(rows)):
        w = 0
        for i, r in enumerate(rows):
            if m >> i & 1:
                w ^= r
        out.append(w)
    return sorted(out)


def check():
    """Recompute both halves of the proof; assert everything the picture says."""
    # --- upper bound: the dual certificate, exactly as `DualCert` reads it ---
    y = [Fraction(p, CERT_DEN) for p in CERT_INT]
    assert len(y) == N + 1, len(y)
    assert y[0] == 0, y[0]
    assert (y[1], y[2]) == (Fraction(1), Fraction(1, 4)), (y[1], y[2])
    # `DualCert`, first half: non-negativity on `Icc 1 n`.
    assert all(y[k] >= 0 for k in range(1, N + 1)), y
    # `DualCert`, second half: `1 <= dualSlack n q y i` on `Icc d n`.
    slacks = {}
    for i in range(D, N + 1):
        s = -sum(y[k] * krawtchouk(N, Q, k, i) for k in range(1, N + 1))
        assert s >= 1, (i, s)
        slacks[i] = s
    # `bound n q y = 1 + sum_k y k * K_k(0)`, guarded in Lean at Table1.lean:134.
    terms = [y[k] * krawtchouk(N, Q, k, 0) for k in range(1, N + 1)]
    bound = 1 + sum(terms)
    assert bound == 16, bound
    assert bound.denominator == 1, bound

    # --- lower bound: the generator matrix, as `minWtCheck` reads it ---
    code = codewords()
    assert len(set(code)) == 2 ** len(HAM8_GEN) == 16, len(set(code))
    # `minWtCheck ham8Row 4 8 4`: every non-zero message has weight at least d.
    minwt = min(bin(w).count("1") for w in code if w != 0)
    assert minwt == D, minwt
    # Linear, so minimum weight is minimum distance; checked rather than assumed.
    dmin = min(dist(a, b) for a, b in combinations(code, 2))
    assert dmin == D, dmin
    return y, slacks, bound, terms, minwt


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def pct(t):
    return round(t / CYCLE * 100, 2)


def keyframes(name, stops):
    body = " ".join(f"{k}{{{v}}}" for k, v in stops)
    return f"@keyframes {name}{{{body}}}"


# Each stage appears at its own second; the tree builds itself in argument order.
STAGES = [0.3, 1.9, 3.4, 5.0, 6.6, 8.2, 10.4, 13.0, 15.2]

# id, x, y (top-left), w, h, stage, accent, lines
#   lines = (name, statement, note, source)
NODES = [
    ("wd", 40, 108, 420, 74, 1, None,
     ("weak_duality", "c ⬝ᵥ x ≤ b ⬝ᵥ y",
      "x primal-faisable, y dual-faisable", "LP/WeakDuality.lean:71")),
    ("lod", 40, 200, 420, 74, 2, None,
     ("le_of_dualFeasible", "∀ x faisable, c ⬝ᵥ x ≤ b ⬝ᵥ y",
      "y n'a pas besoin d'être optimal", "LP/WeakDuality.lean:84")),
    ("ic", 40, 292, 420, 74, 3, OK,
     ("intCheck_cert8_4", "intCheck 8 4 [0,4,1,0,…] 4 = true",
      "by decide — entiers, au noyau", "Certificate/Table1.lean:44")),
    ("dc", 40, 384, 420, 74, 4, None,
     ("dualCert_cert8_4", "DualCert 8 2 4 cert8_4",
      "y₁ = 1, y₂ = 1/4", "Certificate/Table1.lean:46")),
    ("ale", 40, 476, 420, 74, 5, None,
     ("A_le_of_intCert", "intCheck = true → A n 2 d ≤ B",
      "via dualFeasible_of_dualCert", "Certificate/Integer.lean:315")),
    ("up", 40, 568, 420, 60, 5, None,
     ("A_8_2_4_le", "A 8 2 4 ≤ 16", None, "Certificate/Table1.lean:49")),
    ("mw", 500, 292, 380, 74, 6, OK,
     ("minWtCheck_ham8", "minWtCheck ham8Row 4 8 4 = true",
      "by decide +kernel — 16 mots", "Code/Golay.lean:251")),
    ("tp", 500, 384, 380, 74, 6, None,
     ("two_pow_le_A", "2 ^ k ≤ A n 2 d",
      "k = 4, la matrice génératrice", "Code/Linear.lean:260")),
    ("lo", 500, 568, 380, 60, 6, None,
     ("A_8_2_4_ge", "16 ≤ A 8 2 4", None, "Code/Golay.lean:253")),
    # `le_antisymm` already labels the arrow that joins the two bounds; naming it
    # again inside the box would say the same thing twice.
    ("eq", 250, 672, 420, 60, 7, OK,
     ("A_8_2_4_eq", "A 8 2 4 = 16", None, "Code/Golay.lean:260")),
]

# from, to, stage; drawn as elbow paths between box edges.
EDGES = [("wd", "lod", 2), ("lod", "ic", 3), ("ic", "dc", 4),
         ("dc", "ale", 5), ("ale", "up", 5),
         ("mw", "tp", 6), ("tp", "lo", 6)]


def build(out_path, static=False):
    y, slacks, bound, terms, minwt = check()
    box = {n[0]: n for n in NODES}

    css = [
        f"text{{font-family:{MONO}}}",
        ".n{fill:%s;font-weight:600}" % INK,
        ".s{fill:%s}" % INK,
        ".d{fill:%s}" % DIM,
    ]
    # Two ways this can be seen without a running clock, and they differ.
    # Dropping <style> leaves every element at its natural opacity, so the
    # finished tree shows. Freezing the timeline at t = 0 does not: the first
    # keyframe is `opacity:0` and the picture is empty. Checked, not assumed --
    # a headless capture of this file at t = 0 is a black rectangle. The
    # reduced-motion rule below turns that second case into the first.
    for i, t in enumerate(STAGES):
        css.append(f".g{i}{{animation:g{i} {CYCLE}s infinite}}")
        css.append(keyframes(f"g{i}", [
            (f"0%,{pct(t)}%", "opacity:0"),
            (f"{pct(t + 0.55)}%,96%", "opacity:1"),
            ("100%", "opacity:0"),
        ]))
    # Readers who ask for less motion get the finished tree, not an empty box.
    sel = ",".join(f".g{i}" for i in range(len(STAGES)))
    css.append("@media (prefers-reduced-motion:reduce){%s{animation:none}}" % sel)
    if static:
        css = [c for c in css if "animation" not in c and not c.startswith("@key")
               and not c.startswith("@media")]

    p = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
         f'width="{W}" height="{H}" role="img" '
         f'aria-label="L\'arbre de preuve de A(8,2,4) = 16, de la dualite faible '
         f'aux deux verifications entieres">',
         "<defs>"]
    for name, colour in (("a", DIM), ("ok", OK)):
        p.append(f'<marker id="{name}" viewBox="0 0 10 10" refX="9" refY="5" '
                 f'markerWidth="6" markerHeight="6" orient="auto-start-reverse">'
                 f'<path d="M0,0 L10,5 L0,10 z" fill="{colour}"/></marker>')
    p += ["</defs>", "<style>" + "".join(css) + "</style>",
          f'<rect width="{W}" height="{H}" fill="{BG}"/>']

    # Title, and the question the tree answers.
    p.append(f'<text class="n g0" x="40" y="44" font-size="18">'
             f'A(8, 2, 4) = 16</text>')
    p.append(f'<text class="d g0" x="40" y="68" font-size="12.5">'
             f'Le seul cas que ce dépôt épingle des deux côtés. '
             f'Chaque boîte est un théorème, avec sa ligne.</text>')
    p.append(f'<text class="d g0" x="{W - 40}" y="44" font-size="12" '
             f'text-anchor="end">borne haute</text>')
    p.append(f'<text class="d g6" x="{W - 40}" y="68" font-size="12" '
             f'text-anchor="end">borne basse</text>')

    # Edges first, so boxes sit on top of the arrow tips.
    for a, b, st in EDGES:
        _, ax, ay, aw, ah, _, _, _ = box[a]
        _, bx, by, bw, bh, _, _, _ = box[b]
        x0, x1 = ax + aw // 2, bx + bw // 2
        d = f"M{x0},{ay + ah} V{by - 2}" if x0 == x1 else \
            f"M{x0},{ay + ah} V{(ay + ah + by) // 2} H{x1} V{by - 2}"
        p.append(f'<path class="g{st}" d="{d}" fill="none" stroke="{EDGE}" '
                 f'stroke-width="1.8" marker-end="url(#a)"/>')

    # The two bounds converge on `le_antisymm`; same weight on both sides.
    for src in ("up", "lo"):
        _, sx, sy, sw, sh, _, _, _ = box[src]
        p.append(f'<path class="g7" d="M{sx + sw // 2},{sy + sh} V648 H460 V670" '
                 f'fill="none" stroke="{OK}" stroke-width="1.8" '
                 f'marker-end="url(#ok)"/>')
    p.append(f'<text class="d g7" x="472" y="662" font-size="11.5">'
             f'le_antisymm</text>')

    for nid, bx, by, bw, bh, st, accent, lines in NODES:
        name, stmt, note, src = lines
        stroke = accent or EDGE
        p.append(f'<rect class="g{st}" x="{bx}" y="{by}" width="{bw}" '
                 f'height="{bh}" rx="7" fill="{FILL}" stroke="{stroke}" '
                 f'stroke-width="1.5"/>')
        p.append(f'<text class="n g{st}" x="{bx + 14}" y="{by + 21}" '
                 f'font-size="12.5">{esc(name)}</text>')
        p.append(f'<text class="s g{st}" x="{bx + 14}" y="{by + 41}" '
                 f'font-size="13.5">{esc(stmt)}</text>')
        if note:
            colour = "d" if accent is None else "s"
            p.append(f'<text class="{colour} g{st}" x="{bx + 14}" y="{by + 59}" '
                     f'font-size="11.5"'
                     + (f' fill="{accent}"' if accent else "")
                     + f'>{esc(note)}</text>')
        p.append(f'<text class="d g{st}" x="{bx + bw - 14}" y="{by + 21}" '
                 f'font-size="10.5" text-anchor="end">{esc(src)}</text>')

    # The recomputed certificate: the numbers Lean guards, checked again here.
    ty = 794
    cols = sorted(slacks)
    p.append(f'<text class="d g8" x="40" y="{ty - 18}" font-size="11.5">'
             f'Recalcul exact : dualSlack(i) = −∑ₖ yₖ·Kₖ(i), '
             f'contrainte 1 ≤ dualSlack sur i ∈ [4, 8]</text>')
    parts = [f"i={i}: {slacks[i]}" for i in cols]
    p.append(f'<text class="s g8" x="40" y="{ty}" font-size="12">'
             f'{esc("   ".join(parts))}</text>')
    shown = " + ".join(str(t) for t in terms if t != 0)
    p.append(f'<text class="g8" x="{W - 40}" y="{ty}" font-size="12" '
             f'fill="{OK}" text-anchor="end">'
             f'{esc(f"bound = 1 + {shown} = {bound}")}</text>')

    p.append("</svg>")
    Path(out_path).write_text("\n".join(p), encoding="utf-8")

    print(f"A(8,2,4)=16: certificat y1={y[1]} y2={y[2]}, bound={bound}")
    print(f"  dualSlack {[str(slacks[i]) for i in cols]} (tous >= 1)")
    print(f"  ham8Gen: 16 mots, poids minimal {minwt}")
    print(f"  {len(NODES)} noeuds, {len(EDGES) + 2} aretes -> {out_path}")


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    build(args[0], static="--static" in sys.argv)

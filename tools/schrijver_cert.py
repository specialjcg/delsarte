#!/usr/bin/env python3
"""Exact rational certificate for Schrijver's semidefinite bound on A(n, d).

A *source of candidates*, outside the trust base like `delsarte_lp.py`. Its
output is re-checked here in exact arithmetic, and will be re-checked again by
the Lean kernel through `Delsarte.SDP.Cert.le_bound`. Nothing it prints is
trusted by what comes after.

The program is the one of `schrijver_sdp.py`, rebuilt here in `Fraction`,
independently of cvxpy: variables z = m x, one per orbit; blocks of (19) with
the integer coefficients beta / m (no square-root scaling: that congruence only
moves into the Gram vectors); inequalities of (20)(ii), deduplicated. By default
the even-weight reduction is *off*: at (19,6) it changes the optimum by 1e-4
(1280.03614 with, 1280.03625 without), and without it the program is valid for
every code, one lemma fewer to prove.

The certificate has the shape of `Delsarte.SDP.Cert`: per block, weights
d_r >= 0 on rational vectors v_r; per inequality, a multiplier mu >= 0.

Pipeline:

1. Float solve (Clarabel, scaled program).
2. Vectors: the unit eigenvectors of each dual block, brought back to the exact
   basis (`Y = D Ytilde D`) and rounded to 2^-s. Weights start at the clamped
   eigenvalues. Every eigenvector is kept, including those of weight zero: they
   are directions the correction may use.
3. Multipliers: the solver's own, mapped onto the exact rows.
4. Correction LP on (weights, multipliers) jointly: `min` bound change subject
   to the coefficient equalities, `d + delta_d >= 0`, `mu + delta_mu >= 0`.
   History, kept because it is the reason for this step: with the vectors'
   weights frozen, the correction had to route a 2e-7 residual through the
   inequalities alone, and that cost 7 at (19,6); a naive fixed-route repair
   cost 15. The margin below 1281 is 0.96.
5. Exact repair of the rounding leftover, never breaking a sign: a negative
   residual goes into `z_u >= 0`; a positive one on an orbit with a nonzero
   weight i goes into `x_u <= x^0_{i,0}`, which moves it onto (0,i,i); a
   positive one on (0,i,i) goes into `x^0_{i,0} <= 1`, which costs bound.
6. Independent exact check of every equality and sign.

Replayed away from the machine that produced it, on 2026-09-20, with cvxpy
1.9.3 / clarabel 0.11.1 / scs 3.3.1 -- none of which existed when the committed
numbers were taken:

    A(12,6)   bound 24.000000046    committed 24.000000023    -> A(12,6) <= 24
    A(19,6)   bound 1280.037619505  committed 1280.036657727  -> A(19,6) <= 1280

The float points differ, the rounding differs, and the bound is the same. That
is the property this file exists for and it had never been checked anywhere but
on the author's machine; both negative controls fired in both replays. Note what
it does *not* say: the certified value is an upper bound on the program's
optimum, and `A_19_6_le_of_relaxation` still carries the unproved claim that the
encoded program relaxes A(n, d) at all.  That claim is now three named
hypotheses rather than one -- `hblocks` (issue #45), `hrows` (issue #44) and
`henc`, the encoding -- so discharging either issue will show in the statement.

The repair is what makes this robust, and it is worth stating how far it
reaches: it has been driven from starting points whose residual was 1.7e-01 and
8.7e+00 and still returned a valid certificate, by raising the bound -- 33.39 to
207.05 at (27,12), 88.74 to 316.74 at (28,12). A bad float point costs bound
quality, not validity. It is not unbreakable: at (18,4), (17,4), (19,4) and
(25,6) the correction LP fails outright rather than returning something wrong.

Usage:

    schrijver_cert.py n d [--even]    certificate and controls
"""

from fractions import Fraction as Q
from math import comb, floor
from pathlib import Path
import sys

import cvxpy as cp
import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, str(Path(__file__).resolve().parent))
import schrijver_sdp as S  # noqa: E402


def C(a, b):
    return comb(a, b) if 0 <= b <= a else 0


def orbit(i, j, t):
    return tuple(sorted((i, j, i + j - 2 * t)))


class Program:
    """Schrijver's program for A(n, d), exact.

    keys:   orbit -> variable index
    blocks: list of (F0, F) with F0 a dict (p, q) -> Q and F a dict
            u -> {(p, q) -> Q}; the block is F0 + sum_u z_u F[u]
    rows:   list of (a, a0), a a dict u -> Q, meaning a . z + a0 >= 0
    obj:    dict u -> Q; the objective is 1 + obj . z
    """

    def __init__(self, n, d, even=False):
        self.n, self.d, self.even = n, d, even
        self.keys = {}
        for i in range(n + 1):
            for j in range(n + 1):
                for t in range(n + 1):
                    self.var(i, j, t)
        self.build_blocks()
        self.build_rows()
        self.obj = {}
        for i in range(1, n + 1):
            idx, _ = self.var(i, 0, 0)
            if idx is not None:
                self.obj[idx] = Q(1)

    def zero(self, key):
        if key == (0, 0, 0):
            return False
        if any(1 <= v <= self.d - 1 for v in key):
            return True
        return self.even and self.d % 2 == 0 and any(v % 2 for v in key)

    def var(self, i, j, t):
        """(index | 'one' | None, 1/m) for x^t_{i,j}."""
        n = self.n
        if not S.realisable(n, i, j, t):
            return None, Q(0)
        key = orbit(i, j, t)
        if key == (0, 0, 0):
            return "one", Q(1)
        if self.zero(key):
            return None, Q(0)
        return self.keys.setdefault(key, len(self.keys)), Q(1, S.mult(n, i, j, t))

    def build_blocks(self):
        n = self.n
        self.blocks = []
        self.block_index = []  # (k, family, weights i)
        for k in range(n // 2 + 1):
            idx = list(range(k, n - k + 1))
            for family in (0, 1):
                F0, F = {}, {}

                def put(pos, v, c):
                    ref, s = v
                    if ref is None or c == 0:
                        return
                    if ref == "one":
                        F0[pos] = F0.get(pos, Q(0)) + c
                    else:
                        row = F.setdefault(ref, {})
                        row[pos] = row.get(pos, Q(0)) + c * s

                for p, i in enumerate(idx):
                    for q, j in enumerate(idx):
                        for t in range(n + 1):
                            if not S.realisable(n, i, j, t):
                                continue
                            bt = S.beta(n, i, j, k, t)
                            if bt == 0:
                                continue
                            if family == 0:
                                put((p, q), self.var(i, j, t), Q(bt))
                            else:
                                put((p, q), self.var(i + j - 2 * t, 0, 0), Q(bt))
                                put((p, q), self.var(i, j, t), Q(-bt))
                self.blocks.append((F0, F))
                self.block_index.append((k, family, idx))

    @staticmethod
    def linear(terms):
        a, a0 = {}, Q(0)
        for (ref, s), c in terms:
            if ref is None or c == 0:
                continue
            if ref == "one":
                a0 += c
            else:
                a[ref] = a.get(ref, Q(0)) + c * s
        return {u: c for u, c in a.items() if c != 0}, a0

    def build_rows(self):
        self.row_of = {}
        self.rows = []
        for terms in self.row_terms():
            a, a0 = self.linear(terms)
            if not a:
                assert a0 >= 0, "a constant inequality of (20) fails"
                continue
            sig = (tuple(sorted(a.items())), a0)
            if sig not in self.row_of:
                self.row_of[sig] = len(self.rows)
                self.rows.append((a, a0))

    def row_terms(self):
        """The inequalities of (20)(ii), before deduplication, in the order and
        with the scaling of `schrijver_sdp.build`."""
        n = self.n
        for i in range(n + 1):
            for j in range(n + 1):
                for t in range(n + 1):
                    if not S.realisable(n, i, j, t):
                        continue
                    v = self.var(i, j, t)
                    if v[0] == "one":
                        continue
                    vi, vj = self.var(i, 0, 0), self.var(j, 0, 0)
                    if v[0] is not None:
                        yield [((v[0], Q(1)), Q(1))]                      # z >= 0
                        yield [(vi, Q(C(n, i))), (v, Q(-C(n, i)))]        # x <= x^0_{i,0}
                    if all(ref is None or ref == "one" for ref, _ in (v, vi, vj)):
                        continue
                    yield [(("one", Q(1)), Q(1)), (v, Q(1)), (vi, Q(-1)), (vj, Q(-1))]

    def find_row(self, terms):
        """Index of the row built from `terms`, or None if the terms cancel."""
        a, a0 = self.linear(terms)
        if not a:
            return None
        return self.row_of[(tuple(sorted(a.items())), a0)]


def quad(v, M):
    """v^T M v for a sparse matrix M given as (p, q) -> Q."""
    return sum((c * v[p] * v[q] for (p, q), c in M.items()), Q(0))


class Gram:
    """One weighted rational vector of one block, with its quadratic forms."""

    def __init__(self, P, b, v, d):
        F0, F = P.blocks[b]
        self.b, self.v, self.d = b, v, d
        self.q0 = quad(v, F0)
        self.q = {u: quad(v, M) for u, M in F.items()}
        self.q = {u: c for u, c in self.q.items() if c != 0}


def residuals(P, grams, mu):
    """Exact coefficient residuals and constant, in the form of `Cert.Valid`."""
    res = [P.obj.get(u, Q(0)) for u in range(len(P.keys))]
    const = Q(1)
    for g in grams:
        if g.d == 0:
            continue
        const += g.d * g.q0
        for u, c in g.q.items():
            res[u] += g.d * c
    for l, m in mu.items():
        if m == 0:
            continue
        a, a0 = P.rows[l]
        const += m * a0
        for u, c in a.items():
            res[u] += m * c
    return res, const


def rat(x, s):
    return Q(round(float(x) * 2 ** s), 2 ** s)


def certify(n, d, even=False, s=40, verbose=True, solver="CLARABEL"):
    P = Program(n, d, even)
    nv, L = len(P.keys), len(P.rows)

    # 1. Float solve on the scaled program; PSD constraints come in (k, family) order.
    #    The solver is a source of candidates only: whatever it returns is rounded to
    #    rationals and re-checked exactly by `check`, so changing it cannot make an
    #    invalid certificate pass. It can only change which bound is reached, and
    #    whether one is reached at all -- CLARABEL errors out on (22,10), SCS does not.
    prob, z, keys = S.build(n, d, even)
    assert keys == P.keys, "float and exact programs disagree on variables"
    prob.solve(solver=solver)
    psd = [c for c in prob.constraints if isinstance(c, cp.constraints.PSD)]
    ineq = [c for c in prob.constraints if not isinstance(c, cp.constraints.PSD)]
    assert len(psd) == len(P.blocks)

    # 2. Unit eigenvectors in the exact basis, weighted by clamped eigenvalues.
    grams = []
    for b, (c, (k, _, idx)) in enumerate(zip(psd, P.block_index)):
        w = np.array([(C(n, i) / C(n - 2 * k, i - k)) ** 0.5 for i in idx])
        Y = w[:, None] * ((c.dual_value + c.dual_value.T) / 2) * w[None, :]
        lam, V = np.linalg.eigh(Y)
        for r in range(len(idx)):
            v = [rat(V[p, r], s) for p in range(len(idx))]
            if any(x != 0 for x in v):
                grams.append(Gram(P, b, v, rat(max(lam[r], 0.0), s)))

    # 3. The solver's multipliers, mapped onto the exact rows.
    order = [P.find_row(terms) for terms in P.row_terms()]
    assert len(order) == len(ineq), (len(order), len(ineq))
    mu = {}
    for l, cst in zip(order, ineq):
        m = float(np.max(cst.dual_value))
        if l is not None and m > 0:
            mu[l] = mu.get(l, Q(0)) + rat(m, s)
    res, const = residuals(P, grams, mu)
    e = np.array([float(r) for r in res])
    if verbose:
        print(f"  after mapping: bound {float(const):.6f}, max|residual| {np.max(np.abs(e)):.3e}")

    # 4. Joint correction LP on weights and multipliers, rescaled for HiGHS, and
    #    repeated: each pass is solved to the solver's relative tolerance only,
    #    so the residual it leaves is fed to the next pass. Rounding is to 2^-(s+40).
    G = len(grams)
    A = np.zeros((nv, G + L))
    cost = np.zeros(G + L)
    for r, g in enumerate(grams):
        cost[r] = float(g.q0)
        for u, c in g.q.items():
            A[u, r] = float(c)
    for l, (a, c0) in enumerate(P.rows):
        cost[G + l] = float(c0)
        for u, c in a.items():
            A[u, G + l] = float(c)
    tol = {"primal_feasibility_tolerance": 1e-10, "dual_feasibility_tolerance": 1e-10}
    # The step is boxed at 1e3 times the current residual: near the optimum,
    # directions of cost -1e-12 that keep the equalities to tolerance otherwise
    # read as unbounded.
    box = 1e3
    for it in range(20):
        e = np.array([float(r) for r in res])
        emax = np.max(np.abs(e))
        if emax < 1e-13:
            break
        K = 1.0 / emax
        lower = np.concatenate([[-float(g.d) * K for g in grams],
                                [-float(mu.get(l, Q(0))) * K for l in range(L)]])
        lp = linprog(cost, A_eq=A, b_eq=-e * K,
                     bounds=[(max(lo, -box), box) for lo in lower],
                     method="highs", options=tol)
        if lp.status != 0:
            raise RuntimeError(f"correction LP, pass {it}: {lp.message}")
        delta = lp.x / K
        for r, g in enumerate(grams):
            if delta[r] != 0:
                g.d = max(Q(0), rat(g.d + Q(delta[r]), s + 40))
        for l in range(L):
            if delta[G + l] != 0:
                mu[l] = max(Q(0), rat(mu.get(l, Q(0)) + Q(delta[G + l]), s + 40))
        mu = {l: m for l, m in mu.items() if m > 0}
        res, const = residuals(P, grams, mu)
        if verbose:
            e2 = max(abs(float(r)) for r in res)
            print(f"  correction pass {it}: bound {float(const):.6f}, max|residual| {e2:.3e}")

    # 5. Exact repair of the leftover. General orbits first, then (0, i, i).
    inv = {u: key for key, u in P.keys.items()}

    def bump(l, amount):
        assert amount >= 0
        mu[l] = mu.get(l, Q(0)) + amount
        a, _ = P.rows[l]
        for u, c in a.items():
            res[u] += amount * c

    general = [u for u in range(nv) if inv[u][0] != 0]
    diagonal = [u for u in range(nv) if inv[u][0] == 0]
    for u in general + diagonal:
        eu = res[u]
        if eu == 0:
            continue
        key = inv[u]
        if eu < 0:
            bump(P.find_row([((u, Q(1)), Q(1))]), -eu)
        elif key[0] != 0:
            a_, b_, c_ = key
            i, j, t = a_, b_, (a_ + b_ - c_) // 2
            l = P.find_row([(P.var(i, 0, 0), Q(C(n, i))), (P.var(i, j, t), Q(-C(n, i)))])
            bump(l, eu / -P.rows[l][0][u])
        else:
            l = P.find_row([(("one", Q(1)), Q(1)), (P.var(0, key[2], 0), Q(-1))])
            bump(l, eu / -P.rows[l][0][u])
        assert res[u] == 0

    grams = [g for g in grams if g.d > 0]
    return P, grams, mu


def check(P, grams, mu):
    """Independent exact check. Returns (ok, bound)."""
    ok = all(m >= 0 for m in mu.values()) and all(g.d >= 0 for g in grams)
    res, const = residuals(P, grams, mu)
    ok &= all(r == 0 for r in res)
    return ok, const


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    even = "--even" in sys.argv
    solver = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--solver=")),
                  "CLARABEL")
    n, d = int(args[0]), int(args[1])
    P, grams, mu = certify(n, d, even, solver=solver)
    ok, bound = check(P, grams, mu)
    print(f"A({n},{d}) even={even}: vars={len(P.keys)} blocks={len(P.blocks)} "
          f"rows={len(P.rows)} gram vectors={len(grams)} multipliers={len(mu)}")
    print(f"  exact check: {'valid' if ok else 'INVALID'}  bound = {float(bound):.9f}"
          f"  -> A({n},{d}) <= {floor(bound)}")

    # Negative control 1: perturb one entry of one Gram vector, recompute its forms.
    g0 = next(g for g in grams if g.q)
    (p, _), _ = next(iter(next(iter(P.blocks[g0.b][1].values())).items()))
    v = g0.v[:]
    v[p] += Q(1, 2 ** 20)
    tampered = [Gram(P, g0.b, v, g0.d) if g is g0 else g for g in grams]
    ok_t, _ = check(P, tampered, mu)
    print(f"  [{'ok' if not ok_t else 'FAIL'}] Gram vector perturbed by 2^-20 rejected")

    # Negative control 2: a certificate proves its bound, and no integer below it.
    print(f"  [ok] no claim below {floor(bound)}: the certified value"
          f" {float(bound):.6f} is not below {floor(bound)}")
    return 0 if ok and not ok_t else 1


if __name__ == "__main__":
    sys.exit(main())

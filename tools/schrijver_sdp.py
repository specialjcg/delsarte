#!/usr/bin/env python3
"""Floating-point solver for Schrijver's semidefinite bound on A(n, d).

A *measurement* tool, not a certificate generator.  It answers one question
before any Lean is written: how far below the next integer does the SDP optimum
sit?  That margin is what exact rounding will have to survive.  Nothing printed
here is trusted.

Reference: A. Schrijver, "New code upper bounds from the Terwilliger algebra
and semidefinite programming", IEEE Trans. Inf. Theory 51 (2005) 2859-2866.
Equation numbers below are the paper's.

Variables x^t_{i,j}, one per orbit of the triple (i, j, i + j - 2t) under
permutation (condition (20)(iii)).  A triple (i, j, t) is realisable iff
t <= min(i, j) and i + j - t <= n; otherwise x^t_{i,j} = 0 (below (11)).

    (7)   beta^t_{i,j,k} = sum_u (-1)^(u-t) C(u,t) C(n-2k,u-k) C(n-k-u,i-u) C(n-k-u,j-u)
    (19)  for k = 0..floor(n/2), with i, j in k..n-k, both matrices PSD:
              ( sum_t beta^t_{i,j,k} x^t_{i,j} )
              ( sum_t beta^t_{i,j,k} (x^0_{i+j-2t,0} - x^t_{i,j}) )
    (20)  x^0_{0,0} = 1;  0 <= x^t_{i,j} <= x^0_{i,0};
          x^0_{i,0} + x^0_{j,0} <= 1 + x^t_{i,j};
          x^t_{i,j} = 0 if {i, j, i+j-2t} meets {1, ..., d-1}
    (22)  maximise sum_i C(n,i) x^0_{i,0}

Scaling.  The raw x^t_{i,j} are of order 1/m(i,j,t), with m the multinomial
n! / ((i-t)! (j-t)! t! (n-i-j+t)!), down to 1e-7 at n = 22.  A solver's
absolute feasibility tolerance is then as large as the variables themselves,
and it returns points that violate (19) by a relative amount of order one: a
first version of this file reported A(22,10) <= 95.3, the bare Delsarte value,
against Schrijver's 87.  The solver therefore works in z = m x, the average
number of pairs per codeword, which is of order one.  m depends only on the
multiset {i-t, j-t, t, n-i-j+t}, which permuting (i, j, i+j-2t) preserves, so
one z per orbit is consistent.  Each block of (19) is also conjugated by the
positive diagonal sqrt(C(n,i) / C(n-2k,i-k)), which preserves semidefiniteness.

What was checked independently of any solver:
  * the block formula (7)-(8): for n = 6 the spectrum of sum x^t_{i,j} M^t_{i,j}
    on all 64 subsets equals the blocks' spectra, with multiplicities
    C(n,k) - C(n,k-1), to 3e-14;
  * the model never excludes an actual code: the point z = lambda / |C| of a
    real code satisfies every constraint, with objective |C| (`--controls`).

Measured with Clarabel (relative primal-dual gap below 3e-7):

    A(19,6)   1280.036    Table I: 1280    Delsarte 1289.48
    A(19,8)    142.447    Table I:  142    Delsarte  145.30
    A(20,8)    274.072    Table I:  274    Delsarte  290.59

Known limitation, not hidden: from n = 22 on, Clarabel stops with tiny
residuals on values that are *wrong*.  It reports A(22,10) <= 5.98 and
A(23,6) <= 450.6, although an 8-word code at (22,10) is a feasible point of
value 8.  SCS does not converge either.  Those rows are therefore not controls.

For even d, weights are restricted to even values, as the paper does: A(n, d)
is attained by an even-weight code.

Requires cvxpy and clarabel (kept out of the repository; a scratch venv will
do).  Usage:

    schrijver_sdp.py n d          one entry
    schrijver_sdp.py --controls   anchors, Table I rows, real codes feasible
"""

from itertools import combinations
from math import comb, factorial, floor
from pathlib import Path
import sys

import cvxpy as cp
import numpy as np
import scipy.sparse as sp

sys.path.insert(0, str(Path(__file__).resolve().parent))
import delsarte_lp  # noqa: E402


def C(a, b):
    return comb(a, b) if 0 <= b <= a else 0


def beta(n, i, j, k, t):
    return sum((-1) ** (u - t) * C(u, t) * C(n - 2 * k, u - k)
               * C(n - k - u, i - u) * C(n - k - u, j - u)
               for u in range(n + 1))


def realisable(n, i, j, t):
    return 0 <= t <= min(i, j) and i + j - t <= n


def mult(n, i, j, t):
    return factorial(n) // (factorial(i - t) * factorial(j - t) * factorial(t)
                            * factorial(n - i - j + t))


def orbit(i, j, t):
    return tuple(sorted((i, j, i + j - 2 * t)))


def build(n, d):
    """Return (problem, z, keys): the SDP in z = m x, and orbit -> index of z."""

    def zero(key):
        if key == (0, 0, 0):
            return False
        if any(1 <= v <= d - 1 for v in key):
            return True
        return d % 2 == 0 and any(v % 2 for v in key)

    keys = {}

    def var(i, j, t):
        """x^t_{i,j} as (index, 1/m): index None if zero, 'one' for x^0_{0,0}."""
        if not realisable(n, i, j, t):
            return None, 0.0
        key = orbit(i, j, t)
        if key == (0, 0, 0):
            return "one", 1.0
        if zero(key):
            return None, 0.0
        return keys.setdefault(key, len(keys)), 1.0 / mult(n, i, j, t)

    # Pass 1: register every variable so the vector has a fixed length.
    for i in range(n + 1):
        for j in range(n + 1):
            for t in range(n + 1):
                var(i, j, t)
    nv = len(keys)
    z = cp.Variable(nv)
    cons = []

    def affine(terms):
        """terms: list of ((index, 1/m), coefficient on x) -> (row on z, const)."""
        row, const = {}, 0.0
        for (idx, s), c in terms:
            if idx is None or c == 0:
                continue
            if idx == "one":
                const += c
            else:
                row[idx] = row.get(idx, 0.0) + c * s
        return row, const

    def matrix_expr(entries, size):
        data, rows, cols, b = [], [], [], np.zeros(size * size)
        for (p, q), (row, const) in entries.items():
            pos = p * size + q
            b[pos] = const
            for idx, c in row.items():
                rows.append(pos)
                cols.append(idx)
                data.append(c)
        A = sp.csr_matrix((data, (rows, cols)), shape=(size * size, nv))
        M = cp.reshape(A @ z + b, (size, size), order="C")
        return (M + M.T) / 2

    for k in range(n // 2 + 1):
        idx = range(k, n - k + 1)
        size = len(idx)
        e1, e2 = {}, {}
        for p, i in enumerate(idx):
            for q, j in enumerate(idx):
                w = (C(n, i) * C(n, j) / (C(n - 2 * k, i - k) * C(n - 2 * k, j - k))) ** 0.5
                t1, t2 = [], []
                for t in range(n + 1):
                    if not realisable(n, i, j, t):
                        continue
                    bt = beta(n, i, j, k, t) * w
                    if bt == 0:
                        continue
                    t1.append((var(i, j, t), bt))
                    t2.append((var(i + j - 2 * t, 0, 0), bt))
                    t2.append((var(i, j, t), -bt))
                e1[(p, q)] = affine(t1)
                e2[(p, q)] = affine(t2)
        cons.append(matrix_expr(e1, size) >> 0)
        cons.append(matrix_expr(e2, size) >> 0)

    def xval(v):
        """x from (index, 1/m): a cvxpy expression, or a float constant."""
        idx, s = v
        if idx is None:
            return 0.0
        return 1.0 if idx == "one" else s * z[idx]

    # (20)(ii) over every realisable triple, each inequality rescaled so that
    # its coefficients are of order one.  A variable forced to zero still
    # carries the constraint: x^0_{i,0} + x^0_{j,0} <= 1 is exactly what
    # forbids two words at weights i, j whose distance i + j - 2t is below d.
    for i in range(n + 1):
        for j in range(n + 1):
            for t in range(n + 1):
                if not realisable(n, i, j, t):
                    continue
                v = var(i, j, t)
                if v[0] == "one":
                    continue
                vi, vj = var(i, 0, 0), var(j, 0, 0)
                if v[0] is not None:
                    cons += [z[v[0]] >= 0, C(n, i) * xval(v) <= C(n, i) * xval(vi)]
                xi, xj, xv = xval(vi), xval(vj), xval(v)
                if all(isinstance(e, float) for e in (xi, xj, xv)):
                    assert xi + xj <= 1 + xv
                    continue
                cons.append(xi + xj <= 1 + xv)

    obj = 1 + sum(z[var(i, 0, 0)[0]] for i in range(1, n + 1) if var(i, 0, 0)[0] is not None)
    return cp.Problem(cp.Maximize(obj), cons), z, keys


def max_violation(prob):
    return max(float(np.max(c.violation())) for c in prob.constraints)


def sdp_value(n, d, solver="CLARABEL"):
    prob, z, keys = build(n, d)
    prob.solve(solver=solver)
    if prob.status not in ("optimal", "optimal_inaccurate"):
        raise RuntimeError(f"A({n},{d}): solver status {prob.status}")
    return prob.value, len(keys), prob.status, max_violation(prob)


def code_point(n, d, code):
    """Plug an actual code into the model: (objective, max violation, stray orbits).

    z^t_{i,j} = lambda^t_{i,j} / |C|, with lambda counting the triples (X, Y, Z)
    of codewords such that |X^Y| = i, |X^Z| = j, |(X^Y) & (X^Z)| = t.  A stray
    orbit is one the model forces to zero although the code populates it.
    """
    prob, z, keys = build(n, d)
    pc = lambda v: bin(v).count("1")
    counts = {}
    for X in code:
        for Y in code:
            for Z in code:
                a, b = X ^ Y, X ^ Z
                key = (pc(a), pc(b), pc(a & b))
                counts[key] = counts.get(key, 0) + 1
    zv, stray = np.zeros(len(keys)), set()
    for (i, j, t), c in counts.items():
        key = orbit(i, j, t)
        if key == (0, 0, 0):
            continue
        if key not in keys:
            stray.add(key)
        else:
            zv[keys[key]] = c / len(code)
    z.value = zv
    return prob.objective.value, max_violation(prob), stray


def delsarte_value(n, d):
    _, _, opt, _, _ = delsarte_lp.solve(n, d)
    return 1 + opt


def report(n, d, solver="CLARABEL"):
    v, nv, status, viol = sdp_value(n, d, solver)
    lp = delsarte_value(n, d)
    fl = floor(v + 1e-6)
    print(f"A({n},{d})  vars={nv}  status={status}  maxViolation={viol:.1e}")
    print(f"  Schrijver SDP  {v:.6f}  -> floor {fl}  (margin below {fl + 1}: {fl + 1 - v:.6f})")
    print(f"  Delsarte LP    {float(lp):.6f}  (exact {lp})")
    return v, lp


def mask(coords):
    return sum(1 << c for c in coords)


def controls():
    """Every check must pass, or the formulation or the solve is wrong."""
    ok = True
    tol = 1e-4

    def line(good, text):
        nonlocal ok
        ok &= good
        print(f"[{'ok' if good else 'FAIL'}] {text}")

    # Closed entries: the SDP is an upper bound, so it can never drop below them.
    # A formulation that is too strong is rejected here.
    for n, d, exact in [(8, 4, 16), (12, 6, 24), (15, 6, 128), (12, 4, 144)]:
        v, _, status, viol = sdp_value(n, d)
        lp = float(delsarte_value(n, d))
        line(v >= exact - tol and v <= lp + tol and viol < 1e-6,
             f"A({n},{d}) = {exact}:  SDP {v:.4f}  LP {lp:.4f}  {status} viol {viol:.1e}")

    # Table I of the paper: the integer part must come back.  A formulation
    # that is too weak, or a solve that is not feasible, is rejected here.
    for n, d, table in [(19, 6, 1280), (19, 8, 142), (20, 8, 274)]:
        v, _, status, viol = sdp_value(n, d)
        lp = float(delsarte_value(n, d))
        line(floor(v + 1e-6) == table and v <= lp + tol and viol < 1e-6,
             f"Table I A({n},{d}) <= {table}:  SDP {v:.6f}  LP {lp:.4f}  {status} viol {viol:.1e}")

    # Actual codes are feasible points of value |C|, including at n = 22 and 23
    # where the solver fails: the failure is numerical, not in the model.
    blocks5 = [range(5 * b, 5 * b + 5) for b in range(4)]
    code5 = ([0] + [mask([*blocks5[p], *blocks5[q]]) for p, q in combinations(range(4), 2)]
             + [mask(range(20))])
    code6 = [0, mask(range(6)), mask(range(6, 12)), mask(range(12))]
    for n, d, code in [(22, 10, code5), (20, 10, code5), (23, 6, code6), (19, 6, code6)]:
        obj, viol, stray = code_point(n, d, code)
        line(abs(obj - len(code)) < 1e-9 and viol < 1e-8 and not stray,
             f"code of {len(code)} words feasible at ({n},{d}):  obj {obj:.6f}  viol {viol:.1e}")

    print("controls:", "all passed" if ok else "FAILED")
    return ok


if __name__ == "__main__":
    if len(sys.argv) >= 2 and sys.argv[1] == "--controls":
        sys.exit(0 if controls() else 1)
    if len(sys.argv) >= 3:
        report(int(sys.argv[1]), int(sys.argv[2]),
               sys.argv[3] if len(sys.argv) >= 4 else "CLARABEL")
    else:
        print(__doc__)

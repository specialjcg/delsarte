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

    (7)   beta^t_{i,j,k}, the block coefficients; `schrijver_algebra.py` defines
          them and carries the Gram identity their positivity comes from
    (19)  for k = 0..floor(n/2), with i, j in k..n-k, both matrices PSD:
              ( sum_t beta^t_{i,j,k} x^t_{i,j} )
              ( sum_t beta^t_{i,j,k} (x^0_{i+j-2t,0} - x^t_{i,j}) )
    (20)  x^0_{0,0} = 1;  0 <= x^t_{i,j} <= x^0_{i,0};
          x^0_{i,0} + x^0_{j,0} <= 1 + x^t_{i,j};
          x^t_{i,j} = 0 if {i, j, i+j-2t} meets {1, ..., d-1}
    (22)  maximise sum_i C(n,i) x^0_{i,0}

The block coefficients themselves live in `schrijver_algebra.py`, together with
the Gram identity their positivity comes from; `check_beta.py` replays both, and
runs without cvxpy so that CI can.

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
  * the block coefficients: `tools/check_beta.py` replays beta against (7) as
    exact integers for every (n,i,j,k,t) with n <= 24, and replays the Gram
    identity beta is defined by to n = 10, with two negative controls.  It runs
    in CI, so it is rerun by someone other than the author.  An earlier version
    of this line claimed instead that for n = 6 the spectrum of
    sum x^t_{i,j} M^t_{i,j} matched the blocks' spectra to 3e-14.  That
    comparison was made once, by hand, and never committed: no file here could
    reproduce it, and it is not a control.
  * the model never excludes an actual code: the point z = lambda / |C| of a
    real code satisfies every constraint, with objective |C| (`--controls`).

Measured on the default program, Clarabel with SCS as fallback:

    A(19,6)  1280.036247  Table I: 1280  Delsarte 1289.48  viol 2.2e-07
    A(19,8)   142.446060  Table I:  142  Delsarte  145.30  viol 1.7e-05  *
    A(20,8)   274.085704  Table I:  274  Delsarte  290.59  viol 3.9e-08

    * not a control: see UNCONTROLLED.  The floor is right, the residual is not
      small enough to stand on, and no solver setting brings it down.

An earlier version of this block quoted 1280.036, 142.447 and 274.072, which
were the restricted program's numbers.  They are close enough to look like the
same measurement and are not.

Known limitation, not hidden: the even-weight reduction (`--even`) is *not*
sound as implemented.  It forces every orbit component to be even, and on
d = 10 that cuts the feasible set below the true optimum: A(20,10) comes back
as 17.52 where the exact value is 40, and A(22,10) as 5.98 where a 64-word code
exists.  A bound under the true value is not a weak bound, it is a false one.
The default is therefore `even=False` -- the program valid for every code, and
the one `schrijver_cert.py` already used.

An earlier version of this note blamed the solver for those same numbers, and
that was wrong.  With `even=False`, A(22,10) solves cleanly to 87.97.  The
genuine numerical wall is narrower and it announces itself: at (21,10) Clarabel
raises SolverError rather than returning a wrong value, and SCS gives 51.81.

Requires cvxpy and clarabel (kept out of the repository; a scratch venv will
do).  Usage:

    schrijver_sdp.py n d          one entry
    schrijver_sdp.py --controls   anchors, Table I rows, real codes feasible
    schrijver_sdp.py ... --even   the restricted program, kept only to show
                                  that the controls reject it
"""

from itertools import combinations
from math import floor
from pathlib import Path
import sys

import cvxpy as cp
import numpy as np
import scipy.sparse as sp

sys.path.insert(0, str(Path(__file__).resolve().parent))
import delsarte_lp  # noqa: E402

# Re-exported rather than re-imported by `schrijver_cert.py`: what matters is
# that the solver, the certificate generator and `check_beta.py` share the same
# objects, not three copies of the same formula.
from schrijver_algebra import C, beta, mult, orbit, realisable  # noqa: E402,F401


def build(n, d, even=True):
    """Return (problem, z, keys): the SDP in z = m x, and orbit -> index of z.

    `even` applies the even-weight reduction for even d; switching it off gives
    the program valid for every code, without that lemma.
    """

    def zero(key):
        if key == (0, 0, 0):
            return False
        if any(1 <= v <= d - 1 for v in key):
            return True
        return even and d % 2 == 0 and any(v % 2 for v in key)

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


SOLVERS = ("CLARABEL", "SCS")
ACCEPT = 1e-6        # violation below which a point is good enough to keep

# Clarabel runs at its defaults on purpose: tightening tol_gap and tol_feas to
# 1e-12 changed (15,6) by not one bit, so the knobs buy nothing and only cost
# iterations.  SCS is the fallback and is kept sober -- at eps 1e-11 with
# 200000 iterations it never returns, and burned a ten-minute budget on the
# first control without printing a line.
SOLVER_OPTS = {
    "CLARABEL": {},
    "SCS": dict(eps_abs=1e-10, eps_rel=1e-10, max_iters=50000),
}

# Cases where the full program is out of reach of the free solvers: the value
# comes back right, the violation does not come down, and no setting moves it.
# At (19,8) Clarabel converges to 1.7e-5 and five times the iteration budget
# does not shift a digit, while SCS collapses onto the bare Delsarte value at
# violations of 0.2 to 0.6 -- worse the longer it runs.  They are reported and
# left out of the verdict rather than passed by loosening ACCEPT, which would
# hide them.  The remedy is arbitrary precision (SDPA-GMP), not more
# iterations.  It is not a size effect: (19,6) has 156 variables and settles at
# 2.2e-7, better than (19,8) with 86.  Why these two resist is not understood.
UNCONTROLLED = {
    (19, 8): "Clarabel stalls at 1.7e-5, SCS diverges to the LP value",
    (22, 10): "Clarabel stalls at 2.8e-6",
}


def sdp_value(n, d, solver=None, even=False):
    """Solve and return (value, nvars, status, max violation).

    With `solver=None` the entries of `SOLVERS` are tried in order and the
    first point under `ACCEPT` wins; if none qualifies, the smallest violation
    does.  Neither solver is reliable alone on the full program: Clarabel
    stalls at (15,6) on a 3.5e-6 violation that tighter tolerances do not move
    at all and SCS clears to 5e-9, while SCS collapses at (19,8) onto the bare
    Delsarte value with a violation of 0.2.  Choosing per case beats trusting
    either one, and stopping early keeps the cases Clarabel already settles
    from paying for a second solve.

    The violation measures feasibility, never correctness.  The even-weight
    reduction used to return A(22,10) <= 5.98 -- false by a factor of ten --
    at a violation of 2.3e-17.  A clean residual on a wrong model is still a
    wrong answer, which is why `controls` guards values, not residuals.
    """
    prob, z, keys = build(n, d, even)
    best = None
    for name in ([solver] if solver else SOLVERS):
        try:
            prob.solve(solver=name, **SOLVER_OPTS.get(name, {}))
        except Exception:
            continue
        if prob.status not in ("optimal", "optimal_inaccurate"):
            continue
        viol = max_violation(prob)
        if best is None or viol < best[3]:
            best = (prob.value, len(keys), prob.status, viol)
        if viol < ACCEPT:
            break
    if best is None:
        raise RuntimeError(f"A({n},{d}): no solver returned a usable point")
    return best


def code_point(n, d, code, even=False):
    """Plug an actual code into the model: (objective, max violation, stray orbits).

    z^t_{i,j} = lambda^t_{i,j} / |C|, with lambda counting the triples (X, Y, Z)
    of codewords such that |X^Y| = i, |X^Z| = j, |(X^Y) & (X^Z)| = t.  A stray
    orbit is one the model forces to zero although the code populates it.

    `even` must match the program being measured, or the witness is tested
    against a formulation nobody solved.
    """
    prob, z, keys = build(n, d, even)
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


def report(n, d, solver=None, even=False):
    v, nv, status, viol = sdp_value(n, d, solver, even)
    lp = delsarte_value(n, d)
    fl = floor(v + 1e-6)
    print(f"A({n},{d})  vars={nv}  status={status}  maxViolation={viol:.1e}")
    print(f"  Schrijver SDP  {v:.6f}  -> floor {fl}  (margin below {fl + 1}: {fl + 1 - v:.6f})")
    # A float sitting just under an integer does not decide that floor: at
    # (16,8) the optimum is 32 and the solve returns 31.999994, which floors to
    # 31 and would be a false bound.  Only the exact rounding decides, which is
    # what schrijver_cert.py is for.  Say so rather than tune the fudge factor.
    if fl + 1 - v < 1e-3:
        print(f"  ^ within {fl + 1 - v:.1e} of {fl + 1}:"
              f" the float does not decide this floor")
    print(f"  Delsarte LP    {float(lp):.6f}  (exact {lp})")
    return v, lp


def mask(coords):
    return sum(1 << c for c in coords)


def controls(even=False):
    """Every check must pass, or the formulation or the solve is wrong."""
    ok = True
    tol = 1e-4

    def line(good, text):
        nonlocal ok
        ok &= good
        print(f"[{'ok' if good else 'FAIL'}] {text}")

    def check(n, d, good, text):
        """Report a case, withholding the verdict where no solver reaches ACCEPT.

        Only on the full program: under `--even` these same cases converge to
        1e-13, and the guard must still fail on them -- that is the point.
        """
        if not even and (n, d) in UNCONTROLLED:
            print(f"[skip] {text}  -- {UNCONTROLLED[(n, d)]}")
        else:
            line(good, text)

    # Closed entries: the SDP is an upper bound, so it can never drop below them.
    # A formulation that is too strong is rejected here.
    for n, d, exact in [(8, 4, 16), (12, 6, 24), (15, 6, 128), (12, 4, 144)]:
        v, _, status, viol = sdp_value(n, d, even=even)
        lp = float(delsarte_value(n, d))
        check(n, d, v >= exact - tol and v <= lp + tol and viol < ACCEPT,
              f"A({n},{d}) = {exact}:  SDP {v:.4f}  LP {lp:.4f}  {status} viol {viol:.1e}")

    # Open entries at d = 10, where the even-weight reduction collapsed the
    # model below the truth and nothing here noticed.  Only a lower guard
    # catches that: a bound under the true value is not weak, it is false.
    # Values read from Brouwer's table, see tools/crosscheck_brouwer.py.
    for n, d, atleast in [(18, 10, 10), (20, 10, 40), (22, 10, 64)]:
        v, _, status, viol = sdp_value(n, d, even=even)
        check(n, d, v >= atleast - tol and viol < ACCEPT,
              f"A({n},{d}) >= {atleast}:  SDP {v:.4f}  {status} viol {viol:.1e}")

    # Table I of the paper: the integer part must come back.  A formulation
    # that is too weak, or a solve that is not feasible, is rejected here.
    for n, d, table in [(19, 6, 1280), (19, 8, 142), (20, 8, 274)]:
        v, _, status, viol = sdp_value(n, d, even=even)
        lp = float(delsarte_value(n, d))
        check(n, d, floor(v + 1e-6) == table and v <= lp + tol and viol < ACCEPT,
              f"Table I A({n},{d}) <= {table}:  SDP {v:.6f}  LP {lp:.4f}  {status} viol {viol:.1e}")

    # Actual codes are feasible points of value |C|.  These witnesses are small
    # -- 4 and 8 words -- and that is their weakness: at (22,10) a 64-word code
    # exists, so an 8-word witness passed while the model was returning 5.98.
    blocks5 = [range(5 * b, 5 * b + 5) for b in range(4)]
    code5 = ([0] + [mask([*blocks5[p], *blocks5[q]]) for p, q in combinations(range(4), 2)]
             + [mask(range(20))])
    code6 = [0, mask(range(6)), mask(range(6, 12)), mask(range(12))]
    for n, d, code in [(22, 10, code5), (20, 10, code5), (23, 6, code6), (19, 6, code6)]:
        obj, viol, stray = code_point(n, d, code, even)
        line(abs(obj - len(code)) < 1e-9 and viol < 1e-8 and not stray,
             f"code of {len(code)} words feasible at ({n},{d}):  obj {obj:.6f}  viol {viol:.1e}")

    print("controls:", "all passed" if ok else "FAILED")
    return ok


if __name__ == "__main__":
    even = "--even" in sys.argv
    argv = [a for a in sys.argv if a != "--even"]
    if len(argv) >= 2 and argv[1] == "--controls":
        sys.exit(0 if controls(even) else 1)
    if len(argv) >= 3:
        report(int(argv[1]), int(argv[2]),
               argv[3] if len(argv) >= 4 else None, even)
    else:
        print(__doc__)

#!/usr/bin/env python3
"""Schrijver's block coefficients for the Terwilliger algebra of the Hamming cube.

Split out of `schrijver_sdp.py` so that it depends on nothing but the standard
library: `check_beta.py` has to import the *same* functions the solver and the
certificate generator use, and it runs in CI, where cvxpy is not installed.  A
check carrying its own copy of the formula it checks would check nothing -- this
repository has already had two files silently solving different programs once.

Reference: A. Schrijver, "New code upper bounds from the Terwilliger algebra
and semidefinite programming", IEEE Trans. Inf. Theory 51 (2005) 2859-2866.

    (7)   beta^t_{i,j,k} = sum_u (-1)^(u-t) C(u,t) C(n-2k,u-k) C(n-k-u,i-u) C(n-k-u,j-u)
    (7')  beta^t_{i,j,k} = sum_r (-1)^(k-t+r) C(k,t-r) mult_{n-2k}(i-k, j-k, r)

`beta()` computes (7'), not (7).  The two agree as integers for every
(n, i, j, k, t) with n <= 24, which `check_beta.py` replays, and (7') is the form
the blocks' positivity can be proved from.  Fix k disjoint pairs (a_l, b_l) of
coordinates and put

    c(v) = prod_l ([a_l in v] - [b_l in v]),

non-zero exactly when each pair contributes one element to v.  Then

    sum_{|v|=i, |w|=j, |v^w|=t} c(v) c(w) = 2^k beta^t_{i,j,k},

by splitting the 2k paired coordinates off from the n - 2k free ones: writing s
for the number of pairs on which v and w agree, |v ^ w| = s + |v_F ^ w_F| and
c(v) c(w) = (-1)^(k-s), and there are C(k,s) 2^k sign patterns with s agreements.
Summing over s + r = t is (7').  It also explains why i runs over k..n-k and not
0..n: c(v) vanishes unless v meets every pair, so |v| >= k, and likewise for the
complement.

The consequence is the point.  A block entry becomes u_i^T M u_j for the explicit
vectors u_i = sum_{|v|=i} c(v) e_v, so for every w

    w^T B_k w = z^T M z,   z = sum_i w_i u_i,

and M is a sum of rank-one matrices when it comes from a code: with
M_{v,w} = |{x in C : x+v in C, x+w in C}| / |C| it is a sum of chi chi^T, and the
second family of (19) is the same sum over x not in C.  The blocks are positive
because that is a sum of squares -- no eigenvalue, no C*-algebra.  It is the
shape `Delsarte/Hamming/Feasible.lean` already uses one level down, in
`sum_sum_krawtchouk_nonneg`.

None of this is proved here.  (7) = (7') is checked, not derived, and the Gram
identity is checked by brute force only up to the n where 2^n subsets can be
enumerated.  `check_beta.py` states exactly which.

(7) as written is also not integer arithmetic: `(-1) ** (u - t)` returns a float
whenever u < t, which is every t >= 1.  Nothing was lost -- the values stay five
orders of magnitude under 2^53 -- but nothing checked that either, and the
certificate generator was reading them.
"""

from math import comb, factorial


def C(a, b):
    return comb(a, b) if 0 <= b <= a else 0


def realisable(n, i, j, t):
    return 0 <= t <= min(i, j) and i + j - t <= n


def mult(n, i, j, t):
    """Pairs (v, w) with |v| = i, |w| = j, |v ^ w| = t; zero when there are none.

    `beta` evaluates it outside the realisable region, where the factorials would
    raise rather than return the zero the sum wants.
    """
    if not realisable(n, i, j, t):
        return 0
    return factorial(n) // (factorial(i - t) * factorial(j - t) * factorial(t)
                            * factorial(n - i - j + t))


def beta(n, i, j, k, t):
    """The block coefficient, as (7') rather than (7); see the module docstring."""
    return sum((1 if (k - t + r) % 2 == 0 else -1) * C(k, t - r)
               * mult(n - 2 * k, i - k, j - k, r)
               for r in range(t + 1))


def orbit(i, j, t):
    return tuple(sorted((i, j, i + j - 2 * t)))

/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Table1
import Delsarte.Certificate.Table2
import Delsarte.Certificate.Table3

/-!
# A table of certified bounds on `A(n, 2, d)`

Same machinery as `Delsarte.Certificate.Bounds`, applied in bulk. Every vector
below is the optimum of the linear program, computed by `tools/delsarte_lp.py`
and re-verified here; the solver is a source of candidates and appears in no
proof.

The declarations live in `Table1`, `Table2` and `Table3`, which import only the
verifier and therefore elaborate in parallel; this module is the index and the
documentation. Every check there is decided by the kernel in `ℤ`, on the
certificate scaled by its common denominator — see
`Delsarte/Certificate/Integer.lean`; the `#guard` lines re-run the same
certificates through the rational checker and the *binomial* definition of
`krawtchouk`, so each bound is evaluated twice by routes that share no
arithmetic. They are **generated** by `delsarte_lp.emit_lean` rather
than typed. Transcribing a dozen certificates by hand is a good way to introduce a
typo that no theorem would catch — a wrong `y` is usually infeasible, but it can
also be feasible and prove a *different*, weaker bound without anyone noticing.
Generation removes that step; Lean re-checks the result, and
`Delsarte/Certificate/Files.lean` pins each `.cert` file to the definition here.

| bound | true value | Hamming bound |
|---|---|---|
| `A(6,2,3) ≤ 8` | 8 | 9 |
| `A(7,2,4) ≤ 8` | 8 | 16 |
| `A(8,2,4) ≤ 16` | 16 | 28 |
| `A(10,2,5) ≤ 12` | 12 | 18 |
| `A(11,2,5) ≤ 24` | 24 | 30 |
| `A(12,2,5) ≤ 40` | 32 | 51 |
| `A(13,2,3) ≤ 512` | 512 | 585 |
| `A(14,2,5) ≤ 128` | 128 | 154 |
| `A(15,2,5) ≤ 256` | 256 | 270 |
| `A(12,2,6) ≤ 24` | 24 | 51 |
| `A(15,2,6) ≤ 128` | 128 | 270 |
| `A(24,2,8) ≤ 4096` | 4096 | 7216 |

Only upper halves. No code is constructed anywhere in this repository, so no line
of this table may be read as an equality — the "true value" column is quoted from
the literature, not proved here.

`A(12,2,5) ≤ 40` is the entry that is *not* tight, and it is kept for that reason:
the true value is 32, and the plain Delsarte linear program does not reach it.
A table showing only its successes would be advertising.

Every other row is tight, and every row beats the sphere-packing bound in the
last column — which is the point. These are bounds the linear program earns and
elementary counting does not.
-/

namespace Delsarte.Certificate

end Delsarte.Certificate

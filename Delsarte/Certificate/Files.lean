/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Parse
import Delsarte.Certificate.Bounds

/-!
# The shipped certificate files, checked against Lean

A `.cert` file that nothing reads is decoration, and worse, a `.cert` file that
drifts away from the Lean certificate of the same name is a lie about what was
proved. Each file is pulled in with `include_str` and checked when this module
elaborates: the build fails unless the file parses, declares the same `n, q, d`
as the Lean statement, defines the same vector, and passes the checker.

One limitation, measured rather than assumed. Lake does **not** re-elaborate this
module when only a `.cert` changes — neither `IO.FS.readFile` nor `include_str`
makes it a tracked input in this toolchain; both were tried, and a corrupted file
sailed through an incremental build in each case. Forcing re-elaboration does fail
the build, so the guarantee is exactly this: **every fresh build runs these
checks**, which is what CI does on each push. Locally, an incremental build can
miss a `.cert` edit until the module is touched, and
`lake exe delsarte-verify --self-check` is the answer there.

The last file is the opposite case, and is there on purpose: it is well formed,
so the parser accepts it, and the checker refuses it. Parsing and checking are
different jobs and the repository shows both failing modes.

`lake exe delsarte-verify` does the same replay from a terminal, for a reader who
would rather not read any Lean. It is a convenience, not the guarantee; linking it
means compiling mathlib to native code, so it is built on demand rather than in
CI, while the checks below run on every build.
-/

namespace Delsarte.Certificate

/-- Does this file content agree with the Lean certificate in every respect, and
pass the checker? -/
def fileAgrees (content : String) (n q d : ℕ) (y : ℕ → ℚ) : Bool :=
  match parseCert content with
  | .error _ => false
  | .ok c =>
      c.n == n && c.q == q && c.d == d
        && (List.range c.n).all (fun j => c.coeff (j + 1) == y (j + 1))
        && c.check

/-- Does this file content parse, and then get *refused* by the checker? -/
def fileParsesButFails (content : String) : Bool :=
  match parseCert content with
  | .error _ => false
  | .ok c => !c.check

-- The `#`-command linter is off here on purpose: these commands are the point.
set_option linter.hashCommand false

#guard fileAgrees (include_str "examples/a-5-3.cert") 5 2 3 certFiveThree
#guard fileAgrees (include_str "examples/a-5-3-optimal.cert") 5 2 3 certFive
#guard fileAgrees (include_str "examples/a-13-5.cert") 13 2 5 certThirteen
#guard fileAgrees (include_str "examples/a-23-7.cert") 23 2 7 certGolay
#guard fileParsesButFails (include_str "examples/bad-not-feasible.cert")

end Delsarte.Certificate

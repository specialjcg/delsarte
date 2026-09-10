/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte.Certificate.Verify

/-!
# Parsing a certificate file

`Delsarte/Certificate/FORMAT.md` describes the file format; this is its reader.

## Why a parser is not plumbing

A parser produces a *statement*. It decides which `n`, `q`, `d` the bound is
about, so a lax reader that silently accepts a malformed `d` is worse than no
reader at all: it would replay a check and report a claim about a different
problem. Every rule of the format is therefore enforced and every failure is
named:

* exactly four directives, in the order `n`, `q`, `d`, `y`, nothing else;
* `#` starts a whole-line comment; there are no trailing comments, so a stray
  `#` inside a data line is an error rather than a silently dropped tail;
* rationals are `p` or `p/q` with `p` an optional `-` followed by digits and `q`
  digits with nonzero value. No decimal point, no exponent, no whitespace inside
  a number — a format that cannot express `0.1` cannot silently round it;
* `y` carries exactly `n` values, `1 ≤ d ≤ n`, and `2 ≤ q`.

## What reading a file does not do

Nothing here proves anything. `CertFile.coeff` turns a parsed file into the
`ℕ → ℚ` that `DualCert` consumes, and that is the whole contribution: the proof
is still the Lean theorem, and the executable that calls this parser is a replay.
-/

namespace Delsarte.Certificate

/-- A parsed certificate file. -/
structure CertFile where
  /-- Code length. -/
  n : ℕ
  /-- Alphabet size. -/
  q : ℕ
  /-- Minimum distance. -/
  d : ℕ
  /-- The dual vector, `n` values, indexed `k = 1 … n`. -/
  y : List ℚ
deriving Repr, DecidableEq

/-- Digits only, and at least one. `String.toNat?` is not used on its own because
the point here is to reject anything the format does not name. -/
def parseNatStrict (s : String) : Option ℕ :=
  if s ≠ "" && s.all Char.isDigit then s.toNat? else none

/-- An optional single leading `-`, then digits. No `+`, no spaces, no point. -/
def parseIntStrict (s : String) : Option ℤ :=
  if s.startsWith "-" then (parseNatStrict (s.drop 1).toString).map (fun m => -(m : ℤ))
  else (parseNatStrict s).map (fun m => (m : ℤ))

/-- `p` or `p/q`. Anything else — a decimal point, an exponent, a zero
denominator — is rejected. -/
def parseRat (s : String) : Option ℚ :=
  match s.splitOn "/" with
  | [a] => (parseIntStrict a).map (fun z => (z : ℚ))
  | [a, b] =>
      match parseIntStrict a, parseNatStrict b with
      | some z, some m => if m = 0 then none else some ((z : ℚ) / (m : ℚ))
      | _, _ => none
  | _ => none

/-- `String.trimAscii` as a `String`. -/
def trimStr (s : String) : String := s.trimAscii.toString

/-- Split a line into space-separated tokens. -/
def tokens (line : String) : List String :=
  ((line.splitOn " ").map trimStr).filter (· ≠ "")

private def expectNat (key : String) (ts : List String) : Except String ℕ :=
  match ts with
  | [k, v] =>
      if k ≠ key then Except.error s!"expected directive '{key}', found '{k}'"
      else match parseNatStrict v with
        | some m => Except.ok m
        | none => Except.error s!"'{key}': '{v}' is not a natural number"
  | _ => Except.error s!"directive '{key}' takes exactly one value"

private def expectRats (ts : List String) : Except String (List ℚ) :=
  match ts with
  | "y" :: vs =>
      vs.foldlM (fun acc s =>
        match parseRat s with
        | some r => Except.ok (acc ++ [r])
        | none => Except.error s!"'y': '{s}' is not a rational in the accepted form")
        []
  | k :: _ => Except.error s!"expected directive 'y', found '{k}'"
  | [] => Except.error "expected directive 'y'"

/-- Read a certificate file. Every rule of the format is enforced, and every
failure is named. -/
def parseCert (content : String) : Except String CertFile :=
  let ls := ((content.splitOn "\n").map trimStr).map fun l => (l.splitOn "\r").headD l
  let dataLines := ls.filter fun l => l ≠ "" && !l.startsWith "#"
  let ds := dataLines.map tokens
  match ds with
  | [tn, tq, td, ty] =>
      match expectNat "n" tn, expectNat "q" tq, expectNat "d" td, expectRats ty with
      | Except.ok n, Except.ok q, Except.ok d, Except.ok y =>
          if y.length ≠ n then
            Except.error s!"'y' carries {y.length} values, but n = {n}"
          else if q < 2 then
            Except.error s!"q = {q}: the alphabet must have at least two letters"
          else if d = 0 ∨ n < d then
            Except.error s!"d = {d} must satisfy 1 ≤ d ≤ n = {n}"
          else
            Except.ok (CertFile.mk n q d y)
      | Except.error e, _, _, _ => Except.error e
      | _, Except.error e, _, _ => Except.error e
      | _, _, Except.error e, _ => Except.error e
      | _, _, _, Except.error e => Except.error e
  | _ =>
      Except.error s!"expected exactly four directives n, q, d, y; found {ds.length}"

/-- The parsed vector as the `ℕ → ℚ` that `DualCert` consumes: `y k` for
`1 ≤ k ≤ n`, and zero elsewhere. -/
def CertFile.coeff (c : CertFile) (k : ℕ) : ℚ :=
  if 1 ≤ k && k ≤ c.n then c.y.getD (k - 1) 0 else 0

/-- Running the checker on a parsed file. Proves nothing; it is the replay. -/
def CertFile.check (c : CertFile) : Bool := dualCheck c.n c.q c.d c.coeff

/-- The bound a parsed file claims. -/
def CertFile.claimedBound (c : CertFile) : ℚ :=
  _root_.Delsarte.Certificate.bound c.n c.q c.coeff

/-! ## What the parser refuses

A parser that has never rejected anything has not shown it is strict, and
strictness is the whole point: a lax reader would replay a check and report a
claim about a different problem. Each line below is a file the reader must
refuse, and does.
-/

/-- True when the parser refuses the input. -/
def rejects (s : String) : Bool := (parseCert s).toOption.isNone

/-- A well-formed file, for contrast. -/
def sampleGood : String := "# comment\nn 5\nq 2\nd 3\ny 1 0 0 0 0\n"

-- The `#`-command linter is off here on purpose: these commands are the point.
set_option linter.hashCommand false

#guard !rejects sampleGood
#guard (parseCert sampleGood).toOption.map CertFile.n == some 5
#guard (parseCert sampleGood).toOption.map CertFile.d == some 3

-- a decimal: the format cannot express it, so it cannot silently round it
#guard rejects "n 5\nq 2\nd 3\ny 0.5 0 0 0 0\n"
-- an exponent, same reason
#guard rejects "n 5\nq 2\nd 3\ny 1e3 0 0 0 0\n"
-- a zero denominator
#guard rejects "n 5\nq 2\nd 3\ny 1/0 0 0 0 0\n"
-- a trailing comment on a data line: only whole-line comments exist
#guard rejects "n 5\nq 2\nd 3\ny 1 0 0 0 0 # tail\n"
-- too few values for the declared n
#guard rejects "n 5\nq 2\nd 3\ny 1 0 0 0\n"
-- too many
#guard rejects "n 5\nq 2\nd 3\ny 1 0 0 0 0 0\n"
-- directives out of order
#guard rejects "q 2\nn 5\nd 3\ny 1 0 0 0 0\n"
-- a fifth directive
#guard rejects "n 5\nq 2\nd 3\ny 1 0 0 0 0\nz 1\n"
-- a missing directive
#guard rejects "n 5\nq 2\ny 1 0 0 0 0\n"
-- an unknown key in place of a known one
#guard rejects "len 5\nq 2\nd 3\ny 1 0 0 0 0\n"
-- parameters out of range
#guard rejects "n 5\nq 2\nd 0\ny 1 0 0 0 0\n"
#guard rejects "n 5\nq 2\nd 6\ny 1 0 0 0 0\n"
#guard rejects "n 5\nq 1\nd 3\ny 1 0 0 0 0\n"

-- Parsing and checking are separate: this file is well formed, and the checker
-- is what refuses it.
#guard !rejects "n 5\nq 2\nd 3\ny -1 0 0 0 0\n"
#guard ((parseCert "n 5\nq 2\nd 3\ny -1 0 0 0 0\n").toOption.map CertFile.check) == some false

end Delsarte.Certificate

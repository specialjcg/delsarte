/-
Copyright (c) 2026 Jean-Charles Gouleau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Charles Gouleau
-/
import Delsarte

/-!
# `delsarte-verify` — replaying a certificate file

This executable **proves nothing**. It parses a `.cert` file, runs the compiled
checker on it, and prints what the file claims. The proof is the Lean theorem in
`Delsarte/Certificate/Bounds.lean`; this is the independent replay that a reader
can run without reading any Lean.

Because a parser decides *which* statement is at stake, the report always shows
`n`, `q` and `d` next to the bound. A claim without its parameters is not a claim.

`--self-check` compares each shipped `.cert` against the certificate defined in
Lean. Without it the two could drift apart silently, which is the one failure a
repository of certificates must not have.
-/

open Delsarte Delsarte.Certificate

/-- Floor of a rational, by flooring integer division. -/
def floorRat (r : ℚ) : Int := Int.fdiv r.num r.den

/-- The `.cert` files shipped with the repository, each paired with the
certificate the Lean proofs actually use. -/
def known : List (String × (Nat → ℚ)) :=
  [ ("Delsarte/Certificate/examples/a-5-3.cert", certFiveThree)
  , ("Delsarte/Certificate/examples/a-5-3-optimal.cert", certFive)
  , ("Delsarte/Certificate/examples/a-13-5.cert", certThirteen)
  , ("Delsarte/Certificate/examples/a-23-7.cert", certGolay)
  , ("Delsarte/Certificate/examples/a-6-3.cert", cert6_3)
  , ("Delsarte/Certificate/examples/a-7-4.cert", cert7_4)
  , ("Delsarte/Certificate/examples/a-8-4.cert", cert8_4)
  , ("Delsarte/Certificate/examples/a-10-5.cert", cert10_5)
  , ("Delsarte/Certificate/examples/a-11-5.cert", cert11_5)
  , ("Delsarte/Certificate/examples/a-12-5.cert", cert12_5)
  , ("Delsarte/Certificate/examples/a-13-3.cert", cert13_3)
  , ("Delsarte/Certificate/examples/a-14-5.cert", cert14_5)
  , ("Delsarte/Certificate/examples/a-15-5.cert", cert15_5)
  , ("Delsarte/Certificate/examples/a-12-6.cert", cert12_6)
  , ("Delsarte/Certificate/examples/a-15-6.cert", cert15_6)
  , ("Delsarte/Certificate/examples/a-24-8.cert", cert24_8) ]

/-- Parse one file, run the checker, print the claim. -/
def replay (path : String) : IO Bool := do
  let content ← IO.FS.readFile path
  match parseCert content with
  | Except.error e =>
      IO.println s!"{path}"
      IO.println s!"  PARSE ERROR: {e}"
      return false
  | Except.ok c =>
      let ok := c.check
      IO.println s!"{path}"
      IO.println s!"  parameters    : n = {c.n}, q = {c.q}, d = {c.d}"
      IO.println s!"  dual feasible : {if ok then "yes" else "NO"}"
      IO.println s!"  bound         : {c.claimedBound}"
      if !ok then
        IO.println "  claim         : none, the certificate was rejected"
        return false
      if c.q != 2 then
        IO.println "  claim         : none, the soundness theorem covers q = 2 only"
        return true
      IO.println s!"  claim         : A({c.n}, {c.q}, {c.d}) <= {floorRat c.claimedBound}"
      return true

/-- Check that every shipped file still agrees with the Lean certificate of the
same name. -/
def selfCheck : IO Bool := do
  let mut allOk := true
  for (path, f) in known do
    let content ← IO.FS.readFile path
    match parseCert content with
    | Except.error e =>
        IO.println s!"{path}: PARSE ERROR: {e}"
        allOk := false
    | Except.ok c =>
        let agree := (List.range c.n).all fun j => c.coeff (j + 1) == f (j + 1)
        let verdict := if agree then "agrees with the Lean certificate" else "DIFFERS FROM LEAN"
        IO.println s!"{path}: {verdict}"
        if !agree then allOk := false
  return allOk

def usage : IO Unit := do
  IO.println "usage:"
  IO.println "  delsarte-verify <file.cert> ...   replay one or more certificates"
  IO.println "  delsarte-verify --self-check      check the shipped files against Lean"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => usage; return 1
  | ["--self-check"] =>
      let ok ← selfCheck
      if ok then IO.println "\nself-check: all files agree with Lean." else
        IO.println "\nself-check: FAILED."
      return (if ok then 0 else 1)
  | files =>
      let mut allOk := true
      for f in files do
        let ok ← replay f
        if !ok then allOk := false
      IO.println ""
      IO.println "This program proves nothing. It runs the checker; the proof is the"
      IO.println "Lean theorem in Delsarte/Certificate/Bounds.lean."
      return (if allOk then 0 else 1)

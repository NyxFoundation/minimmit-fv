import Lean.Util.CollectAxioms
import Minimmit

/-!
# Axiom audit (CI gate)

Pins the axiom footprint of the formalization (issue #24). Two layers:

1. **Headline lemmas** — a `#guard_msgs`-checked `#print axioms` for each of
   the 10 statements (plus `lemma_5_1_seen`, the only consumer of the crypto
   axiom). A PR that changes any lemma's axiom set must edit this file
   visibly.
2. **Whole-library sweep** — every declaration compiled into a `Minimmit.*`
   module is scanned for *direct* references to axioms outside the allowlist
   below, and for axiom declarations outside it. This catches a `sorry` /
   `admit` (both elaborate to `sorryAx`), a stray `native_decide`
   (`Lean.ofReduceBool`), or a newly declared axiom anywhere in the library —
   including helpers not reachable from the headline lemmas.

Axioms reachable from the lemmas but only *via Mathlib* are covered by
layer 1; layer 2 deliberately checks direct references only, which keeps the
sweep fast and flags each offending declaration at its own site.
-/

set_option autoImplicit false

open Lean

/-- The axioms permitted in this development: Lean's three classical-logic
    axioms plus the idealized-cryptography axiom of `Minimmit.Axioms`
    (Barrier 1). Extending this list is a reviewable act. -/
def axiomAllowlist : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound, ``Minimmit.signature_unforgeable]

open Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : NameSet := axiomAllowlist.foldl (·.insert ·) {}
  let isAxiom (n : Name) : Bool :=
    match env.find? n with
    | some (.axiomInfo _) => true
    | _ => false
  let mut offenders : Array MessageData := #[]
  for (declName, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? declName | continue
    unless (env.header.moduleNames[idx.toNat]!).getRoot == `Minimmit do continue
    -- a new axiom declared inside the library
    if isAxiom declName && !allowed.contains declName then
      offenders := offenders.push
        m!"'{declName}' is an axiom outside the allowlist"
    -- a direct reference to a disallowed axiom (covers `sorryAx` et al.)
    let used := info.type.getUsedConstants
      ++ (info.value?.map (·.getUsedConstants)).getD #[]
    for c in used do
      if isAxiom c && !allowed.contains c then
        offenders := offenders.push
          m!"'{declName}' directly uses disallowed axiom '{c}'"
  unless offenders.isEmpty do
    throwError m!"Axiom audit failed:\n{MessageData.joinSep offenders.toList Format.line}"
  logInfo m!"Axiom audit passed: every Minimmit declaration stays within {axiomAllowlist}"

namespace Minimmit

/-- info: 'Minimmit.lemma_5_1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lemma_5_1

/-- info: 'Minimmit.lemma_5_1_seen' depends on axioms: [propext, signature_unforgeable] -/
#guard_msgs in
#print axioms lemma_5_1_seen

/-- info: 'Minimmit.lemma_5_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_5_2

/-- info: 'Minimmit.lemma_5_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_5_3

/-- info: 'Minimmit.lemma_5_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_5_4

/-- info: 'Minimmit.lemma_5_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_5_5

/-- info: 'Minimmit.lemma_5_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_5_6

/-- info: 'Minimmit.lemma_5_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_5_7

/-- info: 'Minimmit.lemma_5_8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_5_8

/-- info: 'Minimmit.lemma_5_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_5_9

/-- info: 'Minimmit.lemma_5_10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemma_5_10

end Minimmit

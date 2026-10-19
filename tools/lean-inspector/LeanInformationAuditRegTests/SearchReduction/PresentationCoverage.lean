import LeanInformationAuditRegAnalysis.SearchReduction.Presentation
import LeanInformationAuditRegTests.SearchReduction.SingleSourceModel
import LeanInformationAuditRegTests.SearchReduction.PresentationBaseline

/-! Counterexamples for presentation prefilters. These tests exercise the wide structure-exclusion converter; baseline
certification uses the separate single-source relation. -/
namespace LeanInformationAudit.Tests.SearchReduction.PresentationCoverage
open Lean Meta Elab
open LeanInformationAudit.SearchReduction
open PresentationBaseline

/-- A key preserved as an equality by both projections cannot distinguish any
two statements in the same telescope. This does not exclude asymmetric filters
or a necessary condition that also accounts for the baseline. -/
theorem projection_key_constant {Statement Key : Type*}
    (pack : Statement → Statement → Statement) (key : Statement → Key)
    (left : ∀ p q, key (pack p q) = key p)
    (right : ∀ p q, key (pack p q) = key q) (p q : Statement) : key p = key q :=
  (left p q).symm.trans (right p q)

/-- An actual baseline projection supplies arithmetic information absent from
the unrelated source statement used by the conversion test. -/
theorem packagedBaseline (n : Nat) : ramp n = 3 * n ∧ True := by
  constructor
  · have h := ramp_value n
    omega
  · trivial

abbrev scaled (n : Nat) : Nat := 3 * n

abbrev namedStatement (n : Nat) : Prop := ramp n = 3 * n

private def statement (stx : Syntax) : TermElabM Expr := do
  let type ← Term.elabTerm stx (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars type

private def requireConversion (label : String) (target source : Syntax)
    (index : FactIndex := {}) (dependency? : Option Name := none) : TermElabM Unit := do
  let target ← statement target
  let source ← statement source
  let saved ← saveState
  let some conversion ← try restatementConversion target source index
    catch ex => throwError "presentation coverage {label}: {ex.toMessageData}"
    | throwError "presentation coverage counterexample failed: {label}"
  let type ← mkArrow source target
  let conversion ← instantiateMVars conversion
  if let some dependency := dependency? then
    unless conversion.getUsedConstants.contains dependency do
      throwError "presentation coverage did not consume baseline fact: {label}"
  let axioms ← checkProof (← mkFreshUserName `_presentationCoverage) [] type conversion
  unless standardAxioms axioms do throwError "nonstandard coverage axioms: {label}"
  saved.restore
  logInfo m!"presentation coverage: {label}: kernel-checked"

run_elab do
  -- Definitional aliases in explicit subterms and linear arithmetic.
  requireConversion "proposition definition alias"
    (← `(∀ n : Nat, namedStatement n))
    (← `(∀ n : Nat, ramp n = 3 * n))
  requireConversion "nested definition alias"
    (← `(∀ n : Nat, ramp (scaled n) = ramp (3 * n)))
    (← `(∀ n : Nat, n = n))
  requireConversion "arithmetic alias"
    (← `(∀ n : Nat, ramp n = 3 * n))
    (← `(∀ n : Nat, ramp n = n + n + n))
  -- Projection erases all of the unselected component, including its atoms.
  requireConversion "left projection"
    (← `(∀ P Q : Prop, P)) (← `(∀ P Q : Prop, P ∧ Q))
  requireConversion "right projection"
    (← `(∀ P Q : Prop, Q)) (← `(∀ P Q : Prop, P ∧ Q))
  -- Each Iff direction keeps the source's entire outer telescope.
  requireConversion "forward iff"
    (← `(∀ P Q : Prop, P → Q)) (← `(∀ P Q : Prop, P ↔ Q))
  requireConversion "backward iff"
    (← `(∀ P Q : Prop, Q → P)) (← `(∀ P Q : Prop, P ↔ Q))
  -- Packing adds a universally true side condition without new content.
  requireConversion "arithmetic packing"
    (← `(∀ n : Nat, ramp n = 3 * n ∧ 0 ≤ n))
    (← `(∀ n : Nat, ramp n = n + n + n))
  -- Raw opaque-symbol support need not be preserved even without B facts.
  requireConversion "independent reflexive atoms"
    (← `(∀ n : Nat, ramp n = ramp n)) (← `(∀ n : Nat, n = n))
  -- A change of proposition head is permitted by the arithmetic rules.
  requireConversion "independent arithmetic heads"
    (← `(∀ n : Nat, n ≤ n)) (← `(∀ n : Nat, n = n))
  -- B can supply a nontrivial target independently of the source. A source-only
  -- support filter must not discard this pair before consulting B.
  let index ← factIndex
  requireConversion "baseline supplies missing atoms"
    (← `(∀ n : Nat, ramp n = 3 * n)) (← `(∀ n : Nat, n = n)) index
    (some ``packagedBaseline)

#print axioms projection_key_constant
#print axioms packagedBaseline
end LeanInformationAudit.Tests.SearchReduction.PresentationCoverage

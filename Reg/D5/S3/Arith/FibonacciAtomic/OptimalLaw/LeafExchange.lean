import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange

namespace Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange

open scoped BigOperators
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.StrictRounding
noncomputable section

namespace Donor
abbrev signature : Signature where
  Params := ℕ × ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (_ : ℕ × ℕ), ℝ → ℤ :=
  fun _ a x => ⌊(2 : ℝ) ^ a.2 * (x - 1 / (2 : ℝ) ^ a.1)⌋
def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ) (D : ℕ), 1 ≤ D →
    ⌊(2 : ℝ) ^ D * x⌋ = 2 * ⌊(2 : ℝ) ^ (D - 1) * x⌋ + 1 →
    ∀ d : ℕ, d < D → R.readout () (D, d) x = ⌊(2 : ℝ) ^ d * x⌋
theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h (1 / 2) 1 (by decide) (by norm_num) 0 (by decide)
  norm_num [rejected, realize, Realization.readout] at H

def proof_record : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange.donor_prefix)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange.donor_prefix, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(1, 0), 1 / 2, 3 / 2, ?_⟩
    norm_num [actual, observation, realize, Realization.readout]

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange.donor_prefix) (Realization signature) Unit Unit where
  unitName := Lean.Name.str `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange.donor_prefix "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange.Donor.proof_record
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof_record⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange
    definition := none
    coordinates := #[1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Donor

end
end Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.LeafExchange

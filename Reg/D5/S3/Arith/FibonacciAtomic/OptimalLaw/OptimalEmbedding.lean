import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding

namespace Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding

open scoped BigOperators
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ m : ℕ, Fin m
  State := fun a => Fin a.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (a : Σ m : ℕ, Fin m), (Fin a.1 → ℝ) → Bool :=
  fun _ a p => decide (_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.HasOptimalEmbedding a.1 p a.2)

def actual : Realization signature := realize signature observation (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∀ (p : Fin m → ℝ) (k : Fin m),
    (∀ i, 0 < p i) → (∑ i, p i) = 1 → (∀ i, p k ≤ p i) →
    DyadicSupportLines.cost p / p k = OptimalLawStrictSlope.alpha m →
      R.readout () ⟨m, k⟩ p = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, k, hp, hs, hk, ho⟩ := OptimalLawStrictSlope.attained 2 (by decide)
  have H := h 2 (by decide) p k hp hs hk ho
  change false = true at H
  cases H

def proof_record : Registration arena (type_of% (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.result)) where
  actual := actual
  bridge := by simp [arena, actual, observation, realize, Realization.readout]
  variation := ⟨by
    simpa [arena, actual, observation, realize, Realization.readout] using
      _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.result, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    obtain ⟨p, k, hp, hs, hk, ho⟩ := OptimalLawStrictSlope.attained 2 (by decide)
    have good := _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.result
      2 (by decide) p k hp hs hk ho
    have bad : ¬ _root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.HasOptimalEmbedding
        2 (fun _ => -1) k := by
      rintro ⟨sigma, gamma, he, ha, hc⟩
      have H := (TriangularPathNormalization.result 2 (by decide) gamma).1 k
      rw [he] at H
      norm_num at H
    refine ⟨⟨2, k⟩, p, (fun _ => -1), ?_⟩
    change decide (_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.HasOptimalEmbedding 2 p k) ≠
      decide (_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.HasOptimalEmbedding 2 (fun _ => -1) k)
    simp only [good, bad, decide_true, decide_false, ne_eq, Bool.true_eq_false, not_false_eq_true]

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.result) (Realization signature) Unit Unit where
  unitName := Lean.Name.str `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.result "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding.proof_record
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
    owner := `D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.FibonacciAtomic.OptimalLaw.OptimalEmbedding

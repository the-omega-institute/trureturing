import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.BargmannImaginaryMaximizers
import Reg.Support.DependentFamily
import Reg.Support.UniverseSingleReadout

/-! Source-bound audit of the latitude inner-product identity. -/

namespace Reg.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.LatitudeDot

open _root_.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe conjugation of the first complex latitude parameter. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => star z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ z w : ℂ,
    star (latitude t z) ⬝ᵥ latitude t w =
      ((1 - t : ℝ) : ℂ) + (t : ℂ) * R.readout () () z * w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by norm_num) (by norm_num) 1 1
  rw [latitude_dot 1 (by norm_num) (by norm_num) 1 1] at hbad
  norm_num [rejected, realize] at hbad

def source_registration : Registration arena
    (∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ z w : ℂ,
      star (latitude t z) ⬝ᵥ latitude t w =
        ((1 - t : ℝ) : ℂ) + (t : ℂ) * star z * w) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨latitude_dot, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change star (0 : ℂ) ≠ star 1
    norm_num

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude_dot)
    (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude_dot.star
  realizationName :=
    `Reg.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.LatitudeDot.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => star z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.BargmannImaginaryMaximizers
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Latitude.latitude_dot
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.LatitudeDot

namespace Reg.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.WeightedEdgeBound

open _root_.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.Fourier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe a weight at the summation index, retaining the full function as state. -/
abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature (Σ ι : Type u, ι)
    (fun p => Sigma.fst p → ℝ) (fun _ => ℝ)

def actual : Realization signature.{u} :=
  realize signature (fun _ p w => w (Sigma.snd p)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Only the weight occurrence in the upper-bound sum is replaced. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] (w c : ι → ℝ) (M : ℝ),
    (∀ k, 0 ≤ w k) → (∑ k, w k) = 1 → (∀ k, c k ≤ M) →
    (∑ k, c k * R.readout () ⟨ι, k⟩ w) ≤ M ∧
      ((∑ k, c k * w k) = M ↔ ∀ k, c k < M → w k = 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := (h (ι := ULift.{u} Unit) (fun _ => 1) (fun _ => -1) (-1)
    (by intro k; norm_num) (by simp) (by intro k; norm_num)).1
  norm_num [rejected, realize] at hb

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, ULift.up ()⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  exact zero_ne_one

def source_registration : Registration arena.{u} (type_of% @weighted_edge_bound.{u}) where
  actual := realize signature.{u} (actual.{u}).readout (actual.{u}).anchor
  bridge := Iff.rfl
  variation := ⟨@weighted_edge_bound.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weighted_edge_bound.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.WeightedEdgeBound.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.WeightedEdgeBound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (actual.{u}).readout (actual.{u}).anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.BargmannImaginaryMaximizers
    definition := none
    coordinates := #[0, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.BargmannImaginaryMaximizers.WeightedEdgeBound

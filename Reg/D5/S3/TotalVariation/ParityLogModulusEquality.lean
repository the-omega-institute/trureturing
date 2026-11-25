import D5.S3.TotalVariation.ParityLogModulusEquality
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source audit for the attainable equality threshold. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.TotalVariation.ParityLogModulusEquality
open _root_.D5.S3.TotalVariation.ParityLogStability (moment)
open _root_.D5.S3.TotalVariation.GroupedParityBias (law groupBias)
open _root_.D5.S3.TotalVariation.Pinsker (totalVariation)

namespace Reg.D5.S3.TotalVariation.ParityLogModulusEquality.Sufficiency

noncomputable section

universe u

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ d => d) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

open Classical in
def arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} [AddCommGroup A] [Fintype A]
    (_two : ∀ x : A, x + x = 0) (_hcard : 1 < Fintype.card A)
    (a : A) (_ha : a ≠ 0) (e δ : ℝ) (_he : 0 < e) (_hδ : 0 < δ)
    (_hcut :
      let n : ℝ := Fintype.card A
      let beta := (n - 1) / n
      e * (1 + δ / (beta * e)) ^ (n / 2) < 1),
    let n : ℝ := Fintype.card A
    let beta := (n - 1) / n
    let c : {x : A // x ≠ 0} → A := Subtype.val
    ∃ f g : {x : A // x ≠ 0} → ℝ,
      (∀ i, 0 < f i ∧ f i < 1) ∧ (∀ i, 0 < g i ∧ g i < 1) ∧
      let p := law c 0 f
      let q := law c 0 g
      (∀ ψ, e ≤ |moment p ψ| ∧ e ≤ |moment q ψ|) ∧
      totalVariation p q = R.readout () () δ ∧
      |Real.log (groupBias c f a) - Real.log (groupBias c g a)| =
        2 * beta * Real.log (1 + δ / (beta * e))

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A := ULift.{u} (ZMod 2)
  have hcard : Fintype.card A = 2 := by simp [A, ZMod.card]
  have hc : 1 < Fintype.card A := by rw [hcard]; norm_num
  have htwo (x : A) : x + x = 0 := by
    apply ULift.down_injective
    change x.down + x.down = 0
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  have ha : (1 : A) ≠ 0 := by
    intro h
    have hz : (1 : ZMod 2) = 0 := congrArg ULift.down h
    exact one_ne_zero hz
  have hcut : (1 / 4 : ℝ) * (1 + (1 / 8) /
      (((Fintype.card A : ℝ) - 1) / (Fintype.card A : ℝ) * (1 / 4))) ^
        ((Fintype.card A : ℝ) / 2) < 1 := by
    rw [hcard]
    norm_num
  obtain ⟨f, g, hf, hg, hfloor, htv, hgap⟩ :=
    h (A := A) htwo hc 1 ha (1 / 4) (1 / 8) (by norm_num) (by norm_num) hcut
  change totalVariation _ _ = -1 at htv
  apply (by norm_num : ¬ 0 ≤ (-1 : ℝ))
  rw [← htv]
  unfold totalVariation
  positivity

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def sourceRegistration : Registration arena.{u} (type_of% @equality_criterion_sufficient.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@equality_criterion_sufficient, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@equality_criterion_sufficient.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.TotalVariation.ParityLogModulusEquality.Sufficiency.unit
  realizationName :=
    `Reg.D5.S3.TotalVariation.ParityLogModulusEquality.Sufficiency.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => d) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.TotalVariation.ParityLogModulusEquality
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "arg", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.TotalVariation.ParityLogModulusEquality.Sufficiency

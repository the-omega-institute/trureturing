import D5.S3.Factorization.Mordell.CanonicalPointHeight
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic

namespace Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight

open Height Filter Topology
open WeierstrassCurve WeierstrassCurve.Affine
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Filter ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => 𝓝 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 𝓝 (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {F : Type u} [Field F] {W : Affine F}
    [AdmissibleAbsValues F] [DecidableEq F] [W.toAffine.IsElliptic],
    (∀ P : W.Point, Tendsto (fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / (2 * 4 ^ n))
      atTop (R.readout () () P.canonicalHeight)) ∧
    (∃ D, ∀ P : W.Point, |P.canonicalHeight - P.naiveHeight / 2| ≤ D) ∧
    (∀ P Q : W.Point, (P + Q).canonicalHeight + (P - Q).canonicalHeight =
      2 * (P.canonicalHeight + Q.canonicalHeight))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let F := ULift.{u} ℚ
  letI : NumberField F := NumberField.of_ringEquiv ℚ F
    (ULift.ringEquiv : F ≃+* ℚ).symm
  letI : AdmissibleAbsValues F := inferInstance
  let W : Affine F := ⟨0, 0, 0, -1, 0⟩
  letI : W.toAffine.IsElliptic := by
    constructor
    apply isUnit_iff_ne_zero.mpr
    norm_num [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hbad := (h (F := F) (W := W)).1 (0 : W.Point)
  have hgood : Tendsto
      (fun n : ℕ => ((2 ^ n) • (0 : W.Point)).naiveHeight / (2 * 4 ^ n))
      atTop (𝓝 (0 : ℝ)) := by
    simpa [Point.naiveHeight, Point.xRep_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  change Tendsto _ atTop (𝓝 (1 : ℝ)) at hbad
  have hf := tendsto_nhds_unique hgood hbad
  norm_num at hf

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@Point.canonicalHeight_properties.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    change 𝓝 (0 : ℝ) ≠ 𝓝 (1 : ℝ)
    intro h
    have hf := nhds_injective h
    norm_num at hf

register_information_theorem Point.canonicalHeight_properties in arena
  readout via (realize signature (fun _ _ x => 𝓝 x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.Mordell.CanonicalPointHeight
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg",
        "body", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"] }] })
  escape continues (open)

#print axioms registration


end
end Reg.D5.S3.Factorization.Mordell.CanonicalPointHeight

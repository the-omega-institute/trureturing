import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.BooleanRotationCodebook

/-! Complete source reconstruction and actual circular-error observations. -/

noncomputable section
open scoped BigOperators ENNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.BooleanRotationCodebook

namespace Reg.D5.S3.Geometry.BooleanRotationCodebook
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ × ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => circularError p.1 p.2) (fun e => nomatch e)

abbrev noWrapArena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    {L ε : ℝ}, 0 ≤ ε → 3 * ε < L →
    (∀ i ∈ s, 0 ≤ a i ∧ a i ≤ ε) →
    (∀ t ⊆ s, R.readout () () (L, ∑ i ∈ t, a i) ≤ ε) →
    ∑ i ∈ s, a i ≤ ε

theorem noWrapBridge : (type_of% (@nonnegative_sum_no_wrap.{u})) ↔
    noWrapArena.{u}.Law actual := Iff.rfl

abbrev fiberArena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] {L ε : ℝ},
    0 ≤ ε → 3 * ε < L → ∀ a : ι → ℝ, (∀ i, |a i| ≤ L / 2) →
    ((∀ s : Finset ι, R.readout () () (L, ∑ i ∈ s, a i) ≤ ε) ↔ signedBody ε a)

theorem fiberBridge : (type_of% (@exact_error_fiber.{u})) ↔
    fiberArena.{u}.Law actual := Iff.rfl

theorem noWrapPositive : noWrapArena.{u}.Law actual :=
  noWrapBridge.mp (@nonnegative_sum_no_wrap.{u})

theorem fiberPositive : fiberArena.{u}.Law actual :=
  fiberBridge.mp (@exact_error_fiber.{u})

theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (4, 0), (4, 1), ?_⟩
  change circularError 4 0 ≠ circularError 4 1
  have hh : circularError 4 1 = 1 := by
    change ‖((1 : ℝ) : AddCircle (4 : ℝ))‖ = 1
    rw [(AddCircle.norm_coe_eq_abs_iff 4 (by norm_num)).mpr (by norm_num)]
    norm_num
  rw [hh]
  norm_num [circularError]

abbrev orthantSignature : Signature where
  Params := ℕ × ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def orthantActual : Realization orthantSignature :=
  realize orthantSignature
    (fun _ p ε => MeasureTheory.volume (signedOrthant p.1 p.2 ε))
    (fun e => nomatch e)

abbrev orthantArena : Arena where
  signature := orthantSignature
  Law R := ∀ p q : ℕ, ∀ {ε : ℝ}, 0 < ε →
    R.readout () (p, q) ε = ENNReal.ofReal (ε ^ (p + q)) *
      ((p.factorial : ℝ≥0∞)⁻¹ * (q.factorial : ℝ≥0∞)⁻¹)

theorem orthantBridge : (type_of% (@signed_orthant_volume)) ↔
    orthantArena.Law orthantActual := Iff.rfl

theorem orthantPositive : orthantArena.Law orthantActual :=
  orthantBridge.mp (@signed_orthant_volume)

abbrev bodySignature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def bodyActual : Realization bodySignature :=
  realize bodySignature
    (fun _ n ε => MeasureTheory.volume {a : Fin n → ℝ | signedBody ε a})
    (fun e => nomatch e)

abbrev bodyArena : Arena where
  signature := bodySignature
  Law R := ∀ n : ℕ, ∀ {ε : ℝ}, 0 < ε →
    R.readout () n ε = ENNReal.ofReal (((2 * n).choose n : ℝ) * ε ^ n / n.factorial)

theorem bodyBridge : (type_of% (@signed_body_volume)) ↔
    bodyArena.Law bodyActual := Iff.rfl

theorem bodyPositive : bodyArena.Law bodyActual :=
  bodyBridge.mp (@signed_body_volume)

end Reg.D5.S3.Geometry.BooleanRotationCodebook

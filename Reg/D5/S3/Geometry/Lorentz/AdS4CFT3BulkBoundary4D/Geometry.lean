import D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D
import Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.Common

/-! Source laws and interventions for the AdS geometry. -/

open _root_.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Real Set Filter
open scoped Matrix Topology

namespace Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace IsometryRank

abbrev signature : Signature := operandSignature (Fin 5) (Fin 5 → RMat5)

abbrev arena : Arena where
  signature := signature
  Law R := Module.finrank ℝ so23Subspace = 10 ∧ ∀ a b c d : Fin 5,
    (R.readout () () a b) * so23Generator c d - so23Generator c d * so23Generator a b =
      eta23 b c • so23Generator a d - eta23 a c • so23Generator b d -
        eta23 b d • so23Generator a c + eta23 a d • so23Generator b c

def family : Registration arena (type_of% (@so23_isometry_finrank_10)) :=
  adsFamily% arena (@so23_isometry_finrank_10) (adsObserve% (so23Generator))
    (adsObserve% (fun _ _ => 0))
    (by
      intro h
      have e := congrFun (congrFun (h.2 0 1 1 2) 0) 2
      norm_num [realize, so23Generator, eta23, signature23, Matrix.mul_apply, Fin.sum_univ_succ,
        OmegaMath.OrthogonalMatrixGenerators.generator,
        OmegaMath.OrthogonalMatrixGenerators.metric] at e)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrFun (congrFun (congrFun h 1) 0) 1
      norm_num [realize, so23Generator, signature23,
        OmegaMath.OrthogonalMatrixGenerators.generator] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@so23_isometry_finrank_10) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.so23_isometry_finrank_10.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.IsometryRank.family
    arena family (adsObserve% (so23Generator)) #[]
    #[{ path := adsPath% so23_isometry_finrank_10 so23Generator 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end IsometryRank

namespace Preservation

abbrev signature : Signature := operandSignature (Fin 5 → ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (Λ : RMat5) (hΛ : Λᵀ * eta23 * Λ = eta23) (X : Fin 5 → ℝ) (L : ℝ),
    adsForm (Λ *ᵥ X) = R.readout () () X ∧
      (IsOnAdS4 L X → IsOnAdS4 L (Λ *ᵥ X))

def family : Registration arena (type_of% (@so23_preserves_ads4)) :=
  adsFamily% arena (@so23_preserves_ads4) (adsObserve% (adsForm))
    (adsObserve% (fun _ => 0))
    (by
      intro h
      have e := (h 1 (by simp) ![1, 0, 0, 0, 0] 1).1
      norm_num [realize, adsForm] at e)
    (by
      refine ⟨(), ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ?_⟩
      norm_num [realize, adsForm])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@so23_preserves_ads4) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.so23_preserves_ads4.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.Preservation.family
    arena family (adsObserve% (adsForm)) #[]
    #[{ path := adsPath% so23_preserves_ads4 adsForm 0 1
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Preservation

namespace Embedding

abbrev signature : Signature := operandSignature (ℝ) (ℝ → ℝ → ℝ → ℝ → Fin 5 → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {L z : ℝ} (hL : 0 < L) (hz : 0 < z) (t x y : ℝ),
    IsOnAdS4 L (R.readout () () L z t x y) ∧
      poincareEmbed L z t x y 0 + poincareEmbed L z t x y 4 = L ^ 2 / z ∧
      0 < L ^ 2 / z

def family : Registration arena (type_of% (@poincareEmbed_on_ads4)) :=
  adsFamily% arena (@poincareEmbed_on_ads4) (adsObserve% (poincareEmbed))
    (adsObserve% (fun _ _ _ _ _ => 0))
    (by
      intro h
      have e := (h (L := 1) (z := 1) (by norm_num) (by norm_num) 0 0 0).1
      norm_num [realize, IsOnAdS4, adsForm] at e)
    (by
      refine ⟨(), 1, 2, ?_⟩
      intro h
      have e := congrArg (fun f : ℝ → ℝ → ℝ → ℝ → Fin 5 → ℝ => f 1 1 0 0 1) h
      norm_num [realize, poincareEmbed] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@poincareEmbed_on_ads4) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.poincareEmbed_on_ads4.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.Embedding.family
    arena family (adsObserve% (poincareEmbed)) #[]
    #[{ path := adsPath% poincareEmbed_on_ads4 poincareEmbed 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Embedding

namespace Pullback

abbrev signature : Signature := operandSignature (Fin 5 → ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z t x y : ℝ → ℝ} {s dz dt dx dy : ℝ} (L : ℝ)
    (hz : 0 < z s) (hdz : HasDerivAt z dz s) (hdt : HasDerivAt t dt s)
    (hdx : HasDerivAt x dx s) (hdy : HasDerivAt y dy s),
    HasDerivAt (fun u => poincareEmbed L (z u) (t u) (x u) (y u))
      (poincareTangent L (z s) (t s) (x s) (y s) dz dt dx dy) s ∧
    R.readout () () (poincareTangent L (z s) (t s) (x s) (y s) dz dt dx dy) =
      (L ^ 2 / (z s) ^ 2) * (-dt ^ 2 + dx ^ 2 + dy ^ 2 + dz ^ 2)

def family : Registration arena (type_of% (@poincareEmbed_metric_pullback)) :=
  adsFamily% arena (@poincareEmbed_metric_pullback) (adsObserve% (adsForm))
    (adsObserve% (fun _ => 0))
    (by
      intro h
      have e := (h (z := fun _ => 1) (t := id) (x := fun _ => 0) (y := fun _ => 0)
        (s := 0) 1 (by norm_num) (hasDerivAt_const 0 1) (hasDerivAt_id 0)
        (hasDerivAt_const 0 0) (hasDerivAt_const 0 0)).2
      norm_num [realize] at e)
    (by
      refine ⟨(), ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ?_⟩
      norm_num [realize, adsForm])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@poincareEmbed_metric_pullback) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.poincareEmbed_metric_pullback.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.Pullback.family
    arena family (adsObserve% (adsForm)) #[]
    #[{ path := adsPath% poincareEmbed_metric_pullback adsForm 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Pullback

namespace BoundaryNormal

abbrev signature : Signature := operandSignature (ℝ) (ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {L : ℝ} (hL : 0 < L),
    R.readout () () L 0 = 0 ∧
    HasDerivAt (adsConformalFactor L) (1 / L) 0 ∧
    1 / L ≠ 0 ∧ (1 / L) ^ 2 = 1 / L ^ 2 ∧ 0 < 1 / L ^ 2

def family : Registration arena (type_of% (@ads4_timelike_conformal_boundary)) :=
  adsFamily% arena (@ads4_timelike_conformal_boundary) (adsObserve% (adsConformalFactor))
    (adsObserve% (fun _ _ => 1))
    (by
      intro h
      have e := (h (L := 1) (by norm_num)).1
      norm_num [realize] at e)
    (by
      refine ⟨(), 1, 2, ?_⟩
      intro h
      have e := congrFun h 1
      norm_num [realize, adsConformalFactor] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@ads4_timelike_conformal_boundary) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.ads4_timelike_conformal_boundary.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.BoundaryNormal.family
    arena family (adsObserve% (adsConformalFactor)) #[]
    #[{ path := adsPath% ads4_timelike_conformal_boundary adsConformalFactor 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end BoundaryNormal

namespace LightTravel

abbrev signature : Signature := operandSignature (ℝ) (ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {L z₀ : ℝ} (hz₀ : 0 < z₀),
    0 ∈ Ico 0 z₀ ∧ (∀ τ ∈ Ico 0 z₀,
      0 < R.readout () () z₀ τ ∧ L ^ 2 / (z₀ - τ) ^ 2 * (-(1 : ℝ) ^ 2 + (-1 : ℝ) ^ 2) = 0) ∧
    IsLeast {τ : ℝ | z₀ - τ = 0} z₀

def family : Registration arena (type_of% (@radial_light_travel)) :=
  adsFamily% arena (@radial_light_travel) (adsObserve% (fun a b : ℝ => a - b))
    (adsObserve% (fun _ _ => 0))
    (by
      intro h
      have e := ((h (L := 1) (z₀ := 1) (by norm_num)).2.1 0 (by norm_num [Ico])).1
      norm_num [realize] at e)
    (by
      refine ⟨(), 0, 1, ?_⟩
      intro h
      have e := congrFun h 0
      norm_num [realize] at e)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@radial_light_travel) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.radial_light_travel.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.LightTravel.family
    arena family (adsObserve% (fun a b : ℝ => a - b)) #[]
    #[{ path := adsPath% radial_light_travel HSub.hSub 4 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end LightTravel

namespace Distance

abbrev signature : Signature := operandSignature (ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {L z₀ ε : ℝ} (hz₀ : 0 < z₀) (hε : 0 < ε),
    (∫ z in ε..z₀, L / z) = L * R.readout () () (z₀ / ε)

def family : Registration arena (type_of% (@radial_proper_distance)) :=
  adsFamily% arena (@radial_proper_distance) (adsObserve% (Real.log))
    (adsObserve% (fun _ => 0))
    (by
      intro h
      have e := h (L := 1) (z₀ := 2) (ε := 1) (by norm_num) (by norm_num)
      rw [radial_proper_distance (by norm_num) (by norm_num)] at e
      exact (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
        (by simpa [realize] using e))
    (by
      refine ⟨(), 1, 2, ?_⟩
      simpa [realize] using ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@radial_proper_distance) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.radial_proper_distance.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.Distance.family
    arena family (adsObserve% (Real.log)) #[]
    #[{ path := adsPath% radial_proper_distance Real.log 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end Distance

namespace DistanceDivergence

abbrev signature : Signature := operandSignature (ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {L z₀ : ℝ} (hL : 0 < L) (hz₀ : 0 < z₀),
    Tendsto (fun ε => L * R.readout () () (z₀ / ε)) (𝓝[>] 0) atTop

def family : Registration arena (type_of% (@radial_proper_distance_diverges)) :=
  adsFamily% arena (@radial_proper_distance_diverges) (adsObserve% (Real.log))
    (adsObserve% (fun _ => 0))
    (by
      intro h
      have e : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) atTop := by
        simpa [realize] using h (L := 1) (z₀ := 1) (by norm_num) (by norm_num)
      exact not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds e)
    (by
      refine ⟨(), 1, 2, ?_⟩
      simpa [realize] using ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@radial_proper_distance_diverges) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.radial_proper_distance_diverges.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.DistanceDivergence.family
    arena family (adsObserve% (Real.log)) #[]
    #[{ path := adsPath% radial_proper_distance_diverges Real.log 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end DistanceDivergence

namespace AffineNullLine

abbrev signature : Signature := operandSignature (Fin 5 → ℝ) (ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {L z₀ : ℝ} (hz₀ : 0 < z₀) (x y : ℝ),
    ∃ V : Fin 5 → ℝ, R.readout () () V = 0 ∧
      ∀ a : ℝ, 0 ≤ a →
        let z := (1 / z₀ + a)⁻¹
        poincareEmbed L z (z₀ - z) x y = poincareEmbed L z₀ 0 x y + a • V

def family : Registration arena (type_of% (@radial_affine_null_line)) :=
  adsFamily% arena (@radial_affine_null_line) (adsObserve% (adsForm))
    (adsObserve% (fun _ => 1))
    (by
      intro h
      obtain ⟨v, e, _⟩ := h (L := 1) (z₀ := 1) (by norm_num) 0 0
      norm_num [realize] at e)
    (by
      refine ⟨(), ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ?_⟩
      norm_num [realize, adsForm])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@radial_affine_null_line) (Realization signature) Unit Unit :=
  adsBind% `D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.radial_affine_null_line.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D.AffineNullLine.family
    arena family (adsObserve% (adsForm)) #[]
    #[{ path := adsPath% radial_affine_null_line adsForm 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end AffineNullLine

end
end Reg.D5.S3.Geometry.Lorentz.AdS4CFT3BulkBoundary4D

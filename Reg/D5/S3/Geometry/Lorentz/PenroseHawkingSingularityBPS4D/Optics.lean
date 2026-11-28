import D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D
import Reg.Support.UnitSixO

/-! Source observations and interventions for optical and cosmological bounds. -/

open _root_.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D
open _root_.D5.S3.Geometry.Lorentz.SachsJacobsonEinstein4D
open _root_.D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.Support.UnitSixO
open LeanInformationAudit Set

namespace Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Optics

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private def affineExpansion (t : ℝ) : ℝ := -1 - t

private theorem affineExpansion_hasDerivAt (t : ℝ) :
    HasDerivAt affineExpansion (-1) t := by
  exact (hasDerivAt_id t).const_sub (-1 : ℝ)

private def affineShearSq (t : ℝ) : ℝ := 1 - (affineExpansion t) ^ 2 / 2

private theorem affineNull_derivative (t : ℝ) :
    HasDerivAt affineExpansion (-((affineExpansion t) ^ 2) / 2 - affineShearSq t - 0) t := by
  apply (affineExpansion_hasDerivAt t).congr_deriv
  unfold affineShearSq
  ring

private theorem affineShearSq_nonnegative {t : ℝ} (ht : t ∈ Icc 0 (1 / 4)) :
    0 ≤ affineShearSq t := by
  have hlo : 0 ≤ t := ht.1
  have hhi : t ≤ 1 / 4 := ht.2
  unfold affineShearSq affineExpansion
  nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (add_nonneg hlo zero_le_one)]

namespace NullBound

abbrev signature : Signature := operandSignature ℝ ℝ

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {θ σSq Rkk : ℝ → ℝ} {L : ℝ}, 0 ≤ L →
    (∀ t ∈ Icc 0 L, HasDerivAt θ (-((θ t) ^ 2) / 2 - σSq t - Rkk t) t) →
    (∀ t ∈ Icc 0 L, 0 ≤ σSq t) → (∀ t ∈ Icc 0 L, 0 ≤ Rkk t) → θ 0 < 0 →
    StrictAntiOn θ (Icc 0 L) ∧
      (∀ t ∈ Icc 0 L, θ t < 0 ∧ 1 / θ 0 + t / 2 ≤ 1 / θ t) ∧
      L < R.readout () () |θ 0|

def family : Registration arena (type_of% (@penrose_trapped_surface_caustic_bound)) :=
  unitFamily% arena (@penrose_trapped_surface_caustic_bound) (unitObserve% (fun r : ℝ => 2 / r))
    (unitObserve% (fun _ => 0))
    (by
      intro h
      have he := h (θ := affineExpansion) (σSq := affineShearSq) (Rkk := fun _ => 0)
        (L := 1 / 4) (by norm_num) (fun t _ => affineNull_derivative t)
        (fun _ => affineShearSq_nonnegative) (fun _ _ => le_rfl)
        (by norm_num [affineExpansion])
      norm_num [realize] at he)
    (by
      refine ⟨(), 1, 2, ?_⟩
      norm_num [realize])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@penrose_trapped_surface_caustic_bound) (Realization signature) Unit Unit :=
  unitBindOptics% `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.penrose_trapped_surface_caustic_bound.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Optics.NullBound.family
    arena family (unitObserve% (fun r : ℝ => 2 / r)) #[]
    #[{ path := unitPath% penrose_trapped_surface_caustic_bound HDiv.hDiv 5 4
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end NullBound

namespace StrictFocusing

abbrev signature : Signature := operandSignature ℝ ℝ

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {θ σSq Rkk : ℝ → ℝ} {L : ℝ},
    (∀ t ∈ Icc 0 L, HasDerivAt θ (-((θ t) ^ 2) / 2 - σSq t - Rkk t) t) →
    (∀ t ∈ Icc 0 L, 0 ≤ σSq t) → (∀ t ∈ Icc 0 L, 0 ≤ Rkk t) →
    θ 0 < 0 → (0 < σSq 0 ∨ 0 < Rkk 0) →
    ∀ t ∈ Ioc 0 L, R.readout () () (θ 0) + t / 2 < 1 / θ t

def family : Registration arena (type_of% (@penrose_shear_strictly_accelerates_focusing)) :=
  unitFamily% arena (@penrose_shear_strictly_accelerates_focusing)
    (unitObserve% (fun r : ℝ => 1 / r))
    (unitObserve% (fun _ => 0))
    (by
      intro h
      have he := h (θ := affineExpansion) (σSq := affineShearSq) (Rkk := fun _ => 0)
        (L := 1 / 4) (fun t _ => affineNull_derivative t)
        (fun _ => affineShearSq_nonnegative) (fun _ _ => le_rfl) (by norm_num [affineExpansion])
        (Or.inl (by norm_num [affineShearSq, affineExpansion])) (1 / 4) ⟨by norm_num, le_rfl⟩
      norm_num [realize, affineExpansion] at he)
    (by
      refine ⟨(), 1, 2, ?_⟩
      norm_num [realize])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@penrose_shear_strictly_accelerates_focusing) (Realization signature) Unit Unit :=
  unitBindOptics% `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.penrose_shear_strictly_accelerates_focusing.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Optics.StrictFocusing.family
    arena family (unitObserve% (fun r : ℝ => 1 / r)) #[]
    #[{ path := unitPath% penrose_shear_strictly_accelerates_focusing HDiv.hDiv 5 1
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end StrictFocusing

namespace LightSheet

private def staticOptics (r : ℝ) : OpticalData :=
  ⟨fun _ => 0, fun _ => 0, fun _ => r, fun _ => 0, fun _ => 0⟩

private theorem staticOptics_solves (r : ℝ) (I : Set ℝ) : SolvesOn (staticOptics r) I := by
  constructor
  · intro t _
    simpa [staticOptics] using hasDerivAt_const t (0 : ℝ)
  · intro t _
    simpa [staticOptics] using hasDerivAt_const t (0 : ℂ)
  · intro t _
    simpa [staticOptics] using hasDerivAt_const t r

abbrev signature : Signature := operandSignature OpticalData (ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {o : OpticalData} {L : ℝ}, 0 ≤ L →
    SolvesOn o (Icc 0 L) → (∀ t ∈ Icc 0 L, 0 ≤ o.ricciTerm t) →
    (∀ t ∈ Icc 0 L, 0 < o.radius t) → o.expansion 0 ≤ 0 →
    ConcaveOn ℝ (Icc 0 L) (fun t => Real.sqrt (area o t)) ∧
      (∀ t ∈ Icc 0 L, o.expansion t ≤ 0) ∧
      AntitoneOn (R.readout () () o) (Icc 0 L) ∧
      (o.expansion 0 < 0 →
        (∀ t ∈ Icc 0 L, Real.sqrt (area o t) ≤
          Real.sqrt (area o 0) * (1 + (o.expansion 0 / 2) * t)) ∧
        L < 2 / |o.expansion 0|)

def family : Registration arena (type_of% (@bousso_lightsheet_area_monotonicity)) :=
  unitFamily% arena (@bousso_lightsheet_area_monotonicity) (unitObserve% (area))
    (unitObserve% (fun _ t => t))
    (by
      intro h
      have he := h (o := staticOptics 1) (L := 1) (by norm_num)
        (staticOptics_solves 1 _) (fun _ _ => le_rfl) (fun _ _ => zero_lt_one) le_rfl
      have he' := he.2.2.1 (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
      exact not_le_of_gt (zero_lt_one : (0 : ℝ) < 1) he')
    (by
      refine ⟨(), staticOptics 1, staticOptics 2, ?_⟩
      intro h
      have he := congrFun h 0
      norm_num [realize, area, staticOptics] at he)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@bousso_lightsheet_area_monotonicity) (Realization signature) Unit Unit :=
  unitBindOptics% `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.bousso_lightsheet_area_monotonicity.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Optics.LightSheet.family
    arena family (unitObserve% (area)) #[]
    #[{ path := unitPath% bousso_lightsheet_area_monotonicity area 0 1
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end LightSheet

namespace PastLifetime

private theorem affine_hasDerivAt (t : ℝ) : HasDerivAt (fun x : ℝ => x + 1) 1 t :=
  (hasDerivAt_id t).add_const 1

abbrev signature : Signature := operandSignature (ℝ → ℝ) (ℝ → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : ℝ → ℝ} {t₀ T : ℝ}, 0 < T →
    (∀ t ∈ Icc (t₀ - T) t₀, DifferentiableAt ℝ a t) →
    AntitoneOn (deriv a) (Icc (t₀ - T) t₀) → 0 < a t₀ → 0 < deriv a t₀ →
    0 < R.readout () () a t₀ ∧
      (∀ t ∈ Icc (t₀ - T) t₀, a t ≤ a t₀ * (1 + hubble a t₀ * (t - t₀))) ∧
      ((∀ t ∈ Icc (t₀ - T) t₀, 0 < a t) → T < 1 / hubble a t₀)

def family : Registration arena (type_of% (@hawking_past_big_bang_bound)) :=
  unitFamily% arena (@hawking_past_big_bang_bound) (unitObserve% (hubble))
    (unitObserve% (fun _ _ => 0))
    (by
      intro h
      have hanti : AntitoneOn (deriv (fun x : ℝ => x + 1)) (Icc ((0 : ℝ) - 1) 0) := by
        intro x _ y _ _
        rw [(affine_hasDerivAt x).deriv, (affine_hasDerivAt y).deriv]
      have he := h (a := fun x => x + 1) (t₀ := 0) (T := 1) zero_lt_one
        (fun x _ => (affine_hasDerivAt x).differentiableAt) hanti
        (by norm_num) (by rw [(affine_hasDerivAt 0).deriv]; exact zero_lt_one)
      exact lt_irrefl (0 : ℝ) he.1)
    (by
      refine ⟨(), (fun x => x + 1), (fun _ => 1), ?_⟩
      intro h
      have he := congrFun h 0
      change hubble (fun x : ℝ => x + 1) 0 = hubble (fun _ => 1) 0 at he
      norm_num [hubble, (affine_hasDerivAt 0).deriv] at he)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hawking_past_big_bang_bound) (Realization signature) Unit Unit :=
  unitBindOptics% `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.hawking_past_big_bang_bound.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Optics.PastLifetime.family
    arena family (unitObserve% (hubble)) #[]
    #[{ path := unitPath% hawking_past_big_bang_bound hubble 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end PastLifetime

namespace TimelikeBound

abbrev signature : Signature := operandSignature ℝ ℝ

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {θ : ℝ → ℝ} {L : ℝ}, 0 ≤ L →
    (∀ t ∈ Icc 0 L, DifferentiableAt ℝ θ t) →
    (∀ t ∈ Icc 0 L, deriv θ t ≤ -((θ t) ^ 2) / 3) → θ 0 < 0 →
    L < R.readout () () |θ 0|

def family : Registration arena (type_of% (@hawking_timelike_congruence_raychaudhuri)) :=
  unitFamily% arena (@hawking_timelike_congruence_raychaudhuri) (unitObserve% (fun r : ℝ => 3 / r))
    (unitObserve% (fun _ => 0))
    (by
      intro h
      have hd : ∀ t ∈ Icc (0 : ℝ) (1 / 4),
          deriv affineExpansion t ≤ -((affineExpansion t) ^ 2) / 3 := by
        intro t ht
        rw [(affineExpansion_hasDerivAt t).deriv]
        have hs := affineShearSq_nonnegative ht
        unfold affineShearSq at hs
        linarith
      have he := h (θ := affineExpansion) (L := 1 / 4) (by norm_num)
        (fun t _ => (affineExpansion_hasDerivAt t).differentiableAt)
        hd (by norm_num [affineExpansion])
      norm_num [realize] at he)
    (by
      refine ⟨(), 1, 3, ?_⟩
      norm_num [realize])

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hawking_timelike_congruence_raychaudhuri) (Realization signature) Unit Unit :=
  unitBindOptics% `D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.hawking_timelike_congruence_raychaudhuri.__information_unit
    `Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Optics.TimelikeBound.family
    arena family (unitObserve% (fun r : ℝ => 3 / r)) #[]
    #[{ path := unitPath% hawking_timelike_congruence_raychaudhuri HDiv.hDiv 5 1
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end TimelikeBound

end

end Reg.D5.S3.Geometry.Lorentz.PenroseHawkingSingularityBPS4D.Optics

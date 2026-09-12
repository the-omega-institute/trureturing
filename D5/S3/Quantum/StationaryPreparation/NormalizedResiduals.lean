/- GID: D5/S3/Quantum/StationaryPreparation/NormalizedResiduals
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/NormalizedResiduals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized actual stationary residual memories and their emission amplitudes. -/

import D5.S3.Quantum.StationaryPreparation.PhysicalGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.StationaryPreparation.NormalizedResiduals
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.StationaryPreparation.PhysicalGram
variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A]

def residualScale (r : Multiset A) : ℝ := Real.sqrt (multiplicity r.card r : ℝ)
def normalizedResidual (a : Multiset A) (blank : A) (U : Unitary (A × K))
    (x : Space K) (r : Multiset A) : Space K :=
  (residualScale r : ℂ)⁻¹ • residualMemory a blank U x r
def sourceMoment (a : Multiset A) (blank : A) (U : Unitary (A × K))
    (x f : Space K) (r : Multiset A) : ℂ :=
  inner ℂ (normalizedResidual a blank U x r) f

theorem multiplicity_ne_zero (r : Multiset A) : multiplicity r.card r ≠ 0 :=
  (multiplicity_pos r rfl).ne'
theorem scale_pos (r : Multiset A) : 0 < residualScale r :=
  Real.sqrt_pos.mpr (by exact_mod_cast multiplicity_pos r rfl)
theorem scale_ne_zero (r : Multiset A) : (residualScale r : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (scale_pos r).ne'
theorem scale_sq (r : Multiset A) : (residualScale r)^2 = (multiplicity r.card r : ℝ) :=
  Real.sq_sqrt (Nat.cast_nonneg _)
@[simp] theorem scale_zero : residualScale (0 : Multiset A) = 1 := by
  rw [residualScale, multiplicity_eq_factorial (0 : Multiset A) rfl]
  norm_num

theorem scale_normalized (a : Multiset A) (blank : A) (U : Unitary (A × K))
    (x : Space K) (r : Multiset A) :
    (residualScale r : ℂ) • normalizedResidual a blank U x r =
      residualMemory a blank U x r := by
  rw [normalizedResidual, smul_smul, mul_inv_cancel₀ (scale_ne_zero r), one_smul]

theorem prefix_inner_sum (blank : A) (U : Unitary (A × K)) (n : ℕ)
    (x y : Space K) :
    inner ℂ x y = ∑ w : Fin n → A,
      inner ℂ (prefixMemory blank U (List.ofFn w) x)
        (prefixMemory blank U (List.ofFn w) y) := by
  classical
  rw [← (initialized blank n).inner_map_map x y,
    ← (circuit (fun _ => U) n 0).inner_map_map]
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, circuit_fixed_coefficients]

variable (a : Multiset A) (blank : A) (U : Unitary (A × K)) (x f : Space K)
variable (hout : ∀ (w : Fin a.card → A) (k : K),
  circuit (fun _ => U) a.card 0 (initialized blank a.card x) (w, k) =
    sectorVector a.card a w * f k)
include hout in
theorem residual_inner_self (r : Multiset A) (hr : r ≤ a) (hf : ‖f‖ = 1) :
    inner ℂ (residualMemory a blank U x r) (residualMemory a blank U x r) =
      (multiplicity r.card r : ℂ) := by
  classical
  rw [prefix_inner_sum blank U r.card]
  simp_rw [residual_output a blank U x f hout r hr _ List.length_ofFn]
  have hff : inner ℂ f f = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hf]
    norm_num
  trans ∑ w : Fin r.card → A, if occupation w = r then (1 : ℂ) else 0
  · apply Finset.sum_congr rfl
    intro w _
    by_cases hw : occupation w = r <;> simp_all [occupation]
  · simp [D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity, sectorWords]
include hout in
theorem residual_norm_sq (r : Multiset A) (hr : r ≤ a) (hf : ‖f‖ = 1) :
    ‖residualMemory a blank U x r‖^2 = (multiplicity r.card r : ℝ) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), residual_inner_self a blank U x f hout r hr hf]
  rfl
include hout in
theorem normalized_norm (r : Multiset A) (hr : r ≤ a) (hf : ‖f‖ = 1) :
    ‖normalizedResidual a blank U x r‖ = 1 := by
  have hn : ‖residualMemory a blank U x r‖ = residualScale r := by
    have h := residual_norm_sq a blank U x f hout r hr hf
    nlinarith [scale_sq r, scale_pos r, norm_nonneg (residualMemory a blank U x r)]
  rw [normalizedResidual, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (scale_pos r), hn, inv_mul_cancel₀ (scale_pos r).ne']
include hout in
theorem normalized_zero : normalizedResidual a blank U x 0 = f := by
  simp [normalizedResidual, residual_zero a blank U x f hout]

theorem normalized_initial : normalizedResidual a blank U x a = x := by
  have hnil : List.ofFn (representative (a - a) rfl) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp
  simp only [normalizedResidual, residualMemory, hnil, prefix_nil, scaledInitial]
  change (residualScale a : ℂ)⁻¹ • ((residualScale a : ℂ) • x) = x
  rw [smul_smul, inv_mul_cancel₀ (scale_ne_zero a), one_smul]
include hout in
theorem source_moment_zero (hf : ‖f‖ = 1) : sourceMoment a blank U x f 0 = 1 := by
  rw [sourceMoment, normalized_zero a blank U x f hout, inner_self_eq_norm_sq_to_K, hf]
  norm_num
include hout in
theorem prefix_normalized (r : Multiset A) (hr : r ≤ a)
    (u : List A) (hu : (u : Multiset A) = a - r) :
    prefixMemory blank U u x =
      (Real.sqrt ((multiplicity r.card r : ℝ) / (multiplicity a.card a : ℝ)) : ℂ) •
        normalizedResidual a blank U x r := by
  have h := residual_representative_independent a blank U x f hout r hr u hu
  rw [scaledInitial, map_smul] at h
  have hs : (Real.sqrt ((multiplicity r.card r : ℝ) /
      (multiplicity a.card a : ℝ)) : ℂ) =
      (residualScale a : ℂ)⁻¹ * (residualScale r : ℂ) := by
    rw [Real.sqrt_div (Nat.cast_nonneg _), Complex.ofReal_div]
    exact div_eq_inv_mul _ _
  calc
    prefixMemory blank U u x = (residualScale a : ℂ)⁻¹ •
        residualMemory a blank U x r := by
      rw [← h]
      change _ = (residualScale a : ℂ)⁻¹ • ((residualScale a : ℂ) • _)
      rw [smul_smul, inv_mul_cancel₀ (scale_ne_zero a), one_smul]
    _ = _ := by rw [← scale_normalized a blank U x r, smul_smul, hs]
include hout in
theorem normalized_letter_of_mem (r : Multiset A) (hr : r ≤ a)
    (hr0 : r ≠ 0) (i : A) (hi : i ∈ r) :
    letter blank U i (normalizedResidual a blank U x r) =
      (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) •
        normalizedResidual a blank U x (r.erase i) := by
  have hc : (r.erase i).card + 1 = r.card := Multiset.card_erase_add_one hi
  have hm := multiplicity_erase_mul hc.symm i hi
  rw [hc] at hm
  have hmR : (r.card : ℝ) * (multiplicity (r.erase i).card (r.erase i) : ℝ) =
      (r.count i : ℝ) * (multiplicity r.card r : ℝ) := by exact_mod_cast hm
  have heq : (multiplicity (r.erase i).card (r.erase i) : ℝ) /
      (multiplicity r.card r : ℝ) = (r.count i : ℝ) / (r.card : ℝ) := by
    apply (div_eq_div_iff (by exact_mod_cast multiplicity_ne_zero r)
      (by exact_mod_cast (Multiset.card_pos.mpr hr0).ne')).mpr
    nlinarith
  have hs : (residualScale (r.erase i) : ℂ) / (residualScale r : ℂ) =
      (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_div]
    congr 1
    change Real.sqrt _ / Real.sqrt _ = _
    rw [← Real.sqrt_div (Nat.cast_nonneg _), heq]
  calc
    letter blank U i (normalizedResidual a blank U x r) =
        (residualScale r : ℂ)⁻¹ • residualMemory a blank U x (r.erase i) := by
      rw [normalizedResidual, map_smul, residual_letter_of_mem a blank U x f hout r hr i hi]
    _ = _ := by
      rw [← scale_normalized a blank U x (r.erase i), smul_smul, ← div_eq_inv_mul, hs]
include hout in
theorem normalized_letter_of_not_mem (r : Multiset A) (hr : r ≤ a)
    (hr0 : r ≠ 0) (i : A) (hi : i ∉ r) :
    letter blank U i (normalizedResidual a blank U x r) = 0 := by
  simp [normalizedResidual, residual_letter_of_not_mem a blank U x f hout r hr hr0 i hi]

end D5.S3.Quantum.StationaryPreparation.NormalizedResiduals

namespace D5.S3.Quantum.StationaryPreparation.NormalizedResiduals

open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.StationaryPreparation.ResidualCalculus
open D5.S3.Quantum.StationaryPreparation.StationaryOccupationPadding
open D5.S3.Quantum.StationaryPreparation.StationaryOccupationResidualCircuit
open D5.S3.Quantum.StationaryPreparation.StationaryOccupationResidualStep

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- The initial vector already used by the concrete padding circuit. -/
def physicalInitial (a : Multiset A) : Space (Fin (proposedDimension a)) :=
  (residualScale a : ℂ)⁻¹ • physicalResidual a a

theorem physical_residual_step (a : Multiset A) : ResidualStep a := by
  intro r hr hr0 i k
  by_cases ht : 0 < tailCount (maximalHead a) r
  · by_cases hi : i ∈ r
    · rw [if_pos hi]
      exact positive_residual_step a r hr ht i hi k
    · rw [if_neg hi]
      exact physical_residual_step_absent a r hr hr0 i hi k
  · exact physical_residual_step_tail_free a r hr hr0 (by omega) i k

theorem physical_initial_output (a : Multiset A) :
    ∀ (w : Fin a.card → A) (k : Fin (proposedDimension a)),
      circuit (fun _ => physicalGate a) a.card 0
        (initialized (maximalHead a) a.card (physicalInitial a)) (w, k) =
          sectorVector a.card a w * physicalFinal a k :=
  physical_residual_output a (physical_residual_step a)

theorem physical_scaled_initial (a : Multiset A) :
    scaledInitial a (physicalInitial a) = physicalResidual a a := by
  change (residualScale a : ℂ) •
    ((residualScale a : ℂ)⁻¹ • physicalResidual a a) = _
  rw [smul_smul, mul_inv_cancel₀ (scale_ne_zero a), one_smul]

/-- Suffix injectivity identifies B's actual prefix memory with C's chosen vector. -/
theorem physical_residual_identification (a r : Multiset A) (hr : r ≤ a) :
    residualMemory a (maximalHead a) (physicalGate a) (physicalInitial a) r =
      physicalResidual a r := by
  apply suffix_injective (maximalHead a) (physicalGate a) r.card
  intro w
  rw [residual_output a (maximalHead a) (physicalGate a) (physicalInitial a)
    (physicalFinal a) (physical_initial_output a) r hr _ List.length_ofFn]
  ext k
  have h := circuit_output_of_residuals (maximalHead a) (physicalGate a) a
    (physicalResidual a) (physicalFinal a) (physical_residual_zero a)
    (physical_residual_step a) r.card 0 r rfl hr w k
  rw [circuit_fixed_coefficients] at h
  by_cases hw : (List.ofFn w : Multiset A) = r <;>
    simpa [occupation, hw] using h.symm

theorem physical_normalized_identification (a r : Multiset A) (hr : r ≤ a) :
    normalizedResidual a (maximalHead a) (physicalGate a) (physicalInitial a) r =
      (residualScale r : ℂ)⁻¹ • physicalResidual a r := by
  rw [normalizedResidual, physical_residual_identification a r hr]

theorem physical_prefix_identification (a r : Multiset A) (hr : r ≤ a)
    (u : List A) (hu : (u : Multiset A) = a - r) :
    prefixMemory (maximalHead a) (physicalGate a) u (physicalResidual a a) =
      physicalResidual a r := by
  rw [← physical_scaled_initial a, residual_representative_independent a
    (maximalHead a) (physicalGate a) (physicalInitial a) (physicalFinal a)
    (physical_initial_output a) r hr u hu, physical_residual_identification a r hr]

theorem physical_prefix_normalized (a r : Multiset A) (hr : r ≤ a)
    (u : List A) (hu : (u : Multiset A) = a - r) :
    prefixMemory (maximalHead a) (physicalGate a) u (physicalInitial a) =
      (Real.sqrt ((multiplicity r.card r : ℝ) / (multiplicity a.card a : ℝ)) : ℂ) •
        ((residualScale r : ℂ)⁻¹ • physicalResidual a r) := by
  rw [prefix_normalized a (maximalHead a) (physicalGate a) (physicalInitial a)
    (physicalFinal a) (physical_initial_output a) r hr u hu,
    physical_normalized_identification a r hr]

theorem physical_normalized_norm (a r : Multiset A) (hr : r ≤ a) :
    ‖(residualScale r : ℂ)⁻¹ • physicalResidual a r‖ = 1 := by
  rw [← physical_normalized_identification a r hr]
  exact normalized_norm a (maximalHead a) (physicalGate a) (physicalInitial a)
    (physicalFinal a) (physical_initial_output a) r hr (physical_final_norm a)

theorem physical_initial_norm (a : Multiset A) : ‖physicalInitial a‖ = 1 :=
  physical_normalized_norm a a le_rfl

theorem physical_normalized_zero (a : Multiset A) :
    normalizedResidual a (maximalHead a) (physicalGate a) (physicalInitial a) 0 =
      physicalFinal a := by
  rw [physical_normalized_identification a 0 zero_le, physical_residual_zero]
  simp

theorem physical_head_singleton_le (a : Multiset A)
    (hA : 0 < Finset.univ.sup a.count) : ({maximalHead a} : Multiset A) ≤ a := by
  apply Multiset.singleton_le.mpr
  apply Multiset.count_pos.mp
  rwa [maximal_head_spec]

theorem physical_normalized_head (a : Multiset A)
    (hA : 0 < Finset.univ.sup a.count) :
    normalizedResidual a (maximalHead a) (physicalGate a) (physicalInitial a) 0 =
      normalizedResidual a (maximalHead a) (physicalGate a) (physicalInitial a)
        ({maximalHead a} : Multiset A) := by
  have ht : tailCount (maximalHead a) ({maximalHead a} : Multiset A) = 0 := by
    simpa using head_add_tail_count (maximalHead a) ({maximalHead a} : Multiset A)
  have hm : residualScale ({maximalHead a} : Multiset A) = 1 := by
    rw [residualScale, multiplicity_eq_factorial _ rfl]
    have hp : (∏ i : A, (({maximalHead a} : Multiset A).count i).factorial) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i = maximalHead a <;> simp [hi]
    simp [hp]
  rw [physical_normalized_zero, physical_normalized_identification a _
    (physical_head_singleton_le a hA), physical_residual_tail_free a _
    (physical_head_singleton_le a hA) ht, hm]
  simp

theorem physical_normalized_letter (a r : Multiset A) (hr : r ≤ a)
    (hr0 : r ≠ 0) (i : A) :
    letter (maximalHead a) (physicalGate a) i
      ((residualScale r : ℂ)⁻¹ • physicalResidual a r) =
        if i ∈ r then (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) •
          ((residualScale (r.erase i) : ℂ)⁻¹ • physicalResidual a (r.erase i)) else 0 := by
  rw [← physical_normalized_identification a r hr]
  by_cases hi : i ∈ r
  · rw [if_pos hi, ← physical_normalized_identification a (r.erase i)
      ((Multiset.erase_le _ _).trans hr)]
    exact normalized_letter_of_mem a (maximalHead a) (physicalGate a) (physicalInitial a)
      (physicalFinal a) (physical_initial_output a) r hr hr0 i hi
  · rw [if_neg hi]
    exact normalized_letter_of_not_mem a (maximalHead a) (physicalGate a) (physicalInitial a)
      (physicalFinal a) (physical_initial_output a) r hr hr0 i hi

end D5.S3.Quantum.StationaryPreparation.NormalizedResiduals

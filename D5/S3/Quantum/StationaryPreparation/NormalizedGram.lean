/- GID: D5/S3/Quantum/StationaryPreparation/NormalizedGram
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/NormalizedGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Source entries and positive diagonal equivalence for the actual stationary Gram. -/

import D5.S3.Quantum.StationaryPreparation.NormalizedResiduals
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.NormalizedGram
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.StationaryPreparation.NormalizedResiduals
open D5.S1.Ledger.BoundedTimeSlice
variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A]
variable (a : Multiset A) (blank : A) (U : Unitary (A × K)) (x f : Space K)
variable (hout : ∀ (w : Fin a.card → A) (k : K),
  circuit (fun _ => U) a.card 0 (initialized blank a.card x) (w, k) =
    sectorVector a.card a w * f k)
include hout in
theorem residual_prefix (r : Multiset A) (hr : r ≤ a)
    (w : List A) (hw : w.length ≤ r.card) :
    prefixMemory blank U w (residualMemory a blank U x r) =
      if (w : Multiset A) ≤ r then residualMemory a blank U x (r - (w : Multiset A))
      else 0 := by
  classical
  by_cases hwr : (w : Multiset A) ≤ r
  · rw [if_pos hwr]
    apply suffix_injective blank U (r - (w : Multiset A)).card
    intro v
    have hlen : (w ++ List.ofFn v).length = r.card := by
      simp only [List.length_append, List.length_ofFn, Multiset.card_sub hwr, Multiset.coe_card]
      omega
    rw [← prefix_append, residual_output a blank U x f hout r hr _ hlen,
      residual_output a blank U x f hout (r - (w : Multiset A))
        ((tsub_le_self).trans hr) _ List.length_ofFn]
    have he : ((w ++ List.ofFn v : List A) : Multiset A) = r ↔
        (List.ofFn v : Multiset A) = r - (w : Multiset A) := by
      rw [← Multiset.coe_add]
      constructor
      · intro h
        exact add_left_cancel (h.trans (add_tsub_cancel_of_le hwr).symm)
      · intro h
        rw [h, add_tsub_cancel_of_le hwr]
    simp only [he]
  · rw [if_neg hwr]
    apply suffix_injective blank U (r.card - w.length)
    intro v
    have hlen : (w ++ List.ofFn v).length = r.card := by
      simp only [List.length_append, List.length_ofFn]
      omega
    rw [← prefix_append, residual_output a blank U x f hout r hr _ hlen, map_zero]
    have he : ((w ++ List.ofFn v : List A) : Multiset A) ≠ r := by
      intro h
      apply hwr
      rw [← h, ← Multiset.coe_add]
      exact le_add_right le_rfl
    simp [he]
include hout in
theorem residual_inner_of_le (r s : Multiset A) (hr : r ≤ a) (hs : s ≤ a)
    (hsr : s ≤ r) :
    inner ℂ (residualMemory a blank U x r) (residualMemory a blank U x s) =
      (multiplicity s.card s : ℂ) * inner ℂ (residualMemory a blank U x (r - s)) f := by
  classical
  rw [prefix_inner_sum blank U s.card]
  trans ∑ w : Fin s.card → A, if occupation w = s then
    inner ℂ (residualMemory a blank U x (r - s)) f else 0
  · apply Finset.sum_congr rfl
    intro w _
    rw [residual_output a blank U x f hout s hs _ List.length_ofFn]
    by_cases hw : occupation w = s
    · have hl : (List.ofFn w).length ≤ r.card := by
        simpa only [List.length_ofFn] using Multiset.card_le_card hsr
      rw [residual_prefix a blank U x f hout r hr _ hl]
      change (List.ofFn w : Multiset A) = s at hw
      simp [occupation, hw, hsr]
    · simp [occupation] at hw
      simp [occupation, hw]
  · simp [D5.S3.Quantum.Entanglement.OccupancyWordSectors.multiplicity,
      sectorWords, ← Finset.sum_filter]
include hout in
theorem residual_inner_of_not_le (r s : Multiset A) (hr : r ≤ a) (hs : s ≤ a)
    (hcard : s.card ≤ r.card) (hsr : ¬ s ≤ r) :
    inner ℂ (residualMemory a blank U x r) (residualMemory a blank U x s) = 0 := by
  classical
  rw [prefix_inner_sum blank U s.card]
  apply Finset.sum_eq_zero
  intro w _
  rw [residual_output a blank U x f hout s hs _ List.length_ofFn,
    residual_prefix a blank U x f hout r hr _ (by simpa using hcard)]
  by_cases hw : (List.ofFn w : Multiset A) = s
  · simp [hw, hsr]
  · simp [hw]

include hout in
theorem normalized_inner_of_le (r s : Multiset A) (hr : r ≤ a) (hs : s ≤ a)
    (hsr : s ≤ r) (hf : ‖f‖ = 1) :
    inner ℂ (normalizedResidual a blank U x r) (normalizedResidual a blank U x s) =
      (Real.sqrt ((multiplicity s.card s : ℝ) *
        (multiplicity (r-s).card (r-s) : ℝ) / (multiplicity r.card r : ℝ)) : ℂ) *
        sourceMoment a blank U x f (r-s) := by
  have hscale : Real.sqrt ((multiplicity s.card s : ℝ) *
      (multiplicity (r-s).card (r-s) : ℝ) / (multiplicity r.card r : ℝ)) =
      residualScale s * residualScale (r-s) / residualScale r := by
    rw [Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Real.sqrt_mul (Nat.cast_nonneg _)]
    rfl
  have hsq : (multiplicity s.card s : ℂ) = (residualScale s : ℂ)^2 := by
    exact_mod_cast (scale_sq s).symm
  rw [hscale, sourceMoment, normalizedResidual, normalizedResidual, normalizedResidual,
    inner_smul_left, inner_smul_right, inner_smul_left]
  simp only [map_inv₀, Complex.conj_ofReal]
  rw [residual_inner_of_le a blank U x f hout r s hr hs hsr, hsq,
    Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [scale_ne_zero r, scale_ne_zero s, scale_ne_zero (r-s)]
include hout in
theorem normalized_inner_of_ge (r s : Multiset A) (hr : r ≤ a) (hs : s ≤ a)
    (hrs : r ≤ s) (hf : ‖f‖ = 1) :
    inner ℂ (normalizedResidual a blank U x r) (normalizedResidual a blank U x s) =
      (Real.sqrt ((multiplicity r.card r : ℝ) *
        (multiplicity (s-r).card (s-r) : ℝ) / (multiplicity s.card s : ℝ)) : ℂ) *
        star (sourceMoment a blank U x f (s-r)) := by
  rw [← inner_conj_symm, normalized_inner_of_le a blank U x f hout s r hs hr hrs hf]
  simp [map_mul, RCLike.star_def]
include hout in
theorem normalized_inner_incomparable (r s : Multiset A) (hr : r ≤ a) (hs : s ≤ a)
    (hnsr : ¬ s ≤ r) (hnrs : ¬ r ≤ s) (hf : ‖f‖ = 1) :
    inner ℂ (normalizedResidual a blank U x r) (normalizedResidual a blank U x s) = 0 := by
  have h : inner ℂ (residualMemory a blank U x r) (residualMemory a blank U x s) = 0 := by
    rcases le_total s.card r.card with hcard | hcard
    · exact residual_inner_of_not_le a blank U x f hout r s hr hs hcard hnsr
    · rw [← inner_conj_symm, residual_inner_of_not_le a blank U x f hout s r hs hr hcard hnrs,
        map_zero]
  simp only [normalizedResidual, inner_smul_left, inner_smul_right, h, mul_zero]

def normalizedGram : Matrix (TailBox a.count) (TailBox a.count) ℂ :=
  Matrix.gram ℂ (fun r => normalizedResidual a blank U x (boxOccupation a r))
open Classical in
def normalizationDiagonal (a : Multiset A) : Matrix (TailBox a.count) (TailBox a.count) ℂ :=
  Matrix.diagonal (fun r => (residualScale (boxOccupation a r) : ℂ))

theorem diagonal_positive (a : Multiset A) (r : TailBox a.count) :
    0 < (normalizationDiagonal a r r).re := by
  simpa [normalizationDiagonal] using scale_pos (boxOccupation a r)
theorem diagonal_ne_zero (a : Multiset A) (r : TailBox a.count) :
    normalizationDiagonal a r r ≠ 0 := by
  simpa [normalizationDiagonal] using scale_ne_zero (boxOccupation a r)
theorem diagonal_det_ne_zero (a : Multiset A) : (normalizationDiagonal a).det ≠ 0 := by
  classical
  rw [normalizationDiagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun r _ => scale_ne_zero (boxOccupation a r))
theorem occupation_gram_eq_diagonal : occupationGram a blank U x =
    normalizationDiagonal a * normalizedGram a blank U x * normalizationDiagonal a := by
  classical
  ext r s
  simp only [occupationGram, normalizedGram, normalizationDiagonal,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.gram_apply]
  rw [← scale_normalized a blank U x (boxOccupation a r),
    ← scale_normalized a blank U x (boxOccupation a s), inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal]
  ring
theorem occupation_gram_rank_eq :
    (occupationGram a blank U x).rank = (normalizedGram a blank U x).rank := by
  classical
  rw [occupation_gram_eq_diagonal,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (diagonal_det_ne_zero a),
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (diagonal_det_ne_zero a)]
theorem normalized_gram_psd : (normalizedGram a blank U x).PosSemidef :=
  Matrix.posSemidef_gram ℂ _
theorem normalized_gram_rank_le : (normalizedGram a blank U x).rank ≤ Fintype.card K := by
  rw [← occupation_gram_rank_eq]
  exact occupation_gram_rank_le a blank U x

end D5.S3.Quantum.StationaryPreparation.NormalizedGram

namespace D5.S3.Quantum.StationaryPreparation.NormalizedGram

open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
open D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.StationaryPreparation.NormalizedResiduals
open D5.S3.Quantum.StationaryPreparation.StationaryOccupationPadding
open D5.S3.Quantum.StationaryPreparation.StationaryOccupationResidualCircuit
open D5.S3.Quantum.StationaryGram.StationaryOccupationRankNullity
open scoped TensorProduct

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- C's actual blank-input isometry in alphabet-first tensor coordinates. -/
def physicalTensorEmission (a : Multiset A) :
    Space (Fin (proposedDimension a)) →ₗᵢ[ℂ]
      Space A ⊗[ℂ] Space (Fin (proposedDimension a)) :=
  ((EuclideanSpace.basisFun A ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin (proposedDimension a)) ℂ)).repr.symm.toLinearIsometry.comp
      (emission (maximalHead a) (physicalGate a))

theorem physical_tensor_coordinates (a : Multiset A)
    (x : Space (Fin (proposedDimension a))) :
    ((EuclideanSpace.basisFun A ℂ).tensorProduct
      (EuclideanSpace.basisFun (Fin (proposedDimension a)) ℂ)).repr
        (physicalTensorEmission a x) = emission (maximalHead a) (physicalGate a) x := by
  simp [physicalTensorEmission]

variable (a : Multiset A)
local notation "φ" => (fun r : Multiset A => (residualScale r : ℂ)⁻¹ • physicalResidual a r)

/-- The source's tensor equation for the identified actual family, including zero absent terms. -/
theorem physical_tensor_emission (r : Multiset A) (hr : r ≤ a) (hr0 : r ≠ 0) :
    physicalTensorEmission a (φ r) =
      ∑ i : A, (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) •
        ((basis i : Space A) ⊗ₜ[ℂ] φ (r.erase i)) := by
  apply ((EuclideanSpace.basisFun A ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin (proposedDimension a)) ℂ)).repr.injective
  rw [physical_tensor_coordinates]
  ext ⟨i, k⟩
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    smul_eq_mul, OrthonormalBasis.tensorProduct_repr_tmul_apply,
    EuclideanSpace.basisFun_repr, basis_apply, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h := congrArg (fun v : Space (Fin (proposedDimension a)) => v k)
    (physical_normalized_letter a r hr hr0 i)
  by_cases hi : i ∈ r <;> simpa [hi, letter_apply] using h

theorem physical_emission_linearCombination {I : Type*} (r : I → Multiset A)
    (hr : ∀ j, r j ≤ a) (hr0 : ∀ j, r j ≠ 0) (c : I →₀ ℂ) :
    physicalTensorEmission a (Finsupp.linearCombination ℂ (fun j => φ (r j)) c) =
      Finsupp.linearCombination ℂ (fun j =>
        ∑ i : A, (Real.sqrt (((r j).count i : ℝ) / ((r j).card : ℝ)) : ℂ) •
          ((basis i : Space A) ⊗ₜ[ℂ] φ ((r j).erase i))) c := by
  change (physicalTensorEmission a).toLinearMap
    (Finsupp.linearCombination ℂ (fun j => φ (r j)) c) = _
  rw [Finsupp.apply_linearCombination ℂ (physicalTensorEmission a).toLinearMap]
  congr 2
  funext j
  exact physical_tensor_emission a (r j) (hr j) (hr0 j)


/-- The actual isometry preserves every finite dependency, including terminal vectors. -/
theorem physical_image_dependency_iff {I : Type*} (r : I → Multiset A) (c : I →₀ ℂ) :
    Finsupp.linearCombination ℂ (fun j => φ (r j)) c = 0 ↔
      Finsupp.linearCombination ℂ (fun j => physicalTensorEmission a (φ (r j))) c = 0 := by
  have hmap : physicalTensorEmission a (Finsupp.linearCombination ℂ (fun j => φ (r j)) c) =
      Finsupp.linearCombination ℂ (fun j => physicalTensorEmission a (φ (r j))) c :=
    Finsupp.apply_linearCombination ℂ (physicalTensorEmission a).toLinearMap _ _
  rw [← hmap, ← map_zero (physicalTensorEmission a)]
  exact (physicalTensorEmission a).injective.eq_iff.symm

theorem physical_dependency_iff {I : Type*} (r : I → Multiset A)
    (hr : ∀ j, r j ≤ a) (hr0 : ∀ j, r j ≠ 0) (c : I →₀ ℂ) :
    Finsupp.linearCombination ℂ (fun j => φ (r j)) c = 0 ↔
      Finsupp.linearCombination ℂ (fun j =>
        ∑ i : A, (Real.sqrt (((r j).count i : ℝ) / ((r j).card : ℝ)) : ℂ) •
          ((basis i : Space A) ⊗ₜ[ℂ] φ ((r j).erase i))) c = 0 := by
  have h := physical_image_dependency_iff a r c
  have hmap : physicalTensorEmission a (Finsupp.linearCombination ℂ (fun j => φ (r j)) c) =
      Finsupp.linearCombination ℂ (fun j => physicalTensorEmission a (φ (r j))) c :=
    Finsupp.apply_linearCombination ℂ (physicalTensorEmission a).toLinearMap _ _
  rw [← hmap, physical_emission_linearCombination a r hr hr0 c] at h
  exact h

/-- Removing the terminal vector preserves the actual generated subspace. -/
theorem physical_nonterminal_span_eq (hA : 0 < Finset.univ.sup a.count) :
    Submodule.span ℂ {v | ∃ r : Multiset A, r ≤ a ∧ r ≠ 0 ∧ φ r = v} =
      Submodule.span ℂ {v | ∃ r : Multiset A, r ≤ a ∧ φ r = v} := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro v ⟨r, hr, _, hv⟩
    exact ⟨r, hr, hv⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨r, hr, rfl⟩
    apply Submodule.subset_span
    by_cases hr0 : r = 0
    · subst r
      refine ⟨{maximalHead a}, physical_head_singleton_le a hA, by simp, ?_⟩
      dsimp only
      rw [← physical_normalized_identification a _ (physical_head_singleton_le a hA),
        ← physical_normalized_identification a 0 zero_le]
      exact (physical_normalized_head a hA).symm
    · exact ⟨r, hr, hr0, rfl⟩

set_option maxHeartbeats 800000 in
-- Elaborating the actual box Gram and its generated-subspace coordinate basis needs this budget.
/-- The identified actual family fills the physical memory, by its Gram rank in its own span. -/
theorem physical_generated_span_top :
    Submodule.span ℂ {v | ∃ r : Multiset A, r ≤ a ∧ φ r = v} = ⊤ := by
  classical
  let S := Submodule.span ℂ {v | ∃ r : Multiset A, r ≤ a ∧ φ r = v}
  let v : D5.S1.Ledger.BoundedTimeSlice.TailBox a.count → S := fun r =>
    ⟨φ (boxOccupation a r),
      Submodule.subset_span ⟨boxOccupation a r, box_occupation_le a r, rfl⟩⟩
  have hg : Matrix.gram ℂ v =
      normalizedGram a (maximalHead a) (physicalGate a) (physicalInitial a) := by
    ext r s
    change inner ℂ (φ (boxOccupation a r)) (φ (boxOccupation a s)) =
      inner ℂ (normalizedResidual a (maximalHead a) (physicalGate a) (physicalInitial a)
        (boxOccupation a r))
        (normalizedResidual a (maximalHead a) (physicalGate a) (physicalInitial a)
          (boxOccupation a s))
    rw [physical_normalized_identification a _ (box_occupation_le a r),
      physical_normalized_identification a _ (box_occupation_le a s)]
  have hlow := stationary_gram_rank_lower_bound
    a.count (occupationGram a (maximalHead a) (physicalGate a) (physicalInitial a))
    (occupation_gram_psd a _ _ _)
    (occupation_gram_zero a _ _ _ (physicalFinal a) (physical_initial_output a)
      (physical_final_norm a))
    (occupation_gram_recurrence a _ _ _ (physicalFinal a) (physical_initial_output a))
  let m : Matrix (Fin (Module.finrank ℂ S))
      (D5.S1.Ledger.BoundedTimeSlice.TailBox a.count) ℂ :=
    fun i r => (stdOrthonormalBasis ℂ S).repr (v r) i
  have hupper : (occupationGram a (maximalHead a) (physicalGate a) (physicalInitial a)).rank ≤
      Module.finrank ℂ S := by
    rw [occupation_gram_rank_eq, ← hg,
      Matrix.gram_eq_conjTranspose_mul (stdOrthonormalBasis ℂ S)]
    change (m.conjTranspose * m).rank ≤ _
    exact (Matrix.rank_mul_le_right m.conjTranspose m).trans
      (by simpa using Matrix.rank_le_card_height m)
  let q0 : Fintype (D5.S1.Ledger.BoundedTimeSlice.TailBox a.count) := inferInstance
  have hupp : ∀ q : Fintype (D5.S1.Ledger.BoundedTimeSlice.TailBox a.count),
      @Matrix.rank _ _ ℂ q _
        (occupationGram a (maximalHead a) (physicalGate a) (physicalInitial a)) ≤
          Module.finrank ℂ S := by
    intro q
    have hq : q = q0 := Subsingleton.elim _ _
    subst q
    exact hupper
  have hdim : proposedDimension a ≤ Module.finrank ℂ S := hlow.trans (hupp _)
  change S = ⊤
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  simpa [Space] using hdim

theorem physical_nonterminal_span_top (hA : 0 < Finset.univ.sup a.count) :
    Submodule.span ℂ {v | ∃ r : Multiset A, r ≤ a ∧ r ≠ 0 ∧ φ r = v} = ⊤ := by
  rw [physical_nonterminal_span_eq a hA, physical_generated_span_top a]

end D5.S3.Quantum.StationaryPreparation.NormalizedGram

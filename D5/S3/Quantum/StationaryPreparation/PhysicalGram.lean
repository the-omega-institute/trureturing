/- GID: D5/S3/Quantum/StationaryPreparation/PhysicalGram
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PhysicalGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual fixed-unitary residual memories yield a scaled Gram and the stationary memory dimension lower bound. -/

import D5.S3.Quantum.StationaryGram.StationaryOccupationRankNullity
import D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Data.Finsupp.Multiset

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit D5.S3.Quantum.Entanglement.OccupancyWordSectors
open scoped BigOperators ComplexOrder
variable {A K : Type*} [Fintype A] [Fintype K]
open Classical in
def emission (blank : A) (U : Unitary (A × K)) :
    Space K →ₗᵢ[ℂ] Space (A × K) :=
  U.toLinearIsometry.comp
    (coordinateEmbedding (blankInjection blank (Function.Embedding.refl K)))
def letter (blank : A) (U : Unitary (A × K)) (i : A) : Space K →ₗ[ℂ] Space K where
  toFun x := WithLp.toLp 2 (fun k => emission blank U x (i, k))
  map_add' x y := by ext k; simp
  map_smul' c x := by ext k; simp
@[simp] theorem letter_apply (blank : A) (U : Unitary (A × K)) (i : A)
    (x : Space K) (k : K) : letter blank U i x k = emission blank U x (i, k) := rfl
theorem emission_basis (blank : A) (U : Unitary (A × K)) (j : K) :
    emission blank U (basis j) = U (basis (blank, j)) := by
  classical
  change U (coordinateEmbedding (blankInjection blank (Function.Embedding.refl K))
    (basis j)) = U (basis (blank, j))
  rw [show coordinateEmbedding (blankInjection blank (Function.Embedding.refl K))
    (basis j) = basis (blank, j) from coordinate_embedding_basis _ j]
theorem letter_expansion (blank : A) (U : Unitary (A × K)) (i : A)
    (x : Space K) (k : K) :
    letter blank U i x k = ∑ j, x j * U (basis (blank, j)) (i, k) := by
  conv_lhs => rw [basis_expansion x]
  simp [map_sum, emission_basis]
def prefixMemory (blank : A) (U : Unitary (A × K)) : List A → Space K →ₗ[ℂ] Space K
  | [] => LinearMap.id
  | i :: w => (prefixMemory blank U w).comp (letter blank U i)
@[simp] theorem prefix_nil (blank : A) (U : Unitary (A × K)) (x : Space K) :
    prefixMemory blank U [] x = x := rfl
@[simp] theorem prefix_cons (blank : A) (U : Unitary (A × K)) (i : A)
    (w : List A) (x : Space K) :
    prefixMemory blank U (i :: w) x = prefixMemory blank U w (letter blank U i x) := rfl
theorem prefix_append (blank : A) (U : Unitary (A × K))
    (u v : List A) (x : Space K) :
    prefixMemory blank U (u ++ v) x = prefixMemory blank U v (prefixMemory blank U u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons i u ih => simpa only [List.cons_append, prefix_cons] using ih (letter blank U i x)
theorem initialized_zero (blank : A) (x : Space K) (w : Fin 0 → A) (k : K) :
    initialized blank 0 x (w, k) = x k := by
  classical
  have hw : w = (fun _ => blank) := Subsingleton.elim _ _
  subst w
  exact coordinate_embedding_apply _ x k
theorem circuit_fixed_coefficients (blank : A) (U : Unitary (A × K))
    (n t : ℕ) (x : Space K) (w : Fin n → A) (k : K) :
    circuit (fun _ => U) n t (initialized blank n x) (w, k) =
      prefixMemory blank U (List.ofFn w) x k := by
  classical
  induction n generalizing t x with
  | zero => simpa [circuit] using initialized_zero blank x w k
  | succ n ih =>
    have hw : List.ofFn w = w 0 :: List.ofFn (Fin.tail w) := by
      conv_lhs => rw [← Fin.cons_self_tail w]
      exact List.ofFn_cons _ _
    rw [hw, prefix_cons, ← ih (t + 1)]
    conv_lhs => rw [basis_expansion x]
    simp only [map_sum, map_smul, initialize_basis]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
      circuit_blank_succ]
    conv_rhs => rw [basis_expansion (letter blank U (w 0) x)]
    simp only [map_sum, map_smul, initialize_basis, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      smul_eq_mul, letter_expansion]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
theorem suffix_injective (blank : A) (U : Unitary (A × K)) (n : ℕ)
    (x y : Space K)
    (h : ∀ (w : Fin n → A), prefixMemory blank U (List.ofFn w) x =
      prefixMemory blank U (List.ofFn w) y) : x = y := by
  apply (initialized blank n).injective
  apply (circuit (fun _ => U) n 0).injective
  ext p
  rcases p with ⟨w, k⟩
  simp only [circuit_fixed_coefficients]
  exact congrArg (fun z : Space K => z k) (h w)
theorem letter_inner_sum (blank : A) (U : Unitary (A × K)) (x y : Space K) :
    inner ℂ x y = ∑ i, inner ℂ (letter blank U i x) (letter blank U i y) := by
  rw [← (emission blank U).inner_map_map x y]
  simp only [PiLp.inner_apply, Fintype.sum_prod_type, letter_apply]
end D5.S3.Quantum.StationaryPreparation.PhysicalGram
namespace D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit D5.S3.Quantum.Entanglement.OccupancyWordSectors
open scoped BigOperators ComplexOrder
variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A]
def scaledInitial (a : Multiset A) (x : Space K) : Space K :=
  (Real.sqrt (multiplicity a.card a : ℝ) : ℂ) • x
def residualMemory (a : Multiset A) (blank : A) (U : Unitary (A × K))
    (x : Space K) (r : Multiset A) : Space K :=
  prefixMemory blank U (List.ofFn (representative (a - r) rfl)) (scaledInitial a x)
variable (a : Multiset A) (blank : A) (U : Unitary (A × K)) (x f : Space K)
variable (hout : ∀ (w : Fin a.card → A) (k : K),
  circuit (fun _ => U) a.card 0 (initialized blank a.card x) (w, k) =
    sectorVector a.card a w * f k)
include hout in
theorem scaled_full_word (w : Fin a.card → A) :
    prefixMemory blank U (List.ofFn w) (scaledInitial a x) =
      if occupation w = a then f else 0 := by
  have hs : (Real.sqrt (multiplicity a.card a : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (by exact_mod_cast multiplicity_pos a rfl)).ne'
  ext k
  simp only [scaledInitial, map_smul, PiLp.smul_apply, smul_eq_mul]
  rw [← circuit_fixed_coefficients blank U a.card 0 x w k, hout]
  by_cases h : occupation w = a <;>
    simp [sectorVector, sectorWords, h, hs]
include hout in
theorem scaled_full_list (w : List A) (hw : w.length = a.card) :
    prefixMemory blank U w (scaledInitial a x) =
      if (w : Multiset A) = a then f else 0 := by
  have h : ∀ n, n = a.card → ∀ v : Fin n → A,
      prefixMemory blank U (List.ofFn v) (scaledInitial a x) =
        if occupation v = a then f else 0 := by
    intro n hn v
    subst n
    exact scaled_full_word a blank U x f hout v
  simpa [occupation] using h w.length hw w.get
include hout in
theorem prefix_residual_output (r : Multiset A) (hr : r ≤ a)
    (u : List A) (hu : (u : Multiset A) = a - r)
    (v : List A) (hv : v.length = r.card) :
    prefixMemory blank U v (prefixMemory blank U u (scaledInitial a x)) =
      if (v : Multiset A) = r then f else 0 := by
  have hlen : (u ++ v).length = a.card := by
    have huc := congrArg Multiset.card hu
    simp only [Multiset.coe_card] at huc
    rw [List.length_append, huc, hv, Multiset.card_sub hr]
    exact Nat.sub_add_cancel (Multiset.card_le_card hr)
  rw [← prefix_append, scaled_full_list a blank U x f hout (u ++ v) hlen]
  have he : ((u ++ v : List A) : Multiset A) = a ↔ (v : Multiset A) = r := by
    rw [← Multiset.coe_add, hu]
    constructor
    · intro h
      exact add_left_cancel (h.trans (Multiset.sub_add_cancel hr).symm)
    · intro h
      rw [h]
      exact Multiset.sub_add_cancel hr
  simp only [he]
include hout in
theorem residual_output (r : Multiset A) (hr : r ≤ a)
    (v : List A) (hv : v.length = r.card) :
    prefixMemory blank U v (residualMemory a blank U x r) =
      if (v : Multiset A) = r then f else 0 := by
  apply prefix_residual_output a blank U x f hout r hr _ _ v hv
  exact occupation_representative (a - r) rfl
include hout in
theorem residual_representative_independent (r : Multiset A) (hr : r ≤ a)
    (u : List A) (hu : (u : Multiset A) = a - r) :
    prefixMemory blank U u (scaledInitial a x) = residualMemory a blank U x r := by
  apply suffix_injective blank U r.card
  intro v
  rw [prefix_residual_output a blank U x f hout r hr u hu _ List.length_ofFn,
    residual_output a blank U x f hout r hr _ List.length_ofFn]
include hout in
theorem residual_zero : residualMemory a blank U x 0 = f := by
  have h := residual_output a blank U x f hout 0 zero_le [] rfl
  simpa using h
include hout in
theorem residual_letter_of_mem (r : Multiset A) (hr : r ≤ a)
    (i : A) (hi : i ∈ r) :
    letter blank U i (residualMemory a blank U x r) =
      residualMemory a blank U x (r.erase i) := by
  apply suffix_injective blank U (r.erase i).card
  intro v
  have hlen : (i :: List.ofFn v).length = r.card := by
    simpa using Multiset.card_erase_add_one hi
  rw [← prefix_cons,
    residual_output a blank U x f hout r hr _ hlen,
    residual_output a blank U x f hout (r.erase i) ((Multiset.erase_le i r).trans hr)
      _ List.length_ofFn]
  have he : ((i :: List.ofFn v : List A) : Multiset A) = r ↔
      (List.ofFn v : Multiset A) = r.erase i := by
    change i ::ₘ (List.ofFn v : Multiset A) = r ↔ _
    constructor
    · intro h
      exact (Multiset.cons_inj_right i).mp (h.trans (Multiset.cons_erase hi).symm)
    · intro h
      rw [h, Multiset.cons_erase hi]
  simp only [he]
include hout in
theorem residual_letter_of_not_mem (r : Multiset A) (hr : r ≤ a)
    (hr0 : r ≠ 0) (i : A) (hi : i ∉ r) :
    letter blank U i (residualMemory a blank U x r) = 0 := by
  apply suffix_injective blank U (r.card - 1)
  intro v
  have hpos : 0 < r.card := Multiset.card_pos.mpr hr0
  have hlen : (i :: List.ofFn v).length = r.card := by
    simp only [List.length_cons, List.length_ofFn]
    omega
  rw [← prefix_cons, residual_output a blank U x f hout r hr _ hlen, map_zero]
  have he : ((i :: List.ofFn v : List A) : Multiset A) ≠ r := by
    intro h
    apply hi
    rw [← h]
    simp
  simp [he]
end D5.S3.Quantum.StationaryPreparation.PhysicalGram
namespace D5.S3.Quantum.StationaryPreparation.PhysicalGram
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit D5.S3.Quantum.Entanglement.OccupancyWordSectors D5.S1.Ledger.BoundedTimeSlice
open scoped BigOperators ComplexOrder
variable {A K : Type*} [Fintype A] [Fintype K] [DecidableEq A]
def boxOccupation (a : Multiset A) (r : TailBox a.count) : Multiset A :=
  Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm (fun i => (r i).val))
@[simp] theorem box_occupation_count (a : Multiset A) (r : TailBox a.count) (i : A) :
    (boxOccupation a r).count i = (r i).val := by
  simp [boxOccupation]
@[simp] theorem box_occupation_zero (a : Multiset A) : boxOccupation a 0 = 0 := by
  apply Multiset.ext.mpr
  intro i
  simp
theorem box_occupation_le (a : Multiset A) (r : TailBox a.count) :
    boxOccupation a r ≤ a := by
  apply Multiset.le_iff_count.mpr
  intro i
  rw [box_occupation_count]
  exact Nat.le_of_lt_succ (r i).isLt
theorem box_occupation_ne_zero (a : Multiset A) (r : TailBox a.count) (hr : r ≠ 0) :
    boxOccupation a r ≠ 0 := by
  intro h
  apply hr
  funext i
  apply Fin.ext
  have hc := congrArg (Multiset.count i) h
  simpa using hc
theorem box_occupation_mem (a : Multiset A) (r : TailBox a.count) (i : A) :
    i ∈ boxOccupation a r ↔ 0 < (r i).val := by
  rw [← Multiset.count_pos, box_occupation_count]
theorem box_occupation_lower (a : Multiset A) (r : TailBox a.count) (i : A) :
    boxOccupation a (D5.S3.Quantum.StationaryGram.StationaryOccupationRankNullity.lower a.count i r) = (boxOccupation a r).erase i := by
  apply Multiset.ext.mpr
  intro j
  rw [box_occupation_count, D5.S3.Quantum.StationaryGram.StationaryOccupationRankNullity.lower_val]
  by_cases h : j = i
  · subst j
    simp
  · simp [h, Multiset.count_erase_of_ne h]
def occupationGram (a : Multiset A) (blank : A) (U : Unitary (A × K))
    (x : Space K) : Matrix (TailBox a.count) (TailBox a.count) ℂ :=
  Matrix.gram ℂ (fun r => residualMemory a blank U x (boxOccupation a r))
theorem occupation_gram_psd (a : Multiset A) (blank : A) (U : Unitary (A × K))
    (x : Space K) : (occupationGram a blank U x).PosSemidef :=
  Matrix.posSemidef_gram ℂ _
theorem occupation_gram_rank_le (a : Multiset A) (blank : A) (U : Unitary (A × K))
    (x : Space K) : (occupationGram a blank U x).rank ≤ Fintype.card K := by
  classical
  rw [occupationGram, Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun K ℂ)]
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height _)
variable (a : Multiset A) (blank : A) (U : Unitary (A × K)) (x f : Space K)
variable (hout : ∀ (w : Fin a.card → A) (k : K),
  circuit (fun _ => U) a.card 0 (initialized blank a.card x) (w, k) =
    sectorVector a.card a w * f k)
include hout in
theorem occupation_gram_zero (hf : ‖f‖ = 1) : occupationGram a blank U x 0 0 = 1 := by
  simp only [occupationGram, Matrix.gram_apply, box_occupation_zero,
    residual_zero a blank U x f hout]
  rw [inner_self_eq_norm_sq_to_K, hf]
  norm_num
include hout in
theorem occupation_gram_recurrence (r s : TailBox a.count) (hr : r ≠ 0) (hs : s ≠ 0) :
    occupationGram a blank U x r s = ∑ i,
      if 0 < (r i).val ∧ 0 < (s i).val then
        occupationGram a blank U x (D5.S3.Quantum.StationaryGram.StationaryOccupationRankNullity.lower a.count i r)
          (D5.S3.Quantum.StationaryGram.StationaryOccupationRankNullity.lower a.count i s) else 0 := by
  classical
  change inner ℂ (residualMemory a blank U x (boxOccupation a r))
    (residualMemory a blank U x (boxOccupation a s)) = _
  rw [letter_inner_sum blank U]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hri : 0 < (r i).val
  · rw [residual_letter_of_mem a blank U x f hout (boxOccupation a r)
      (box_occupation_le a r) i ((box_occupation_mem a r i).mpr hri)]
    by_cases hsi : 0 < (s i).val
    · rw [residual_letter_of_mem a blank U x f hout (boxOccupation a s)
        (box_occupation_le a s) i ((box_occupation_mem a s i).mpr hsi)]
      simp [hri, hsi, occupationGram, box_occupation_lower]
    · rw [residual_letter_of_not_mem a blank U x f hout (boxOccupation a s)
        (box_occupation_le a s) (box_occupation_ne_zero a s hs) i
        (fun h => hsi ((box_occupation_mem a s i).mp h))]
      simp [hsi]
  · rw [residual_letter_of_not_mem a blank U x f hout (boxOccupation a r)
      (box_occupation_le a r) (box_occupation_ne_zero a r hr) i
      (fun h => hri ((box_occupation_mem a r i).mp h))]
    simp [hri]
theorem unit_memory_card_pos (y : Space K) (hy : ‖y‖ = 1) : 0 < Fintype.card K := by
  classical
  by_contra h
  have : IsEmpty K := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos h)
  have hz : y = 0 := by ext k; exact isEmptyElim k
  simp [hz] at hy
set_option maxHeartbeats 800000 in
theorem stationary_memory_dimension_lower_bound
    (a : Multiset A) (blank : A) (U : Unitary (A × K))
    (x f : Space K) (hx : ‖x‖ = 1) (hf : ‖f‖ = 1)
    (hout : ∀ (w : Fin a.card → A) (k : K),
      circuit (fun _ => U) a.card 0 (initialized blank a.card x) (w, k) =
        sectorVector a.card a w * f k) :
    (∏ i, (a.count i + 1)) - Finset.univ.sup a.count ≤ Fintype.card K := by
  classical
  by_cases ha : a = 0
  · subst a
    simp only [Multiset.count_zero, zero_add, Finset.prod_const_one]
    exact (Nat.sub_le _ _).trans (Nat.succ_le_of_lt (unit_memory_card_pos x hx))
  · have hlow := D5.S3.Quantum.StationaryGram.StationaryOccupationRankNullity.stationary_gram_rank_lower_bound a.count
      (occupationGram a blank U x) (occupation_gram_psd a blank U x)
      (occupation_gram_zero a blank U x f hout hf)
      (occupation_gram_recurrence a blank U x f hout)
    let q0 : Fintype (TailBox a.count) := inferInstance
    have hu0 := occupation_gram_rank_le a blank U x
    have hupp : ∀ q : Fintype (TailBox a.count),
        @Matrix.rank (TailBox a.count) (TailBox a.count) ℂ q _
          (occupationGram a blank U x) ≤ Fintype.card K := by
      intro q
      have hq : q = q0 := Subsingleton.elim _ _
      subst q
      exact hu0
    exact hlow.trans (hupp _)
end D5.S3.Quantum.StationaryPreparation.PhysicalGram

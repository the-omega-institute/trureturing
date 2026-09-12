/- GID: D5/S3/Quantum/StationaryPreparation/StationaryOccupationAttainment
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/StationaryOccupationAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stationary occupation attainment by the exact last-tail padding Gram. -/

import D5.S3.Quantum.Algebra.StationaryGramRank
import D5.S3.Quantum.StationaryPreparation.PaddingTransition
import D5.S3.Quantum.StationaryPreparation.PaddingResidualGram
import D5.S3.Quantum.StationaryPreparation.PaddingResidualAction
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.StationaryOccupationAttainment

open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit

universe u v w

section
variable {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K]

private def blankMemory (blank : A) : Space K →ₗᵢ[ℂ] Space (A × K) :=
  coordinateEmbedding (blankInjection blank (Function.Embedding.refl K))

private theorem circuit_output_of_residuals (blank : A) (U : Unitary (A × K))
    (a : Multiset A) (r : Multiset A → Space K) (f : Space K)
    (hzero : r 0 = f)
    (hstep : ∀ b, b ≤ a → b ≠ 0 → ∀ i k,
      U (blankMemory blank (r b)) (i, k) = if i ∈ b then r (b.erase i) k else 0) :
    ∀ n t b, b.card = n → b ≤ a → ∀ (w : Word A n) k,
      circuit (fun _ => U) n t (initialized blank n (r b)) (w, k) =
        if occupation w = b then f k else 0 := by
  have initialized_apply_all {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K] (blank : A) (n : ℕ) (x : Space K)
      (w : Fin n → A) (k : K) :
      initialized blank n x (w, k) = if w = (fun _ => blank) then x k else 0 := by
    classical
    conv_lhs => rw [basis_expansion x]
    simp only [map_sum, map_smul, initialize_basis]
    by_cases hw : w = (fun _ => blank) <;>
      simp [blankState, basis_apply, Prod.mk.injEq, hw]
  have blank_memory_apply {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K] (blank : A) (x : Space K) (i : A) (k : K) :
      blankMemory blank x (i, k) = if i = blank then x k else 0 := by
    by_cases hi : i = blank
    · subst i
      simpa [blankMemory, blankInjection] using
        (coordinate_embedding_apply (blankInjection blank (Function.Embedding.refl K)) x k)
    · rw [if_neg hi]
      apply coordinate_embedding_off_range
      rintro ⟨j, hj⟩
      exact hi (congrArg Prod.fst hj).symm
  have first_gate_initialized {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K] (blank : A) (n : ℕ) (U : Unitary (A × K))
      (x : Space K) (w : Fin (n + 1) → A) (k : K) :
      firstGate n U (initialized blank (n + 1) x) (w, k) =
        if Fin.tail w = (fun _ => blank) then U (blankMemory blank x) (w 0, k) else 0 := by
    rw [first_gate_apply]
    have hc (i : A) (u : Fin n → A) :
        Fin.cons i u = (fun _ => blank) ↔ i = blank ∧ u = (fun _ => blank) := by
      simp [funext_iff, Fin.forall_fin_succ]
    have hv : (WithLp.toLp 2 (fun p : A × K =>
        initialized blank (n + 1) x (Fin.cons p.1 (Fin.tail w), p.2))) =
        if Fin.tail w = (fun _ => blank) then blankMemory blank x else 0 := by
      ext p
      rcases p with ⟨i, j⟩
      by_cases ht : Fin.tail w = (fun _ => blank) <;>
        simp [initialized_apply_all, hc, ht, blank_memory_apply]
    rw [hv]
    split <;> simp_all
  have circuit_initialized_step {A : Type u} [Fintype A] [DecidableEq A] {K : Type v} [Fintype K] [DecidableEq K] (blank : A) (U : ℕ → Unitary (A × K))
      (n t : ℕ) (x : Space K) (w : Fin (n + 1) → A) (k : K) :
      circuit U (n + 1) t (initialized blank (n + 1) x) (w, k) =
        circuit U n (t + 1)
          (initialized blank n (WithLp.toLp 2
            (fun j : K => U t (blankMemory blank x) (w 0, j)))) (Fin.tail w, k) := by
    simp only [circuit, LinearIsometryEquiv.trans_apply, tail_gate_apply]
    have hv : (WithLp.toLp 2 (fun p : Register A K n =>
        firstGate n (U t) (initialized blank (n + 1) x) (Fin.cons (w 0) p.1, p.2))) =
        initialized blank n (WithLp.toLp 2
          (fun j : K => U t (blankMemory blank x) (w 0, j))) := by
      ext p
      rcases p with ⟨u, j⟩
      simp [first_gate_initialized, initialized_apply_all]
    rw [hv]
  have occupation_cons_eq {A : Type u} [Fintype A] [DecidableEq A] {n : ℕ} (i : A) (w : Word A n) :
      occupation (Fin.cons i w) = i ::ₘ occupation w := by
    simp only [occupation, List.ofFn_cons]
    rfl
  have occupation_head_tail_iff {A : Type u} [Fintype A] [DecidableEq A] {n : ℕ} (w : Word A (n + 1)) (b : Multiset A) :
      occupation w = b ↔ w 0 ∈ b ∧ occupation (Fin.tail w) = b.erase (w 0) := by
    conv_lhs => rw [← Fin.cons_self_tail w, occupation_cons_eq]
    rw [← Multiset.singleton_add, add_comm ({w 0} : Multiset A),
      Multiset.add_singleton_eq_iff]

  intro n
  induction n with
  | zero =>
    intro t b hb hba w k
    have hb0 : b = 0 := Multiset.card_eq_zero.mp hb
    subst b
    have hw : w = (fun _ => blank) := Subsingleton.elim _ _
    simp [circuit, initialized_apply_all, hzero, hw, occupation]
  | succ n ih =>
    intro t b hb hba w k
    have hb0 : b ≠ 0 := by intro hz; simp [hz] at hb
    rw [circuit_initialized_step]
    have hv : (WithLp.toLp 2
        (fun j : K => U (blankMemory blank (r b)) (w 0, j))) =
        if w 0 ∈ b then r (b.erase (w 0)) else 0 := by
      ext j
      by_cases hi : w 0 ∈ b <;> simp [hstep b hba hb0, hi]
    rw [hv]
    by_cases hi : w 0 ∈ b
    · rw [if_pos hi]
      have hcard : (b.erase (w 0)).card = n := by
        simp [Multiset.card_erase_of_mem hi, hb]
      rw [ih (t + 1) (b.erase (w 0)) hcard ((Multiset.erase_le _ _).trans hba)]
      simp only [occupation_head_tail_iff w b, hi, true_and]
    · have hw : occupation w ≠ b := fun h => hi ((occupation_head_tail_iff w b).mp h).1
      simp [hi, hw]

end

section
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

/-- The actual padding vectors realize every source block and its normalized Gram data. -/
private theorem padding_gram_data (a : Multiset σ) (head : σ) :
    (∀ b : PaddingTransition.Tail a head,
      PaddingResidualGram.block a head b = PaddingResidualGram.L (a.count head) *
        Matrix.diagonal (fun j : Fin (a.count head + 1) => (PaddingResidualGram.delta a head b j.val : ℂ)) *
          (PaddingResidualGram.L (a.count head)).transpose ∧
      (PaddingResidualGram.block a head b).rank = (if b = 0 then 1 else a.count head + 1) ∧
      (b = 0 → PaddingResidualGram.m a head b 0 = 1 ∧ ∀ j : ℕ, PaddingResidualGram.delta a head b j = if j = 0 then 1 else 0) ∧
      (b ≠ 0 → (∀ j : Fin (a.count head + 1), 0 < PaddingResidualGram.delta a head b j.val) ∧
        (∀ j : Fin (a.count head + 1),
          PaddingResidualGram.lastTail head (PaddingResidualGram.slice a head b j.val) = PaddingResidualGram.delta a head b j.val)) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ a.count head →
        PaddingResidualGram.m a head b j / PaddingResidualGram.m a head b (j - 1) =
          ((j : ℝ) + ((PaddingResidualGram.tailWord a head b).card : ℝ)) / (j : ℝ) ∧
        (b ≠ 0 → 1 < PaddingResidualGram.m a head b j / PaddingResidualGram.m a head b (j - 1)))) ∧
    Matrix.gram ℂ (fun r : PaddingTransition.Box a => PaddingResidualGram.padding a head (PaddingResidualGram.occ a r)) = PaddingResidualGram.B a head ∧
    PaddingResidualGram.D a * PaddingResidualGram.G a head * PaddingResidualGram.D a = PaddingResidualGram.B a head ∧
    (Matrix.gram ℂ (fun r : PaddingTransition.Box a => PaddingResidualGram.padding a head (PaddingResidualGram.occ a r))).rank =
      (Matrix.gram ℂ (fun r : PaddingTransition.Box a => PaddingResidualGram.phi a head (PaddingResidualGram.occ a r))).rank ∧
    PaddingResidualGram.B a head 0 0 = 1 ∧
    PaddingResidualGram.phi a head 0 = basis none ∧ PaddingResidualGram.padding a head 0 = basis none ∧
    (∀ j : ℕ, j ≤ a.count head → PaddingResidualGram.phi a head (Multiset.replicate j head) = basis none) ∧
    (∀ r : Multiset σ, r ≤ a → inner ℂ (PaddingResidualGram.phi a head r) (PaddingResidualGram.phi a head 0) = PaddingResidualGram.z head r) := by
  let paddingGram := Matrix.gram ℂ (fun r : PaddingTransition.Box a =>
    PaddingResidualGram.padding a head (PaddingResidualGram.occ a r))
  let normalizedPaddingGram := Matrix.gram ℂ (fun r : PaddingTransition.Box a =>
    PaddingResidualGram.phi a head (PaddingResidualGram.occ a r))
  have capacities_multiset_echo (c : σ → ℕ) :
      (∀ i : σ, (∑ j : σ, Multiset.replicate (c j) j).count i = c i) ∧
        (∑ j : σ, Multiset.replicate (c j) j).card = ∑ j : σ, c j := by
    simp [Multiset.count_sum', Multiset.count_replicate]
  have occ_count (r : PaddingTransition.Box a) (i : σ) :
      (PaddingResidualGram.occ a r).count i = (r i).val :=
    (capacities_multiset_echo (fun j => (r j).val)).1 i
  have scale_pos (r : Multiset σ) : 0 < PaddingResidualGram.residualScale r := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast multiplicity_pos r rfl)
  have scale_ne_zero (r : Multiset σ) : (PaddingResidualGram.residualScale r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (scale_pos r).ne'
  have diagonal_det_ne_zero : (PaddingResidualGram.D a).det ≠ 0 := by
    rw [PaddingResidualGram.D, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun r _ => scale_ne_zero (PaddingResidualGram.occ a r))
  have head_slice_count_head (b : Multiset σ) (h : ℕ) :
      (PaddingResidualGram.headSlice head b h).count head = h := by
    simp [PaddingResidualGram.headSlice, Multiset.count_filter]
  have head_slice_count_tail (b : Multiset σ) (h : ℕ)
      (i : σ) (hi : i ≠ head) : (PaddingResidualGram.headSlice head b h).count i = b.count i := by
    simp [head_slice_count_head, PaddingResidualGram.headSlice, Multiset.count_filter, Multiset.count_replicate, hi, Ne.symm hi]
  have head_slice_self (b : Multiset σ) :
      PaddingResidualGram.headSlice head b (b.count head) = b := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i; exact head_slice_count_head b _
    · exact head_slice_count_tail b _ i hi
  have tail_count_zero_iff (b : Multiset σ) :
      PaddingResidualGram.tailCount head b = 0 ↔ ∀ i, i ≠ head → b.count i = 0 := by
    simp only [PaddingResidualGram.tailCount, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
    constructor
    · intro h i hi
      exact h ⟨i, hi⟩
    · intro h i
      exact h i.val i.property
  have tail_filter_eq_zero (b : Multiset σ) :
      b.filter (fun i => i ≠ head) = 0 ↔ PaddingResidualGram.tailCount head b = 0 := by
    rw [tail_count_zero_iff]
    constructor
    · intro h i hi
      have := congrArg (Multiset.count i) h
      simpa [Multiset.count_filter, hi] using this
    · intro h
      apply Multiset.ext.mpr
      intro i
      by_cases hi : i = head
      · subst i; simp []
      · simp [hi, h i hi]
  have padding_residual_tail_free (b : Multiset σ)
      (hb : b ≤ a) (hr : PaddingResidualGram.tailCount head b = 0) : PaddingResidualGram.padding a head b = basis none := by
    classical
    have hf : PaddingResidualGram.tailOcc head b = 0 :=
      (tail_filter_eq_zero b).mpr hr
    ext k
    cases k with
    | none => simp [PaddingResidualGram.padding, hb, hf, basis_apply]
    | some p =>
      rcases p with ⟨d, j⟩
      by_cases ht : PaddingResidualGram.tailWord a head d.val = 0
      · simp [PaddingResidualGram.padding, hb, hf, ht, PaddingResidualGram.slice,
          PaddingResidualGram.lastTail, PaddingResidualGram.tailOcc,
          Multiset.mem_replicate, basis_apply]
      · simp [PaddingResidualGram.padding, hb, hf, Ne.symm ht, basis_apply]
  have tail_free_multiplicity (b : Multiset σ)
      (hr : PaddingResidualGram.tailCount head b = 0) (n : ℕ) :
      multiplicity (PaddingResidualGram.headSlice head b n).card (PaddingResidualGram.headSlice head b n) = 1 := by
    have hf := (tail_filter_eq_zero b).mpr hr
    simp only [PaddingResidualGram.headSlice, hf, add_zero, Multiset.card_replicate]
    rw [multiplicity_eq_factorial _ (Multiset.card_replicate _ _)]
    simp_rw [Multiset.count_replicate, apply_ite Nat.factorial]
    simp only [Nat.factorial_zero, Finset.prod_ite_eq, Finset.mem_univ, if_true]
    exact Nat.div_self (Nat.factorial_pos n)
  have normalized_padding_tail_free (b : Multiset σ)
      (hb : b ≤ a) (hr : PaddingResidualGram.tailCount head b = 0) : PaddingResidualGram.phi a head b = basis none := by
    have hm : multiplicity b.card b = 1 := by
      simpa only [head_slice_self] using tail_free_multiplicity b hr (b.count head)
    simp [PaddingResidualGram.phi, PaddingResidualGram.M, padding_residual_tail_free b hb hr, PaddingResidualGram.residualScale, hm]
  have normalized_padding_zero :
      PaddingResidualGram.phi a head 0 = basis none := by
    apply normalized_padding_tail_free 0 (Multiset.zero_le _)
    simp [PaddingResidualGram.tailCount]
  have padding_gram_eq_diagonal : paddingGram =
      PaddingResidualGram.D a * normalizedPaddingGram *
        PaddingResidualGram.D a := by
    classical
    ext r s
    simp only [paddingGram, normalizedPaddingGram, PaddingResidualGram.D,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.gram_apply,
      PaddingResidualGram.phi, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal]
    simp only [PaddingResidualGram.M]
    simp only [PaddingResidualGram.residualScale] at scale_ne_zero
    field_simp [scale_ne_zero (PaddingResidualGram.occ a r), scale_ne_zero (PaddingResidualGram.occ a s)]
  have padding_gram_rank_eq :
      (paddingGram).rank = (normalizedPaddingGram).rank := by
    classical
    rw [padding_gram_eq_diagonal,
      Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (diagonal_det_ne_zero),
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (diagonal_det_ne_zero)]
  have box_occupation_le (r : PaddingTransition.Box a) : PaddingResidualGram.occ a r ≤ a := by
    apply Multiset.le_iff_count.mpr
    intro i
    rw [occ_count]
    exact Nat.le_of_lt_succ (r i).isLt
  have lower_ones_det (H : ℕ) : (PaddingResidualGram.L H).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ (by
      intro i j hij
      exact if_neg (not_le.mpr hij))]
    simp [PaddingResidualGram.L]
  have tail_word_count_head (b : PaddingTransition.Tail a head) : (PaddingResidualGram.tailWord a head b).count head = 0 := by
    simp only [PaddingResidualGram.tailWord, Multiset.count_sum', Multiset.count_replicate]
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg i.property
  have tail_word_count (b : PaddingTransition.Tail a head) (i : PaddingTransition.TailAlphabet head) :
      (PaddingResidualGram.tailWord a head b).count i.val = (b i).val := by
    simp only [PaddingResidualGram.tailWord, Multiset.count_sum', Multiset.count_replicate, Subtype.val_inj]
    simpa only [Finset.mem_univ, if_true] using
      Finset.sum_ite_eq' Finset.univ i (fun j => (b j).val)
  have block_occupation_slice (b : PaddingTransition.Tail a head) (j k : ℕ) :
      PaddingResidualGram.headSlice head (PaddingResidualGram.slice a head b j) k = PaddingResidualGram.slice a head b k := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i
      simp [PaddingResidualGram.slice, head_slice_count_head, tail_word_count_head]
    · simp [PaddingResidualGram.slice, head_slice_count_tail, Multiset.count_replicate,
        hi, Ne.symm hi, tail_word_count]
  have tail_word_zero :
      PaddingResidualGram.tailWord a head 0 = 0 := by
    simp [tail_word_count_head, tail_word_count, PaddingResidualGram.tailWord]
  have tail_word_residual (r : Multiset σ) (hr : r ≤ a) :
      PaddingResidualGram.tailWord a head (PaddingResidualGram.residualTail head a r hr) = PaddingResidualGram.tailOcc head r := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i
      simp [tail_word_count_head, tail_word_count, tail_word_zero, PaddingResidualGram.tailOcc]
    · rw [show i = (⟨i, hi⟩ : PaddingTransition.TailAlphabet head).val from rfl, tail_word_count]
      simp [tail_word_count_head, tail_word_count, tail_word_zero, PaddingResidualGram.residualTail, PaddingResidualGram.tailOcc, hi]
  have slice_eq_head_slice (r : Multiset σ) (hr : r ≤ a) (j : ℕ) :
      PaddingResidualGram.slice a head (PaddingResidualGram.residualTail head a r hr) j = PaddingResidualGram.headSlice head r j := by
    rw [PaddingResidualGram.slice, tail_word_residual]
    rfl
  have padding_block_factorization (b : PaddingTransition.Tail a head) :
      PaddingResidualGram.block a head b = PaddingResidualGram.L (a.count head) *
        Matrix.diagonal (fun j : Fin (a.count head + 1) => (PaddingResidualGram.delta a head b j.val : ℂ)) *
          (PaddingResidualGram.L (a.count head)).transpose := by
    have partial_sum (n : ℕ) (hn : n ≤ a.count head) :
        (∑ j : Fin (a.count head + 1), if j.val ≤ n then
          (PaddingResidualGram.delta a head b j.val : ℂ) else 0) =
          (PaddingResidualGram.m a head b n : ℂ) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun j : ℕ => if j ≤ n then (PaddingResidualGram.delta a head b j : ℂ) else 0)]
      trans ∑ j ∈ Finset.range (n + 1), (PaddingResidualGram.delta a head b j : ℂ)
      · apply Finset.sum_congr_of_eq_on_inter
        · intro j _ hj
          exact if_neg (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj)
        · intro j hj hk
          simp only [Finset.mem_range] at hj hk
          omega
        · intro j _ hj
          exact if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      · simp only [PaddingResidualGram.delta, apply_ite Complex.ofReal, Complex.ofReal_sub]
        exact (Finset.eq_sum_range_sub' (fun j => (PaddingResidualGram.m a head b j : ℂ)) n).symm
    ext j k
    change (PaddingResidualGram.m a head b (min j.val k.val) : ℂ) = _
    rw [← partial_sum _ (le_trans (min_le_left _ _) (Nat.le_of_lt_succ j.isLt)), Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, PaddingResidualGram.L,
      ite_mul, zero_mul, mul_ite, mul_zero, one_mul, mul_one, ← ite_and,
      Fin.le_def, le_min_iff, and_comm]
  have tail_sum_eq_zero_iff {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : TailBox c) :
      tailSum b = 0 ↔ b = PaddingTransition.zeroTail c := by
    constructor
    · intro h
      have hz : ∀ i, (b i).val = 0 := by
        simpa only [tailSum, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
          using h
      funext i
      exact Fin.ext (hz i)
    · rintro rfl
      simp [tailSum, PaddingTransition.zeroTail]
  have positive_tail_sum {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : PaddingTransition.PaddingTail c) :
      0 < tailSum b.val :=
    Nat.pos_of_ne_zero (fun h => b.property ((tail_sum_eq_zero_iff c b.val).mp h))
  have head_add_tail_count (b : Multiset σ) :
      b.count head + PaddingResidualGram.tailCount head b = b.card := by
    unfold PaddingResidualGram.tailCount
    rw [← Fintype.sum_eq_add_sum_subtype_ne b.count head]
    exact Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)
  have last_tail_mass_pos (b : Multiset σ) (hR : 0 < PaddingResidualGram.tailCount head b) :
      0 < PaddingResidualGram.lastTailMass head b := by
    have hn : 0 < b.card := by have := head_add_tail_count b; omega
    unfold PaddingResidualGram.lastTailMass
    exact div_pos (mul_pos (by exact_mod_cast hR)
      (by exact_mod_cast multiplicity_pos b rfl)) (by exact_mod_cast hn)
  have erase_multiplicity_real (b : Multiset σ) (i : σ) (hi : i ∈ b) :
      (b.card : ℝ) * (multiplicity (b.erase i).card (b.erase i) : ℝ) =
        (b.count i : ℝ) * (multiplicity b.card b : ℝ) := by
    have hn : (b.erase i).card + 1 = b.card := by
      simpa using congrArg Multiset.card (Multiset.cons_erase hi)
    have hm := multiplicity_erase_mul (n := (b.erase i).card) hn.symm i hi
    rw [hn] at hm
    exact_mod_cast hm
  have head_slice_tail_count (b : Multiset σ) (h : ℕ) :
      PaddingResidualGram.tailCount head (PaddingResidualGram.headSlice head b h) = PaddingResidualGram.tailCount head b := by
    apply Finset.sum_congr rfl
    intro i _
    exact head_slice_count_tail b h i.val i.property
  have head_slice_card (b : Multiset σ) (h : ℕ) :
      (PaddingResidualGram.headSlice head b h).card = h + PaddingResidualGram.tailCount head b := by
    rw [← head_add_tail_count, head_slice_count_head, head_slice_tail_count]
  have head_slice_erase_head (b : Multiset σ) (h : ℕ) :
      (PaddingResidualGram.headSlice head b h).erase head = PaddingResidualGram.headSlice head b (h - 1) := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i
      simp [head_slice_count_head]
    · rw [Multiset.count_erase_of_ne hi,
        head_slice_count_tail b h i hi, head_slice_count_tail b (h - 1) i hi]
  have last_tail_mass_head_slice (b : Multiset σ)
      (hr : 0 < PaddingResidualGram.tailCount head b) (j : ℕ) :
      PaddingResidualGram.lastTailMass head (PaddingResidualGram.headSlice head b j) =
        if j = 0 then
          (multiplicity (PaddingResidualGram.headSlice head b 0).card (PaddingResidualGram.headSlice head b 0) : ℝ)
        else
          (multiplicity (PaddingResidualGram.headSlice head b j).card (PaddingResidualGram.headSlice head b j) : ℝ) -
          (multiplicity (PaddingResidualGram.headSlice head b (j - 1)).card (PaddingResidualGram.headSlice head b (j - 1)) : ℝ) := by
    have hn : (0 : ℝ) < (PaddingResidualGram.headSlice head b j).card := by
      exact_mod_cast (show 0 < (PaddingResidualGram.headSlice head b j).card by rw [head_slice_card]; omega)
    by_cases hj : j = 0
    · subst j
      simp only [ite_true, PaddingResidualGram.lastTailMass, head_slice_tail_count, head_slice_card, zero_add]
      exact mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne')
    · rw [if_neg hj]
      have hm := erase_multiplicity_real (PaddingResidualGram.headSlice head b j) head
        (Multiset.count_pos.mp (by simpa [head_slice_count_head] using Nat.pos_of_ne_zero hj))
      rw [head_slice_erase_head, head_slice_count_head] at hm
      have hs : ((PaddingResidualGram.headSlice head b j).card : ℝ) = j + (PaddingResidualGram.tailCount head b : ℝ) := by
        exact_mod_cast head_slice_card b j
      unfold PaddingResidualGram.lastTailMass
      rw [head_slice_tail_count, div_eq_iff hn.ne']
      nlinarith [congrArg (fun x : ℝ =>
        x * (multiplicity (PaddingResidualGram.headSlice head b j).card (PaddingResidualGram.headSlice head b j) : ℝ)) hs]
  have block_occupation_tail (b : PaddingTransition.Tail a head) (j : ℕ) :
      PaddingResidualGram.tailCount head (PaddingResidualGram.slice a head b j) = tailSum b := by
    unfold PaddingResidualGram.tailCount tailSum
    apply Finset.sum_congr rfl
    intro i _
    simp [PaddingResidualGram.slice, Multiset.count_replicate, i.property, Ne.symm i.property, tail_word_count]
  have block_difference_pos (b : PaddingTransition.Tail a head)
      (hb : b ≠ PaddingTransition.zeroTail _) (j : ℕ) : 0 < PaddingResidualGram.delta a head b j := by
    have hr : 0 < PaddingResidualGram.tailCount head (PaddingResidualGram.slice a head b 0) := by
      rw [block_occupation_tail]
      exact positive_tail_sum _ ⟨b, hb⟩
    have h := last_tail_mass_head_slice (PaddingResidualGram.slice a head b 0) hr j
    rw [block_occupation_slice, block_occupation_slice, block_occupation_slice] at h
    change PaddingResidualGram.lastTailMass head (PaddingResidualGram.slice a head b j) = PaddingResidualGram.delta a head b j at h
    rw [← h]
    apply last_tail_mass_pos
    rw [block_occupation_tail]
    exact positive_tail_sum _ ⟨b, hb⟩
  have block_difference_zero_tail (j : ℕ) :
      PaddingResidualGram.delta a head (PaddingTransition.zeroTail _) j = if j=0 then 1 else 0 := by
    have hm (n : ℕ) : PaddingResidualGram.m a head (PaddingTransition.zeroTail _) n = 1 := by
      have h := tail_free_multiplicity 0 (by simp [PaddingResidualGram.tailCount]) n
      simpa [PaddingResidualGram.m, PaddingResidualGram.M, PaddingResidualGram.headSlice,
        PaddingResidualGram.slice, tail_word_zero] using congrArg (fun x : ℕ => (x : ℝ)) h
    simp [PaddingResidualGram.delta, hm]
  have padding_gram_eq_B :
      paddingGram = PaddingResidualGram.B a head := by
    have hindex (r : PaddingTransition.Box a) :
        PaddingResidualGram.residualTail head a (PaddingResidualGram.occ a r)
          (box_occupation_le r) = PaddingResidualGram.tailIndex a head r := by
      funext i
      exact Fin.ext (occ_count r i.val)
    have hslice (r : PaddingTransition.Box a) (j : ℕ) :
        PaddingResidualGram.headSlice head (PaddingResidualGram.occ a r) j =
          PaddingResidualGram.slice a head (PaddingResidualGram.tailIndex a head r) j := by
      rw [← slice_eq_head_slice (PaddingResidualGram.occ a r) (box_occupation_le r), hindex]
    ext r t
    have ht : (PaddingResidualGram.occ a r).filter (fun i => i ≠ head) =
        (PaddingResidualGram.occ a t).filter (fun i => i ≠ head) ↔
          PaddingResidualGram.tailIndex a head r = PaddingResidualGram.tailIndex a head t := by
      constructor
      · intro h
        funext i
        apply Fin.ext
        have hc := congrArg (Multiset.count i.val) h
        simpa [Multiset.count_filter, i.property, occ_count,
          PaddingResidualGram.tailIndex] using hc
      · intro h
        apply Multiset.ext.mpr
        intro i
        by_cases hi : i = head
        · subst i; simp
        · have hc := congrArg (fun b : PaddingTransition.Tail a head => (b ⟨i, hi⟩).val) h
          simpa [Multiset.count_filter, hi, occ_count, PaddingResidualGram.tailIndex] using hc
    simp only [paddingGram, Matrix.gram_apply, PaddingResidualGram.padding_inner a head
      _ _ (box_occupation_le r) (box_occupation_le t), PaddingResidualGram.B,
      PaddingResidualGram.block, PaddingResidualGram.m, PaddingResidualGram.M,
      occ_count, hslice, ht, Complex.ofReal_natCast]
  have block_rank_diagonal (b : PaddingTransition.Tail a head) :
      (PaddingResidualGram.block a head b).rank =
        (Matrix.diagonal (fun j : Fin (a.count head + 1) =>
          (PaddingResidualGram.delta a head b j.val : ℂ))).rank := by
    rw [padding_block_factorization,
      Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (by simp [Matrix.det_transpose, lower_ones_det]),
      Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (by simp [lower_ones_det])]
  have padding_block_rank_zero :
      (PaddingResidualGram.block a head (PaddingTransition.zeroTail _)).rank = 1 := by
    classical
    rw [block_rank_diagonal, Matrix.rank_diagonal]
    have hn (j : Fin (a.count head + 1)) :
        (PaddingResidualGram.delta a head (PaddingTransition.zeroTail _) j.val : ℂ) ≠ 0 ↔ j = 0 := by
      simp [block_difference_zero_tail]
    simp only [hn]
    exact Fintype.card_subtype_eq (0 : Fin (a.count head + 1))
  have padding_block_rank_positive (b : PaddingTransition.Tail a head) (hb : b ≠ PaddingTransition.zeroTail _) :
      (PaddingResidualGram.block a head b).rank = a.count head + 1 := by
    classical
    rw [block_rank_diagonal, Matrix.rank_diagonal]
    have hn (j : Fin (a.count head + 1)) : (PaddingResidualGram.delta a head b j.val : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (block_difference_pos b hb j.val).ne'
    simp [hn]
  have block_rank (b : PaddingTransition.Tail a head) :
      (PaddingResidualGram.block a head b).rank = if b = 0 then 1 else a.count head + 1 := by
    split_ifs with hb
    · simpa [hb] using padding_block_rank_zero
    · exact padding_block_rank_positive b hb

  have tail_occ_card (r : Multiset σ) :
      (PaddingResidualGram.tailOcc head r).card = PaddingResidualGram.tailCount head r := by
    have h := congrArg Multiset.card (Multiset.filter_add_not (fun i : σ => i = head) r)
    simp only [Multiset.card_add, Multiset.filter_eq', Multiset.card_replicate] at h
    have hc := head_add_tail_count r
    change r.count head + (PaddingResidualGram.tailOcc head r).card = r.card at h
    omega

  have last_tail_eq_mass (r : Multiset σ) :
      PaddingResidualGram.lastTail head r = PaddingResidualGram.lastTailMass head r := by
    rw [PaddingResidualGram.lastTail, tail_occ_card]
    rfl
  have last_tail_delta (b : PaddingTransition.Tail a head)
      (hb : b ≠ 0) (j : ℕ) : PaddingResidualGram.lastTail head (PaddingResidualGram.slice a head b j) = PaddingResidualGram.delta a head b j := by
    have hr : 0 < PaddingResidualGram.tailCount head (PaddingResidualGram.slice a head b 0) := by
      rw [block_occupation_tail]
      exact positive_tail_sum _ ⟨b, hb⟩
    have h := last_tail_mass_head_slice (PaddingResidualGram.slice a head b 0) hr j
    simp only [block_occupation_slice] at h
    change PaddingResidualGram.lastTailMass head (PaddingResidualGram.slice a head b j) = PaddingResidualGram.delta a head b j at h
    simpa only [last_tail_eq_mass] using h
  have block_ratio (b : PaddingTransition.Tail a head)
      (j : ℕ) (hj : 1 ≤ j) :
      PaddingResidualGram.m a head b j / PaddingResidualGram.m a head b (j - 1) =
        ((j : ℝ) + ((PaddingResidualGram.tailWord a head b).card : ℝ)) / (j : ℝ) := by
    let r := PaddingResidualGram.slice a head b j
    have hh : r.count head = j := by simp [r, PaddingResidualGram.slice, tail_word_count_head]
    have hmem : head ∈ r := Multiset.count_pos.mp (by rw [hh]; exact hj)
    have he : r.erase head = PaddingResidualGram.slice a head b (j - 1) := by
      change (PaddingResidualGram.slice a head b j).erase head = _
      rw [← block_occupation_slice b 0 j, head_slice_erase_head, block_occupation_slice]
    have hc : r.card = j + (PaddingResidualGram.tailWord a head b).card := by
      rw [show r = PaddingResidualGram.slice a head b j from rfl]
      simp only [PaddingResidualGram.slice, Multiset.card_add, Multiset.card_replicate]
    have hm := erase_multiplicity_real r head hmem
    rw [he, hh] at hm
    have hp : PaddingResidualGram.m a head b (j - 1) ≠ 0 := by
      dsimp only [PaddingResidualGram.m, PaddingResidualGram.M]
      exact_mod_cast (multiplicity_pos (PaddingResidualGram.slice a head b (j - 1)) rfl).ne'
    apply (div_eq_div_iff hp (by exact_mod_cast Nat.ne_of_gt hj)).mpr
    calc
      PaddingResidualGram.m a head b j * (j : ℝ) = (r.card : ℝ) * PaddingResidualGram.m a head b (j - 1) := by
        simpa only [r, PaddingResidualGram.m, PaddingResidualGram.M, mul_comm] using hm.symm
      _ = ((j : ℝ) + ((PaddingResidualGram.tailWord a head b).card : ℝ)) * PaddingResidualGram.m a head b (j - 1) := by
        rw [hc, Nat.cast_add]
  have block_ratio_strict (b : PaddingTransition.Tail a head)
      (hb : b ≠ 0) (j : ℕ) (hj : 1 ≤ j) :
      1 < PaddingResidualGram.m a head b j / PaddingResidualGram.m a head b (j - 1) := by
    apply (one_lt_div₀ (show (0 : ℝ) < PaddingResidualGram.m a head b (j - 1) by
      dsimp only [PaddingResidualGram.m, PaddingResidualGram.M]
      exact_mod_cast multiplicity_pos (PaddingResidualGram.slice a head b (j - 1)) rfl)).mpr
    have hp := block_difference_pos b hb j
    simpa only [PaddingResidualGram.delta, if_neg (Nat.ne_of_gt hj), sub_pos] using hp
  have padding_residual_none (b : Multiset σ)
      (hb : b ≤ a) (hr : 0 < PaddingResidualGram.tailCount head b) : PaddingResidualGram.padding a head b none = 0 := by
    have hf : PaddingResidualGram.tailOcc head b ≠ 0 :=
      fun h => (Nat.ne_of_gt hr) ((tail_filter_eq_zero b).mp h)
    simp [PaddingResidualGram.padding, hb, hf]

  have gram_congruence : PaddingResidualGram.D a * PaddingResidualGram.G a head * PaddingResidualGram.D a = PaddingResidualGram.B a head := by
    rw [← PaddingResidualGram.phi_gram a head, ← padding_gram_eq_diagonal, padding_gram_eq_B]
  have padding_moment (b : Multiset σ) (hb : b ≤ a) :
      inner ℂ (PaddingResidualGram.phi a head b) (basis none) = if PaddingResidualGram.tailCount head b = 0 then 1 else 0 := by
    classical
    by_cases hr : PaddingResidualGram.tailCount head b = 0
    · simp [occ_count, head_slice_count_head, normalized_padding_zero, normalized_padding_tail_free b hb hr, hr,
        basis]
    · rw [PaddingResidualGram.phi, PaddingResidualGram.M, inner_smul_left, if_neg hr]
      have hz : inner ℂ (PaddingResidualGram.padding a head b) (basis none) = 0 := by
        apply inner_eq_zero_symm.mp
        simpa only [basis, EuclideanSpace.basisFun_inner] using
          padding_residual_none b hb (Nat.pos_of_ne_zero hr)
      rw [hz, mul_zero]
  have phi_moment (r : Multiset σ) (hr : r ≤ a) :
      inner ℂ (PaddingResidualGram.phi a head r) (PaddingResidualGram.phi a head 0) = PaddingResidualGram.z head r := by
    simpa only [PaddingResidualGram.z, normalized_padding_zero,
      show PaddingResidualGram.tailOcc head r = 0 ↔ PaddingResidualGram.tailCount head r = 0 from tail_filter_eq_zero r]
      using padding_moment r hr
  have zero_block_mass : PaddingResidualGram.m a head 0 0 = 1 := by
    simpa [PaddingResidualGram.delta] using block_difference_zero_tail 0
  have B_zero_zero : PaddingResidualGram.B a head 0 0 = 1 := by
    change (if (0 : PaddingTransition.Tail a head) = 0 then (PaddingResidualGram.m a head 0 0 : ℂ) else 0) = 1
    rw [if_pos rfl, zero_block_mass, Complex.ofReal_one]

  have normalized_padding_axis (j : ℕ)
      (hj : j ≤ a.count head) :
      PaddingResidualGram.phi a head (Multiset.replicate j head) = basis none := by
    apply normalized_padding_tail_free
    · apply Multiset.le_iff_count.mpr
      intro i
      by_cases hi : head = i
      · subst i; simpa only [Multiset.count_replicate_self] using hj
      · simp only [Multiset.count_replicate, if_neg hi]; exact Nat.zero_le _
    · apply (tail_count_zero_iff _).mpr
      intro i hi
      simp only [Multiset.count_replicate, if_neg (Ne.symm hi)]
  have padding_residual_zero :
      PaddingResidualGram.padding a head 0 = basis none := by
    apply padding_residual_tail_free 0 (Multiset.zero_le _)
    simp [PaddingResidualGram.tailCount]
  refine ⟨?_, padding_gram_eq_B, gram_congruence, padding_gram_rank_eq, B_zero_zero,
    normalized_padding_zero, padding_residual_zero, normalized_padding_axis, phi_moment⟩
  intro b
  refine ⟨padding_block_factorization b, block_rank b, ?_, ?_, ?_⟩
  · rintro rfl
    exact ⟨zero_block_mass, block_difference_zero_tail⟩
  · intro hb
    exact ⟨fun j => block_difference_pos b hb j.val, fun j => last_tail_delta b hb j.val⟩
  · intro j hj _
    exact ⟨block_ratio b j hj, fun hb => block_ratio_strict b hb j hj⟩

theorem stationary_attainment_full [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) :
    (∀ r : Multiset σ, PaddingResidualGram.M r = r.card.factorial / ∏ i : σ, (r.count i).factorial) ∧
    PaddingResidualGram.z head 0 = 1 ∧
    (∀ h : ℕ, 1 ≤ h → h ≤ a.count head → PaddingResidualGram.z head (Multiset.replicate h head) = 1) ∧
    (∀ r : Multiset σ, r ≤ a → PaddingResidualGram.tailOcc head r ≠ 0 → PaddingResidualGram.z head r = 0) ∧
    Function.Bijective (fun r : PaddingTransition.Box a => (PaddingResidualGram.tailIndex a head r, r head)) ∧
    (∀ b : PaddingTransition.Tail a head,
      PaddingResidualGram.block a head b = PaddingResidualGram.L (a.count head) *
        Matrix.diagonal (fun j : Fin (a.count head + 1) => (PaddingResidualGram.delta a head b j.val : ℂ)) *
          (PaddingResidualGram.L (a.count head)).transpose ∧
      (PaddingResidualGram.block a head b).rank = (if b = 0 then 1 else a.count head + 1) ∧
      (b = 0 → PaddingResidualGram.m a head b 0 = 1 ∧ ∀ j : ℕ, PaddingResidualGram.delta a head b j = if j = 0 then 1 else 0) ∧
      (b ≠ 0 → (∀ j : Fin (a.count head + 1), 0 < PaddingResidualGram.delta a head b j.val) ∧
        (∀ j : Fin (a.count head + 1),
          PaddingResidualGram.lastTail head (PaddingResidualGram.slice a head b j.val) = PaddingResidualGram.delta a head b j.val)) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ a.count head →
        PaddingResidualGram.m a head b j / PaddingResidualGram.m a head b (j - 1) =
          ((j : ℝ) + ((PaddingResidualGram.tailWord a head b).card : ℝ)) / (j : ℝ) ∧
        (b ≠ 0 → 1 < PaddingResidualGram.m a head b j / PaddingResidualGram.m a head b (j - 1)))) ∧
    Fintype.card (PaddingTransition.K a head) = PaddingTransition.N a ∧
    (∀ r : Multiset σ, r ≤ a → ‖PaddingResidualGram.phi a head r‖ = 1) ∧
    Matrix.gram ℂ (fun r : PaddingTransition.Box a => PaddingResidualGram.phi a head (PaddingResidualGram.occ a r)) = PaddingResidualGram.G a head ∧
    (∀ r : Multiset σ, r ≤ a → inner ℂ (PaddingResidualGram.phi a head r) (PaddingResidualGram.phi a head 0) = PaddingResidualGram.z head r) ∧
    (PaddingResidualGram.G a head).PosSemidef ∧ (PaddingResidualGram.B a head).PosSemidef ∧
    PaddingResidualGram.D a * PaddingResidualGram.G a head * PaddingResidualGram.D a = PaddingResidualGram.B a head ∧
    (PaddingResidualGram.B a head) 0 0 = 1 ∧
    (PaddingResidualGram.G a head).rank = PaddingTransition.N a ∧ (PaddingResidualGram.B a head).rank = PaddingTransition.N a ∧
    (PaddingResidualGram.B a head).rank = 1 + (Fintype.card (PaddingTransition.Tail a head) - 1) * (a.count head + 1) ∧
    (∀ r s : PaddingTransition.Box a, PaddingResidualGram.occ a r ≠ 0 → PaddingResidualGram.occ a s ≠ 0 →
      (PaddingResidualGram.B a head) r s = ∑ i : σ, if 0 < (r i).val ∧ 0 < (s i).val then
        (PaddingResidualGram.B a head)
          (fun j => ⟨(r j).val - if j = i then 1 else 0,
            lt_of_le_of_lt (Nat.sub_le _ _) (r j).isLt⟩)
          (fun j => ⟨(s j).val - if j = i then 1 else 0,
            lt_of_le_of_lt (Nat.sub_le _ _) (s j).isLt⟩)
      else 0) ∧
    (∀ r s : Multiset σ, r ≤ a → s ≤ a →
      inner ℂ (PaddingResidualAction.image a head r) (PaddingResidualAction.image a head s) = inner ℂ (PaddingResidualGram.phi a head r) (PaddingResidualGram.phi a head s)) ∧
    (∀ (J : Type v) [Fintype J] (r : J → Multiset σ) (c : J → ℂ), (∀ j, r j ≤ a) →
      (∑ j : J, c j • PaddingResidualGram.phi a head (r j)) = 0 → (∑ j : J, c j • PaddingResidualAction.image a head (r j)) = 0) ∧
    (0 < a.count head → PaddingResidualGram.phi a head 0 = PaddingResidualGram.phi a head (Multiset.replicate 1 head) ∧
      Submodule.span ℂ {v : Space (PaddingTransition.K a head) |
        ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = PaddingResidualGram.phi a head r} = ⊤) ∧
    (a = 0 → PaddingTransition.N a = 1 ∧ Nonempty (Space (PaddingTransition.K a head) ≃ₗᵢ[ℂ] ℂ)) ∧
    ∃ (e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a))
      (V : Space (Fin (PaddingTransition.N a)) →ₗᵢ[ℂ] (Space σ ⊗[ℂ] Space (Fin (PaddingTransition.N a))))
      (U : Unitary (σ × Fin (PaddingTransition.N a))),
      Matrix.gram ℂ (fun r : PaddingTransition.Box a => PaddingResidualAction.phiFin a head e (PaddingResidualGram.occ a r)) = PaddingResidualGram.G a head ∧
      (0 < a.count head → PaddingResidualAction.phiFin a head e 0 = PaddingResidualAction.phiFin a head e (Multiset.replicate 1 head) ∧
        Submodule.span ℂ {v : Space (Fin (PaddingTransition.N a)) |
          ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = PaddingResidualAction.phiFin a head e r} = ⊤) ∧
      (∀ x : Space (Fin (PaddingTransition.N a)),
        V x = PaddingResidualAction.tensorCoordinates (PaddingTransition.N a) (U (PaddingResidualAction.blankEmbed (PaddingTransition.N a) head x))) ∧
      (∀ r : Multiset σ, r ≤ a → r ≠ 0 → V (PaddingResidualAction.phiFin a head e r) =
        ∑ i : σ, (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) •
          ((basis i : Space σ) ⊗ₜ[ℂ] PaddingResidualAction.phiFin a head e (r.erase i))) ∧
      V (PaddingResidualAction.phiFin a head e 0) = (basis head : Space σ) ⊗ₜ[ℂ] PaddingResidualAction.phiFin a head e 0 ∧
      ‖PaddingResidualAction.phiFin a head e a‖ = 1 ∧ ‖PaddingResidualAction.phiFin a head e 0‖ = 1 ∧
      (∀ (w : Fin a.card → σ) (k : Fin (PaddingTransition.N a)),
        circuit (fun _ => U) a.card 0 (initialized head a.card (PaddingResidualAction.phiFin a head e a)) (w, k) =
          (if occupation w = a then (Real.sqrt (PaddingResidualGram.M a : ℝ) : ℂ)⁻¹ else 0) * PaddingResidualAction.phiFin a head e 0 k) := by
  cases Subsingleton.elim (inferInstance : DecidableEq σ) (Classical.typeDecidableEq σ)
  classical
  let occupationSplit := Equiv.piSplitAt head (fun i : σ => Fin (a.count i + 1))
  let normalizedPaddingGram := Matrix.gram ℂ (fun r : PaddingTransition.Box a =>
    PaddingResidualGram.phi a head (PaddingResidualGram.occ a r))
  let lowerBox (r : PaddingTransition.Box a) (i : σ) : PaddingTransition.Box a :=
    fun j => ⟨(r j).val - if j = i then 1 else 0,
      lt_of_le_of_lt (Nat.sub_le _ _) (r j).isLt⟩
  obtain ⟨block_data, padding_gram_eq_B, gram_congruence, padding_gram_rank_eq, B_zero_zero,
    normalized_padding_zero, padding_residual_zero, normalized_padding_axis, phi_moment⟩ :=
      padding_gram_data a head
  have occ_count (r : PaddingTransition.Box a) (i : σ) :
      (PaddingResidualGram.occ a r).count i = (r i).val := by
    simp [PaddingResidualGram.occ, Multiset.count_sum', Multiset.count_replicate]
  have box_occupation_le (r : PaddingTransition.Box a) : PaddingResidualGram.occ a r ≤ a := by
    apply Multiset.le_iff_count.mpr
    intro i
    rw [occ_count]
    exact Nat.le_of_lt_succ (r i).isLt
  have stationary_bound := D5.S3.Quantum.Algebra.StationaryGramRank.stationary_gram_rank_lower_bound
    a.count (PaddingResidualGram.B a head)

  have memory_card : Fintype.card (PaddingTransition.K a head) = PaddingTransition.N a := by
    simpa only [Fintype.card_fin, PaddingTransition.N] using
      Fintype.card_congr (PaddingTransition.occupationMemoryEquiv a head hmax)
  have occupation_memory_card :
      Fintype.card (PaddingTransition.K a head) =
        (∏ i : σ, (a.count i + 1)) - a.count head := by
    simpa only [PaddingTransition.N, ← hmax] using memory_card
  have prescribed_dependencies
      (J : Type v) [Fintype J] (r : J → Multiset σ) (c : J → ℂ)
      (hr : ∀ j, r j ≤ a) (hdep : (∑ j : J, c j • PaddingResidualGram.phi a head (r j)) = 0) :
      (∑ j : J, c j • PaddingResidualAction.image a head (r j)) = 0 := by
    let E := ((EuclideanSpace.basisFun σ ℂ).tensorProduct
      (EuclideanSpace.basisFun (PaddingTransition.K a head) ℂ)).repr
    have hi (j : J) : E (PaddingResidualAction.image a head (r j)) =
        PaddingResidualAction.emitLinear a head (PaddingResidualGram.phi a head (r j)) :=
      PaddingResidualAction.image_coordinates a head hmax (r j) (hr j)
    apply E.injective
    simpa only [map_sum, map_smul, hi, map_zero] using
      congrArg (PaddingResidualAction.emitLinear a head) hdep
  have residual_linear_step
      (r : Multiset σ) (hr : r ≤ a) (hr0 : r ≠ 0) (i : σ) (k : PaddingTransition.K a head) :
      PaddingResidualAction.emitLinear a head (PaddingResidualGram.padding a head r) (i, k) =
        if i ∈ r then PaddingResidualGram.padding a head (r.erase i) k else 0 := by
    have h := PaddingResidualAction.padding_residual_intertwining a head hmax r hr hr0 i k
    exact h
  have residual_gram_recurrence (r s : Multiset σ)
      (hr : r ≤ a) (hs : s ≤ a) (hr0 : r ≠ 0) (hs0 : s ≠ 0) :
      inner ℂ (PaddingResidualGram.padding a head r) (PaddingResidualGram.padding a head s) =
        ∑ i : σ, if i ∈ r ∧ i ∈ s then
          inner ℂ (PaddingResidualGram.padding a head (r.erase i)) (PaddingResidualGram.padding a head (s.erase i))
        else 0 := by
    have h := (matrixIsometry (PaddingTransition.W a head) (PaddingTransition.W_gram a head)).inner_map_map
      (PaddingResidualGram.padding a head r) (PaddingResidualGram.padding a head s)
    change inner ℂ (PaddingResidualAction.emitLinear a head (PaddingResidualGram.padding a head r))
      (PaddingResidualAction.emitLinear a head (PaddingResidualGram.padding a head s)) = _ at h
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    change (∑ q : σ × PaddingTransition.K a head,
      PaddingResidualAction.emitLinear a head (PaddingResidualGram.padding a head s) q *
        star (PaddingResidualAction.emitLinear a head (PaddingResidualGram.padding a head r) q)) = _ at h
    rw [Fintype.sum_prod_type] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [residual_linear_step r hr hr0 i,
      residual_linear_step s hs hs0 i]
    by_cases hir : i ∈ r <;> by_cases his : i ∈ s
    · simp only [hir, his, and_self, if_true]
      rfl
    all_goals simp [hir, his]
  have lower_occ (r : PaddingTransition.Box a) (i : σ) :
      PaddingResidualGram.occ a (lowerBox r i) = (PaddingResidualGram.occ a r).erase i := by
    apply Multiset.ext.mpr
    intro j
    by_cases hji : j = i
    · subst j
      simp only [occ_count, lowerBox, if_true, Multiset.count_erase_self]
    · simp only [occ_count, lowerBox, if_neg hji, Nat.sub_zero,
        Multiset.count_erase_of_ne hji]
  have B_recurrence (r s : PaddingTransition.Box a)
      (hr : PaddingResidualGram.occ a r ≠ 0) (hs : PaddingResidualGram.occ a s ≠ 0) :
      PaddingResidualGram.B a head r s = ∑ i : σ, if 0 < (r i).val ∧ 0 < (s i).val then
        PaddingResidualGram.B a head (lowerBox r i) (lowerBox s i) else 0 := by
    simp only [← padding_gram_eq_B, Matrix.gram_apply, lower_occ]
    rw [residual_gram_recurrence _ _ (box_occupation_le r)
      (box_occupation_le s) hr hs]
    simp only [← Multiset.count_pos, occ_count]
  have padding_gram_rank :
      (PaddingResidualGram.B a head).rank = (∏ i : σ, (a.count i + 1)) - a.count head := by
    apply le_antisymm
    · rw [← occupation_memory_card, ← padding_gram_eq_B]
      rw [Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (PaddingTransition.K a head) ℂ)]
      exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_le_card_height _)
    · apply (congrArg (fun n => (∏ i : σ, (a.count i + 1)) - n) hmax).le.trans
      refine stationary_bound ?_ B_zero_zero ?_
      · rw [← padding_gram_eq_B]
        exact Matrix.posSemidef_gram _ _
      · have hn (r : PaddingTransition.Box a) (hr : r ≠ 0) : PaddingResidualGram.occ a r ≠ 0 := by
          intro he
          apply hr
          funext i
          apply Fin.ext
          have hz := congrArg (Multiset.count i) he
          simpa only [occ_count, Multiset.count_zero, Pi.zero_apply, Fin.val_zero] using hz
        intro r s hr hs
        exact B_recurrence r s (hn r hr) (hn s hs)
  have normalized_padding_gram_rank :
      (normalizedPaddingGram).rank = (∏ i : σ, (a.count i + 1)) - a.count head := by
    rw [← padding_gram_rank_eq, padding_gram_eq_B, padding_gram_rank]

  have phi_span :
      Submodule.span ℂ {v : Space (PaddingTransition.K a head) |
        ∃ r : Multiset σ, r ≤ a ∧ v = PaddingResidualGram.phi a head r} = ⊤ := by
    let S := Submodule.span ℂ {v : Space (PaddingTransition.K a head) |
      ∃ r : Multiset σ, r ≤ a ∧ v = PaddingResidualGram.phi a head r}
    let f : PaddingTransition.Box a → S := fun r =>
      ⟨PaddingResidualGram.phi a head (PaddingResidualGram.occ a r), Submodule.subset_span ⟨PaddingResidualGram.occ a r, box_occupation_le r, rfl⟩⟩
    have hg : Matrix.gram ℂ f = PaddingResidualGram.G a head := by
      rw [← PaddingResidualGram.phi_gram]
      ext r s
      exact (Submodule.coe_inner S (f r) (f s)).symm
    have hb : (Matrix.gram ℂ f).rank ≤ Module.finrank ℂ S := by
      rw [Matrix.gram_eq_conjTranspose_mul (stdOrthonormalBasis ℂ S) f]
      exact (Matrix.rank_mul_le_right _ _).trans (by
        simpa [occ_count] using Matrix.rank_le_card_height
          (Matrix.of fun i r => (stdOrthonormalBasis ℂ S).repr (f r) i))
    rw [hg, ← PaddingResidualGram.phi_gram a head, normalized_padding_gram_rank] at hb
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le S)
    rw [finrank_euclideanSpace]
    exact (occupation_memory_card).le.trans hb
  have phi_nonterminal (hh : 0 < a.count head) :
      PaddingResidualGram.phi a head 0 = PaddingResidualGram.phi a head (Multiset.replicate 1 head) ∧
        Submodule.span ℂ {v : Space (PaddingTransition.K a head) |
          ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = PaddingResidualGram.phi a head r} = ⊤ := by
    have heq : PaddingResidualGram.phi a head 0 = PaddingResidualGram.phi a head (Multiset.replicate 1 head) := by
      rw [normalized_padding_zero, normalized_padding_axis 1 hh]
    refine ⟨heq, ?_⟩
    rw [← top_le_iff, ← phi_span]
    apply Submodule.span_le.mpr
    rintro v ⟨r, hr, rfl⟩
    apply Submodule.subset_span
    by_cases hz : r = 0
    · refine ⟨Multiset.replicate 1 head, ?_, by simp [], hz ▸ heq⟩
      simpa only [Multiset.replicate_one, Multiset.singleton_le] using Multiset.count_pos.mp hh
    · exact ⟨r, hr, hz, rfl⟩
  have zero_memory : PaddingTransition.N (0 : Multiset σ) = 1 ∧
      Nonempty (Space (PaddingTransition.K (0 : Multiset σ) head) ≃ₗᵢ[ℂ] ℂ) := by
    have hn : PaddingTransition.N (0 : Multiset σ) = 1 := by simp [PaddingTransition.N, Finset.sup_const Finset.univ_nonempty]
    let e := (PaddingTransition.occupationMemoryEquiv (0 : Multiset σ) head
      (by simp [Finset.sup_const Finset.univ_nonempty])).trans (finCongr hn)
    exact ⟨hn, ⟨(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).trans
      (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm⟩⟩

  have emit_linear_sink :
      PaddingResidualAction.emitLinear a head (basis none) = basis (head, none) := by
    ext ⟨i, k⟩
    have h := congrArg (fun x : Space (σ × PaddingTransition.K a head) => x (i, k))
      (PaddingResidualAction.image_coordinates a head hmax 0 (Multiset.zero_le _))
    rw [PaddingResidualAction.image, if_pos rfl, normalized_padding_zero] at h
    simpa [OrthonormalBasis.tensorProduct_repr_tmul_apply, EuclideanSpace.basisFun_repr,
      basis_apply, Prod.mk.injEq, ite_and] using h.symm

  have memory_coordinates_apply (e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a)) (x : Space (PaddingTransition.K a head)) (k : PaddingTransition.K a head) :
      PaddingResidualAction.memoryCoordinates a head e x (e k) = x k := by
    change x (e.symm (e k)) = x k
    rw [e.symm_apply_apply]
  have memory_coordinates_eq_embedding (e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a)) (x : Space (PaddingTransition.K a head)) :
      PaddingResidualAction.memoryCoordinates a head e x = coordinateEmbedding e.toEmbedding x := by
    ext k
    change x (e.symm k) = coordinateEmbedding e.toEmbedding x k
    simpa only [Equiv.coe_toEmbedding, e.apply_symm_apply] using
      (coordinate_embedding_apply e.toEmbedding x (e.symm k)).symm
  have phiFin_eq_coordinates (e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a)) (r : Multiset σ) :
      PaddingResidualAction.phiFin a head e r = PaddingResidualAction.memoryCoordinates a head e (PaddingResidualGram.phi a head r) := by
    rw [memory_coordinates_eq_embedding]
    rfl
  have emission_coordinates_apply (e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a)) (x : Space (PaddingTransition.K a head)) (i : σ) (k : PaddingTransition.K a head) :
      PaddingResidualAction.emissionCoordinates a head e (PaddingResidualAction.memoryCoordinates a head e x) (i, e k) =
        PaddingResidualAction.emitLinear a head x (i, k) := by
    change (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.prodCongr (Equiv.refl σ) e)
      (matrixIsometry (PaddingTransition.W a head) (PaddingTransition.W_gram a head)
        ((PaddingResidualAction.memoryCoordinates a head e).symm (PaddingResidualAction.memoryCoordinates a head e x)))) (i, e k) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
    change PaddingResidualAction.emitLinear a head x (i, e.symm (e k)) = _
    rw [e.symm_apply_apply]
  have normalized_emit_step (r : Multiset σ) (hr : r ≤ a)
      (hr0 : r ≠ 0) (i : σ) (k : PaddingTransition.K a head) :
      PaddingResidualAction.emitLinear a head (PaddingResidualGram.phi a head r) (i, k) =
        (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) * PaddingResidualGram.phi a head (r.erase i) k := by
    have h := congrArg (fun x : Space (σ × PaddingTransition.K a head) => x (i, k))
      (PaddingResidualAction.image_coordinates a head hmax r hr)
    simp only [PaddingResidualAction.image, if_neg hr0, map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, OrthonormalBasis.tensorProduct_repr_tmul_apply,
      EuclideanSpace.basisFun_repr, basis_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h.symm
  have phiFin_gram (e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a)) :
      Matrix.gram ℂ (fun r : PaddingTransition.Box a => PaddingResidualAction.phiFin a head e (PaddingResidualGram.occ a r)) = PaddingResidualGram.G a head := by
    rw [← PaddingResidualGram.phi_gram]
    ext r s
    exact (coordinateEmbedding e.toEmbedding).inner_map_map _ _
  have phiFin_nonterminal (e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a)) (hh : 0 < a.count head) :
      PaddingResidualAction.phiFin a head e 0 = PaddingResidualAction.phiFin a head e (Multiset.replicate 1 head) ∧
        Submodule.span ℂ {v : Space (Fin (PaddingTransition.N a)) |
          ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = PaddingResidualAction.phiFin a head e r} = ⊤ := by
    have h := phi_nonterminal hh
    constructor
    · exact congrArg (coordinateEmbedding e.toEmbedding) h.1
    · let E := PaddingResidualAction.memoryCoordinates a head e
      let S := {v : Space (PaddingTransition.K a head) |
        ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = PaddingResidualGram.phi a head r}
      have hs : {v : Space (Fin (PaddingTransition.N a)) |
          ∃ r : Multiset σ, r ≤ a ∧ r ≠ 0 ∧ v = PaddingResidualAction.phiFin a head e r} = E '' S := by
        ext v
        simp [S, E, Set.mem_image, phiFin_eq_coordinates, eq_comm, and_assoc]
      rw [hs]
      change Submodule.span ℂ (E.toLinearEquiv.toLinearMap '' S) = ⊤
      rw [← Submodule.map_span, show Submodule.span ℂ S = ⊤ from h.2,
        Submodule.map_top, LinearMap.range_eq_top.mpr E.surjective]
  have B_rank_blocks :
      (PaddingResidualGram.B a head).rank = 1 + (Fintype.card (PaddingTransition.Tail a head) - 1) * (a.count head + 1) := by
    rw [padding_gram_rank, ← occupation_memory_card]
    change Fintype.card (PaddingTransition.K a head) = _
    have ht : Fintype.card (PaddingTransition.PositiveTail a head) = Fintype.card (PaddingTransition.Tail a head) - 1 := by
      simpa only [Fintype.card_unique] using
        Fintype.card_subtype_compl (fun b : PaddingTransition.Tail a head => b = 0)
    simp only [PaddingTransition.K, Fintype.card_option, Fintype.card_prod, Fintype.card_fin, ht]
    omega

  refine ⟨(fun r => multiplicity_eq_factorial r rfl), ?_, ?_, ?_, ?_, ?_,
    memory_card, PaddingResidualGram.phi_norm a head, PaddingResidualGram.phi_gram a head, phi_moment,
    ?_, ?_, gram_congruence, B_zero_zero, ?_, (by simpa only [PaddingTransition.N, hmax] using padding_gram_rank),
    B_rank_blocks, B_recurrence, PaddingResidualAction.prescribed_image_gram a head hmax,
    prescribed_dependencies, phi_nonterminal, ?_,
    ?_⟩
  · simp [PaddingResidualGram.z, PaddingResidualGram.tailOcc]
  · intro h _ _
    simp [PaddingResidualGram.z, PaddingResidualGram.tailOcc, Multiset.mem_replicate]
  · intro r _ hr
    exact if_neg hr
  · exact ((occupationSplit).trans (Equiv.prodComm _ _)).bijective
  · exact block_data
  · rw [← PaddingResidualGram.phi_gram]
    exact Matrix.posSemidef_gram _ _
  · rw [← padding_gram_eq_B]
    exact Matrix.posSemidef_gram _ _
  · rw [← PaddingResidualGram.phi_gram a head]
    simpa only [PaddingTransition.N, hmax] using normalized_padding_gram_rank
  · rintro rfl
    exact zero_memory

  · let e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a) := PaddingTransition.occupationMemoryEquiv a head hmax
    let E := PaddingResidualAction.memoryCoordinates a head e
    let T := PaddingResidualAction.emissionCoordinates a head e
    let V := (PaddingResidualAction.tensorCoordinates (σ := σ) (PaddingTransition.N a)).toLinearIsometry.comp T
    obtain ⟨U, hU⟩ := exists_unitary_agree (PaddingResidualAction.blankEmbed (PaddingTransition.N a) head) T
    have hcoord (x : Space (PaddingTransition.K a head)) (i : σ) (k : PaddingTransition.K a head) :
        T (E x) (i, e k) = PaddingResidualAction.emitLinear a head x (i, k) :=
      emission_coordinates_apply e x i k
    refine ⟨e, V, U, phiFin_gram e, phiFin_nonterminal e, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      change PaddingResidualAction.tensorCoordinates (PaddingTransition.N a) (T x) = PaddingResidualAction.tensorCoordinates (PaddingTransition.N a) (U (PaddingResidualAction.blankEmbed (PaddingTransition.N a) head x))
      rw [hU]
    · intro r hr hr0
      let b := (EuclideanSpace.basisFun σ ℂ).tensorProduct (EuclideanSpace.basisFun (Fin (PaddingTransition.N a)) ℂ)
      apply b.repr.injective
      change b.repr (b.repr.symm (T (PaddingResidualAction.phiFin a head e r))) = _
      rw [b.repr.apply_symm_apply, phiFin_eq_coordinates]
      ext ⟨i, k⟩
      rw [← e.apply_symm_apply k]
      rw [hcoord, normalized_emit_step r hr hr0 i (e.symm k)]
      simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        b, OrthonormalBasis.tensorProduct_repr_tmul_apply, EuclideanSpace.basisFun_repr,
        basis_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [phiFin_eq_coordinates, memory_coordinates_apply]
    · let b := (EuclideanSpace.basisFun σ ℂ).tensorProduct (EuclideanSpace.basisFun (Fin (PaddingTransition.N a)) ℂ)
      apply b.repr.injective
      change b.repr (b.repr.symm (T (PaddingResidualAction.phiFin a head e 0))) = _
      rw [b.repr.apply_symm_apply, phiFin_eq_coordinates]
      ext ⟨i, k⟩
      rw [← e.apply_symm_apply k]
      rw [hcoord, normalized_padding_zero, emit_linear_sink]
      simp only [b, OrthonormalBasis.tensorProduct_repr_tmul_apply,
        EuclideanSpace.basisFun_repr, memory_coordinates_apply,
        basis_apply, Prod.mk.injEq, ite_and, ite_mul, one_mul, zero_mul]
      split_ifs <;> rfl
    · rw [phiFin_eq_coordinates, LinearIsometryEquiv.norm_map]
      exact PaddingResidualGram.phi_norm a head a le_rfl
    · rw [phiFin_eq_coordinates, LinearIsometryEquiv.norm_map]
      exact PaddingResidualGram.phi_norm a head 0 (Multiset.zero_le _)
    · let R : Multiset σ → Space (Fin (PaddingTransition.N a)) := fun r => E (PaddingResidualGram.padding a head r)
      have hz : R 0 = PaddingResidualAction.phiFin a head e 0 := by
        rw [phiFin_eq_coordinates, normalized_padding_zero]
        change E (PaddingResidualGram.padding a head 0) = E (basis none)
        rw [padding_residual_zero]
      have hstep (r : Multiset σ) (hr : r ≤ a) (hr0 : r ≠ 0) (i : σ) (k : Fin (PaddingTransition.N a)) :
          U (blankMemory head (R r)) (i, k) = if i ∈ r then R (r.erase i) k else 0 := by
        change U (PaddingResidualAction.blankEmbed (PaddingTransition.N a) head (R r)) (i, k) = _
        rw [hU]
        rw [← e.apply_symm_apply k, hcoord]
        change (PaddingTransition.W a head).mulVec (fun s => PaddingResidualGram.padding a head r s) (i, e.symm k) = _
        rw [PaddingResidualAction.padding_residual_intertwining a head hmax r hr hr0 i (e.symm k)]
        by_cases hi : i ∈ r
        · rw [if_pos hi, if_pos hi]
          exact (memory_coordinates_apply e (PaddingResidualGram.padding a head (r.erase i)) (e.symm k)).symm
        · simp only [if_neg hi]
      have hx : (Real.sqrt (multiplicity a.card a : ℝ) : ℂ)⁻¹ • R a = PaddingResidualAction.phiFin a head e a := by
        rw [phiFin_eq_coordinates, PaddingResidualGram.phi, map_smul]
        rfl
      intro w k
      rw [← hx]
      simp only [map_smul]
      change (Real.sqrt (multiplicity a.card a : ℝ) : ℂ)⁻¹ *
        circuit (fun _ => U) a.card 0 (initialized head a.card (R a)) (w, k) = _
      rw [circuit_output_of_residuals head U a R (PaddingResidualAction.phiFin a head e 0)
        hz hstep a.card 0 a rfl le_rfl]
      by_cases hw : occupation w = a <;> simp [hw, PaddingResidualGram.M]

end

end D5.S3.Quantum.StationaryPreparation.StationaryOccupationAttainment

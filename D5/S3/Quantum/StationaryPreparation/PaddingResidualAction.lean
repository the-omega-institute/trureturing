/- GID: D5/S3/Quantum/StationaryPreparation/PaddingResidualAction
   generality: G
   mirror-B: D5/B/S3/Quantum/StationaryPreparation/PaddingResidualAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Residual action and prescribed image Gram. -/

import D5.S3.Quantum.StationaryPreparation.PaddingTransition
import D5.S3.Quantum.StationaryPreparation.PaddingResidualGram
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators TensorProduct ComplexOrder

namespace D5.S3.Quantum.StationaryPreparation.PaddingResidualAction

open D5.S1.Ledger.BoundedTimeSlice
open D5.S3.Quantum.Entanglement.OccupancyWordSectors
open D5.S3.Quantum.Entanglement.SequentialRegisterCircuit

universe u v w

section
variable {σ : Type u} [Fintype σ] [DecidableEq σ]

def image (a : Multiset σ) (head : σ) (r : Multiset σ) :
    Space σ ⊗[ℂ] Space (PaddingTransition.K a head) :=
  if r = 0 then (basis head : Space σ) ⊗ₜ[ℂ] PaddingResidualGram.phi a head 0
  else ∑ i : σ, (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) •
    ((basis i : Space σ) ⊗ₜ[ℂ] PaddingResidualGram.phi a head (r.erase i))

def phiFin (a : Multiset σ) (head : σ) (e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a))
    (r : Multiset σ) : Space (Fin (PaddingTransition.N a)) :=
  coordinateEmbedding e.toEmbedding (PaddingResidualGram.phi a head r)

def tensorCoordinates (n : ℕ) :
    Space (σ × Fin n) ≃ₗᵢ[ℂ] (Space σ ⊗[ℂ] Space (Fin n)) :=
  ((EuclideanSpace.basisFun σ ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin n) ℂ)).repr.symm

def blankEmbed (n : ℕ) (head : σ) : Space (Fin n) →ₗᵢ[ℂ] Space (σ × Fin n) :=
  coordinateEmbedding (blankInjection head (Function.Embedding.refl (Fin n)))

def emitLinear (a : Multiset σ) (head : σ) :
    Space (PaddingTransition.K a head) →ₗ[ℂ] Space (σ × PaddingTransition.K a head) := (PaddingTransition.W a head).toEuclideanLin

private def residualMemoryIndex (head : σ) (a b : Multiset σ) (hb : b ≤ a)
    (hr : 0 < PaddingResidualGram.tailCount head b) (h : Fin (b.count head + 1)) : PaddingTransition.K a head :=
  some (PaddingResidualGram.residualPaddingTail head a b hb hr, PaddingResidualGram.residualHeadIndex head a b hb h)

theorem padding_residual_intertwining [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) (r : Multiset σ) (hr : r ≤ a)
    (hr0 : r ≠ 0) (i : σ) (k : PaddingTransition.K a head) :
    (PaddingTransition.W a head).mulVec (fun s : PaddingTransition.K a head => PaddingResidualGram.padding a head r s) (i, k) =
      if i ∈ r then PaddingResidualGram.padding a head (r.erase i) k else 0 := by
  have tail_count_erase_head {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
      PaddingResidualGram.tailCount head (b.erase head) = PaddingResidualGram.tailCount head b := by
    apply Finset.sum_congr rfl
    intro i _
    exact Multiset.count_erase_of_ne i.property b
  have padding_residual_tail_free {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A)
      (hb : b ≤ a) (hr : PaddingResidualGram.tailCount head b = 0) : PaddingResidualGram.paddingResidual head a b = basis none := by
    simp [PaddingResidualGram.paddingResidual, hb, hr]
  have head_add_tail_count {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
      b.count head + PaddingResidualGram.tailCount head b = b.card := by
    unfold PaddingResidualGram.tailCount
    rw [← Fintype.sum_eq_add_sum_subtype_ne b.count head]
    exact Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _)
  have tail_count_zero_iff {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
      PaddingResidualGram.tailCount head b = 0 ↔ ∀ i, i ≠ head → b.count i = 0 := by
    simp only [PaddingResidualGram.tailCount, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
    constructor
    · intro h i hi
      exact h ⟨i, hi⟩
    · intro h i
      exact h i.val i.property
  have tail_free_membership {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A)
      (hr : PaddingResidualGram.tailCount head b = 0) (hb : b ≠ 0) (i : A) : i ∈ b ↔ i = head := by
    have ht := (tail_count_zero_iff head b).mp hr
    constructor
    · intro hi
      by_contra hne
      exact (Multiset.count_pos.mpr hi).ne' (ht i hne)
    · intro hi
      subst i
      have hn : b.card ≠ 0 := fun hz => hb (Multiset.card_eq_zero.mp hz)
      have hs := head_add_tail_count head b
      apply Multiset.count_pos.mp
      omega
  have emit_linear_basis {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ) (s : PaddingTransition.K a head)
      (i : σ) (k : PaddingTransition.K a head) : emitLinear a head (basis s) (i, k) = PaddingTransition.W a head (i, k) s := by
    exact matrix_isometry_basis (PaddingTransition.W a head) (PaddingTransition.W_gram a head) s (i, k)
  have W_sink {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head i : σ) (k : PaddingTransition.K a head) :
      PaddingTransition.W a head (i, k) none = if i = head ∧ k = none then 1 else 0 := by
    change (if PaddingTransition.paddingNext (a.count head) (fun j : PaddingTransition.TailAlphabet head => a.count j.val)
        none ((Equiv.optionSubtypeNe head).symm i) = k then
      (Real.sqrt (PaddingTransition.paddingProbability (a.count head)
        (fun j : PaddingTransition.TailAlphabet head => a.count j.val) none
        ((Equiv.optionSubtypeNe head).symm i)) : ℂ) else 0) = _
    by_cases hi : i = head
    · subst i
      rw [Equiv.optionSubtypeNe_symm_self]
      simp only [PaddingTransition.paddingNext, PaddingTransition.paddingProbability, Real.sqrt_one, Complex.ofReal_one,
        true_and]
      congr 1
      exact propext eq_comm
    · rw [Equiv.optionSubtypeNe_symm_of_ne hi]
      simp only [PaddingTransition.paddingNext, PaddingTransition.paddingProbability, Real.sqrt_zero, Complex.ofReal_zero,
        ite_self, hi, false_and, if_false]
  have emit_linear_sink {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ) :
      emitLinear a head (basis none) = basis (head, none) := by
    ext ⟨i, k⟩
    rw [emit_linear_basis, W_sink]
    simpa only [Prod.mk.injEq] using (basis_apply (head, none) (i, k)).symm
  have residual_linear_tail_free {σ : Type u} [Fintype σ] [DecidableEq σ] (head : σ) (a b : Multiset σ)
      (hb : b ≤ a) (hb0 : b ≠ 0) (hr : PaddingResidualGram.tailCount head b = 0) (i : σ) (k : PaddingTransition.K a head) :
      emitLinear a head (PaddingResidualGram.paddingResidual head a b) (i, k) =
        if i ∈ b then PaddingResidualGram.paddingResidual head a (b.erase i) k else 0 := by
    rw [padding_residual_tail_free head a b hb hr, emit_linear_sink]
    have hi := tail_free_membership head b hr hb0 i
    by_cases hih : i = head
    · subst i
      rw [if_pos (hi.mpr rfl), padding_residual_tail_free head a (b.erase head)
        ((Multiset.erase_le _ _).trans hb) (by rwa [tail_count_erase_head])]
      rw [basis_apply (head, none) (head, k), basis_apply none k]
      simp only [Prod.mk.injEq, true_and]
    · rw [if_neg (fun hib => hih (hi.mp hib))]
      rw [basis_apply (head, none) (i, k)]
      simp only [Prod.mk.injEq, hih, false_and, if_false]
  have head_slice_count_head {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) :
      (PaddingResidualGram.headSlice head b h).count head = h := by
    simp [PaddingResidualGram.headSlice, Multiset.count_filter]
  have residual_linear_formula {σ : Type u} [Fintype σ] [DecidableEq σ] (head : σ) (a b : Multiset σ) (hb : b ≤ a)
      (hr : 0 < PaddingResidualGram.tailCount head b) (i : σ) (k : PaddingTransition.K a head) :
      emitLinear a head (PaddingResidualGram.paddingResidual head a b) (i, k) =
        ∑ h : Fin (b.count head + 1),
          (Real.sqrt (PaddingResidualGram.lastTailMass head (PaddingResidualGram.headSlice head b h.val)) : ℂ) *
            PaddingTransition.W a head (i, k) (residualMemoryIndex head a b hb hr h) := by
    rw [PaddingResidualGram.paddingResidual, dif_pos hb, dif_pos hr]
    simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul, emit_linear_basis]
    rfl
  have decrement_same {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : TailBox c) (i : I) :
      (PaddingTransition.decrement c b i i).val = (b i).val - 1 := by simp [PaddingTransition.decrement]
  have decrement_other {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : TailBox c) (i j : I) (hji : j ≠ i) :
      PaddingTransition.decrement c b i j = b j := by simp [decrement_same, PaddingTransition.decrement, hji]
  have residual_matrix_absent {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A) (hb : b ≤ a)
      (hr : 0 < PaddingResidualGram.tailCount head b) (i : A) (hi : i ∉ b)
      (k : PaddingTransition.K a head) (h : Fin (b.count head + 1)) :
      PaddingTransition.W a head (i, k) (residualMemoryIndex head a b hb hr h) = 0 := by
    have hc : b.count i = 0 := Multiset.count_eq_zero.mpr hi
    by_cases hih : i = head
    · subst i
      have hh : h.val = 0 := by have := h.isLt; omega
      simp [head_slice_count_head, decrement_same, decrement_other, PaddingTransition.W, PaddingTransition.relabelMatrix, PaddingTransition.weightedMatrix, PaddingTransition.relabelProbability,
        residualMemoryIndex, Equiv.optionSubtypeNe_symm_self, PaddingTransition.paddingProbability,
        PaddingResidualGram.residualHeadIndex, hh, PaddingTransition.headProbability]
    · simp [head_slice_count_head, decrement_same, decrement_other, PaddingTransition.W, PaddingTransition.relabelMatrix, PaddingTransition.weightedMatrix, PaddingTransition.relabelProbability,
        residualMemoryIndex, Equiv.optionSubtypeNe_symm_of_ne hih, PaddingTransition.paddingProbability,
        PaddingResidualGram.residualPaddingTail, PaddingResidualGram.residualTail, PaddingTransition.tailProbability, hc]
  have residual_linear_absent {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A) (hb : b ≤ a)
      (hb0 : b ≠ 0) (i : A) (hi : i ∉ b) (k : PaddingTransition.K a head) :
      emitLinear a head (PaddingResidualGram.paddingResidual head a b) (i, k) = 0 := by
    by_cases hr : 0 < PaddingResidualGram.tailCount head b
    · rw [residual_linear_formula head a b hb hr]
      simp only [residual_matrix_absent head a b hb hr i hi k, mul_zero, Finset.sum_const_zero]
    · simpa only [if_neg hi] using residual_linear_tail_free head a b hb hb0 (by omega) i k
  have tail_count_erase_tail {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (i : A)
      (hi : i ≠ head) (hib : i ∈ b) :
      PaddingResidualGram.tailCount head (b.erase i) + 1 = PaddingResidualGram.tailCount head b := by
    have h1 := head_add_tail_count head b
    have h2 := head_add_tail_count head (b.erase i)
    have hc : (b.erase i).count head = b.count head :=
      Multiset.count_erase_of_ne (Ne.symm hi) b
    have hn : (b.erase i).card + 1 = b.card := by
      simpa [] using congrArg Multiset.card (Multiset.cons_erase hib)
    omega
  have erase_multiplicity_real {A : Type u} [Fintype A] [DecidableEq A] (b : Multiset A) (i : A) (hi : i ∈ b) :
      (b.card : ℝ) * (multiplicity (b.erase i).card (b.erase i) : ℝ) =
        (b.count i : ℝ) * (multiplicity b.card b : ℝ) := by
    have hn : (b.erase i).card + 1 = b.card := by
      simpa [] using congrArg Multiset.card (Multiset.cons_erase hi)
    have hm := multiplicity_erase_mul (n := (b.erase i).card) hn.symm i hi
    rw [hn] at hm
    exact_mod_cast hm
  have last_tail_mass_erase_tail {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (i : A)
      (hi : i ≠ head) (hib : i ∈ b) (hR : 2 ≤ PaddingResidualGram.tailCount head b) :
      PaddingResidualGram.lastTailMass head (b.erase i) =
        PaddingTransition.tailProbability (b.count head) (PaddingResidualGram.tailCount head b) (b.count i) * PaddingResidualGram.lastTailMass head b := by
    have hsum := head_add_tail_count head b
    have hc : (b.erase i).card + 1 = b.card := by
      simpa [] using congrArg Multiset.card (Multiset.cons_erase hib)
    have ht := tail_count_erase_tail head b i hi hib
    have hn : (0 : ℝ) < b.card := by exact_mod_cast (by omega : 0 < b.card)
    have he : (0 : ℝ) < (b.erase i).card := by
      exact_mod_cast (by omega : 0 < (b.erase i).card)
    have hr : (0 : ℝ) < PaddingResidualGram.tailCount head b := by exact_mod_cast (by omega : 0 < PaddingResidualGram.tailCount head b)
    have hcR : ((b.erase i).card : ℝ) + 1 = b.card := by exact_mod_cast hc
    have hsR : (b.count head : ℝ) + PaddingResidualGram.tailCount head b = b.card := by exact_mod_cast hsum
    have htR : (PaddingResidualGram.tailCount head (b.erase i) : ℝ) + 1 = PaddingResidualGram.tailCount head b := by exact_mod_cast ht
    have hm := erase_multiplicity_real b i hib
    unfold PaddingResidualGram.lastTailMass PaddingTransition.tailProbability
    have hd : (b.count head : ℝ) + PaddingResidualGram.tailCount head b - 1 = (b.erase i).card := by linarith
    rw [hd, show (PaddingResidualGram.tailCount head (b.erase i) : ℝ) = PaddingResidualGram.tailCount head b - 1 by linarith]
    field_simp [hn.ne', he.ne', hr.ne']
    nlinarith [congrArg (fun x : ℝ => ((PaddingResidualGram.tailCount head b : ℝ) - 1) * x) hm]
  have last_tail_tail_amplitude {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (i : A)
      (hi : i ≠ head) (hib : i ∈ b) (hR : 2 ≤ PaddingResidualGram.tailCount head b) :
      (Real.sqrt (PaddingTransition.tailProbability (b.count head) (PaddingResidualGram.tailCount head b) (b.count i)) : ℂ) *
        (Real.sqrt (PaddingResidualGram.lastTailMass head b) : ℂ) =
        (Real.sqrt (PaddingResidualGram.lastTailMass head (b.erase i)) : ℂ) := by
    have hr : (2 : ℝ) ≤ PaddingResidualGram.tailCount head b := by exact_mod_cast hR
    have hp : 0 ≤ PaddingTransition.tailProbability (b.count head) (PaddingResidualGram.tailCount head b) (b.count i) := by
      unfold PaddingTransition.tailProbability
      apply div_nonneg
      · exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
      · exact mul_nonneg (Nat.cast_nonneg _)
          (by linarith [Nat.cast_nonneg (α := ℝ) (b.count head)])
    rw [last_tail_mass_erase_tail head b i hi hib hR, Real.sqrt_mul hp, Complex.ofReal_mul]
  have head_slice_count_tail {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ)
      (i : A) (hi : i ≠ head) : (PaddingResidualGram.headSlice head b h).count i = b.count i := by
    simp [head_slice_count_head, PaddingResidualGram.headSlice, Multiset.count_filter, Multiset.count_replicate, hi, Ne.symm hi]
  have head_slice_tail_count {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) :
      PaddingResidualGram.tailCount head (PaddingResidualGram.headSlice head b h) = PaddingResidualGram.tailCount head b := by
    apply Finset.sum_congr rfl
    intro i _
    exact head_slice_count_tail head b h i.val i.property
  have head_slice_erase_tail {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ)
      (i : A) (hi : i ≠ head) :
      (PaddingResidualGram.headSlice head b h).erase i = PaddingResidualGram.headSlice head (b.erase i) h := by
    apply Multiset.ext.mpr
    intro j
    by_cases hj : j = head
    · subst j
      rw [Multiset.count_erase_of_ne (Ne.symm hi)]
      simp [head_slice_count_head]
    · by_cases hji : j = i
      · subst j
        simp [head_slice_count_head, head_slice_count_tail head _ _ i hi]
      · rw [Multiset.count_erase_of_ne hji,
          head_slice_count_tail head b h j hj,
          head_slice_count_tail head (b.erase i) h j hj,
          Multiset.count_erase_of_ne hji]
  have head_slice_tail_amplitude {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) (i : A)
      (hi : i ≠ head) (hib : i ∈ b) (hr : 2 ≤ PaddingResidualGram.tailCount head b) :
      (Real.sqrt (PaddingTransition.tailProbability h (PaddingResidualGram.tailCount head b) (b.count i)) : ℂ) *
        (Real.sqrt (PaddingResidualGram.lastTailMass head (PaddingResidualGram.headSlice head b h)) : ℂ) =
        (Real.sqrt (PaddingResidualGram.lastTailMass head (PaddingResidualGram.headSlice head (b.erase i) h)) : ℂ) := by
    have hm : i ∈ PaddingResidualGram.headSlice head b h := by
      apply Multiset.count_pos.mp
      rw [head_slice_count_tail head b h i hi]
      exact Multiset.count_pos.mpr hib
    simpa only [head_slice_count_head, head_slice_tail_count,
      head_slice_count_tail head b h i hi, head_slice_erase_tail head b h i hi] using
      last_tail_tail_amplitude head (PaddingResidualGram.headSlice head b h) i hi hm
        (by rwa [head_slice_tail_count])
  have residual_tail_erase {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A) (hb : b ≤ a)
      (i : PaddingTransition.TailAlphabet head) :
      PaddingTransition.decrement (fun j : PaddingTransition.TailAlphabet head => a.count j.val)
        (PaddingResidualGram.residualTail head a b hb) i =
        PaddingResidualGram.residualTail head a (b.erase i.val) ((Multiset.erase_le _ _).trans hb) := by
    funext j
    apply Fin.ext
    by_cases hji : j = i
    · subst j
      simp [decrement_same, decrement_other, PaddingResidualGram.residualTail]
    · have hval : j.val ≠ i.val := fun h => hji (Subtype.ext h)
      simp [decrement_same, decrement_other, decrement_other, hji, PaddingResidualGram.residualTail, Multiset.count_erase_of_ne hval]
  have residual_positive_tail_erase {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A) (hb : b ≤ a)
      (i : PaddingTransition.TailAlphabet head) (hi : i.val ∈ b) (hr : 2 ≤ PaddingResidualGram.tailCount head b)
      (he : 0 < PaddingResidualGram.tailCount head (b.erase i.val)) :
      PaddingTransition.decrementPositive (fun j : PaddingTransition.TailAlphabet head => a.count j.val)
        (PaddingResidualGram.residualPaddingTail head a b hb (by omega)) i (Multiset.count_pos.mpr hi)
        (by exact hr) =
        PaddingResidualGram.residualPaddingTail head a (b.erase i.val) ((Multiset.erase_le _ _).trans hb) he := by
    apply Subtype.ext
    exact residual_tail_erase head a b hb i
  have residual_tail_matrix {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A) (hb : b ≤ a)
      (i : A) (hi : i ≠ head) (hib : i ∈ b)
      (hr : 2 ≤ PaddingResidualGram.tailCount head b)
      (he : 0 < PaddingResidualGram.tailCount head (b.erase i))
      (h : Fin (b.count head + 1)) (k : PaddingTransition.K a head) :
      PaddingTransition.W a head (i, k) (residualMemoryIndex head a b hb (by omega) h) =
        (Real.sqrt (PaddingTransition.tailProbability h.val (PaddingResidualGram.tailCount head b) (b.count i)) : ℂ) *
          basis ((Equiv.refl (PaddingTransition.K a head)) (some
            (PaddingResidualGram.residualPaddingTail head a (b.erase i)
              ((Multiset.erase_le _ _).trans hb) he,
             PaddingResidualGram.residualHeadIndex head a b hb h))) k := by
    have hd := residual_positive_tail_erase head a b hb ⟨i, hi⟩ hib hr he
    have hc : 0 < b.count i := Multiset.count_pos.mpr hib
    have hp : PaddingTransition.paddingProbability (a.count head)
        (fun j : PaddingTransition.TailAlphabet head => a.count j.val)
        (some (PaddingResidualGram.residualPaddingTail head a b hb (by omega),
          PaddingResidualGram.residualHeadIndex head a b hb h)) (some ⟨i, hi⟩) =
        PaddingTransition.tailProbability h.val (PaddingResidualGram.tailCount head b) (b.count i) := by
      change (if PaddingResidualGram.tailCount head b = 1 then _ else _) = _
      rw [if_neg (by omega)]
      rfl
    have hn : PaddingTransition.paddingNext (a.count head)
        (fun j : PaddingTransition.TailAlphabet head => a.count j.val)
        (some (PaddingResidualGram.residualPaddingTail head a b hb (by omega),
          PaddingResidualGram.residualHeadIndex head a b hb h)) (some ⟨i, hi⟩) =
        some (PaddingResidualGram.residualPaddingTail head a (b.erase i)
          ((Multiset.erase_le _ _).trans hb) he,
          PaddingResidualGram.residualHeadIndex head a b hb h) := by
      dsimp only [PaddingTransition.paddingNext]
      rw [dif_pos (show 0 < ((PaddingResidualGram.residualPaddingTail head a b hb (by omega)).val
          ⟨i, hi⟩).val from hc)]
      rw [dif_pos (show 1 < tailSum
          (PaddingResidualGram.residualPaddingTail head a b hb (by omega)).val from hr), hd]
    simp only [PaddingTransition.W, PaddingTransition.relabelMatrix, PaddingTransition.weightedMatrix, PaddingTransition.relabelNext,
      PaddingTransition.relabelProbability, residualMemoryIndex, Equiv.symm_apply_apply, Equiv.refl_apply, Equiv.refl_symm,
      Equiv.optionSubtypeNe_symm_of_ne hi]
    rw [hp, hn]
    simp [decrement_same, decrement_other, basis_apply, eq_comm]
  have residual_linear_tail {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A) (hb : b ≤ a)
      (i : A) (hi : i ≠ head) (hib : i ∈ b)
      (hr : 2 ≤ PaddingResidualGram.tailCount head b) (k : PaddingTransition.K a head) :
      emitLinear a head (PaddingResidualGram.paddingResidual head a b) (i, k) =
        PaddingResidualGram.paddingResidual head a (b.erase i) k := by
    have he : 0 < PaddingResidualGram.tailCount head (b.erase i) := by
      have := tail_count_erase_tail head b i hi hib
      omega
    have hbe : b.erase i ≤ a := (Multiset.erase_le _ _).trans hb
    have hh : (b.erase i).count head = b.count head :=
      Multiset.count_erase_of_ne (Ne.symm hi) b
    rw [residual_linear_formula head a b hb (by omega)]
    simp_rw [residual_tail_matrix head a b hb i hi hib hr he]
    rw [PaddingResidualGram.paddingResidual, dif_pos hbe, dif_pos he]
    simp only [WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.smul_apply, smul_eq_mul]
    have hs := head_slice_tail_amplitude head b
    simp_rw [← mul_assoc, mul_comm _ (Real.sqrt (PaddingTransition.tailProbability _ _ _) : ℂ),
      hs _ i hi hib hr]
    apply Fintype.sum_equiv (finCongr (congrArg (fun n => n + 1) hh.symm))
    intro h
    rfl
  have head_slice_erase_head_source {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) :
      PaddingResidualGram.headSlice head (b.erase head) h = PaddingResidualGram.headSlice head b h := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i; simp [head_slice_count_head]
    · rw [head_slice_count_tail head _ _ i hi, head_slice_count_tail head _ _ i hi,
        Multiset.count_erase_of_ne hi]
  have last_tail_mass_erase_head {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A)
      (hi : head ∈ b) (hR : 0 < PaddingResidualGram.tailCount head b) :
      PaddingResidualGram.lastTailMass head (b.erase head) =
        PaddingTransition.headProbability (b.count head) (PaddingResidualGram.tailCount head b) * PaddingResidualGram.lastTailMass head b := by
    have hsum := head_add_tail_count head b
    have hc : (b.erase head).card + 1 = b.card := by
      simpa [] using congrArg Multiset.card (Multiset.cons_erase hi)
    have hb : 0 < b.count head := Multiset.count_pos.mpr hi
    have hn : (0 : ℝ) < b.card := by exact_mod_cast (by omega : 0 < b.card)
    have he : (0 : ℝ) < (b.erase head).card := by
      exact_mod_cast (by omega : 0 < (b.erase head).card)
    have hcR : ((b.erase head).card : ℝ) + 1 = b.card := by exact_mod_cast hc
    have hsR : (b.count head : ℝ) + PaddingResidualGram.tailCount head b = b.card := by exact_mod_cast hsum
    have hm := erase_multiplicity_real b head hi
    unfold PaddingResidualGram.lastTailMass PaddingTransition.headProbability
    rw [tail_count_erase_head]
    have hd : (b.count head : ℝ) + PaddingResidualGram.tailCount head b - 1 = (b.erase head).card := by linarith
    rw [hd]
    field_simp [hn.ne', he.ne']
    nlinarith [congrArg (fun x : ℝ => (PaddingResidualGram.tailCount head b : ℝ) * x) hm]
  have last_tail_head_amplitude {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A)
      (hi : head ∈ b) (hR : 0 < PaddingResidualGram.tailCount head b) :
      (Real.sqrt (PaddingTransition.headProbability (b.count head) (PaddingResidualGram.tailCount head b)) : ℂ) *
        (Real.sqrt (PaddingResidualGram.lastTailMass head b) : ℂ) =
        (Real.sqrt (PaddingResidualGram.lastTailMass head (b.erase head)) : ℂ) := by
    have hr : (1 : ℝ) ≤ PaddingResidualGram.tailCount head b := by exact_mod_cast hR
    have hp : 0 ≤ PaddingTransition.headProbability (b.count head) (PaddingResidualGram.tailCount head b) := by
      unfold PaddingTransition.headProbability
      exact div_nonneg (Nat.cast_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) (b.count head)])
    rw [last_tail_mass_erase_head head b hi hR, Real.sqrt_mul hp, Complex.ofReal_mul]
  have head_slice_erase_head {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ) :
      (PaddingResidualGram.headSlice head b h).erase head = PaddingResidualGram.headSlice head b (h - 1) := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i
      simp [head_slice_count_head]
    · rw [Multiset.count_erase_of_ne hi,
        head_slice_count_tail head b h i hi, head_slice_count_tail head b (h - 1) i hi]
  have head_slice_head_amplitude {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ)
      (hh : 0 < h) (hr : 0 < PaddingResidualGram.tailCount head b) :
      (Real.sqrt (PaddingTransition.headProbability h (PaddingResidualGram.tailCount head b)) : ℂ) *
        (Real.sqrt (PaddingResidualGram.lastTailMass head (PaddingResidualGram.headSlice head b h)) : ℂ) =
        (Real.sqrt (PaddingResidualGram.lastTailMass head (PaddingResidualGram.headSlice head b (h - 1))) : ℂ) := by
    have hm : head ∈ PaddingResidualGram.headSlice head b h := by
      apply Multiset.count_pos.mp
      simpa [head_slice_count_head] using hh
    simpa only [head_slice_count_head, head_slice_tail_count, head_slice_erase_head] using
      last_tail_head_amplitude head (PaddingResidualGram.headSlice head b h) hm (by rwa [head_slice_tail_count])
  have residual_linear_head {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A) (hb : b ≤ a)
      (hr : 0 < PaddingResidualGram.tailCount head b) (hh : head ∈ b)
      (k : PaddingTransition.K a head) :
        emitLinear a head (PaddingResidualGram.paddingResidual head a b)
          (head, k) =
        PaddingResidualGram.paddingResidual head a (b.erase head) k := by
    rw [residual_linear_formula head a b hb hr]
    have hbe : b.erase head ≤ a :=
      (Multiset.erase_le _ _).trans hb
    have hre : 0 < PaddingResidualGram.tailCount head (b.erase head) := by
      simpa only [tail_count_erase_head] using hr
    rw [PaddingResidualGram.paddingResidual, dif_pos hbe, dif_pos hre]
    simp only [WithLp.ofLp_sum,
      Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    have hc : (b.erase head).count head + 1 =
        b.count head := by
      have hbc := congrArg (Multiset.count head)
        (Multiset.cons_erase hh)
      simp only [Multiset.count_cons_self] at hbc
      rw [hbc]
    rw [Fin.sum_univ_succ]
    let e : Fin (b.count head) ≃
        Fin ((b.erase head).count head + 1) := finCongr hc.symm
    have hzero : (Real.sqrt (PaddingResidualGram.lastTailMass head
        (PaddingResidualGram.headSlice head b 0)) : ℂ) *
        PaddingTransition.W a head (head, k)
          (residualMemoryIndex head a b hb hr 0) = 0 := by
      simp [head_slice_count_head, decrement_same, decrement_other, PaddingTransition.W, PaddingTransition.relabelMatrix, PaddingTransition.weightedMatrix, PaddingTransition.relabelProbability,
        PaddingTransition.paddingProbability, residualMemoryIndex,
        PaddingResidualGram.residualHeadIndex, PaddingTransition.headProbability]
    have hzero' : (Real.sqrt (PaddingResidualGram.lastTailMass head
        (PaddingResidualGram.headSlice head b (↑(0 : Fin (b.count head + 1))))) : ℂ) *
        PaddingTransition.W a head (head, k)
          (residualMemoryIndex head a b hb hr (0 : Fin (b.count head + 1))) = 0 := by
      exact hzero
    rw [hzero', zero_add]
    apply Fintype.sum_equiv e
    intro c
    have htail : PaddingResidualGram.residualPaddingTail head a b hb hr =
        PaddingResidualGram.residualPaddingTail head a (b.erase head) hbe hre := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      simp [head_slice_count_head, decrement_same, decrement_other, PaddingResidualGram.residualPaddingTail, PaddingResidualGram.residualTail, Multiset.count_erase_of_ne i.property]
    have hhead : PaddingTransition.headPredecessor
        (PaddingResidualGram.residualHeadIndex head a b hb c.succ) =
        PaddingResidualGram.residualHeadIndex head a (b.erase head) hbe (e c) := by
      apply Fin.ext
      change c.val + 1 - 1 = c.val
      exact Nat.add_sub_cancel _ _
    have hp : PaddingTransition.paddingProbability (a.count head)
        (fun j : PaddingTransition.TailAlphabet head => a.count j.val)
        (some (PaddingResidualGram.residualPaddingTail head a b hb hr,
          PaddingResidualGram.residualHeadIndex head a b hb c.succ)) none =
        PaddingTransition.headProbability c.succ.val (PaddingResidualGram.tailCount head b) := by
      change (if PaddingResidualGram.tailCount head b = 1 then _ else _) = _
      by_cases hR : PaddingResidualGram.tailCount head b = 1
      · have hidxval : (PaddingResidualGram.residualHeadIndex head a b hb c.succ).val ≠ 0 :=
          Nat.succ_ne_zero c.val
        rw [if_pos hR, if_neg hidxval]
        simp only [PaddingTransition.headProbability, hR, Nat.cast_one, add_sub_cancel_right]
        have hpos : (0 : ℝ) < (c.val : ℝ) + 1 := by positivity
        simpa only [Fin.val_succ, Nat.cast_add, Nat.cast_one] using (div_self hpos.ne').symm
      · rw [if_neg hR]
        rfl
    have hn : PaddingTransition.paddingNext (a.count head)
        (fun j : PaddingTransition.TailAlphabet head => a.count j.val)
        (some (PaddingResidualGram.residualPaddingTail head a b hb hr,
          PaddingResidualGram.residualHeadIndex head a b hb c.succ)) none =
        some (PaddingResidualGram.residualPaddingTail head a (b.erase head) hbe hre,
          PaddingResidualGram.residualHeadIndex head a (b.erase head) hbe (e c)) := by
      dsimp only [PaddingTransition.paddingNext]
      rw [htail, hhead]
    simp only [PaddingTransition.W, PaddingTransition.relabelMatrix, PaddingTransition.weightedMatrix, PaddingTransition.relabelNext,
      PaddingTransition.relabelProbability, residualMemoryIndex, Equiv.symm_apply_apply, Equiv.refl_apply, Equiv.refl_symm,
      Equiv.optionSubtypeNe_symm_self]
    rw [hp, hn]
    by_cases hmem : ((Equiv.refl (PaddingTransition.K a head)))
        (some (PaddingResidualGram.residualPaddingTail head a (b.erase head) hbe hre,
          PaddingResidualGram.residualHeadIndex head a (b.erase head) hbe (e c))) = k
    · change some _ = k at hmem
      rw [if_pos hmem]
      simp only [basis_apply, if_pos hmem.symm, mul_one]
      have ha := head_slice_head_amplitude head b c.succ.val
        (Nat.succ_pos c.val) hr
      rw [head_slice_erase_head_source head b ((e c).val)]
      have hec : (e c).val = c.val := rfl
      rw [hec]
      simpa only [Fin.val_succ, Nat.add_sub_cancel] using (mul_comm _ _).trans ha
    · change some _ ≠ k at hmem
      rw [if_neg hmem]
      simp only [basis_apply, if_neg (Ne.symm hmem), mul_zero]
  have tail_coordinate_le_sum {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : TailBox c) (i : I) :
      (b i).val ≤ tailSum b :=
    Finset.single_le_sum (f := fun j => (b j).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have sum_one_coordinate {I : Type u} [Fintype I] [DecidableEq I] (c : I → ℕ) (b : TailBox c)
      (hs : tailSum b = 1) (i : I) (hi : 0 < (b i).val) :
      ∀ j, (b j).val = if j = i then 1 else 0 := by
    have hbi : (b i).val = 1 := by have := tail_coordinate_le_sum c b i; omega
    intro j
    by_cases hji : j = i
    · subst j
      simp [hbi]
    · have hsum : (b i).val + (b j).val ≤ tailSum b := by
        have hm : ({i, j} : Finset I) ⊆ Finset.univ := Finset.subset_univ _
        have hh := Finset.sum_le_sum_of_subset_of_nonneg hm
          (fun k _ _ => Nat.zero_le ((b k).val))
        simpa [Finset.sum_pair (Ne.symm hji), tailSum] using hh
      simp only [if_neg hji]
      omega
  have last_tail_mass_singleton {A : Type u} [Fintype A] [DecidableEq A] (head i : A) (hi : i ≠ head) :
      PaddingResidualGram.lastTailMass head ({i} : Multiset A) = 1 := by
    have hs := head_add_tail_count head ({i} : Multiset A)
    have ht : PaddingResidualGram.tailCount head ({i} : Multiset A) = 1 := by simpa [hi, Ne.symm hi] using hs
    have hm : multiplicity ({i} : Multiset A).card ({i} : Multiset A) = 1 := by
      rw [multiplicity_eq_factorial _ rfl]
      have hp : (∏ z : A, (({i} : Multiset A).count z).factorial) = 1 := by
        apply Finset.prod_eq_one
        intro z _
        by_cases hz : z = i <;> simp [hz]
      simp [hp]
    unfold PaddingResidualGram.lastTailMass
    rw [ht, hm]
    simp []
  have last_tail_mass_one {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A)
      (hR : PaddingResidualGram.tailCount head b = 1) : PaddingResidualGram.lastTailMass head b = 1 := by
    induction hn : b.card using Nat.strong_induction_on generalizing b with
    | h n ih =>
      by_cases hh : head ∈ b
      · have he : (b.erase head).card < n := by
          rw [Multiset.card_erase_of_mem hh, hn]
          have : b.card ≠ 0 := by
            intro hz
            have hb := Multiset.card_eq_zero.mp hz
            simpa [hb] using hh
          exact Nat.pred_lt (by simpa [hn] using this)
        have hr : PaddingResidualGram.tailCount head (b.erase head) = 1 := by
          rw [tail_count_erase_head, hR]
        have hm := ih _ he (b.erase head) hr rfl
        have hp : PaddingTransition.headProbability (b.count head) (PaddingResidualGram.tailCount head b) = 1 := by
          have hc : (b.count head : ℝ) ≠ 0 := by
            exact_mod_cast (Multiset.count_pos.mpr hh).ne'
          simp [PaddingTransition.headProbability, hR, hc]
        rw [last_tail_mass_erase_head head b hh (by omega), hp, one_mul] at hm
        exact hm
      · have hc : b.card = 1 := by
          simpa [Multiset.count_eq_zero.mpr hh, hR] using
            (head_add_tail_count head b).symm
        obtain ⟨i, rfl⟩ := Multiset.card_eq_one.mp hc
        apply last_tail_mass_singleton
        simpa [eq_comm] using hh
  have head_slice_one_amplitude {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) (h : ℕ)
      (hr : PaddingResidualGram.tailCount head b = 1) :
      (Real.sqrt (PaddingResidualGram.lastTailMass head (PaddingResidualGram.headSlice head b h)) : ℂ) = 1 := by
    rw [last_tail_mass_one head _ (by rwa [head_slice_tail_count])]
    simp [head_slice_count_head]
  have residual_linear_one_tail {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A) (hb : b ≤ a)
      (hr : PaddingResidualGram.tailCount head b = 1) (i : A) (hib : i ∈ b)
      (hi : i ≠ head) (k : PaddingTransition.K a head) :
      emitLinear a head (PaddingResidualGram.paddingResidual head a b) (i, k) =
        PaddingResidualGram.paddingResidual head a (b.erase i) k := by
    rw [residual_linear_formula head a b hb (by omega) i k]
    simp_rw [head_slice_one_amplitude head b _ hr]
    have htail : tailSum (PaddingResidualGram.residualTail head a b hb) = 1 := by
      exact hr
    have hbi : 0 < (PaddingResidualGram.residualTail head a b hb ⟨i, hi⟩).val := by
      simpa [decrement_same, decrement_other, PaddingResidualGram.residualTail] using (Multiset.count_pos.mpr hib)
    have hcoords := sum_one_coordinate
      (fun j : PaddingTransition.TailAlphabet head => a.count j.val)
      (PaddingResidualGram.residualTail head a b hb) htail ⟨i, hi⟩ hbi
    have hcount : b.count i = 1 := by
      simpa [decrement_same, decrement_other, PaddingResidualGram.residualTail] using hcoords ⟨i, hi⟩
    have herase : PaddingResidualGram.tailCount head (b.erase i) = 0 := by
      have ht := tail_count_erase_tail head b i hi hib
      omega
    have hberase : b.erase i ≤ a := (Multiset.erase_le _ _).trans hb
    have hsum : ∑ x : Fin (b.count head + 1),
        (Real.sqrt (if x = 0 then (1 : ℝ) else 0) : ℂ) = 1 := by
      rw [Fin.sum_univ_succ]
      simp [decrement_same, decrement_other]
    rw [padding_residual_tail_free head a (b.erase i) hberase herase]
    simp [head_slice_count_head, decrement_same, decrement_other, PaddingTransition.W, PaddingTransition.relabelMatrix, PaddingTransition.weightedMatrix, PaddingTransition.relabelNext,
      PaddingTransition.relabelProbability, PaddingTransition.paddingNext, PaddingTransition.paddingProbability, residualMemoryIndex,
      PaddingResidualGram.residualPaddingTail, PaddingResidualGram.residualTail, hcount, htail, hi,
      PaddingResidualGram.residualHeadIndex, hsum]
    simp only [basis_apply, eq_comm]
  have residual_linear_step {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (r : Multiset σ) (hr : r ≤ a) (hr0 : r ≠ 0) (i : σ) (k : PaddingTransition.K a head) :
      emitLinear a head (PaddingResidualGram.paddingResidual head a r) (i, k) =
        if i ∈ r then PaddingResidualGram.paddingResidual head a (r.erase i) k else 0 := by
    by_cases ht : 0 < PaddingResidualGram.tailCount head r
    · by_cases hi : i ∈ r
      · rw [if_pos hi]
        by_cases hh : i = head
        · subst i
          exact residual_linear_head head a r hr ht hi k
        · by_cases hR : PaddingResidualGram.tailCount head r = 1
          · exact residual_linear_one_tail head a r hr hR i hi hh k
          · exact residual_linear_tail head a r hr i hh hi (by omega) k
      · rw [if_neg hi]
        exact residual_linear_absent head a r hr hr0 i hi k
    · exact residual_linear_tail_free head a r hr hr0 (by omega) i k
  have tail_filter_eq_zero {A : Type u} [Fintype A] [DecidableEq A] (head : A) (b : Multiset A) :
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
  have padding_residual_none {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A)
      (hb : b ≤ a) (hr : 0 < PaddingResidualGram.tailCount head b) : PaddingResidualGram.paddingResidual head a b none = 0 := by
    simp [head_slice_count_head, decrement_same, decrement_other, PaddingResidualGram.paddingResidual, hb, hr, WithLp.ofLp_sum, Finset.sum_apply,
      basis_apply]
  have padding_residual_coordinates {A : Type u} [Fintype A] [DecidableEq A] (head : A) (a b : Multiset A)
      (hb : b ≤ a) (hr : 0 < PaddingResidualGram.tailCount head b)
      (t : PaddingTransition.PaddingTail (fun i : PaddingTransition.TailAlphabet head => a.count i.val))
      (k : Fin (a.count head + 1)) :
      PaddingResidualGram.paddingResidual head a b (some (t, k)) =
        if t = PaddingResidualGram.residualPaddingTail head a b hb hr ∧ k.val ≤ b.count head then
          (Real.sqrt (PaddingResidualGram.lastTailMass head (PaddingResidualGram.headSlice head b k.val)) : ℂ) else 0 := by
    classical
    rw [PaddingResidualGram.paddingResidual, dif_pos hb, dif_pos hr]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
      basis_apply, Option.some.injEq, Prod.mk.injEq]
    by_cases ht : t = PaddingResidualGram.residualPaddingTail head a b hb hr
    · subst t
      by_cases hk : k.val ≤ b.count head
      · rw [if_pos ⟨rfl, hk⟩]
        let j : Fin (b.count head + 1) := ⟨k.val, Nat.lt_succ_of_le hk⟩
        rw [Finset.sum_eq_single j]
        · simp [head_slice_count_head, j, PaddingResidualGram.residualHeadIndex]
        · intro i _ hij
          have hi : k ≠ PaddingResidualGram.residualHeadIndex head a b hb i := by
            intro he
            apply hij
            exact Fin.ext (congrArg Fin.val he).symm
          simp [head_slice_count_head, hi]
        · simp [head_slice_count_head]
      · rw [if_neg (by simp [head_slice_count_head, hk])]
        apply Finset.sum_eq_zero
        intro i _
        have hi : k ≠ PaddingResidualGram.residualHeadIndex head a b hb i := by
          intro he
          have := congrArg Fin.val he
          have := i.isLt
          simp only [PaddingResidualGram.residualHeadIndex] at *
          omega
        simp [head_slice_count_head, hi]
    · simp [head_slice_count_head, ht]
  have tail_word_count_head {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (b : PaddingTransition.Tail a head) : (PaddingResidualGram.tailWord a head b).count head = 0 := by
    simp only [PaddingResidualGram.tailWord, Multiset.count_sum', Multiset.count_replicate]
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg i.property
  have tail_word_count {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (b : PaddingTransition.Tail a head) (i : PaddingTransition.TailAlphabet head) :
      (PaddingResidualGram.tailWord a head b).count i.val = (b i).val := by
    simp only [PaddingResidualGram.tailWord, Multiset.count_sum', Multiset.count_replicate, Subtype.val_inj]
    simpa only [Finset.mem_univ, if_true] using
      Finset.sum_ite_eq' Finset.univ i (fun j => (b j).val)
  have tail_word_injective {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ) :
      Function.Injective (PaddingResidualGram.tailWord a head) := by
    intro b c h
    funext i
    apply Fin.ext
    simpa only [tail_word_count] using congrArg (Multiset.count i.val) h
  have tail_word_zero {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ) :
      PaddingResidualGram.tailWord a head 0 = 0 := by
    simp [tail_word_count_head, tail_word_count, PaddingResidualGram.tailWord]
  have tail_word_ne_zero {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (b : PaddingTransition.PositiveTail a head) : PaddingResidualGram.tailWord a head b.val ≠ 0 := by
    intro h
    apply b.property
    apply tail_word_injective a head
    simpa only [tail_word_zero] using h
  have tail_word_residual {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (r : Multiset σ) (hr : r ≤ a) :
      PaddingResidualGram.tailWord a head (PaddingResidualGram.residualTail head a r hr) = PaddingResidualGram.tailOcc head r := by
    apply Multiset.ext.mpr
    intro i
    by_cases hi : i = head
    · subst i
      simp [tail_word_count_head, tail_word_count, tail_word_zero, PaddingResidualGram.tailOcc]
    · rw [show i = (⟨i, hi⟩ : PaddingTransition.TailAlphabet head).val from rfl, tail_word_count]
      simp [tail_word_count_head, tail_word_count, tail_word_zero, PaddingResidualGram.residualTail, PaddingResidualGram.tailOcc, hi]
  have tail_occ_card {σ : Type u} [Fintype σ] [DecidableEq σ] (head : σ) (r : Multiset σ) :
      (PaddingResidualGram.tailOcc head r).card = PaddingResidualGram.tailCount head r := by
    have h := head_add_tail_count head (PaddingResidualGram.tailOcc head r)
    have ht : PaddingResidualGram.tailCount head (PaddingResidualGram.tailOcc head r) = PaddingResidualGram.tailCount head r := by
      apply Finset.sum_congr rfl
      intro i _
      simp [PaddingResidualGram.tailOcc, Multiset.count_filter, i.property]
    rw [ht] at h
    simpa [PaddingResidualGram.tailOcc] using h.symm
  have last_tail_eq_mass {σ : Type u} [Fintype σ] [DecidableEq σ] (head : σ) (r : Multiset σ) :
      PaddingResidualGram.lastTail head r = PaddingResidualGram.lastTailMass head r := by
    rw [PaddingResidualGram.lastTail, tail_occ_card]
    rfl
  have slice_eq_head_slice {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (r : Multiset σ) (hr : r ≤ a) (j : ℕ) :
      PaddingResidualGram.slice a head (PaddingResidualGram.residualTail head a r hr) j = PaddingResidualGram.headSlice head r j := by
    rw [PaddingResidualGram.slice, tail_word_residual]
    rfl
  have padding_eq_residual {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ) (r : Multiset σ) :
      PaddingResidualGram.padding a head r = PaddingResidualGram.paddingResidual head a r := by
    by_cases hr : r ≤ a
    · by_cases ht : 0 < PaddingResidualGram.tailCount head r
      · have hf : PaddingResidualGram.tailOcc head r ≠ 0 := by
          intro h
          have := (tail_filter_eq_zero head r).mp h
          omega
        ext q
        cases q with
        | none => simp [tail_word_count_head, tail_word_count, tail_word_zero, PaddingResidualGram.padding, hr, hf, padding_residual_none head a r hr ht]
        | some q =>
          rcases q with ⟨b, j⟩
          rw [padding_residual_coordinates head a r hr ht]
          have he : PaddingResidualGram.tailOcc head r = PaddingResidualGram.tailWord a head b.val ↔
              b = PaddingResidualGram.residualPaddingTail head a r hr ht := by
            rw [← tail_word_residual a head r hr]
            constructor
            · intro h
              exact Subtype.ext ((tail_word_injective a head h).symm)
            · rintro rfl
              rfl
          change (if r ≤ a ∧ PaddingResidualGram.tailOcc head r = PaddingResidualGram.tailWord a head b.val ∧ j.val ≤ r.count head
            then (Real.sqrt (PaddingResidualGram.lastTail head (PaddingResidualGram.slice a head b.val j.val)) : ℂ) else 0) = _
          simp only [hr, true_and, he]
          by_cases hb : b = PaddingResidualGram.residualPaddingTail head a r hr ht
          · subst b
            simp only [true_and, PaddingResidualGram.residualPaddingTail, slice_eq_head_slice, last_tail_eq_mass]
          · simp only [hb, false_and, if_false]
      · have hz : PaddingResidualGram.tailCount head r = 0 := by omega
        have hf : PaddingResidualGram.tailOcc head r = 0 := (tail_filter_eq_zero head r).mpr hz
        rw [padding_residual_tail_free head a r hr hz]
        ext q
        cases q with
        | none => simp [tail_word_count_head, tail_word_count, tail_word_zero, PaddingResidualGram.padding, hr, hf]
        | some q =>
          rcases q with ⟨b, j⟩
          have hn := tail_word_ne_zero a head b
          simp [tail_word_count_head, tail_word_count, tail_word_zero, PaddingResidualGram.padding, hr, hf, Ne.symm hn, basis_apply]
    · ext q
      cases q <;> simp [tail_word_count_head, tail_word_count, tail_word_zero, PaddingResidualGram.padding, PaddingResidualGram.paddingResidual, hr]
  have padding_residual_intertwining_all_heads {σ : Type u} [Fintype σ] [DecidableEq σ] (a : Multiset σ) (head : σ)
      (r : Multiset σ) (hr : r ≤ a) (hr0 : r ≠ 0) (i : σ) (k : PaddingTransition.K a head) :
      (PaddingTransition.W a head).mulVec (fun s : PaddingTransition.K a head => PaddingResidualGram.padding a head r s) (i, k) =
        if i ∈ r then PaddingResidualGram.padding a head (r.erase i) k else 0 := by
    simp only [padding_eq_residual]
    exact residual_linear_step a head r hr hr0 i k

  exact padding_residual_intertwining_all_heads a head r hr hr0 i k

theorem image_coordinates [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) (r : Multiset σ) (hr : r ≤ a) :
    ((EuclideanSpace.basisFun σ ℂ).tensorProduct
      (EuclideanSpace.basisFun (PaddingTransition.K a head) ℂ)).repr (image a head r) =
        emitLinear a head (PaddingResidualGram.phi a head r) := by
  have emit_linear_basis  (s : PaddingTransition.K a head)
      (i : σ) (k : PaddingTransition.K a head) : emitLinear a head (basis s) (i, k) = PaddingTransition.W a head (i, k) s := by
    exact matrix_isometry_basis (PaddingTransition.W a head) (PaddingTransition.W_gram a head) s (i, k)
  have W_sink (i : σ) (k : PaddingTransition.K a head) :
      PaddingTransition.W a head (i, k) none = if i = head ∧ k = none then 1 else 0 := by
    change (if PaddingTransition.paddingNext (a.count head) (fun j : PaddingTransition.TailAlphabet head => a.count j.val)
        none ((Equiv.optionSubtypeNe head).symm i) = k then
      (Real.sqrt (PaddingTransition.paddingProbability (a.count head)
        (fun j : PaddingTransition.TailAlphabet head => a.count j.val) none
        ((Equiv.optionSubtypeNe head).symm i)) : ℂ) else 0) = _
    by_cases hi : i = head
    · subst i
      rw [Equiv.optionSubtypeNe_symm_self]
      simp only [PaddingTransition.paddingNext, PaddingTransition.paddingProbability, Real.sqrt_one, Complex.ofReal_one,
        true_and]
      congr 1
      exact propext eq_comm
    · rw [Equiv.optionSubtypeNe_symm_of_ne hi]
      simp only [PaddingTransition.paddingNext, PaddingTransition.paddingProbability, Real.sqrt_zero, Complex.ofReal_zero,
        ite_self, hi, false_and, if_false]
  have emit_linear_sink  :
      emitLinear a head (basis none) = basis (head, none) := by
    ext ⟨i, k⟩
    rw [emit_linear_basis, W_sink]
    simpa only [Prod.mk.injEq] using (basis_apply (head, none) (i, k)).symm
  have phi_zero  : PaddingResidualGram.phi a head 0 = basis none := by
    classical
    have hm : PaddingResidualGram.M (0 : Multiset σ) = 1 := by
      simpa [PaddingResidualGram.M] using multiplicity_eq_factorial (0 : Multiset σ) rfl
    ext k
    cases k with
    | none => simp [PaddingResidualGram.phi, PaddingResidualGram.padding,
        hm, PaddingResidualGram.tailOcc,
        basis_apply]
    | some p =>
      rcases p with ⟨b, j⟩
      by_cases hj : j = 0
      · subst j
        by_cases hb : PaddingResidualGram.tailWord a head b.val = 0
        · simp [PaddingResidualGram.phi, PaddingResidualGram.padding,
          PaddingResidualGram.tailOcc, PaddingResidualGram.slice,
          PaddingResidualGram.lastTail, hb, hm, basis_apply]
        · simp [PaddingResidualGram.phi, PaddingResidualGram.padding,
            PaddingResidualGram.tailOcc, Ne.symm hb, basis_apply]
      · have hjv : ¬ j.val ≤ 0 := fun h => hj (Fin.ext (Nat.eq_zero_of_le_zero h))
        simp [PaddingResidualGram.phi, PaddingResidualGram.padding, PaddingResidualGram.tailOcc, hj, hjv, basis_apply]
  have erase_multiplicity_real (b : Multiset σ) (i : σ) (hi : i ∈ b) :
      (b.card : ℝ) * (multiplicity (b.erase i).card (b.erase i) : ℝ) =
        (b.count i : ℝ) * (multiplicity b.card b : ℝ) := by
    have hn : (b.erase i).card + 1 = b.card := by
      simpa using congrArg Multiset.card (Multiset.cons_erase hi)
    have hm := multiplicity_erase_mul (n := (b.erase i).card) hn.symm i hi
    rw [hn] at hm
    exact_mod_cast hm
  have scale_pos  (r : Multiset σ) : 0 < PaddingResidualGram.residualScale r := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast multiplicity_pos r rfl)
  have scale_ne_zero  (r : Multiset σ) : (PaddingResidualGram.residualScale r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (scale_pos r).ne'
  have erasure_normalization  (r : Multiset σ) (i : σ) (hi : i ∈ r) :
      (Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) : ℂ) *
        (PaddingResidualGram.residualScale (r.erase i) : ℂ)⁻¹ = (PaddingResidualGram.residualScale r : ℂ)⁻¹ := by
    have hc : (0 : ℝ) < r.card := by
      have hr0 : r ≠ 0 := by
        intro h
        simpa [h] using hi
      exact_mod_cast Multiset.card_pos.mpr hr0
    have hm := erase_multiplicity_real r i hi
    have he : (PaddingResidualGram.M (r.erase i) : ℝ) = ((r.count i : ℝ) / (r.card : ℝ)) * (PaddingResidualGram.M r : ℝ) := by
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hc.ne').mpr
      simpa only [PaddingResidualGram.M, mul_comm] using hm
    have hs : PaddingResidualGram.residualScale (r.erase i) =
        Real.sqrt ((r.count i : ℝ) / (r.card : ℝ)) * PaddingResidualGram.residualScale r := by
      change Real.sqrt (PaddingResidualGram.M (r.erase i) : ℝ) = _
      rw [he, Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) hc.le)]
      rfl
    apply (mul_inv_eq_iff_eq_mul₀ (scale_ne_zero (r.erase i))).mpr
    rw [hs, Complex.ofReal_mul]
    field_simp [scale_ne_zero r]

  by_cases hz : r = 0
  · subst r
    rw [image, if_pos rfl, phi_zero, emit_linear_sink]
    ext ⟨i, k⟩
    simp only [OrthonormalBasis.tensorProduct_repr_tmul_apply,
      EuclideanSpace.basisFun_repr, basis_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  · rw [image, if_neg hz]
    ext ⟨i, k⟩
    simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      OrthonormalBasis.tensorProduct_repr_tmul_apply, EuclideanSpace.basisFun_repr,
      basis_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have hstep := padding_residual_intertwining a head hmax r hr hz i k
    simp only [PaddingResidualGram.phi, map_smul, PiLp.smul_apply, smul_eq_mul]
    change _ = (PaddingResidualGram.residualScale r : ℂ)⁻¹ *
      (PaddingTransition.W a head).mulVec (fun s => PaddingResidualGram.padding a head r s) (i, k)
    rw [hstep]
    by_cases hi : i ∈ r
    · rw [if_pos hi]
      change _ * ((PaddingResidualGram.residualScale (r.erase i) : ℂ)⁻¹ * PaddingResidualGram.padding a head (r.erase i) k) = _
      rw [← mul_assoc, erasure_normalization r i hi]
    · rw [if_neg hi, Multiset.count_eq_zero.mpr hi]
      simp

theorem prescribed_image_gram [Nonempty σ] (a : Multiset σ) (head : σ)
    (hmax : a.count head = Finset.univ.sup a.count) (r s : Multiset σ)
    (hr : r ≤ a) (hs : s ≤ a) :
    inner ℂ (image a head r) (image a head s) = inner ℂ (PaddingResidualGram.phi a head r) (PaddingResidualGram.phi a head s) := by
  let b := (EuclideanSpace.basisFun σ ℂ).tensorProduct (EuclideanSpace.basisFun (PaddingTransition.K a head) ℂ)
  rw [← b.repr.inner_map_map, image_coordinates a head hmax r hr,
    image_coordinates a head hmax s hs]
  exact (matrixIsometry (PaddingTransition.W a head) (PaddingTransition.W_gram a head)).inner_map_map _ _

def memoryCoordinates (a : Multiset σ) (head : σ) (e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a)) :
    Space (PaddingTransition.K a head) ≃ₗᵢ[ℂ] Space (Fin (PaddingTransition.N a)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

def emissionCoordinates (a : Multiset σ) (head : σ) (e : PaddingTransition.K a head ≃ Fin (PaddingTransition.N a)) :
    Space (Fin (PaddingTransition.N a)) →ₗᵢ[ℂ] Space (σ × Fin (PaddingTransition.N a)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr (Equiv.refl σ) e)).toLinearIsometry.comp
      ((matrixIsometry (PaddingTransition.W a head) (PaddingTransition.W_gram a head)).comp
        (memoryCoordinates a head e).symm.toLinearIsometry)

end

end D5.S3.Quantum.StationaryPreparation.PaddingResidualAction

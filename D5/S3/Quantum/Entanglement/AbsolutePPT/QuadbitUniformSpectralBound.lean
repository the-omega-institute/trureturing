/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.A
   digest: Three-row scalar purity bound with the natural integer optimizer. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound

open scoped BigOperators Matrix
open NonnegativeKernelCircuit NonnegativeKernelCofactor
open D5.S3.Arith.Lattices.CofactorKernel (cofactor augment kernel_cross_identity)

private def FullSupport (n m : ℕ) :=
  {S : Finset (Fin n) // S.card = m + 1}

private noncomputable def fullCof {n m : ℕ}
    (B : Matrix (Fin m) (Fin n) ℝ) (S : FullSupport n m) : Fin n → ℝ :=
  liftCof B (Function.Embedding.refl (Fin m))
    (S.val.orderEmbOfFin S.property).toEmbedding

-- The two zero-extension identities are used for both the original selection
-- and the final ordered full-row selection.
private theorem liftCof_at {n m k : ℕ}
    (B : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin k ↪ Fin m) (σ : Fin (k + 1) ↪ Fin n) (i : Fin (k + 1)) :
    liftCof B ρ σ (σ i) = cofactor (B.submatrix ρ σ) i := by
  classical
  simp [liftCof, Finset.sum_apply, Pi.single_apply, σ.injective.eq_iff]

private theorem liftCof_off {n m k : ℕ}
    (B : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin k ↪ Fin m) (σ : Fin (k + 1) ↪ Fin n)
    (j : Fin n) (hj : j ∉ Set.range σ) : liftCof B ρ σ j = 0 := by
  classical
  unfold liftCof
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hji : j ≠ σ i := fun h => hj ⟨i, h.symm⟩
  simp [hji]

-- All coordinates of x may vanish except for one; positivity of every
-- coordinate is neither assumed nor inferred.
private theorem positive_kernel_eq_oriented_cofactor {m : ℕ}
    (M : Matrix (Fin m) (Fin (m + 1)) ℝ) (x : Fin (m + 1) → ℝ)
    (hx : M *ᵥ x = 0) (hn : ∀ i, 0 ≤ x i) (hx0 : x ≠ 0)
    (hc : ∃ i, cofactor M i ≠ 0) :
    ∃ ε a : ℝ, (ε = 1 ∨ ε = -1) ∧ 0 < a ∧
      x = a • (ε • cofactor M) := by
  classical
  let H : ℝ := ∑ j, x j
  let δ : ℝ := (augment M).det
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
  have hxi : 0 < x i := lt_of_le_of_ne (hn i) hi.symm
  have hH : 0 < H := lt_of_lt_of_le hxi
    (Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i))
  have hcross (j : Fin (m + 1)) : δ * x j = H * cofactor M j :=
    kernel_cross_identity M x hx j
  obtain ⟨j, hj⟩ := hc
  have hδ : δ ≠ 0 := by
    intro hz
    have he := hcross j
    rw [hz, zero_mul] at he
    exact (mul_ne_zero hH.ne' hj) he.symm
  have hratio (j : Fin (m + 1)) : x j = H / δ * cofactor M j := by
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hδ).mpr ((mul_comm (x j) δ).trans (hcross j))
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · refine ⟨-1, H / (-δ), Or.inr rfl, div_pos hH (neg_pos.mpr hneg), ?_⟩
    funext j
    change x j = H / (-δ) * (-1 * cofactor M j)
    simpa only [div_neg, neg_mul, one_mul, mul_neg, neg_neg] using hratio j
  · refine ⟨1, H / δ, Or.inl rfl, div_pos hH hpos, ?_⟩
    funext j
    change x j = H / δ * (1 * cofactor M j)
    simpa only [one_mul] using hratio j

-- The premise is exact cofactorCandidates membership, including all original
-- row equations. An arbitrary nonnegative kernel vector is not an input here.
private theorem cofactor_candidate_ordered_full {n m : ℕ}
    (B : Matrix (Fin m) (Fin n) ℝ)
    (hspan : Submodule.span ℝ (Set.range B.col) = ⊤)
    {w : Fin n → ℝ} (hw : w ∈ cofactorCandidates B) :
    ∃ (S : FullSupport n m) (ε a : ℝ),
      (ε = 1 ∨ ε = -1) ∧ 0 < a ∧
      w = a • (ε • fullCof B S) := by
  classical
  obtain ⟨k, _hk, ρ, σ, ε, _hε, heq, hwK, hw0⟩ := hw
  let A : Matrix (Fin k) (Fin (k + 1)) ℝ := B.submatrix ρ σ
  let c : Fin (k + 1) → ℝ := cofactor A
  have hwσ (i : Fin (k + 1)) : w (σ i) = ε * c i := by
    rw [heq]
    change ε * liftCof B ρ σ (σ i) = ε * c i
    rw [liftCof_at]
  have hwout (j : Fin n) (hj : j ∉ Set.range σ) : w j = 0 := by
    rw [heq]
    change ε * liftCof B ρ σ j = 0
    rw [liftCof_off B ρ σ j hj, mul_zero]
  -- A nonzero original coordinate selects a nonzero deleted minor.
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
  have hjσ : j ∈ Set.range σ := by
    by_contra h
    exact hj (hwout j h)
  obtain ⟨p, rfl⟩ := hjσ
  have hwb : w (σ p) ≠ 0 := hj
  have hp : c p ≠ 0 := by
    intro hz
    apply hwb
    rw [hwσ p, hz, mul_zero]
  have hdet : (A.submatrix id p.succAbove).det ≠ 0 := by
    change (-1 : ℝ) ^ p.val * (A.submatrix id p.succAbove).det ≠ 0 at hp
    exact (mul_ne_zero_iff.mp hp).2
  have hminor : LinearIndependent ℝ (A.submatrix id p.succAbove).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  let τ : Fin k ↪ Fin n :=
    ⟨fun t => σ (p.succAbove t), σ.injective.comp Fin.succAbove_right_injective⟩
  let U : Set (Fin n) := Set.range τ
  let b : Fin n := σ p
  let restrictRows : (Fin m → ℝ) →ₗ[ℝ] (Fin k → ℝ) := {
    toFun := fun y r => y (ρ r)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hτ : LinearIndependent ℝ (fun t : Fin k => B.col (τ t)) := by
    apply LinearIndependent.of_comp restrictRows
    change LinearIndependent ℝ (A.submatrix id p.succAbove).col
    exact hminor
  have hU : LinearIndepOn ℝ B.col U :=
    (linearIndepOn_range_iff τ.injective B.col).mpr hτ
  have hbU : b ∉ U := by
    rintro ⟨t, ht⟩
    exact Fin.succAbove_ne p t (σ.injective ht)
  -- Restrict the ORIGINAL Bw=0 relation using the exact zero extension.
  have hsum : (∑ i : Fin (k + 1), w (σ i) • B.col (σ i)) = 0 := by
    ext r
    rw [Finset.sum_apply]
    change (∑ i : Fin (k + 1), w (σ i) * B r (σ i)) = 0
    calc
      (∑ i : Fin (k + 1), w (σ i) * B r (σ i)) =
          ∑ j : Fin n, w j * B r j := by
        apply Fintype.sum_of_injective σ σ.injective
        · intro j hj
          rw [hwout j hj, zero_mul]
        · intro i
          rfl
      _ = 0 := by simpa only [mul_comm] using hwK.2 r
  have hrelation : w b • B.col b +
      (∑ t : Fin k, w (τ t) • B.col (τ t)) = 0 := by
    rw [Fin.sum_univ_succAbove _ p] at hsum
    exact hsum
  have hrest : (∑ t : Fin k, w (τ t) • B.col (τ t)) ∈
      Submodule.span ℝ (B.col '' U) := by
    apply Submodule.sum_mem
    intro t _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨τ t, ⟨t, rfl⟩, rfl⟩
  have hbspan : B.col b ∈ Submodule.span ℝ (B.col '' U) := by
    have hmul : w b • B.col b ∈ Submodule.span ℝ (B.col '' U) := by
      rw [eq_neg_of_add_eq_zero_left hrelation]
      exact Submodule.neg_mem _ hrest
    have hinv := (Submodule.span ℝ (B.col '' U)).smul_mem (w b)⁻¹ hmul
    simpa only [smul_smul, inv_mul_cancel₀ (show w b ≠ 0 from hwb), one_smul] using hinv
  -- Extend AMONG INDICES, keeping repeated-valued columns distinct.
  obtain ⟨T, _hTuniv, hUT, hTspan, hT⟩ :=
    exists_linearIndepOn_extension hU (Set.subset_univ U)
  have hspanT : Submodule.span ℝ (B.col '' T) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hTspan ⟨j, Set.mem_univ j, rfl⟩
  have hbT : b ∉ T := by
    intro hb
    apply hT.notMem_span hb
    apply Submodule.span_mono (Set.image_mono ?_) hbspan
    intro j hj
    refine ⟨hUT hj, ?_⟩
    intro hjb
    have hjb' : j = b := Set.mem_singleton_iff.mp hjb
    exact hbU (hjb' ▸ hj)
  let : Fintype T := Fintype.ofFinite T
  have hrangeT : Set.range (fun j : T => B.col j.val) = B.col '' T := by
    ext y
    constructor
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hcardT : Fintype.card T = m := by
    calc
      Fintype.card T =
          Module.finrank ℝ (Submodule.span ℝ (Set.range (fun j : T => B.col j.val))) :=
        (finrank_span_eq_card hT).symm
      _ = m := by rw [hrangeT, hspanT]; simp
  -- Sort a support of size m+1; no permutation law for cofactors is needed.
  let C : Finset (Fin n) := insert b T.toFinset
  have hcardC : C.card = m + 1 := by
    change (insert b T.toFinset).card = m + 1
    rw [Finset.card_insert_of_notMem (by simpa using hbT), Set.toFinset_card, hcardT]
  let S : FullSupport n m := ⟨C, hcardC⟩
  let e : Fin (m + 1) ↪o Fin n := C.orderEmbOfFin hcardC
  have herange : Set.range e = (C : Set (Fin n)) :=
    Finset.range_orderEmbOfFin C hcardC
  have hσC (i : Fin (k + 1)) : σ i ∈ C := by
    by_cases hip : i = p
    · subst i
      exact Finset.mem_insert_self b T.toFinset
    · obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hip
      have hiT : σ i ∈ T := hUT ⟨t, by change σ (p.succAbove t) = σ i; rw [ht]⟩
      exact Finset.mem_insert_of_mem (by simpa using hiT)
  have hwCout (j : Fin n) (hj : j ∉ C) : w j = 0 := by
    apply hwout j
    rintro ⟨i, hi⟩
    exact hj (hi ▸ hσC i)
  have hbC : b ∈ C := Finset.mem_insert_self b T.toFinset
  have hberange : b ∈ Set.range e := by rw [herange]; exact hbC
  obtain ⟨q, hq⟩ := hberange
  let M : Matrix (Fin m) (Fin (m + 1)) ℝ := B.submatrix id e
  let x : Fin (m + 1) → ℝ := fun i => w (e i)
  -- Deleting the sorted slot of b gives an independent square full-row minor.
  have heT (i : Fin m) : e (q.succAbove i) ∈ T := by
    have hmem : e (q.succAbove i) ∈ C :=
      Finset.orderEmbOfFin_mem C hcardC (q.succAbove i)
    have hne : e (q.succAbove i) ≠ b := by
      intro h
      exact Fin.succAbove_ne q i (e.injective (h.trans hq.symm))
    have hor : e (q.succAbove i) = b ∨ e (q.succAbove i) ∈ T := by
      simpa only [C, Finset.mem_insert, Set.mem_toFinset] using hmem
    exact hor.resolve_left hne
  let f : Fin m → T := fun i => ⟨e (q.succAbove i), heT i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have heq : e (q.succAbove i) = e (q.succAbove j) :=
      congrArg (fun t : T => t.val) hij
    exact Fin.succAbove_right_injective (e.injective heq)
  have hdeleted : LinearIndependent ℝ (M.submatrix id q.succAbove).col := by
    change LinearIndependent ℝ ((fun j : T => B.col j.val) ∘ f)
    exact hT.comp f hf
  have hdeletedDet : (M.submatrix id q.succAbove).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_cols_iff_isUnit.mp hdeleted)).ne_zero
  have hcq : cofactor M q ≠ 0 := by
    change (-1 : ℝ) ^ q.val * (M.submatrix id q.succAbove).det ≠ 0
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hdeletedDet
  have hx : M *ᵥ x = 0 := by
    ext r
    change (∑ i : Fin (m + 1), B r (e i) * w (e i)) = 0
    calc
      (∑ i : Fin (m + 1), B r (e i) * w (e i)) =
          ∑ j : Fin n, B r j * w j := by
        apply Fintype.sum_of_injective e e.injective
        · intro j hj
          have hjC : j ∉ C := by intro hjC; exact hj (herange.symm ▸ hjC)
          rw [hwCout j hjC, mul_zero]
        · intro i
          rfl
      _ = 0 := hwK.2 r
  have hxn (i : Fin (m + 1)) : 0 ≤ x i := hwK.1 (e i)
  have hx0 : x ≠ 0 := by
    intro hz
    apply hwb
    have h := congrFun hz q
    change w (e q) = 0 at h
    rw [hq] at h
    exact h
  obtain ⟨η, a, hη, ha, hxpro⟩ :=
    positive_kernel_eq_oriented_cofactor M x hx hxn hx0 ⟨q, hcq⟩
  -- Extend the proportionality by zero, preserving every vanishing coordinate.
  refine ⟨S, η, a, hη, ha, ?_⟩
  funext j
  by_cases hjC : j ∈ C
  · have hjerange : j ∈ Set.range e := by rw [herange]; exact hjC
    obtain ⟨i, rfl⟩ := hjerange
    have hlift : fullCof B S (e i) = cofactor M i := by
      exact liftCof_at B (Function.Embedding.refl (Fin m)) e.toEmbedding i
    change w (e i) = a * (η * fullCof B S (e i))
    rw [hlift]
    exact congrFun hxpro i
  · have hjerange : j ∉ Set.range e := by rw [herange]; exact hjC
    have hlift : fullCof B S j = 0 :=
      liftCof_off B (Function.Embedding.refl (Fin m)) e.toEmbedding j hjerange
    change w j = a * (η * fullCof B S j)
    rw [hwCout j hjC, hlift, mul_zero, mul_zero]

#print axioms liftCof_at
#print axioms liftCof_off
#print axioms positive_kernel_eq_oriented_cofactor
#print axioms cofactor_candidate_ordered_full

open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

-- These slots, including equal columns at different slots, are never quotiented.
def A : Matrix (Fin 3) (Fin 16) ℝ :=
  ![![-1,-2,-3,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3],
    ![-1,-2,-3,-4,-5,-6,-5,-4,-3,-2,-1,0,1,2,3,4],
    ![-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2]]

private def middleColumn : Fin 3 → ℝ := ![-3,-6,-1]

-- Piecewise arithmetic makes the inverse slot map available without a search.
private def positions (N j : ℕ) (q : Fin 16) : ℕ :=
  if q.val < 5 then q.val + 1 else
  if q.val = 5 then j else N - 10 + (q.val - 6) + 1

private theorem positions_literal (N j : ℕ) (hN : 67 ≤ N) :
    positions N j = ![1,2,3,4,5,j,N-9,N-8,N-7,N-6,N-5,N-4,N-3,N-2,N-1,N] := by
  funext q
  fin_cases q <;> simp [positions] <;> omega

private theorem positions_bounds (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) :
    1 ≤ positions N j q ∧ positions N j q ≤ N := by
  have hq := q.isLt
  dsimp [positions]
  split_ifs <;> omega

private theorem positions_strict (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) : StrictMono (positions N j) := by
  intro q r hqr
  have hq := q.isLt
  have hr := r.isLt
  have hqr' : q.val < r.val := hqr
  dsimp [positions]
  split_ifs <;> omega

-- The embedding is in ORIGINAL gap indices, so its value is one below the step.
private def slot (N : ℕ) (hN : 67 ≤ N) (j : ℕ) (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    Fin 16 ↪ Fin N where
  toFun q := ⟨positions N j q - 1, by
    have := positions_bounds N j hN hj hj' q
    omega⟩
  inj' := by
    intro q r h
    have he : positions N j q - 1 = positions N j r - 1 := congrArg Fin.val h
    have hq := positions_bounds N j hN hj hj' q
    have hr := positions_bounds N j hN hj hj' r
    apply (positions_strict N j hN hj hj').injective
    omega

private theorem slot_step (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) :
    (slot N hN j hj hj' q).val + 1 = positions N j q := by
  have := positions_bounds N j hN hj hj' q
  change positions N j q - 1 + 1 = positions N j q
  omega

private theorem slot_five (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    (slot N hN j hj hj' 5).val + 1 = j := by
  simpa [positions] using slot_step N j hN hj hj' 5

private def middle (N : ℕ) : Finset (Fin N) :=
  univ.filter (fun k => 5 ≤ k.val ∧ k.val < N-10)

private theorem mem_middle {N : ℕ} (k : Fin N) :
    k ∈ middle N ↔ 5 ≤ k.val ∧ k.val < N-10 := by
  simp [middle]

private theorem slot_boundary (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) (hq : q ≠ 5) :
    slot N hN j hj hj' q ∉ middle N := by
  have hqv := q.isLt
  have hq5 : q.val ≠ 5 := by
    intro he
    apply hq
    exact Fin.ext he
  rw [mem_middle]
  change ¬ (5 ≤ positions N j q - 1 ∧ positions N j q - 1 < N-10)
  dsimp only [positions]
  split_ifs <;> omega

private theorem boundary_covered (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (k : Fin N) (hk : k ∉ middle N) :
    ∃ q : Fin 16, q ≠ 5 ∧ slot N hN j hj hj' q = k := by
  have hkN := k.isLt
  have hk' : ¬ (5 ≤ k.val ∧ k.val < N-10) := by
    simpa only [mem_middle] using hk
  by_cases hhead : k.val < 5
  · refine ⟨⟨k.val, by omega⟩, ?_, ?_⟩
    · intro he
      have he' : k.val = 5 := congrArg Fin.val he
      omega
    · apply Fin.ext
      change positions N j ⟨k.val, by omega⟩ - 1 = k.val
      simp [positions, hhead]
  · have htail : N-10 ≤ k.val := by omega
    refine ⟨⟨6 + (k.val - (N-10)), by omega⟩, ?_, ?_⟩
    · intro he
      have he' : 6 + (k.val - (N-10)) = 5 := congrArg Fin.val he
      omega
    · apply Fin.ext
      change positions N j ⟨6 + (k.val - (N-10)), by omega⟩ - 1 = k.val
      dsimp only [positions]
      split_ifs <;> omega

private def middleMass {N : ℕ} (g : Fin N → ℝ) : ℝ := ∑ k ∈ middle N, g k

private def boundaryGaps {N : ℕ} (g : Fin N → ℝ) : Fin N → ℝ :=
  fun k => if k ∈ middle N then 0 else g k

private def unitGap {N : ℕ} (k : Fin N) : Fin N → ℝ := Pi.single k 1

private def fixedGaps {N : ℕ} (g : Fin N → ℝ) (k : Fin N) : Fin N → ℝ :=
  boundaryGaps g + middleMass g • unitGap k

-- All 15 boundary entries are literally unchanged in EVERY fixed term.
private theorem fixedGaps_boundary {N : ℕ} (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) (i : Fin N) (hi : i ∉ middle N) :
    fixedGaps g k i = g i := by
  have hik : i ≠ k := by intro he; exact hi (he.symm ▸ hk)
  simp [fixedGaps, boundaryGaps, unitGap, hi, hik, Ne.symm hik]

-- Fixed coordinates do not depend on the middle position j.
private def packed {N : ℕ} (hN : 67 ≤ N) (g : Fin N → ℝ) (q : Fin 16) : ℝ :=
  if hh : q.val < 5 then g ⟨q.val, by omega⟩ else
  if q.val = 5 then middleMass g else
  g ⟨N - 10 + (q.val - 6), by have := q.isLt; omega⟩

private theorem packed_boundary (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (g : Fin N → ℝ)
    (q : Fin 16) (hq : q ≠ 5) :
    packed hN g q = g (slot N hN j hj hj' q) := by
  have hqv := q.isLt
  have hq5 : q.val ≠ 5 := by
    intro he
    apply hq
    exact Fin.ext he
  by_cases hh : q.val < 5
  · simp only [packed, dif_pos hh]
    congr 1
    apply Fin.ext
    change q.val = positions N j q - 1
    simp [positions, hh]
  · simp only [packed, dif_neg hh, if_neg hq5]
    congr 1
    apply Fin.ext
    change N - 10 + (q.val - 6) = positions N j q - 1
    simp only [positions, if_neg hh, if_neg hq5]
    omega

private theorem packed_nonneg {N : ℕ} (hN : 67 ≤ N)
    (g : Fin N → ℝ) (hg : ∀ k, 0 ≤ g k) : ∀ q, 0 ≤ packed hN g q := by
  intro q
  dsimp only [packed]
  split_ifs
  · exact hg _
  · exact sum_nonneg (fun k _ => hg k)
  · exact hg _

-- This is only a linear zero extension; the distinct slot embedding is explicit.
private def lift16 (N j : ℕ) (hN : 67 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    (Fin 16 → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun x := ∑ q, x q • unitGap (slot N hN j hj hj' q)
  map_add' x y := by simp [add_smul, sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]

private theorem lift_packed (N : ℕ) (hN : 67 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    lift16 N (k.val+1) hN (by have := (mem_middle k).mp hk; omega)
      (by have := (mem_middle k).mp hk; omega) (packed hN g) = fixedGaps g k := by
  let hj : 6 ≤ k.val+1 := by have := (mem_middle k).mp hk; omega
  let hj' : k.val+1 ≤ N-10 := by have := (mem_middle k).mp hk; omega
  let e := slot N hN (k.val+1) hj hj'
  have he5 : e 5 = k := by
    apply Fin.ext
    have := slot_five N (k.val+1) hN hj hj'
    change (e 5).val + 1 = k.val + 1 at this
    omega
  ext i
  change (∑ q : Fin 16, packed hN g q • unitGap (e q)) i = fixedGaps g k i
  rw [Finset.sum_apply]
  by_cases hi : i ∈ middle N
  · rw [Finset.sum_eq_single (5 : Fin 16)]
    · simp [fixedGaps, boundaryGaps, unitGap, packed, hi, he5]
    · intro q _ hq
      have hqi : e q ≠ i := by
        intro he
        have hb := slot_boundary N (k.val+1) hN hj hj' q hq
        exact hb (he.symm ▸ hi)
      simp [unitGap, hqi, Ne.symm hqi]
    · simp
  · obtain ⟨q, hq, heq⟩ := boundary_covered N (k.val+1) hN hj hj' i hi
    change e q = i at heq
    rw [Finset.sum_eq_single q]
    · rw [packed_boundary N (k.val+1) hN hj hj' g q hq]
      change g (e q) • unitGap (e q) i = fixedGaps g k i
      rw [heq, fixedGaps_boundary g k hk i hi]
      simp [unitGap]
    · intro r _ hr
      have hri : e r ≠ i := by
        intro he
        exact hr (e.injective (he.trans heq.symm))
      simp [unitGap, hri, Ne.symm hri]
    · simp

-- The old step synthesis generalized from Fin 9 to Fin m is the ONLY synthesis.
private abbrev fullSynth (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  synth (fun k : Fin N => k.val+1)

private theorem fullSynth_unit {N : ℕ} (k : Fin N) :
    fullSynth N (unitGap k) = step N (k.val+1) := by
  classical
  simp [fullSynth, synth, unitGap]

private theorem synth_lift (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ) :
    fullSynth N (lift16 N j hN hj hj' x) = synth (d := N) (positions N j) x := by
  change fullSynth N (∑ q, x q • unitGap (slot N hN j hj hj' q)) = _
  rw [map_sum]
  simp_rw [map_smul, fullSynth_unit, slot_step N j hN hj hj']
  rfl

-- The exact original sums, oriented bottom minus top. No selected terms dropped.
private def slackMap (N : ℕ) (hN : 67 ≤ N) : (Fin N → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun l := ![
    (∑ i : Fin 6, l ⟨N-6+i.val, by omega⟩) - ∑ i : Fin 3, l ⟨i.val, by omega⟩,
    (∑ i : Fin 10, l ⟨N-10+i.val, by omega⟩) - ∑ i : Fin 6, l ⟨i.val, by omega⟩,
    (∑ i : Fin 3, l ⟨N-3+i.val, by omega⟩) - l ⟨0, by omega⟩]
  map_add' x y := by
    ext r
    fin_cases r <;> simp [Finset.sum_add_distrib] <;> ring
  map_smul' a x := by
    ext r
    fin_cases r <;> simp [Finset.mul_sum, mul_sub] <;> ring

private theorem middle_step_slack (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    slackMap N hN (step N j) = middleColumn := by
  ext r
  fin_cases r <;>
    simp (disch := omega) [slackMap, middleColumn, step, Fin.sum_univ_succ,
      if_pos, if_neg] <;> norm_num

set_option maxHeartbeats 2000000 in
-- All sixteen slots and all three original rows are evaluated separately.
private theorem slot_step_slack (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) :
    slackMap N hN (step N (positions N j q)) = fun r => A r q := by
  rw [positions_literal N j hN]
  ext r
  fin_cases q <;> fin_cases r <;>
    simp (disch := omega) [slackMap, A, step, Fin.sum_univ_succ, if_pos, if_neg] <;>
    norm_num

private theorem slack_synth (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ) :
    slackMap N hN (synth (d := N) (positions N j) x) = A *ᵥ x := by
  change slackMap N hN (∑ q, x q • step N (positions N j q)) = _
  rw [map_sum]
  simp_rw [map_smul, slot_step_slack N j hN hj hj']
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

-- The A-image of the full Fin N gap vector is the original row-slack vector.
private def gapRows (N : ℕ) (hN : 67 ≤ N) : (Fin N → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (slackMap N hN).comp (fullSynth N)

private theorem gaps_split {N : ℕ} (g : Fin N → ℝ) :
    boundaryGaps g + ∑ k ∈ middle N, g k • unitGap k = g := by
  classical
  ext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i ∈ middle N
  · rw [Finset.sum_eq_single i]
    · simp [boundaryGaps, unitGap, hi]
    · intro k _ hki
      simp [unitGap, hki, Ne.symm hki]
    · exact fun h => (h hi).elim
  · have hz : (∑ k ∈ middle N, g k * unitGap k i) = 0 := by
      apply sum_eq_zero
      intro k hk
      have hki : k ≠ i := by intro he; exact hi (he ▸ hk)
      simp [unitGap, hki, Ne.symm hki]
    simp [boundaryGaps, hi, hz]

private theorem gapRows_fixed (N : ℕ) (hN : 67 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    gapRows N hN (fixedGaps g k) = gapRows N hN g := by
  have hu (i : Fin N) (hi : i ∈ middle N) :
      gapRows N hN (unitGap i) = middleColumn := by
    change slackMap N hN (fullSynth N (unitGap i)) = _
    rw [fullSynth_unit]
    exact middle_step_slack N (i.val+1) hN
      (by have := (mem_middle i).mp hi; omega)
      (by have := (mem_middle i).mp hi; omega)
  have hsum : middleMass g • middleColumn =
      ∑ i ∈ middle N, g i • gapRows N hN (unitGap i) := by
    rw [middleMass, Finset.sum_smul]
    apply sum_congr rfl
    intro i hi
    rw [hu i hi]
  calc
    gapRows N hN (fixedGaps g k) =
        gapRows N hN (boundaryGaps g) + middleMass g • middleColumn := by
      simp only [fixedGaps, map_add, map_smul, hu k hk]
    _ = gapRows N hN (boundaryGaps g + ∑ i ∈ middle N, g i • unitGap i) := by
      rw [map_add, map_sum]
      simp_rw [map_smul]
      rw [hsum]
    _ = gapRows N hN g := by rw [gaps_split g]

private theorem packed_image (N : ℕ) (hN : 67 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    A *ᵥ packed hN g = gapRows N hN g := by
  have hj : 6 ≤ k.val+1 := by have := (mem_middle k).mp hk; omega
  have hj' : k.val+1 ≤ N-10 := by have := (mem_middle k).mp hk; omega
  rw [← slack_synth N (k.val+1) hN hj hj', ← synth_lift N (k.val+1) hN hj hj']
  rw [lift_packed N hN g k hk]
  exact gapRows_fixed N hN g k hk

-- This expression is an equality of FULL original gaps, not just row images.
private theorem middle_barycentric {N : ℕ} (g : Fin N → ℝ)
    (hM : middleMass g ≠ 0) :
    (∑ k ∈ middle N, (g k / middleMass g) • fixedGaps g k) = g := by
  simp only [fixedGaps, smul_add, smul_smul, sum_add_distrib]
  rw [← sum_smul, ← sum_div]
  change (middleMass g / middleMass g) • boundaryGaps g +
    (∑ k ∈ middle N, (g k / middleMass g * middleMass g) • unitGap k) = g
  simp only [div_self hM, one_smul, div_mul_cancel₀ _ hM]
  exact gaps_split g

-- The fixed-cone fact is the remaining mathematical dependency, to be proved
-- by the cofactor and scalar estimates inside the substantive scalar proof.
private theorem norm_from_fixed_cones (N : ℕ) (hN : 67 ≤ N) (c : ℝ)
    (fixedGood : ∀ (j : ℕ), 6 ≤ j → j ≤ N-10 →
      ∀ x : Fin 16 → ℝ, (∀ q, 0 ≤ x q) → (∀ r, 0 ≤ (A *ᵥ x) r) →
        spectralGood c (synth (d := N) (positions N j) x))
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hrows : ∀ r, 0 ≤ slackMap N hN l r) : spectralGood c l := by
  let g := spectralGap l
  have hg : ∀ k, 0 ≤ g k := spectralGap_nonneg l ho hn
  have hrecon : fullSynth N g = l := gap_reconstruct l
  have hmass : 0 ≤ middleMass g := sum_nonneg (fun k _ => hg k)
  have hpacked : ∀ q, 0 ≤ packed hN g q := packed_nonneg hN g hg
  have hfixed (k : Fin N) (hk : k ∈ middle N) :
      spectralGood c (fullSynth N (fixedGaps g k)) := by
    have hj : 6 ≤ k.val+1 := by have := (mem_middle k).mp hk; omega
    have hj' : k.val+1 ≤ N-10 := by have := (mem_middle k).mp hk; omega
    rw [← lift_packed N hN g k hk, synth_lift N (k.val+1) hN hj hj']
    apply fixedGood (k.val+1) hj hj' (packed hN g) hpacked
    intro r
    rw [packed_image N hN g k hk]
    change 0 ≤ slackMap N hN (fullSynth N g) r
    simpa only [hrecon] using hrows r
  by_cases hM : middleMass g = 0
  · -- Boundary-only branch, no division: every middle gap is actually zero.
    have hz : ∀ k ∈ middle N, g k = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun k _ => hg k)).mp hM
    have hb : boundaryGaps g = g := by
      ext k
      by_cases hk : k ∈ middle N
      · simp [boundaryGaps, hk, hz k hk]
      · simp [boundaryGaps, hk]
    let k : Fin N := ⟨5, by omega⟩
    have hk : k ∈ middle N := by simp [middle, k]; omega
    have hf := hfixed k hk
    have he : fixedGaps g k = g := by simp [fixedGaps, hM, hb]
    rwa [he, hrecon] at hf
  · -- Positive branch: weights g_k/M ≥ 0, sum=1, boundaries unchanged.
    have hgood : spectralGood c
        (fullSynth N (∑ k ∈ middle N, (g k / middleMass g) • fixedGaps g k)) := by
      rw [map_sum]
      apply sum_mem_of_closed (spectralGood c) (spectralGood_zero N c)
        (fun x y hx hy => spectralGood_add c x y hx hy)
      intro k hk
      rw [map_smul]
      exact spectralGood_smul c _ _ (div_nonneg (hg k) hmass) (hfixed k hk)
    rwa [middle_barycentric g hM, hrecon] at hgood

-- The exact scalar target uses the natural integer optimizer.
private def target (N : ℕ) : ℝ :=
  let t : ℕ := (3*N+4)/8
  (9*(N : ℝ)+16*(t : ℝ))/(3*(N : ℝ)+2*(t : ℝ))^2

private theorem target_nonneg (N : ℕ) : 0 ≤ target N := by
  dsimp [target]
  positivity


#print axioms positions_strict
#print axioms lift_packed
#print axioms slack_synth
#print axioms gapRows_fixed
#print axioms middle_barycentric
#print axioms norm_from_fixed_cones
#print axioms target_nonneg

end

end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open Finset Matrix

private def bulkIndex (N : ℕ) : ℕ := (3 * N + 4) / 8
private def bulkValue (N j : ℝ) : ℝ := (9*N + 16*j) / (3*N + 2*j)^2
private def boundaryEnvelope (N : ℝ) : ℝ := (N+11)/(N+3)^2
private def middleEnvelope₁ (N : ℝ) : ℝ := 25/(24*(N-1))
private def middleEnvelope₂ (N : ℝ) : ℝ := 36/(35*N-80)
private def commonEnvelope (N : ℝ) : ℝ := 16*(15*N-8)/(15*N-4)^2

private lemma scalar_denominators (N : ℝ) (hN : 67 ≤ N) :
    0 < N+3 ∧ 0 < 24*(N-1) ∧ 0 < 35*N-80 ∧ 0 < 15*N-4 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private lemma bulk_denominator (N j : ℝ) (hN : 67 ≤ N) (hj : 0 ≤ j) :
    0 < 3*N+2*j := by linarith

private lemma bulk_index_bounds (N : ℕ) (hN : 67 ≤ N) :
    6 ≤ bulkIndex N ∧ bulkIndex N ≤ N-10 ∧
      3*N ≤ 8*bulkIndex N+3 ∧ 8*bulkIndex N ≤ 3*N+4 := by
  dsimp [bulkIndex]
  omega

private lemma bulk_rounding_bounds (N : ℕ) (hN : 67 ≤ N) :
    -4 ≤ 3*(N : ℝ)-8*(bulkIndex N : ℝ) ∧
      3*(N : ℝ)-8*(bulkIndex N : ℝ) ≤ 3 := by
  obtain ⟨_, _, hl, hu⟩ := bulk_index_bounds N hN
  have hlR : 3*(N : ℝ) ≤ 8*(bulkIndex N : ℝ)+3 := by exact_mod_cast hl
  have huR : 8*(bulkIndex N : ℝ) ≤ 3*(N : ℝ)+4 := by exact_mod_cast hu
  constructor <;> linarith

/- The next certificate is the THREE shifted quadratic coefficients, with no
   division by u: this also covers the rays attaining H_N exactly. -/
private def boundaryCertificate (u c C : ℝ) : Prop :=
  0 ≤ 2*u*c+5*u^2-C ∧
  0 ≤ 134*(2*u*c+5*u^2-C)+(c^2+22*u*c-9*u^2-6*C) ∧
  0 ≤ 4489*(2*u*c+5*u^2-C)+67*(c^2+22*u*c-9*u^2-6*C)+(11*c^2-9*C)

private lemma boundary_ray_bound (N u c C : ℝ) (hN : 67 ≤ N)
    (hM : 0 < u*N+c) (hc : boundaryCertificate u c C) :
    (u^2*N+C)/(u*N+c)^2 ≤ boundaryEnvelope N := by
  obtain ⟨h2, h1, h0⟩ := hc
  have hx : 0 ≤ N-67 := sub_nonneg.mpr hN
  have hp : 0 ≤ (N+11)*(u*N+c)^2-(u^2*N+C)*(N+3)^2 := by
    calc
      _ = (2*u*c+5*u^2-C)*(N-67)^2 +
          (134*(2*u*c+5*u^2-C)+(c^2+22*u*c-9*u^2-6*C))*(N-67) +
          (4489*(2*u*c+5*u^2-C)+67*(c^2+22*u*c-9*u^2-6*C)+(11*c^2-9*C)) := by ring
      _ ≥ 0 := add_nonneg (add_nonneg (mul_nonneg h2 (sq_nonneg _))
        (mul_nonneg h1 hx)) h0
  exact (div_le_div_iff₀ (sq_pos_of_pos hM)
    (sq_pos_of_pos (scalar_denominators N hN).1)).2 (sub_nonneg.mp hp)

/- For k/(a*N+b), the only ray-specific envelope witnesses are the slope
   and value at N=67. For E1 use (k,a,b)=(25,24,-24); for E2=(36,35,-80). -/
private def middleCertificate (k a b u v c C : ℝ) : Prop :=
  0 ≤ 4*k*u*(u+v)-a*(2*u+v)^2 ∧
  0 ≤ 4*k*(67*u*(u+v)+(2*u+v)*c-C)-(67*a+b)*(2*u+v)^2

private lemma middle_ray_envelope (N j k a b u v c C : ℝ) (hN : 67 ≤ N)
    (hk : 0 < k) (hD : 0 < a*N+b) (hh : 0 < 2*u+v)
    (hM : 0 < u*N+v*j+c) (hc : middleCertificate k a b u v c C) :
    (u^2*N+(v^2+2*u*v)*j+C)/(u*N+v*j+c)^2 ≤ k/(a*N+b) := by
  let h := 2*u+v
  let S := u*N+v*j+c
  let Q := u^2*N+(v^2+2*u*v)*j+C
  let K := u*(u+v)*N+h*c-C
  obtain ⟨hα, hβ⟩ := hc
  have hx : 0 ≤ N-67 := sub_nonneg.mpr hN
  have hline : 0 ≤ 4*k*K-(a*N+b)*h^2 := by
    calc
      _ = (4*k*u*(u+v)-a*(2*u+v)^2)*(N-67) +
          (4*k*(67*u*(u+v)+(2*u+v)*c-C)-(67*a+b)*(2*u+v)^2) := by dsimp [K,h]; ring
      _ ≥ 0 := add_nonneg (mul_nonneg hα hx) hβ
  have hh2 : 0 < h^2 := sq_pos_of_pos hh
  have hK : 0 < K := by
    have hpos := mul_pos hD hh2
    have hkK : 0 < 4*k*K := lt_of_lt_of_le hpos (sub_nonneg.mp hline)
    by_contra hnot
    have hnon : 4*k*K ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (by positivity) (le_of_not_gt hnot)
    linarith
  have hQ : Q = h*S-K := by dsimp [Q,h,S,K]; ring
  have hsquare : Q/S^2 ≤ h^2/(4*K) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hM) (by positivity : 0 < 4*K)).2
    rw [hQ]
    nlinarith only [sq_nonneg (h*S-2*K)]
  have hinverse : h^2/(4*K) ≤ k/(a*N+b) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*K) hD).2
    nlinarith only [hline]
  exact hsquare.trans hinverse

private lemma boundary_envelope_le_common (N : ℝ) (hN : 67 ≤ N) :
    boundaryEnvelope N ≤ commonEnvelope N := by
  obtain ⟨hH, _, _, hB⟩ := scalar_denominators N hN
  have hx : 0 ≤ N-67 := sub_nonneg.mpr hN
  apply (div_le_div_iff₀ (sq_pos_of_pos hH) (sq_pos_of_pos hB)).2
  apply sub_nonneg.mp
  calc
    _ = 15*(N-67)^3+1972*(N-67)^2+64939*(N-67)+8722 := by ring
    _ ≥ 0 := by positivity

private lemma middle_envelope₁_le_common (N : ℝ) (hN : 67 ≤ N) :
    middleEnvelope₁ N ≤ commonEnvelope N := by
  obtain ⟨_, hE, _, hB⟩ := scalar_denominators N hN
  have hx : 0 ≤ N-67 := sub_nonneg.mpr hN
  apply (div_le_div_iff₀ hE (sq_pos_of_pos hB)).2
  apply sub_nonneg.mp
  calc
    _ = 135*(N-67)^2+12258*(N-67)+217943 := by ring
    _ ≥ 0 := by positivity

private lemma middle_envelope₂_le_common (N : ℝ) (hN : 67 ≤ N) :
    middleEnvelope₂ N ≤ commonEnvelope N := by
  obtain ⟨_, _, hE, hB⟩ := scalar_denominators N hN
  have hx : 0 ≤ N-67 := sub_nonneg.mpr hN
  apply (div_le_div_iff₀ hE (sq_pos_of_pos hB)).2
  apply sub_nonneg.mp
  calc
    _ = 300*(N-67)^2+20840*(N-67)+59244 := by ring
    _ ≥ 0 := by positivity

private lemma common_le_bulk_of_rounding (N t : ℝ) (hN : 67 ≤ N)
    (hl : -4 ≤ 8*t-3*N) (hu : 8*t-3*N ≤ 4) :
    commonEnvelope N ≤ bulkValue N t := by
  let z := 8*t-3*N
  have hB := (scalar_denominators N hN).2.2.2
  have hD : 0 < 3*N+2*t := by linarith
  have hA : 0 ≤ 15*N-8 := by linarith
  have hleft : 0 ≤ z+4 := by dsimp [z]; linarith
  have hright : 0 ≤ (15*N-8)*(4-z)+32 :=
    add_nonneg (mul_nonneg hA (by dsimp [z]; linarith)) (by norm_num)
  apply (div_le_div_iff₀ (sq_pos_of_pos hB) (sq_pos_of_pos hD)).2
  apply sub_nonneg.mp
  calc
    _ = (z+4)*((15*N-8)*(4-z)+32) := by dsimp [z]; ring
    _ ≥ 0 := mul_nonneg hleft hright

private lemma common_le_integer_bulk (N : ℕ) (hN : 67 ≤ N) :
    commonEnvelope (N : ℝ) ≤ bulkValue (N : ℝ) (bulkIndex N : ℝ) := by
  obtain ⟨hl, hu⟩ := bulk_rounding_bounds N hN
  apply common_le_bulk_of_rounding _ _ (by exact_mod_cast hN) <;> linarith

/- Strict optimality over ALL natural j, hence over 6 <= j <= N-10.
   d=-4 is included: the left-neighbor bracket is exactly 16, so the
   half-integer continuous tie is resolved in favor of this t. -/
private lemma bulk_integer_strict (N j : ℕ) (hN : 67 ≤ N) (hne : j ≠ bulkIndex N) :
    bulkValue (N : ℝ) (j : ℝ) < bulkValue (N : ℝ) (bulkIndex N : ℝ) := by
  let n : ℝ := N
  let t : ℝ := bulkIndex N
  let d : ℝ := 3*n-8*t
  let R (x : ℝ) := 36*n^2-36*n*(t+x)-64*t*x
  have hn : 67 ≤ n := by dsimp [n]; exact_mod_cast hN
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hround : -4 ≤ d ∧ d ≤ 3 := bulk_rounding_bounds N hN
  have hcoef : 0 ≤ 36*n+64*t := by linarith
  have hleft : 0 < R (t-1) := by
    have hp : 0 ≤ (d+4)*(15*n-(d+4)) := mul_nonneg (by linarith [hround.1])
      (by linarith [hround.2])
    have he : R (t-1) = 16+(d+4)*(15*n-(d+4)) := by dsimp [R,d]; ring
    rw [he]
    linarith
  have hright : R (t+1) < 0 := by
    have hp : 0 ≤ 15*n*((4-d)-1) := mul_nonneg (by linarith) (by linarith [hround.2])
    have he : R (t+1) = 16-(4-d)^2-15*n*(4-d) := by dsimp [R,d]; ring
    rw [he]
    nlinarith only [hp, hn, sq_nonneg (4-d)]
  have hprod : 0 < (t-(j : ℝ))*R (j : ℝ) := by
    rcases lt_or_gt_of_ne hne with hj | hj
    · have hdist : (j : ℝ)+1 ≤ t := by
        dsimp [t]
        exact_mod_cast (show j+1 ≤ bulkIndex N by omega)
      have hp : 0 ≤ (36*n+64*t)*(t-1-(j : ℝ)) := mul_nonneg hcoef (by linarith)
      have he : R (j : ℝ) = R (t-1)+(36*n+64*t)*(t-1-(j : ℝ)) := by dsimp [R]; ring
      apply mul_pos (by linarith)
      rw [he]
      linarith
    · have hdist : t+1 ≤ (j : ℝ) := by
        dsimp [t]
        exact_mod_cast (show bulkIndex N+1 ≤ j by omega)
      have hp : 0 ≤ (36*n+64*t)*((j : ℝ)-(t+1)) := mul_nonneg hcoef (by linarith)
      have he : R (j : ℝ) = R (t+1)-(36*n+64*t)*((j : ℝ)-(t+1)) := by dsimp [R]; ring
      apply mul_pos_of_neg_of_neg (by linarith)
      rw [he]
      linarith
  have hjD := bulk_denominator n (j : ℝ) hn (Nat.cast_nonneg _)
  have htD := bulk_denominator n t hn ht
  apply (div_lt_div_iff₀ (sq_pos_of_pos hjD) (sq_pos_of_pos htD)).2
  apply sub_pos.mp
  calc
    _ = (t-(j : ℝ))*R (j : ℝ) := by dsimp [R]; ring
    _ > 0 := hprod

private lemma bulk_integer_maximum (N j : ℕ) (hN : 67 ≤ N) :
    bulkValue (N : ℝ) (j : ℝ) ≤ bulkValue (N : ℝ) (bulkIndex N : ℝ) := by
  by_cases hj : j = bulkIndex N
  · simp [hj]
  · exact (bulk_integer_strict N j hN hj).le

end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open Finset Matrix

private inductive RayBranch where
  | boundary | envelope₁ | envelope₂ | bulk
  deriving DecidableEq

private structure RayData where
  gap : Fin 16 → ℕ
  u : ℤ
  v : ℤ
  c : ℤ
  C : ℤ
  branch : RayBranch

/- These are exactly the coefficients of the ORIGINAL ordered positions
   (1,2,3,4,5,j,N-9,N-8,...,N). No duplicate columns are removed. -/
private def positionN : Fin 16 → ℤ := ![0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1]
private def positionJ : Fin 16 → ℤ := ![0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0]
private def positionC : Fin 16 → ℤ := ![1,2,3,4,5,0,-9,-8,-7,-6,-5,-4,-3,-2,-1,0]
private def positions₁₆ (N j : ℕ) : Fin 16 → ℕ :=
  ![1,2,3,4,5,j,N-9,N-8,N-7,N-6,N-5,N-4,N-3,N-2,N-1,N]

private def massMoment (r : RayData) (p : Fin 16 → ℤ) : ℤ :=
  ∑ i, (r.gap i : ℤ)*p i
private def squareMoment (r : RayData) (p : Fin 16 → ℤ) : ℤ :=
  ∑ i, ∑ k, (r.gap i : ℤ)*(r.gap k : ℤ)*p (min i k)

private def MomentWitness (r : RayData) : Prop :=
  massMoment r positionN = r.u ∧
  massMoment r positionJ = r.v ∧
  massMoment r positionC = r.c ∧
  squareMoment r positionN = r.u^2 ∧
  squareMoment r positionJ = r.v^2+2*r.u*r.v ∧
  squareMoment r positionC = r.C

private def branchValid (r : RayData) : Prop :=
  match r.branch with
  | .boundary => r.v = 0 ∧ boundaryCertificate (r.u : ℝ) (r.c : ℝ) (r.C : ℝ)
  | .envelope₁ => 0 < (r.v : ℝ) ∧
      middleCertificate 25 24 (-24) (r.u : ℝ) (r.v : ℝ) (r.c : ℝ) (r.C : ℝ)
  | .envelope₂ => 0 < (r.v : ℝ) ∧
      middleCertificate 36 35 (-80) (r.u : ℝ) (r.v : ℝ) (r.c : ℝ) (r.C : ℝ)
  | .bulk => r.u = 3 ∧ r.v = 2 ∧ r.c = 0 ∧ r.C = 0

private structure RayData.Valid (r : RayData) : Prop where
  u_nonneg : 0 ≤ (r.u : ℝ)
  v_nonneg : 0 ≤ (r.v : ℝ)
  mass67_pos : 0 < 67*(r.u : ℝ)+6*(r.v : ℝ)+(r.c : ℝ)
  moments : MomentWitness r
  branch_valid : branchValid r

private def rayMass (r : RayData) (N j : ℝ) : ℝ := (r.u : ℝ)*N+(r.v : ℝ)*j+(r.c : ℝ)
private def raySquare (r : RayData) (N j : ℝ) : ℝ :=
  (r.u : ℝ)^2*N+((r.v : ℝ)^2+2*(r.u : ℝ)*(r.v : ℝ))*j+(r.C : ℝ)

private lemma ray_mass_positive (r : RayData) (hr : r.Valid) (N j : ℝ)
    (hN : 67 ≤ N) (hj : 6 ≤ j) : 0 < rayMass r N j := by
  have h1 := mul_nonneg hr.u_nonneg (sub_nonneg.mpr hN)
  have h2 := mul_nonneg hr.v_nonneg (sub_nonneg.mpr hj)
  dsimp [rayMass]
  nlinarith only [h1, h2, hr.mass67_pos]

private lemma ray_nonbulk_le_common (r : RayData) (hr : r.Valid) (N j : ℝ)
    (hN : 67 ≤ N) (hj : 6 ≤ j) (hne : r.branch ≠ .bulk) :
    raySquare r N j/(rayMass r N j)^2 ≤ commonEnvelope N := by
  have hM := ray_mass_positive r hr N j hN hj
  have hc := hr.branch_valid
  cases hb : r.branch with
  | boundary =>
      simp only [branchValid, hb] at hc
      obtain ⟨hv, hcert⟩ := hc
      have hM' : 0 < (r.u : ℝ)*N+(r.c : ℝ) := by simpa [rayMass, hv] using hM
      have h := boundary_ray_bound N (r.u : ℝ) (r.c : ℝ) (r.C : ℝ) hN hM' hcert
      have h' : raySquare r N j/(rayMass r N j)^2 ≤ boundaryEnvelope N := by
        simpa [raySquare, rayMass, hv] using h
      exact h'.trans (boundary_envelope_le_common N hN)
  | envelope₁ =>
      simp only [branchValid, hb] at hc
      obtain ⟨hv, hcert⟩ := hc
      have hh : 0 < 2*(r.u : ℝ)+(r.v : ℝ) := by linarith [hr.u_nonneg]
      have hD : 0 < 24*N+(-24) := by linarith
      have h := middle_ray_envelope N j 25 24 (-24) (r.u : ℝ) (r.v : ℝ)
        (r.c : ℝ) (r.C : ℝ) hN (by norm_num) hD hh hM hcert
      have h' : raySquare r N j/(rayMass r N j)^2 ≤ middleEnvelope₁ N := by
        have hden : 24*N+(-24 : ℝ) = 24*(N-1) := by ring
        rw [hden] at h
        exact h
      exact h'.trans (middle_envelope₁_le_common N hN)
  | envelope₂ =>
      simp only [branchValid, hb] at hc
      obtain ⟨hv, hcert⟩ := hc
      have hh : 0 < 2*(r.u : ℝ)+(r.v : ℝ) := by linarith [hr.u_nonneg]
      have hD : 0 < 35*N+(-80) := by linarith
      have h := middle_ray_envelope N j 36 35 (-80) (r.u : ℝ) (r.v : ℝ)
        (r.c : ℝ) (r.C : ℝ) hN (by norm_num) hD hh hM hcert
      have h' : raySquare r N j/(rayMass r N j)^2 ≤ middleEnvelope₂ N := by
        simpa only [raySquare, rayMass, middleEnvelope₂, sub_eq_add_neg] using h
      exact h'.trans (middle_envelope₂_le_common N hN)
  | bulk => exact False.elim (hne hb)

private lemma ray_scalar_bound (r : RayData) (hr : r.Valid) (N j : ℕ)
    (hN : 67 ≤ N) (hj : 6 ≤ j) :
    raySquare r (N : ℝ) (j : ℝ) ≤
      bulkValue (N : ℝ) (bulkIndex N : ℝ)*(rayMass r (N : ℝ) (j : ℝ))^2 := by
  have hn : (67 : ℝ) ≤ N := by exact_mod_cast hN
  have hjR : (6 : ℝ) ≤ j := by exact_mod_cast hj
  have hM := ray_mass_positive r hr (N : ℝ) (j : ℝ) hn hjR
  apply (div_le_iff₀ (sq_pos_of_pos hM)).1
  by_cases hb : r.branch = .bulk
  · have hc := hr.branch_valid
    simp only [branchValid, hb] at hc
    obtain ⟨hu, hv, hc, hC⟩ := hc
    have he : raySquare r (N : ℝ) (j : ℝ)/(rayMass r (N : ℝ) (j : ℝ))^2 =
        bulkValue (N : ℝ) (j : ℝ) := by
      norm_num [raySquare, rayMass, hu, hv, hc, hC, bulkValue]
    rw [he]
    exact bulk_integer_maximum N j hN
  · exact (ray_nonbulk_le_common r hr (N : ℝ) (j : ℝ) hn hjR hb).trans
      (common_le_integer_bulk N hN)

private lemma positions₁₆_le (N j : ℕ) (hN : 67 ≤ N) (hj : j ≤ N-10) :
    ∀ i, positions₁₆ N j i ≤ N := by
  intro i
  fin_cases i <;> simp [positions₁₆] <;> omega

private lemma positions₁₆_monotone (N j : ℕ) (hN : 67 ≤ N) (hl : 6 ≤ j) (hu : j ≤ N-10) :
    Monotone (positions₁₆ N j) := by
  have he : positions N j = positions₁₆ N j := by
    rw [positions_literal N j hN]
    rfl
  rw [← he]
  exact (positions_strict N j hN hl hu).monotone

private lemma positions₁₆_cast (N j : ℕ) (hN : 67 ≤ N) (i : Fin 16) :
    (positions₁₆ N j i : ℝ) =
      (positionN i : ℝ)*(N : ℝ)+(positionJ i : ℝ)*(j : ℝ)+(positionC i : ℝ) := by
  fin_cases i <;> simp only [positions₁₆, positionN, positionJ, positionC,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  all_goals push_cast [show 9 ≤ N from by omega, show 8 ≤ N from by omega,
    show 7 ≤ N from by omega, show 6 ≤ N from by omega, show 5 ≤ N from by omega,
    show 4 ≤ N from by omega, show 3 ≤ N from by omega, show 2 ≤ N from by omega,
    show 1 ≤ N from by omega]
  all_goals ring

private lemma mass_moment_real (r : RayData) (p : Fin 16 → ℤ) (z : ℤ)
    (h : massMoment r p = z) : ∑ i, (r.gap i : ℝ)*(p i : ℝ) = (z : ℝ) := by
  dsimp [massMoment] at h
  exact_mod_cast h

private lemma square_moment_real (r : RayData) (p : Fin 16 → ℤ) (z : ℤ)
    (h : squareMoment r p = z) :
    ∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(p (min i k) : ℝ) = (z : ℝ) := by
  dsimp [squareMoment] at h
  exact_mod_cast h

private lemma ray_mass_identity (r : RayData) (hr : MomentWitness r) (N j : ℕ) (hN : 67 ≤ N) :
    (∑ i, (r.gap i : ℝ)*(positions₁₆ N j i : ℝ)) = rayMass r (N : ℝ) (j : ℝ) := by
  obtain ⟨hu, hv, hc, _, _, _⟩ := hr
  have huR := mass_moment_real r positionN r.u hu
  have hvR := mass_moment_real r positionJ r.v hv
  have hcR := mass_moment_real r positionC r.c hc
  simp_rw [positions₁₆_cast N j hN]
  calc
    _ = (∑ i, (r.gap i : ℝ)*(positionN i : ℝ))*(N : ℝ) +
        (∑ i, (r.gap i : ℝ)*(positionJ i : ℝ))*(j : ℝ) +
        (∑ i, (r.gap i : ℝ)*(positionC i : ℝ)) := by
          simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by rw [huR, hvR, hcR]; rfl

private lemma ray_square_identity (r : RayData) (hr : MomentWitness r) (N j : ℕ)
    (hN : 67 ≤ N) (hl : 6 ≤ j) (hu : j ≤ N-10) :
    (∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*
      (min (positions₁₆ N j i) (positions₁₆ N j k) : ℕ)) = raySquare r (N : ℝ) (j : ℝ) := by
  obtain ⟨_, _, _, hN₂, hj₂, hC₂⟩ := hr
  have hN₂R : ∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(positionN (min i k) : ℝ) = (r.u : ℝ)^2 := by
    have h := square_moment_real r positionN (r.u^2) hN₂
    simpa using h
  have hj₂R : ∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(positionJ (min i k) : ℝ) =
      (r.v : ℝ)^2+2*(r.u : ℝ)*(r.v : ℝ) := by
    have h := square_moment_real r positionJ (r.v^2+2*r.u*r.v) hj₂
    simpa using h
  have hC₂R := square_moment_real r positionC r.C hC₂
  have hmin : ∀ i k, min (positions₁₆ N j i) (positions₁₆ N j k) = positions₁₆ N j (min i k) := by
    intro i k
    rcases le_total i k with hik | hki
    · rw [min_eq_left hik, min_eq_left (positions₁₆_monotone N j hN hl hu hik)]
    · rw [min_eq_right hki, min_eq_right (positions₁₆_monotone N j hN hl hu hki)]
  simp_rw [hmin, positions₁₆_cast N j hN]
  calc
    _ = (∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(positionN (min i k) : ℝ))*(N : ℝ) +
        (∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(positionJ (min i k) : ℝ))*(j : ℝ) +
        (∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*(positionC (min i k) : ℝ)) := by
          simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by rw [hN₂R, hj₂R, hC₂R]; rfl

/- This is the exact interface for the generalized ORIGINAL square_synth and
   mass_synth lemmas; it introduces no replacement norm/step implementation. -/
private lemma ray_gram_bound (r : RayData) (hr : r.Valid) (N j : ℕ)
    (hN : 67 ≤ N) (hl : 6 ≤ j) (hu : j ≤ N-10) :
    (∑ i, ∑ k, (r.gap i : ℝ)*(r.gap k : ℝ)*
      (min (positions₁₆ N j i) (positions₁₆ N j k) : ℕ)) ≤
      bulkValue (N : ℝ) (bulkIndex N : ℝ)*
        (∑ i, (r.gap i : ℝ)*(positions₁₆ N j i : ℝ))^2 := by
  rw [ray_square_identity r hr.moments N j hN hl hu, ray_mass_identity r hr.moments N j hN]
  exact ray_scalar_bound r hr N j hN hl

end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open Finset Matrix

private def originalRay (i : Fin 187) : RayData :=
  match i.val with
  | 0 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0], u := 1, v := 0, c := (-2), C := (-2), branch := .boundary }
  | 1 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := (-1), C := (-1), branch := .boundary }
  | 2 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 0, C := 0, branch := .boundary }
  | 3 => { gap := ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := 0, C := 2, branch := .boundary }
  | 4 => { gap := ![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 2, C := 8, branch := .boundary }
  | 5 => { gap := ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := 1, C := 5, branch := .boundary }
  | 6 => { gap := ![0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 6, C := 42, branch := .boundary }
  | 7 => { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 3, C := 39, branch := .boundary }
  | 8 => { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 3, C := 9, branch := .boundary }
  | 9 => { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 5, C := 55, branch := .boundary }
  | 10 => { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 4, C := 12, branch := .boundary }
  | 11 => { gap := ![0,0,0,0,3,0,0,0,0,0,0,0,0,0,5,0], u := 5, v := 0, c := 10, C := 170, branch := .boundary }
  | 12 => { gap := ![0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,5], u := 5, v := 0, c := 20, C := 280, branch := .boundary }
  | 13 => { gap := ![0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0], u := 2, v := 1, c := (-2), C := (-4), branch := .envelope₁ }
  | 14 => { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,3], u := 3, v := 2, c := 0, C := 0, branch := .bulk }
  | 15 => { gap := ![0,0,0,0,0,0,3,0,0,0,0,0,0,0,5,0], u := 8, v := 0, c := (-32), C := (-376), branch := .boundary }
  | 16 => { gap := ![0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,5], u := 9, v := 0, c := (-36), C := (-504), branch := .boundary }
  | 17 => { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,0,0,3,0], u := 5, v := 0, c := (-19), C := (-137), branch := .boundary }
  | 18 => { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1], u := 2, v := 0, c := (-8), C := (-24), branch := .boundary }
  | 19 => { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,0,0,3,0], u := 5, v := 0, c := (-17), C := (-121), branch := .boundary }
  | 20 => { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1], u := 2, v := 0, c := (-7), C := (-21), branch := .boundary }
  | 21 => { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,0,0,3,0], u := 5, v := 0, c := (-15), C := (-105), branch := .boundary }
  | 22 => { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1], u := 2, v := 0, c := (-6), C := (-18), branch := .boundary }
  | 23 => { gap := ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0], u := 2, v := 0, c := (-6), C := (-16), branch := .boundary }
  | 24 => { gap := ![0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,2], u := 5, v := 0, c := (-15), C := (-105), branch := .boundary }
  | 25 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0], u := 2, v := 0, c := (-5), C := (-13), branch := .boundary }
  | 26 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1], u := 3, v := 0, c := (-8), C := (-32), branch := .boundary }
  | 27 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0], u := 2, v := 0, c := (-4), C := (-10), branch := .boundary }
  | 28 => { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1], u := 3, v := 0, c := (-6), C := (-24), branch := .boundary }
  | 29 => { gap := ![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 3, C := 11, branch := .boundary }
  | 30 => { gap := ![1,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
  | 31 => { gap := ![3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 6, C := 42, branch := .boundary }
  | 32 => { gap := ![1,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 3, C := 23, branch := .boundary }
  | 33 => { gap := ![3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 7, C := 47, branch := .boundary }
  | 34 => { gap := ![1,0,0,0,1,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 4, C := 28, branch := .boundary }
  | 35 => { gap := ![3,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 8, C := 52, branch := .boundary }
  | 36 => { gap := ![3,0,0,0,0,2,0,0,0,0,0,0,0,0,5,0], u := 5, v := 2, c := (-2), C := 26, branch := .envelope₂ }
  | 37 => { gap := ![8,0,0,0,0,2,0,0,0,0,0,0,0,0,0,5], u := 5, v := 2, c := 8, C := 176, branch := .envelope₂ }
  | 38 => { gap := ![1,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0], u := 3, v := 0, c := (-10), C := (-42), branch := .boundary }
  | 39 => { gap := ![3,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-6), C := (-18), branch := .boundary }
  | 40 => { gap := ![1,0,0,0,0,0,0,1,0,0,0,0,0,0,2,0], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
  | 41 => { gap := ![3,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-5), C := (-13), branch := .boundary }
  | 42 => { gap := ![1,0,0,0,0,0,0,0,1,0,0,0,0,0,2,0], u := 3, v := 0, c := (-8), C := (-32), branch := .boundary }
  | 43 => { gap := ![3,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2], u := 3, v := 0, c := (-4), C := (-8), branch := .boundary }
  | 44 => { gap := ![1,0,0,0,0,0,0,0,0,1,0,0,0,0,2,0], u := 3, v := 0, c := (-7), C := (-27), branch := .boundary }
  | 45 => { gap := ![3,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2], u := 3, v := 0, c := (-3), C := (-3), branch := .boundary }
  | 46 => { gap := ![1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1], u := 2, v := 0, c := (-4), C := (-10), branch := .boundary }
  | 47 => { gap := ![0,1,0,0,2,0,0,0,0,0,0,0,0,0,4,0], u := 4, v := 0, c := 8, C := 110, branch := .boundary }
  | 48 => { gap := ![0,3,0,0,2,0,0,0,0,0,0,0,0,0,0,4], u := 4, v := 0, c := 16, C := 190, branch := .boundary }
  | 49 => { gap := ![0,3,0,0,0,2,0,0,0,0,0,0,0,0,6,0], u := 6, v := 2, c := 0, C := 78, branch := .envelope₂ }
  | 50 => { gap := ![0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 66, branch := .envelope₂ }
  | 51 => { gap := ![0,1,0,0,0,0,2,0,0,0,0,0,0,0,4,0], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
  | 52 => { gap := ![0,3,0,0,0,0,2,0,0,0,0,0,0,0,0,4], u := 6, v := 0, c := (-12), C := (-90), branch := .boundary }
  | 53 => { gap := ![0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,1], u := 2, v := 0, c := (-2), C := (-2), branch := .boundary }
  | 54 => { gap := ![0,3,0,0,0,0,0,0,0,0,0,0,1,0,0,2], u := 3, v := 0, c := 3, C := 39, branch := .boundary }
  | 55 => { gap := ![0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,1], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
  | 56 => { gap := ![0,0,1,0,3,0,0,0,0,0,0,0,0,0,6,0], u := 6, v := 0, c := 12, C := 246, branch := .boundary }
  | 57 => { gap := ![0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 8, C := 46, branch := .boundary }
  | 58 => { gap := ![0,0,1,0,0,1,0,0,0,0,0,0,0,0,3,0], u := 3, v := 1, c := 0, C := 18, branch := .envelope₂ }
  | 59 => { gap := ![0,0,2,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 60, branch := .envelope₂ }
  | 60 => { gap := ![0,0,1,0,0,0,3,0,0,0,0,0,0,0,6,0], u := 9, v := 0, c := (-30), C := (-384), branch := .boundary }
  | 61 => { gap := ![0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-6), C := (-24), branch := .boundary }
  | 62 => { gap := ![0,0,1,0,0,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-3), C := (-3), branch := .boundary }
  | 63 => { gap := ![0,0,1,0,0,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-9), C := (-51), branch := .boundary }
  | 64 => { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 0, C := 30, branch := .boundary }
  | 65 => { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 0, C := 6, branch := .boundary }
  | 66 => { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 0, C := 8, branch := .boundary }
  | 67 => { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 0, C := 30, branch := .boundary }
  | 68 => { gap := ![0,0,0,1,1,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 6, C := 62, branch := .boundary }
  | 69 => { gap := ![0,0,0,3,0,1,0,0,0,0,0,0,0,0,6,0], u := 6, v := 1, c := 6, C := 168, branch := .envelope₂ }
  | 70 => { gap := ![0,0,0,1,0,0,1,0,0,0,0,0,0,0,3,0], u := 4, v := 0, c := (-8), C := (-36), branch := .boundary }
  | 71 => { gap := ![0,0,0,1,0,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-2), C := 4, branch := .boundary }
  | 72 => { gap := ![0,0,0,1,0,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-8), C := (-40), branch := .boundary }
  | 73 => { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 2, C := 50, branch := .boundary }
  | 74 => { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 1, C := 11, branch := .boundary }
  | 75 => { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 1, C := 13, branch := .boundary }
  | 76 => { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 2, C := 50, branch := .boundary }
  | 77 => { gap := ![0,0,0,0,1,0,0,1,0,0,0,0,0,0,3,0], u := 4, v := 0, c := (-6), C := (-20), branch := .boundary }
  | 78 => { gap := ![0,0,0,0,3,0,0,0,1,0,0,0,0,0,6,0], u := 7, v := 0, c := 2, C := 128, branch := .boundary }
  | 79 => { gap := ![0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,2], u := 3, v := 0, c := (-2), C := 0, branch := .boundary }
  | 80 => { gap := ![0,0,0,0,5,0,0,0,0,1,0,0,0,0,9,0], u := 10, v := 0, c := 10, C := 430, branch := .boundary }
  | 81 => { gap := ![0,0,0,0,2,0,0,0,0,1,0,0,0,0,0,3], u := 4, v := 0, c := 4, C := 58, branch := .boundary }
  | 82 => { gap := ![0,0,0,0,4,0,0,0,0,0,1,0,0,0,7,0], u := 8, v := 0, c := 8, C := 276, branch := .boundary }
  | 83 => { gap := ![0,0,0,0,5,0,0,0,0,0,3,0,0,0,0,7], u := 10, v := 0, c := 10, C := 370, branch := .boundary }
  | 84 => { gap := ![0,0,0,0,1,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-1), C := 11, branch := .boundary }
  | 85 => { gap := ![0,0,0,0,3,0,0,0,0,0,0,1,0,0,5,0], u := 6, v := 0, c := 6, C := 156, branch := .boundary }
  | 86 => { gap := ![0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-7), C := (-29), branch := .boundary }
  | 87 => { gap := ![0,0,0,0,4,0,0,0,0,0,0,3,0,0,0,5], u := 8, v := 0, c := 8, C := 244, branch := .boundary }
  | 88 => { gap := ![0,0,0,0,2,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 4, C := 70, branch := .boundary }
  | 89 => { gap := ![0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 2, C := 16, branch := .boundary }
  | 90 => { gap := ![0,0,0,0,1,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
  | 91 => { gap := ![0,0,0,0,2,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 4, C := 70, branch := .boundary }
  | 92 => { gap := ![0,0,0,0,0,1,0,3,0,0,0,0,0,0,6,0], u := 9, v := 1, c := (-30), C := (-396), branch := .envelope₂ }
  | 93 => { gap := ![0,0,0,0,0,1,0,0,1,0,0,0,0,0,3,0], u := 4, v := 1, c := (-10), C := (-58), branch := .envelope₂ }
  | 94 => { gap := ![0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,3], u := 5, v := 1, c := (-14), C := (-112), branch := .envelope₂ }
  | 95 => { gap := ![0,0,0,0,0,5,0,0,0,3,0,0,0,0,12,0], u := 15, v := 5, c := (-30), C := (-630), branch := .envelope₂ }
  | 96 => { gap := ![0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,2], u := 3, v := 1, c := (-6), C := (-30), branch := .envelope₂ }
  | 97 => { gap := ![0,0,0,0,0,4,0,0,0,0,3,0,0,0,9,0], u := 12, v := 4, c := (-24), C := (-396), branch := .envelope₂ }
  | 98 => { gap := ![0,0,0,0,0,5,0,0,0,0,6,0,0,0,0,9], u := 15, v := 5, c := (-30), C := (-720), branch := .envelope₂ }
  | 99 => { gap := ![0,0,0,0,0,1,0,0,0,0,0,1,0,0,2,0], u := 3, v := 1, c := (-6), C := (-24), branch := .envelope₂ }
  | 100 => { gap := ![0,0,0,0,0,1,0,0,0,0,0,3,0,0,0,2], u := 5, v := 1, c := (-12), C := (-84), branch := .envelope₂ }
  | 101 => { gap := ![0,0,0,0,0,2,0,0,0,0,0,3,0,0,0,3], u := 6, v := 2, c := (-12), C := (-108), branch := .envelope₂ }
  | 102 => { gap := ![0,0,0,0,0,4,0,0,0,0,0,0,3,0,7,0], u := 10, v := 4, c := (-16), C := (-202), branch := .envelope₂ }
  | 103 => { gap := ![0,0,0,0,0,6,0,0,0,0,0,0,8,0,0,7], u := 15, v := 6, c := (-24), C := (-528), branch := .envelope₂ }
  | 104 => { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,3,2,0], u := 5, v := 2, c := (-8), C := (-46), branch := .envelope₂ }
  | 105 => { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,4,0,1], u := 5, v := 2, c := (-8), C := (-48), branch := .envelope₂ }
  | 106 => { gap := ![0,0,0,0,0,0,1,1,0,0,0,0,0,0,3,0], u := 5, v := 0, c := (-20), C := (-146), branch := .boundary }
  | 107 => { gap := ![0,0,0,0,0,0,3,0,1,0,0,0,0,0,6,0], u := 10, v := 0, c := (-40), C := (-586), branch := .boundary }
  | 108 => { gap := ![0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2], u := 4, v := 0, c := (-16), C := (-98), branch := .boundary }
  | 109 => { gap := ![0,0,0,0,0,0,5,0,0,1,0,0,0,0,9,0], u := 15, v := 0, c := (-60), C := (-1320), branch := .boundary }
  | 110 => { gap := ![0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,3], u := 6, v := 0, c := (-24), C := (-222), branch := .boundary }
  | 111 => { gap := ![0,0,0,0,0,0,4,0,0,0,1,0,0,0,7,0], u := 12, v := 0, c := (-48), C := (-844), branch := .boundary }
  | 112 => { gap := ![0,0,0,0,0,0,5,0,0,0,3,0,0,0,0,7], u := 15, v := 0, c := (-60), C := (-1380), branch := .boundary }
  | 113 => { gap := ![0,0,0,0,0,0,1,0,0,0,0,1,0,0,2,0], u := 4, v := 0, c := (-15), C := (-87), branch := .boundary }
  | 114 => { gap := ![0,0,0,0,0,0,3,0,0,0,0,1,0,0,5,0], u := 9, v := 0, c := (-36), C := (-474), branch := .boundary }
  | 115 => { gap := ![0,0,0,0,0,0,1,0,0,0,0,3,0,0,0,2], u := 6, v := 0, c := (-21), C := (-183), branch := .boundary }
  | 116 => { gap := ![0,0,0,0,0,0,4,0,0,0,0,3,0,0,0,5], u := 12, v := 0, c := (-48), C := (-876), branch := .boundary }
  | 117 => { gap := ![0,0,0,0,0,0,2,0,0,0,0,0,1,0,3,0], u := 6, v := 0, c := (-24), C := (-210), branch := .boundary }
  | 118 => { gap := ![0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1], u := 3, v := 0, c := (-12), C := (-54), branch := .boundary }
  | 119 => { gap := ![0,0,0,0,0,0,1,0,0,0,0,0,0,1,1,0], u := 3, v := 0, c := (-12), C := (-52), branch := .boundary }
  | 120 => { gap := ![0,0,0,0,0,0,2,0,0,0,0,0,0,3,0,1], u := 6, v := 0, c := (-24), C := (-210), branch := .boundary }
  | 121 => { gap := ![0,0,0,0,0,0,0,1,0,0,0,1,0,0,2,0], u := 4, v := 0, c := (-14), C := (-80), branch := .boundary }
  | 122 => { gap := ![0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,2], u := 6, v := 0, c := (-20), C := (-172), branch := .boundary }
  | 123 => { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,1,0,3,0], u := 6, v := 0, c := (-22), C := (-190), branch := .boundary }
  | 124 => { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,1], u := 3, v := 0, c := (-11), C := (-49), branch := .boundary }
  | 125 => { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,0,1,1,0], u := 3, v := 0, c := (-11), C := (-47), branch := .boundary }
  | 126 => { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,0,3,0,1], u := 6, v := 0, c := (-22), C := (-190), branch := .boundary }
  | 127 => { gap := ![0,0,0,0,0,0,0,0,1,0,0,1,0,0,2,0], u := 4, v := 0, c := (-13), C := (-73), branch := .boundary }
  | 128 => { gap := ![0,0,0,0,0,0,0,0,1,0,0,3,0,0,0,2], u := 6, v := 0, c := (-19), C := (-161), branch := .boundary }
  | 129 => { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,1,0,3,0], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
  | 130 => { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1], u := 3, v := 0, c := (-10), C := (-44), branch := .boundary }
  | 131 => { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,0], u := 3, v := 0, c := (-10), C := (-42), branch := .boundary }
  | 132 => { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,0,3,0,1], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
  | 133 => { gap := ![0,0,0,0,0,0,0,0,0,1,0,1,0,0,2,0], u := 4, v := 0, c := (-12), C := (-66), branch := .boundary }
  | 134 => { gap := ![0,0,0,0,0,0,0,0,0,1,0,3,0,0,0,2], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
  | 135 => { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,1,0,3,0], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
  | 136 => { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1], u := 3, v := 0, c := (-9), C := (-39), branch := .boundary }
  | 137 => { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
  | 138 => { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,0,3,0,1], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
  | 139 => { gap := ![0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
  | 140 => { gap := ![0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,2], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
  | 141 => { gap := ![0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,1], u := 4, v := 0, c := (-12), C := (-66), branch := .boundary }
  | 142 => { gap := ![1,1,0,0,0,1,0,0,0,0,0,0,0,0,3,0], u := 3, v := 1, c := 0, C := 20, branch := .envelope₂ }
  | 143 => { gap := ![4,1,0,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 74, branch := .envelope₂ }
  | 144 => { gap := ![3,0,1,0,0,2,0,0,0,0,0,0,0,0,6,0], u := 6, v := 2, c := 0, C := 78, branch := .envelope₂ }
  | 145 => { gap := ![9,0,1,0,0,2,0,0,0,0,0,0,0,0,0,6], u := 6, v := 2, c := 12, C := 294, branch := .envelope₂ }
  | 146 => { gap := ![2,0,0,1,0,1,0,0,0,0,0,0,0,0,4,0], u := 4, v := 1, c := 2, C := 56, branch := .envelope₂ }
  | 147 => { gap := ![6,0,0,1,0,1,0,0,0,0,0,0,0,0,0,4], u := 4, v := 1, c := 10, C := 152, branch := .envelope₂ }
  | 148 => { gap := ![2,0,0,0,0,1,0,1,0,0,0,0,0,0,4,0], u := 5, v := 1, c := (-10), C := (-60), branch := .envelope₂ }
  | 149 => { gap := ![6,0,0,0,0,1,0,1,0,0,0,0,0,0,0,4], u := 5, v := 1, c := (-2), C := 36, branch := .envelope₂ }
  | 150 => { gap := ![3,0,0,0,0,2,0,0,1,0,0,0,0,0,6,0], u := 7, v := 2, c := (-10), C := (-64), branch := .envelope₂ }
  | 151 => { gap := ![9,0,0,0,0,2,0,0,1,0,0,0,0,0,0,6], u := 7, v := 2, c := 2, C := 152, branch := .envelope₂ }
  | 152 => { gap := ![4,0,0,0,0,3,0,0,0,1,0,0,0,0,8,0], u := 9, v := 3, c := (-10), C := (-54), branch := .envelope₂ }
  | 153 => { gap := ![12,0,0,0,0,3,0,0,0,1,0,0,0,0,0,8], u := 9, v := 3, c := 6, C := 330, branch := .envelope₂ }
  | 154 => { gap := ![2,0,0,0,0,2,0,0,0,0,1,0,0,0,5,0], u := 6, v := 2, c := (-8), C := (-44), branch := .envelope₂ }
  | 155 => { gap := ![7,0,0,0,0,2,0,0,0,0,1,0,0,0,0,5], u := 6, v := 2, c := 2, C := 106, branch := .envelope₂ }
  | 156 => { gap := ![2,0,0,0,0,1,0,0,0,0,0,1,0,0,0,2], u := 3, v := 1, c := (-2), C := 0, branch := .envelope₂ }
  | 157 => { gap := ![0,2,0,0,0,2,0,0,0,0,0,0,1,0,5,0], u := 6, v := 2, c := (-4), C := 14, branch := .envelope₂ }
  | 158 => { gap := ![0,3,0,0,0,3,0,0,0,0,0,0,4,0,0,5], u := 9, v := 3, c := (-6), C := (-6), branch := .envelope₂ }
  | 159 => { gap := ![0,1,0,0,0,1,0,0,0,0,0,0,0,1,2,0], u := 3, v := 1, c := (-2), C := 4, branch := .envelope₂ }
  | 160 => { gap := ![0,1,0,0,0,1,0,0,0,0,0,0,0,2,0,1], u := 3, v := 1, c := (-2), C := 2, branch := .envelope₂ }
  | 161 => { gap := ![0,0,2,0,0,4,0,0,0,0,0,0,3,0,9,0], u := 12, v := 4, c := (-12), C := (-66), branch := .envelope₂ }
  | 162 => { gap := ![0,0,1,0,0,2,0,0,0,0,0,0,3,0,0,3], u := 6, v := 2, c := (-6), C := (-30), branch := .envelope₂ }
  | 163 => { gap := ![0,0,1,0,0,2,0,0,0,0,0,0,0,3,3,0], u := 6, v := 2, c := (-6), C := (-12), branch := .envelope₂ }
  | 164 => { gap := ![0,0,2,0,0,4,0,0,0,0,0,0,0,9,0,3], u := 12, v := 4, c := (-12), C := (-66), branch := .envelope₂ }
  | 165 => { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,1,0,3,0], u := 4, v := 1, c := (-2), C := 14, branch := .envelope₂ }
  | 166 => { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,2], u := 4, v := 1, c := (-2), C := 8, branch := .envelope₂ }
  | 167 => { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,0,2,2,0], u := 4, v := 1, c := (-2), C := 16, branch := .envelope₂ }
  | 168 => { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,0,3,0,1], u := 4, v := 1, c := (-2), C := 14, branch := .envelope₂ }
  | 169 => { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,1,0,3,0], u := 5, v := 1, c := (-14), C := (-102), branch := .envelope₂ }
  | 170 => { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,2,0,0,2], u := 5, v := 1, c := (-14), C := (-108), branch := .envelope₂ }
  | 171 => { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,0,2,2,0], u := 5, v := 1, c := (-14), C := (-100), branch := .envelope₂ }
  | 172 => { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,0,3,0,1], u := 5, v := 1, c := (-14), C := (-102), branch := .envelope₂ }
  | 173 => { gap := ![0,0,0,0,0,4,0,0,2,0,0,0,3,0,9,0], u := 14, v := 4, c := (-32), C := (-634), branch := .envelope₂ }
  | 174 => { gap := ![0,0,0,0,0,2,0,0,1,0,0,0,3,0,0,3], u := 7, v := 2, c := (-16), C := (-172), branch := .envelope₂ }
  | 175 => { gap := ![0,0,0,0,0,2,0,0,1,0,0,0,0,3,3,0], u := 7, v := 2, c := (-16), C := (-154), branch := .envelope₂ }
  | 176 => { gap := ![0,0,0,0,0,4,0,0,2,0,0,0,0,9,0,3], u := 14, v := 4, c := (-32), C := (-634), branch := .envelope₂ }
  | 177 => { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,2,0,6,0], u := 9, v := 3, c := (-18), C := (-222), branch := .envelope₂ }
  | 178 => { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,4,0,0,4], u := 9, v := 3, c := (-18), C := (-246), branch := .envelope₂ }
  | 179 => { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,0,4,4,0], u := 9, v := 3, c := (-18), C := (-214), branch := .envelope₂ }
  | 180 => { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,0,6,0,2], u := 9, v := 3, c := (-18), C := (-222), branch := .envelope₂ }
  | 181 => { gap := ![0,0,0,0,0,2,0,0,0,0,1,0,1,0,4,0], u := 6, v := 2, c := (-12), C := (-98), branch := .envelope₂ }
  | 182 => { gap := ![0,0,0,0,0,6,0,0,0,0,3,0,7,0,0,8], u := 18, v := 6, c := (-36), C := (-978), branch := .envelope₂ }
  | 183 => { gap := ![0,0,0,0,0,2,0,0,0,0,1,0,0,2,3,0], u := 6, v := 2, c := (-12), C := (-96), branch := .envelope₂ }
  | 184 => { gap := ![0,0,0,0,0,4,0,0,0,0,2,0,0,7,0,3], u := 12, v := 4, c := (-24), C := (-402), branch := .envelope₂ }
  | 185 => { gap := ![0,0,0,0,0,3,0,0,0,0,0,3,2,0,0,4], u := 9, v := 3, c := (-18), C := (-240), branch := .envelope₂ }
  | _ => { gap := ![0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,1], u := 3, v := 1, c := (-6), C := (-26), branch := .envelope₂ }

/- Direct supplied witnesses at each id. No exists-search, no native_decide,
   no VM evaluation and no appeal to the Python assertions as a Lean proof. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
set_option diagnostics true in
private theorem originalRay_valid (i : Fin 187) : (originalRay i).Valid := by
  fin_cases i
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0], u := 1, v := 0, c := (-2), C := (-2), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := (-1), C := (-1), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 0, C := 0, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := 0, C := 2, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 2, C := 8, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0], u := 1, v := 0, c := 1, C := 5, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 6, C := 42, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 3, C := 39, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 3, C := 9, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 5, C := 55, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 4, C := 12, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,3,0,0,0,0,0,0,0,0,0,5,0], u := 5, v := 0, c := 10, C := 170, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,5], u := 5, v := 0, c := 20, C := 280, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0], u := 2, v := 1, c := (-2), C := (-4), branch := .envelope₁ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,3], u := 3, v := 2, c := 0, C := 0, branch := .bulk }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,3,0,0,0,0,0,0,0,5,0], u := 8, v := 0, c := (-32), C := (-376), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,5], u := 9, v := 0, c := (-36), C := (-504), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,0,0,3,0], u := 5, v := 0, c := (-19), C := (-137), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1], u := 2, v := 0, c := (-8), C := (-24), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,0,0,3,0], u := 5, v := 0, c := (-17), C := (-121), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1], u := 2, v := 0, c := (-7), C := (-21), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,0,0,3,0], u := 5, v := 0, c := (-15), C := (-105), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1], u := 2, v := 0, c := (-6), C := (-18), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0], u := 2, v := 0, c := (-6), C := (-16), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,2], u := 5, v := 0, c := (-15), C := (-105), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0], u := 2, v := 0, c := (-5), C := (-13), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1], u := 3, v := 0, c := (-8), C := (-32), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0], u := 2, v := 0, c := (-4), C := (-10), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1], u := 3, v := 0, c := (-6), C := (-24), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1], u := 1, v := 0, c := 3, C := 11, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 6, C := 42, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 3, C := 23, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 7, C := 47, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,1,0,0,0,0,0,0,0,0,0,2,0], u := 2, v := 0, c := 4, C := 28, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 8, C := 52, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,2,0,0,0,0,0,0,0,0,5,0], u := 5, v := 2, c := (-2), C := 26, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![8,0,0,0,0,2,0,0,0,0,0,0,0,0,0,5], u := 5, v := 2, c := 8, C := 176, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0], u := 3, v := 0, c := (-10), C := (-42), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-6), C := (-18), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,0,1,0,0,0,0,0,0,2,0], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-5), C := (-13), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,0,0,1,0,0,0,0,0,2,0], u := 3, v := 0, c := (-8), C := (-32), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2], u := 3, v := 0, c := (-4), C := (-8), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,0,0,0,1,0,0,0,0,2,0], u := 3, v := 0, c := (-7), C := (-27), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2], u := 3, v := 0, c := (-3), C := (-3), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1], u := 2, v := 0, c := (-4), C := (-10), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,2,0,0,0,0,0,0,0,0,0,4,0], u := 4, v := 0, c := 8, C := 110, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,2,0,0,0,0,0,0,0,0,0,0,4], u := 4, v := 0, c := 16, C := 190, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,2,0,0,0,0,0,0,0,0,6,0], u := 6, v := 2, c := 0, C := 78, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 66, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,0,0,2,0,0,0,0,0,0,0,4,0], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,0,2,0,0,0,0,0,0,0,0,4], u := 6, v := 0, c := (-12), C := (-90), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,1], u := 2, v := 0, c := (-2), C := (-2), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,0,0,0,0,0,0,0,1,0,0,2], u := 3, v := 0, c := 3, C := 39, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,1], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,3,0,0,0,0,0,0,0,0,0,6,0], u := 6, v := 0, c := 12, C := 246, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,2], u := 2, v := 0, c := 8, C := 46, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,1,0,0,0,0,0,0,0,0,3,0], u := 3, v := 1, c := 0, C := 18, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 60, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,3,0,0,0,0,0,0,0,6,0], u := 9, v := 0, c := (-30), C := (-384), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,2], u := 3, v := 0, c := (-6), C := (-24), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-3), C := (-3), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-9), C := (-51), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 0, C := 30, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 0, C := 6, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 0, C := 8, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 0, C := 30, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,1,0,0,0,0,0,0,0,0,0,3,0], u := 3, v := 0, c := 6, C := 62, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,3,0,1,0,0,0,0,0,0,0,0,6,0], u := 6, v := 1, c := 6, C := 168, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,1,0,0,0,0,0,0,0,3,0], u := 4, v := 0, c := (-8), C := (-36), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-2), C := 4, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-8), C := (-40), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 2, C := 50, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 1, C := 11, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 1, C := 13, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 2, C := 50, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,1,0,0,0,0,0,0,3,0], u := 4, v := 0, c := (-6), C := (-20), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,3,0,0,0,1,0,0,0,0,0,6,0], u := 7, v := 0, c := 2, C := 128, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,2], u := 3, v := 0, c := (-2), C := 0, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,5,0,0,0,0,1,0,0,0,0,9,0], u := 10, v := 0, c := 10, C := 430, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,2,0,0,0,0,1,0,0,0,0,0,3], u := 4, v := 0, c := 4, C := 58, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,4,0,0,0,0,0,1,0,0,0,7,0], u := 8, v := 0, c := 8, C := 276, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,5,0,0,0,0,0,3,0,0,0,0,7], u := 10, v := 0, c := 10, C := 370, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,0,0,0,0,1,0,0,2,0], u := 3, v := 0, c := (-1), C := 11, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,3,0,0,0,0,0,0,1,0,0,5,0], u := 6, v := 0, c := 6, C := 156, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,2], u := 5, v := 0, c := (-7), C := (-29), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,4,0,0,0,0,0,0,3,0,0,0,5], u := 8, v := 0, c := 8, C := 244, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,2,0,0,0,0,0,0,0,1,0,3,0], u := 4, v := 0, c := 4, C := 70, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1], u := 2, v := 0, c := 2, C := 16, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,1,0,0,0,0,0,0,0,0,1,1,0], u := 2, v := 0, c := 2, C := 18, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,2,0,0,0,0,0,0,0,0,3,0,1], u := 4, v := 0, c := 4, C := 70, branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,3,0,0,0,0,0,0,6,0], u := 9, v := 1, c := (-30), C := (-396), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,1,0,0,0,0,0,3,0], u := 4, v := 1, c := (-10), C := (-58), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,3], u := 5, v := 1, c := (-14), C := (-112), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,5,0,0,0,3,0,0,0,0,12,0], u := 15, v := 5, c := (-30), C := (-630), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,2], u := 3, v := 1, c := (-6), C := (-30), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,4,0,0,0,0,3,0,0,0,9,0], u := 12, v := 4, c := (-24), C := (-396), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,5,0,0,0,0,6,0,0,0,0,9], u := 15, v := 5, c := (-30), C := (-720), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,0,0,0,1,0,0,2,0], u := 3, v := 1, c := (-6), C := (-24), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,0,0,0,3,0,0,0,2], u := 5, v := 1, c := (-12), C := (-84), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,0,3,0,0,0,3], u := 6, v := 2, c := (-12), C := (-108), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,4,0,0,0,0,0,0,3,0,7,0], u := 10, v := 4, c := (-16), C := (-202), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,6,0,0,0,0,0,0,8,0,0,7], u := 15, v := 6, c := (-24), C := (-528), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,3,2,0], u := 5, v := 2, c := (-8), C := (-46), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,0,0,0,4,0,1], u := 5, v := 2, c := (-8), C := (-48), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,1,0,0,0,0,0,0,3,0], u := 5, v := 0, c := (-20), C := (-146), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,3,0,1,0,0,0,0,0,6,0], u := 10, v := 0, c := (-40), C := (-586), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2], u := 4, v := 0, c := (-16), C := (-98), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,5,0,0,1,0,0,0,0,9,0], u := 15, v := 0, c := (-60), C := (-1320), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,3], u := 6, v := 0, c := (-24), C := (-222), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,4,0,0,0,1,0,0,0,7,0], u := 12, v := 0, c := (-48), C := (-844), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,5,0,0,0,3,0,0,0,0,7], u := 15, v := 0, c := (-60), C := (-1380), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,0,0,0,0,1,0,0,2,0], u := 4, v := 0, c := (-15), C := (-87), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,3,0,0,0,0,1,0,0,5,0], u := 9, v := 0, c := (-36), C := (-474), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,0,0,0,0,3,0,0,0,2], u := 6, v := 0, c := (-21), C := (-183), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,4,0,0,0,0,3,0,0,0,5], u := 12, v := 0, c := (-48), C := (-876), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,2,0,0,0,0,0,1,0,3,0], u := 6, v := 0, c := (-24), C := (-210), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1], u := 3, v := 0, c := (-12), C := (-54), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,1,0,0,0,0,0,0,1,1,0], u := 3, v := 0, c := (-12), C := (-52), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,2,0,0,0,0,0,0,3,0,1], u := 6, v := 0, c := (-24), C := (-210), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,1,0,0,0,1,0,0,2,0], u := 4, v := 0, c := (-14), C := (-80), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,2], u := 6, v := 0, c := (-20), C := (-172), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,1,0,3,0], u := 6, v := 0, c := (-22), C := (-190), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,1], u := 3, v := 0, c := (-11), C := (-49), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,1,0,0,0,0,0,1,1,0], u := 3, v := 0, c := (-11), C := (-47), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,2,0,0,0,0,0,3,0,1], u := 6, v := 0, c := (-22), C := (-190), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,1,0,0,1,0,0,2,0], u := 4, v := 0, c := (-13), C := (-73), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,1,0,0,3,0,0,0,2], u := 6, v := 0, c := (-19), C := (-161), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,1,0,3,0], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1], u := 3, v := 0, c := (-10), C := (-44), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,0], u := 3, v := 0, c := (-10), C := (-42), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,2,0,0,0,0,3,0,1], u := 6, v := 0, c := (-20), C := (-170), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,1,0,1,0,0,2,0], u := 4, v := 0, c := (-12), C := (-66), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,1,0,3,0,0,0,2], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,1,0,3,0], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1], u := 3, v := 0, c := (-9), C := (-39), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,2,0,0,0,3,0,1], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1], u := 3, v := 0, c := (-9), C := (-37), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,2], u := 6, v := 0, c := (-18), C := (-150), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,1], u := 4, v := 0, c := (-12), C := (-66), branch := .boundary }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![1,1,0,0,0,1,0,0,0,0,0,0,0,0,3,0], u := 3, v := 1, c := 0, C := 20, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![4,1,0,0,0,1,0,0,0,0,0,0,0,0,0,3], u := 3, v := 1, c := 6, C := 74, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,1,0,0,2,0,0,0,0,0,0,0,0,6,0], u := 6, v := 2, c := 0, C := 78, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![9,0,1,0,0,2,0,0,0,0,0,0,0,0,0,6], u := 6, v := 2, c := 12, C := 294, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![2,0,0,1,0,1,0,0,0,0,0,0,0,0,4,0], u := 4, v := 1, c := 2, C := 56, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![6,0,0,1,0,1,0,0,0,0,0,0,0,0,0,4], u := 4, v := 1, c := 10, C := 152, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![2,0,0,0,0,1,0,1,0,0,0,0,0,0,4,0], u := 5, v := 1, c := (-10), C := (-60), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![6,0,0,0,0,1,0,1,0,0,0,0,0,0,0,4], u := 5, v := 1, c := (-2), C := 36, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![3,0,0,0,0,2,0,0,1,0,0,0,0,0,6,0], u := 7, v := 2, c := (-10), C := (-64), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![9,0,0,0,0,2,0,0,1,0,0,0,0,0,0,6], u := 7, v := 2, c := 2, C := 152, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![4,0,0,0,0,3,0,0,0,1,0,0,0,0,8,0], u := 9, v := 3, c := (-10), C := (-54), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![12,0,0,0,0,3,0,0,0,1,0,0,0,0,0,8], u := 9, v := 3, c := 6, C := 330, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![2,0,0,0,0,2,0,0,0,0,1,0,0,0,5,0], u := 6, v := 2, c := (-8), C := (-44), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![7,0,0,0,0,2,0,0,0,0,1,0,0,0,0,5], u := 6, v := 2, c := 2, C := 106, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![2,0,0,0,0,1,0,0,0,0,0,1,0,0,0,2], u := 3, v := 1, c := (-2), C := 0, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,2,0,0,0,2,0,0,0,0,0,0,1,0,5,0], u := 6, v := 2, c := (-4), C := 14, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,3,0,0,0,3,0,0,0,0,0,0,4,0,0,5], u := 9, v := 3, c := (-6), C := (-6), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,0,1,0,0,0,0,0,0,0,1,2,0], u := 3, v := 1, c := (-2), C := 4, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,1,0,0,0,1,0,0,0,0,0,0,0,2,0,1], u := 3, v := 1, c := (-2), C := 2, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,4,0,0,0,0,0,0,3,0,9,0], u := 12, v := 4, c := (-12), C := (-66), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,2,0,0,0,0,0,0,3,0,0,3], u := 6, v := 2, c := (-6), C := (-30), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,1,0,0,2,0,0,0,0,0,0,0,3,3,0], u := 6, v := 2, c := (-6), C := (-12), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,2,0,0,4,0,0,0,0,0,0,0,9,0,3], u := 12, v := 4, c := (-12), C := (-66), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,1,0,3,0], u := 4, v := 1, c := (-2), C := 14, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,2], u := 4, v := 1, c := (-2), C := 8, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,0,2,2,0], u := 4, v := 1, c := (-2), C := 16, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,1,0,1,0,0,0,0,0,0,0,3,0,1], u := 4, v := 1, c := (-2), C := 14, branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,1,0,3,0], u := 5, v := 1, c := (-14), C := (-102), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,2,0,0,2], u := 5, v := 1, c := (-14), C := (-108), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,0,2,2,0], u := 5, v := 1, c := (-14), C := (-100), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,1,0,0,0,0,0,3,0,1], u := 5, v := 1, c := (-14), C := (-102), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,4,0,0,2,0,0,0,3,0,9,0], u := 14, v := 4, c := (-32), C := (-634), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,1,0,0,0,3,0,0,3], u := 7, v := 2, c := (-16), C := (-172), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,1,0,0,0,0,3,3,0], u := 7, v := 2, c := (-16), C := (-154), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,4,0,0,2,0,0,0,0,9,0,3], u := 14, v := 4, c := (-32), C := (-634), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,2,0,6,0], u := 9, v := 3, c := (-18), C := (-222), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,4,0,0,4], u := 9, v := 3, c := (-18), C := (-246), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,0,4,4,0], u := 9, v := 3, c := (-18), C := (-214), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,3,0,0,0,1,0,0,0,6,0,2], u := 9, v := 3, c := (-18), C := (-222), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,1,0,1,0,4,0], u := 6, v := 2, c := (-12), C := (-98), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,6,0,0,0,0,3,0,7,0,0,8], u := 18, v := 6, c := (-36), C := (-978), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,2,0,0,0,0,1,0,0,2,3,0], u := 6, v := 2, c := (-12), C := (-96), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,4,0,0,0,0,2,0,0,7,0,3], u := 12, v := 4, c := (-24), C := (-402), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,3,0,0,0,0,0,3,2,0,0,4], u := 9, v := 3, c := (-18), C := (-240), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }
  · change RayData.Valid { gap := ![0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,1], u := 3, v := 1, c := (-6), C := (-26), branch := .envelope₂ }
    refine {
      u_nonneg := by norm_num
      v_nonneg := by norm_num
      mass67_pos := by norm_num
      moments := by
        unfold MomentWitness
        decide +kernel
      branch_valid := by
        norm_num [branchValid, boundaryCertificate, middleCertificate] }

/- To be called immediately after the ORIGINAL owning mass_synth and
   square_synth identities, generalized at their owner from Fin 9 to Fin m. -/
private theorem original_ray_gram_bound (i : Fin 187) (N j : ℕ)
    (hN : 67 ≤ N) (hl : 6 ≤ j) (hu : j ≤ N-10) :
    (∑ a, ∑ b, ((originalRay i).gap a : ℝ)*((originalRay i).gap b : ℝ)*
      (min (positions₁₆ N j a) (positions₁₆ N j b) : ℕ)) ≤
      bulkValue (N : ℝ) (bulkIndex N : ℝ)*
        (∑ a, ((originalRay i).gap a : ℝ)*(positions₁₆ N j a : ℝ))^2 := by
  exact ray_gram_bound (originalRay i) (originalRay_valid i) N j hN hl hu

end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound


end

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators
open Finset Matrix
open NonnegativeKernelCircuit NonnegativeKernelCofactor
open D5.S3.Arith.Lattices.CofactorKernel (cofactor)
open UniformSpectralBound.SharedSpectral
noncomputable section

namespace ScalarCertificate

set_option maxRecDepth 8192 in
private def aZ : Matrix (Fin 3) (Fin 16) ℤ :=
  ![![-1,-2,-3,-3,-3,-3,-3,-3,-3,-3,-2,-1,0,1,2,3],
    ![-1,-2,-3,-4,-5,-6,-5,-4,-3,-2,-1,0,1,2,3,4],
    ![-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,0,1,2]]
set_option maxRecDepth 8192 in
private def bZ : Matrix (Fin 3) (Fin 19) ℤ := fun r =>
  Fin.append (aZ r) (fun s : Fin 3 => if r = s then -1 else 0)
set_option maxRecDepth 8192 in
private def aR : Matrix (Fin 3) (Fin 16) ℝ := fun r j => (aZ r j : ℝ)
set_option maxRecDepth 8192 in
private def bR : Matrix (Fin 3) (Fin 19) ℝ := fun r j => (bZ r j : ℝ)
set_option maxRecDepth 8192 in
private def project : (Fin 19 → ℝ) →ₗ[ℝ] (Fin 16 → ℝ) := {
  toFun := fun z j => z (Fin.castAdd 3 j)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl }
set_option maxRecDepth 8192 in
private def liftGap : (Fin 16 → ℝ) → (Fin 19 → ℝ) := fun g =>
  Fin.append g (aR *ᵥ g)

-- Fixed 3x3 polynomial, with columns u,v,w. No determinant evaluator in data checks.
set_option maxRecDepth 8192 in
private def det3 : (Fin 3 → ℤ) → (Fin 3 → ℤ) → (Fin 3 → ℤ) → ℤ := fun u v w =>
  u 0 * v 1 * w 2 - u 0 * w 1 * v 2 - v 0 * u 1 * w 2 +
  v 0 * w 1 * u 2 + w 0 * u 1 * v 2 - w 0 * v 1 * u 2
set_option maxRecDepth 8192 in
private def cof4 : (Fin 4 → Fin 19) → (Fin 4 → ℤ) := fun e =>
  ![det3 (fun r => bZ r (e 1)) (fun r => bZ r (e 2)) (fun r => bZ r (e 3)),
    -det3 (fun r => bZ r (e 0)) (fun r => bZ r (e 2)) (fun r => bZ r (e 3)),
    det3 (fun r => bZ r (e 0)) (fun r => bZ r (e 1)) (fun r => bZ r (e 3)),
    -det3 (fun r => bZ r (e 0)) (fun r => bZ r (e 1)) (fun r => bZ r (e 2))]
set_option maxRecDepth 8192 in
private def extend4 : (Fin 4 → Fin 19) → (Fin 4 → ℤ) → (Fin 19 → ℤ) := fun e c =>
  ∑ i : Fin 4, Pi.single (e i) (c i)
set_option maxRecDepth 8192 in
private def realCof : (Fin 4 → Fin 19) → (Fin 19 → ℝ) := fun e j =>
  (extend4 e (cof4 e) j : ℝ)

-- Structural size-four enumerator. It constructs only a<b<c<d; no all-Finset Fintype.
set_option maxRecDepth 8192 in
private def fourTuples : Fin 19 → List (Fin 4 → Fin 19) := fun a =>
  ((List.finRange 19).filter (fun b => a < b)).flatMap fun b =>
    ((List.finRange 19).filter (fun c => b < c)).flatMap fun c =>
      ((List.finRange 19).filter (fun d => c < d)).map fun d => ![a,b,c,d]

-- inl(p,n)=mixed; inr none=zero; inr(some(negative,scale,id))=ray.
private abbrev Witness := (Fin 4 × Fin 4) ⊕ Option (Bool × ℕ × Fin 187)
private abbrev Entry := (Fin 4 → Fin 19) × Witness

/- Local literal catalog. Original ids are used without renumbering. -/
set_option maxRecDepth 8192 in
private def gZ : Fin 187 → Fin 16 → ℤ :=
  ![![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
    ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    ![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
    ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    ![0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,2],
    ![0,0,2,0,0,0,0,0,0,0,0,0,0,0,3,0],
    ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1],
    ![0,0,0,2,0,0,0,0,0,0,0,0,0,0,3,0],
    ![0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1],
    ![0,0,0,0,3,0,0,0,0,0,0,0,0,0,5,0],
    ![0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,5],
    ![0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0],
    ![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,3],
    ![0,0,0,0,0,0,3,0,0,0,0,0,0,0,5,0],
    ![0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,5],
    ![0,0,0,0,0,0,0,2,0,0,0,0,0,0,3,0],
    ![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1],
    ![0,0,0,0,0,0,0,0,2,0,0,0,0,0,3,0],
    ![0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1],
    ![0,0,0,0,0,0,0,0,0,2,0,0,0,0,3,0],
    ![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1],
    ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0],
    ![0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,2],
    ![0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0],
    ![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1],
    ![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
    ![1,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0],
    ![3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,2],
    ![1,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0],
    ![3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2],
    ![1,0,0,0,1,0,0,0,0,0,0,0,0,0,2,0],
    ![3,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2],
    ![3,0,0,0,0,2,0,0,0,0,0,0,0,0,5,0],
    ![8,0,0,0,0,2,0,0,0,0,0,0,0,0,0,5],
    ![1,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0],
    ![3,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2],
    ![1,0,0,0,0,0,0,1,0,0,0,0,0,0,2,0],
    ![3,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2],
    ![1,0,0,0,0,0,0,0,1,0,0,0,0,0,2,0],
    ![3,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2],
    ![1,0,0,0,0,0,0,0,0,1,0,0,0,0,2,0],
    ![3,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2],
    ![1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1],
    ![0,1,0,0,2,0,0,0,0,0,0,0,0,0,4,0],
    ![0,3,0,0,2,0,0,0,0,0,0,0,0,0,0,4],
    ![0,3,0,0,0,2,0,0,0,0,0,0,0,0,6,0],
    ![0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,3],
    ![0,1,0,0,0,0,2,0,0,0,0,0,0,0,4,0],
    ![0,3,0,0,0,0,2,0,0,0,0,0,0,0,0,4],
    ![0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,1],
    ![0,3,0,0,0,0,0,0,0,0,0,0,1,0,0,2],
    ![0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,1],
    ![0,0,1,0,3,0,0,0,0,0,0,0,0,0,6,0],
    ![0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,2],
    ![0,0,1,0,0,1,0,0,0,0,0,0,0,0,3,0],
    ![0,0,2,0,0,1,0,0,0,0,0,0,0,0,0,3],
    ![0,0,1,0,0,0,3,0,0,0,0,0,0,0,6,0],
    ![0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,2],
    ![0,0,1,0,0,0,0,0,0,0,0,1,0,0,2,0],
    ![0,0,1,0,0,0,0,0,0,0,0,3,0,0,0,2],
    ![0,0,2,0,0,0,0,0,0,0,0,0,1,0,3,0],
    ![0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,1],
    ![0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0],
    ![0,0,2,0,0,0,0,0,0,0,0,0,0,3,0,1],
    ![0,0,0,1,1,0,0,0,0,0,0,0,0,0,3,0],
    ![0,0,0,3,0,1,0,0,0,0,0,0,0,0,6,0],
    ![0,0,0,1,0,0,1,0,0,0,0,0,0,0,3,0],
    ![0,0,0,1,0,0,0,0,0,0,0,1,0,0,2,0],
    ![0,0,0,1,0,0,0,0,0,0,0,3,0,0,0,2],
    ![0,0,0,2,0,0,0,0,0,0,0,0,1,0,3,0],
    ![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1],
    ![0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0],
    ![0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,1],
    ![0,0,0,0,1,0,0,1,0,0,0,0,0,0,3,0],
    ![0,0,0,0,3,0,0,0,1,0,0,0,0,0,6,0],
    ![0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,2],
    ![0,0,0,0,5,0,0,0,0,1,0,0,0,0,9,0],
    ![0,0,0,0,2,0,0,0,0,1,0,0,0,0,0,3],
    ![0,0,0,0,4,0,0,0,0,0,1,0,0,0,7,0],
    ![0,0,0,0,5,0,0,0,0,0,3,0,0,0,0,7],
    ![0,0,0,0,1,0,0,0,0,0,0,1,0,0,2,0],
    ![0,0,0,0,3,0,0,0,0,0,0,1,0,0,5,0],
    ![0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,2],
    ![0,0,0,0,4,0,0,0,0,0,0,3,0,0,0,5],
    ![0,0,0,0,2,0,0,0,0,0,0,0,1,0,3,0],
    ![0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1],
    ![0,0,0,0,1,0,0,0,0,0,0,0,0,1,1,0],
    ![0,0,0,0,2,0,0,0,0,0,0,0,0,3,0,1],
    ![0,0,0,0,0,1,0,3,0,0,0,0,0,0,6,0],
    ![0,0,0,0,0,1,0,0,1,0,0,0,0,0,3,0],
    ![0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,3],
    ![0,0,0,0,0,5,0,0,0,3,0,0,0,0,12,0],
    ![0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,2],
    ![0,0,0,0,0,4,0,0,0,0,3,0,0,0,9,0],
    ![0,0,0,0,0,5,0,0,0,0,6,0,0,0,0,9],
    ![0,0,0,0,0,1,0,0,0,0,0,1,0,0,2,0],
    ![0,0,0,0,0,1,0,0,0,0,0,3,0,0,0,2],
    ![0,0,0,0,0,2,0,0,0,0,0,3,0,0,0,3],
    ![0,0,0,0,0,4,0,0,0,0,0,0,3,0,7,0],
    ![0,0,0,0,0,6,0,0,0,0,0,0,8,0,0,7],
    ![0,0,0,0,0,2,0,0,0,0,0,0,0,3,2,0],
    ![0,0,0,0,0,2,0,0,0,0,0,0,0,4,0,1],
    ![0,0,0,0,0,0,1,1,0,0,0,0,0,0,3,0],
    ![0,0,0,0,0,0,3,0,1,0,0,0,0,0,6,0],
    ![0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2],
    ![0,0,0,0,0,0,5,0,0,1,0,0,0,0,9,0],
    ![0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,3],
    ![0,0,0,0,0,0,4,0,0,0,1,0,0,0,7,0],
    ![0,0,0,0,0,0,5,0,0,0,3,0,0,0,0,7],
    ![0,0,0,0,0,0,1,0,0,0,0,1,0,0,2,0],
    ![0,0,0,0,0,0,3,0,0,0,0,1,0,0,5,0],
    ![0,0,0,0,0,0,1,0,0,0,0,3,0,0,0,2],
    ![0,0,0,0,0,0,4,0,0,0,0,3,0,0,0,5],
    ![0,0,0,0,0,0,2,0,0,0,0,0,1,0,3,0],
    ![0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1],
    ![0,0,0,0,0,0,1,0,0,0,0,0,0,1,1,0],
    ![0,0,0,0,0,0,2,0,0,0,0,0,0,3,0,1],
    ![0,0,0,0,0,0,0,1,0,0,0,1,0,0,2,0],
    ![0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,2],
    ![0,0,0,0,0,0,0,2,0,0,0,0,1,0,3,0],
    ![0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,1],
    ![0,0,0,0,0,0,0,1,0,0,0,0,0,1,1,0],
    ![0,0,0,0,0,0,0,2,0,0,0,0,0,3,0,1],
    ![0,0,0,0,0,0,0,0,1,0,0,1,0,0,2,0],
    ![0,0,0,0,0,0,0,0,1,0,0,3,0,0,0,2],
    ![0,0,0,0,0,0,0,0,2,0,0,0,1,0,3,0],
    ![0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1],
    ![0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,0],
    ![0,0,0,0,0,0,0,0,2,0,0,0,0,3,0,1],
    ![0,0,0,0,0,0,0,0,0,1,0,1,0,0,2,0],
    ![0,0,0,0,0,0,0,0,0,1,0,3,0,0,0,2],
    ![0,0,0,0,0,0,0,0,0,2,0,0,1,0,3,0],
    ![0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1],
    ![0,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0],
    ![0,0,0,0,0,0,0,0,0,2,0,0,0,3,0,1],
    ![0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1],
    ![0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,2],
    ![0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,1],
    ![1,1,0,0,0,1,0,0,0,0,0,0,0,0,3,0],
    ![4,1,0,0,0,1,0,0,0,0,0,0,0,0,0,3],
    ![3,0,1,0,0,2,0,0,0,0,0,0,0,0,6,0],
    ![9,0,1,0,0,2,0,0,0,0,0,0,0,0,0,6],
    ![2,0,0,1,0,1,0,0,0,0,0,0,0,0,4,0],
    ![6,0,0,1,0,1,0,0,0,0,0,0,0,0,0,4],
    ![2,0,0,0,0,1,0,1,0,0,0,0,0,0,4,0],
    ![6,0,0,0,0,1,0,1,0,0,0,0,0,0,0,4],
    ![3,0,0,0,0,2,0,0,1,0,0,0,0,0,6,0],
    ![9,0,0,0,0,2,0,0,1,0,0,0,0,0,0,6],
    ![4,0,0,0,0,3,0,0,0,1,0,0,0,0,8,0],
    ![12,0,0,0,0,3,0,0,0,1,0,0,0,0,0,8],
    ![2,0,0,0,0,2,0,0,0,0,1,0,0,0,5,0],
    ![7,0,0,0,0,2,0,0,0,0,1,0,0,0,0,5],
    ![2,0,0,0,0,1,0,0,0,0,0,1,0,0,0,2],
    ![0,2,0,0,0,2,0,0,0,0,0,0,1,0,5,0],
    ![0,3,0,0,0,3,0,0,0,0,0,0,4,0,0,5],
    ![0,1,0,0,0,1,0,0,0,0,0,0,0,1,2,0],
    ![0,1,0,0,0,1,0,0,0,0,0,0,0,2,0,1],
    ![0,0,2,0,0,4,0,0,0,0,0,0,3,0,9,0],
    ![0,0,1,0,0,2,0,0,0,0,0,0,3,0,0,3],
    ![0,0,1,0,0,2,0,0,0,0,0,0,0,3,3,0],
    ![0,0,2,0,0,4,0,0,0,0,0,0,0,9,0,3],
    ![0,0,0,1,0,1,0,0,0,0,0,0,1,0,3,0],
    ![0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,2],
    ![0,0,0,1,0,1,0,0,0,0,0,0,0,2,2,0],
    ![0,0,0,1,0,1,0,0,0,0,0,0,0,3,0,1],
    ![0,0,0,0,0,1,0,1,0,0,0,0,1,0,3,0],
    ![0,0,0,0,0,1,0,1,0,0,0,0,2,0,0,2],
    ![0,0,0,0,0,1,0,1,0,0,0,0,0,2,2,0],
    ![0,0,0,0,0,1,0,1,0,0,0,0,0,3,0,1],
    ![0,0,0,0,0,4,0,0,2,0,0,0,3,0,9,0],
    ![0,0,0,0,0,2,0,0,1,0,0,0,3,0,0,3],
    ![0,0,0,0,0,2,0,0,1,0,0,0,0,3,3,0],
    ![0,0,0,0,0,4,0,0,2,0,0,0,0,9,0,3],
    ![0,0,0,0,0,3,0,0,0,1,0,0,2,0,6,0],
    ![0,0,0,0,0,3,0,0,0,1,0,0,4,0,0,4],
    ![0,0,0,0,0,3,0,0,0,1,0,0,0,4,4,0],
    ![0,0,0,0,0,3,0,0,0,1,0,0,0,6,0,2],
    ![0,0,0,0,0,2,0,0,0,0,1,0,1,0,4,0],
    ![0,0,0,0,0,6,0,0,0,0,3,0,7,0,0,8],
    ![0,0,0,0,0,2,0,0,0,0,1,0,0,2,3,0],
    ![0,0,0,0,0,4,0,0,0,0,2,0,0,7,0,3],
    ![0,0,0,0,0,3,0,0,0,0,0,3,2,0,0,4],
    ![0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,1]]
set_option maxRecDepth 8192 in
private def originalGap : Fin 187 → Fin 16 → ℤ :=
  ![![0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
    ![1,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    ![2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
    ![0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0],
    ![0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,2],
    ![0,0,2,0,0,0,0,0,0,0,0,0,0,0,3,0],
    ![0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,1],
    ![0,0,0,2,0,0,0,0,0,0,0,0,0,0,3,0],
    ![0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1],
    ![0,0,0,0,3,0,0,0,0,0,0,0,0,0,5,0],
    ![0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,5],
    ![0,0,0,0,0,1,0,0,0,0,0,0,0,0,2,0],
    ![0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,3],
    ![0,0,0,0,0,0,3,0,0,0,0,0,0,0,5,0],
    ![0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,5],
    ![0,0,0,0,0,0,0,2,0,0,0,0,0,0,3,0],
    ![0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1],
    ![0,0,0,0,0,0,0,0,2,0,0,0,0,0,3,0],
    ![0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1],
    ![0,0,0,0,0,0,0,0,0,2,0,0,0,0,3,0],
    ![0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1],
    ![0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0],
    ![0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,2],
    ![0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0],
    ![0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,1],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,0,1,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,1],
    ![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,1],
    ![1,0,1,0,0,0,0,0,0,0,0,0,0,0,2,0],
    ![3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,2],
    ![1,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0],
    ![3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,2],
    ![1,0,0,0,1,0,0,0,0,0,0,0,0,0,2,0],
    ![3,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2],
    ![3,0,0,0,0,2,0,0,0,0,0,0,0,0,5,0],
    ![8,0,0,0,0,2,0,0,0,0,0,0,0,0,0,5],
    ![1,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0],
    ![3,0,0,0,0,0,1,0,0,0,0,0,0,0,0,2],
    ![1,0,0,0,0,0,0,1,0,0,0,0,0,0,2,0],
    ![3,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2],
    ![1,0,0,0,0,0,0,0,1,0,0,0,0,0,2,0],
    ![3,0,0,0,0,0,0,0,1,0,0,0,0,0,0,2],
    ![1,0,0,0,0,0,0,0,0,1,0,0,0,0,2,0],
    ![3,0,0,0,0,0,0,0,0,1,0,0,0,0,0,2],
    ![1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1],
    ![0,1,0,0,2,0,0,0,0,0,0,0,0,0,4,0],
    ![0,3,0,0,2,0,0,0,0,0,0,0,0,0,0,4],
    ![0,3,0,0,0,2,0,0,0,0,0,0,0,0,6,0],
    ![0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,3],
    ![0,1,0,0,0,0,2,0,0,0,0,0,0,0,4,0],
    ![0,3,0,0,0,0,2,0,0,0,0,0,0,0,0,4],
    ![0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,1],
    ![0,3,0,0,0,0,0,0,0,0,0,0,1,0,0,2],
    ![0,2,0,0,0,0,0,0,0,0,0,0,0,1,0,1],
    ![0,0,1,0,3,0,0,0,0,0,0,0,0,0,6,0],
    ![0,0,1,0,1,0,0,0,0,0,0,0,0,0,0,2],
    ![0,0,1,0,0,1,0,0,0,0,0,0,0,0,3,0],
    ![0,0,2,0,0,1,0,0,0,0,0,0,0,0,0,3],
    ![0,0,1,0,0,0,3,0,0,0,0,0,0,0,6,0],
    ![0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,2],
    ![0,0,1,0,0,0,0,0,0,0,0,1,0,0,2,0],
    ![0,0,1,0,0,0,0,0,0,0,0,3,0,0,0,2],
    ![0,0,2,0,0,0,0,0,0,0,0,0,1,0,3,0],
    ![0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,1],
    ![0,0,1,0,0,0,0,0,0,0,0,0,0,1,1,0],
    ![0,0,2,0,0,0,0,0,0,0,0,0,0,3,0,1],
    ![0,0,0,1,1,0,0,0,0,0,0,0,0,0,3,0],
    ![0,0,0,3,0,1,0,0,0,0,0,0,0,0,6,0],
    ![0,0,0,1,0,0,1,0,0,0,0,0,0,0,3,0],
    ![0,0,0,1,0,0,0,0,0,0,0,1,0,0,2,0],
    ![0,0,0,1,0,0,0,0,0,0,0,3,0,0,0,2],
    ![0,0,0,2,0,0,0,0,0,0,0,0,1,0,3,0],
    ![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,1],
    ![0,0,0,1,0,0,0,0,0,0,0,0,0,1,1,0],
    ![0,0,0,2,0,0,0,0,0,0,0,0,0,3,0,1],
    ![0,0,0,0,1,0,0,1,0,0,0,0,0,0,3,0],
    ![0,0,0,0,3,0,0,0,1,0,0,0,0,0,6,0],
    ![0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,2],
    ![0,0,0,0,5,0,0,0,0,1,0,0,0,0,9,0],
    ![0,0,0,0,2,0,0,0,0,1,0,0,0,0,0,3],
    ![0,0,0,0,4,0,0,0,0,0,1,0,0,0,7,0],
    ![0,0,0,0,5,0,0,0,0,0,3,0,0,0,0,7],
    ![0,0,0,0,1,0,0,0,0,0,0,1,0,0,2,0],
    ![0,0,0,0,3,0,0,0,0,0,0,1,0,0,5,0],
    ![0,0,0,0,1,0,0,0,0,0,0,3,0,0,0,2],
    ![0,0,0,0,4,0,0,0,0,0,0,3,0,0,0,5],
    ![0,0,0,0,2,0,0,0,0,0,0,0,1,0,3,0],
    ![0,0,0,0,1,0,0,0,0,0,0,0,1,0,0,1],
    ![0,0,0,0,1,0,0,0,0,0,0,0,0,1,1,0],
    ![0,0,0,0,2,0,0,0,0,0,0,0,0,3,0,1],
    ![0,0,0,0,0,1,0,3,0,0,0,0,0,0,6,0],
    ![0,0,0,0,0,1,0,0,1,0,0,0,0,0,3,0],
    ![0,0,0,0,0,1,0,0,2,0,0,0,0,0,0,3],
    ![0,0,0,0,0,5,0,0,0,3,0,0,0,0,12,0],
    ![0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,2],
    ![0,0,0,0,0,4,0,0,0,0,3,0,0,0,9,0],
    ![0,0,0,0,0,5,0,0,0,0,6,0,0,0,0,9],
    ![0,0,0,0,0,1,0,0,0,0,0,1,0,0,2,0],
    ![0,0,0,0,0,1,0,0,0,0,0,3,0,0,0,2],
    ![0,0,0,0,0,2,0,0,0,0,0,3,0,0,0,3],
    ![0,0,0,0,0,4,0,0,0,0,0,0,3,0,7,0],
    ![0,0,0,0,0,6,0,0,0,0,0,0,8,0,0,7],
    ![0,0,0,0,0,2,0,0,0,0,0,0,0,3,2,0],
    ![0,0,0,0,0,2,0,0,0,0,0,0,0,4,0,1],
    ![0,0,0,0,0,0,1,1,0,0,0,0,0,0,3,0],
    ![0,0,0,0,0,0,3,0,1,0,0,0,0,0,6,0],
    ![0,0,0,0,0,0,1,0,1,0,0,0,0,0,0,2],
    ![0,0,0,0,0,0,5,0,0,1,0,0,0,0,9,0],
    ![0,0,0,0,0,0,2,0,0,1,0,0,0,0,0,3],
    ![0,0,0,0,0,0,4,0,0,0,1,0,0,0,7,0],
    ![0,0,0,0,0,0,5,0,0,0,3,0,0,0,0,7],
    ![0,0,0,0,0,0,1,0,0,0,0,1,0,0,2,0],
    ![0,0,0,0,0,0,3,0,0,0,0,1,0,0,5,0],
    ![0,0,0,0,0,0,1,0,0,0,0,3,0,0,0,2],
    ![0,0,0,0,0,0,4,0,0,0,0,3,0,0,0,5],
    ![0,0,0,0,0,0,2,0,0,0,0,0,1,0,3,0],
    ![0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,1],
    ![0,0,0,0,0,0,1,0,0,0,0,0,0,1,1,0],
    ![0,0,0,0,0,0,2,0,0,0,0,0,0,3,0,1],
    ![0,0,0,0,0,0,0,1,0,0,0,1,0,0,2,0],
    ![0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,2],
    ![0,0,0,0,0,0,0,2,0,0,0,0,1,0,3,0],
    ![0,0,0,0,0,0,0,1,0,0,0,0,1,0,0,1],
    ![0,0,0,0,0,0,0,1,0,0,0,0,0,1,1,0],
    ![0,0,0,0,0,0,0,2,0,0,0,0,0,3,0,1],
    ![0,0,0,0,0,0,0,0,1,0,0,1,0,0,2,0],
    ![0,0,0,0,0,0,0,0,1,0,0,3,0,0,0,2],
    ![0,0,0,0,0,0,0,0,2,0,0,0,1,0,3,0],
    ![0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,1],
    ![0,0,0,0,0,0,0,0,1,0,0,0,0,1,1,0],
    ![0,0,0,0,0,0,0,0,2,0,0,0,0,3,0,1],
    ![0,0,0,0,0,0,0,0,0,1,0,1,0,0,2,0],
    ![0,0,0,0,0,0,0,0,0,1,0,3,0,0,0,2],
    ![0,0,0,0,0,0,0,0,0,2,0,0,1,0,3,0],
    ![0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1],
    ![0,0,0,0,0,0,0,0,0,1,0,0,0,1,1,0],
    ![0,0,0,0,0,0,0,0,0,2,0,0,0,3,0,1],
    ![0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1],
    ![0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,2],
    ![0,0,0,0,0,0,0,0,0,0,2,0,0,1,0,1],
    ![1,1,0,0,0,1,0,0,0,0,0,0,0,0,3,0],
    ![4,1,0,0,0,1,0,0,0,0,0,0,0,0,0,3],
    ![3,0,1,0,0,2,0,0,0,0,0,0,0,0,6,0],
    ![9,0,1,0,0,2,0,0,0,0,0,0,0,0,0,6],
    ![2,0,0,1,0,1,0,0,0,0,0,0,0,0,4,0],
    ![6,0,0,1,0,1,0,0,0,0,0,0,0,0,0,4],
    ![2,0,0,0,0,1,0,1,0,0,0,0,0,0,4,0],
    ![6,0,0,0,0,1,0,1,0,0,0,0,0,0,0,4],
    ![3,0,0,0,0,2,0,0,1,0,0,0,0,0,6,0],
    ![9,0,0,0,0,2,0,0,1,0,0,0,0,0,0,6],
    ![4,0,0,0,0,3,0,0,0,1,0,0,0,0,8,0],
    ![12,0,0,0,0,3,0,0,0,1,0,0,0,0,0,8],
    ![2,0,0,0,0,2,0,0,0,0,1,0,0,0,5,0],
    ![7,0,0,0,0,2,0,0,0,0,1,0,0,0,0,5],
    ![2,0,0,0,0,1,0,0,0,0,0,1,0,0,0,2],
    ![0,2,0,0,0,2,0,0,0,0,0,0,1,0,5,0],
    ![0,3,0,0,0,3,0,0,0,0,0,0,4,0,0,5],
    ![0,1,0,0,0,1,0,0,0,0,0,0,0,1,2,0],
    ![0,1,0,0,0,1,0,0,0,0,0,0,0,2,0,1],
    ![0,0,2,0,0,4,0,0,0,0,0,0,3,0,9,0],
    ![0,0,1,0,0,2,0,0,0,0,0,0,3,0,0,3],
    ![0,0,1,0,0,2,0,0,0,0,0,0,0,3,3,0],
    ![0,0,2,0,0,4,0,0,0,0,0,0,0,9,0,3],
    ![0,0,0,1,0,1,0,0,0,0,0,0,1,0,3,0],
    ![0,0,0,1,0,1,0,0,0,0,0,0,2,0,0,2],
    ![0,0,0,1,0,1,0,0,0,0,0,0,0,2,2,0],
    ![0,0,0,1,0,1,0,0,0,0,0,0,0,3,0,1],
    ![0,0,0,0,0,1,0,1,0,0,0,0,1,0,3,0],
    ![0,0,0,0,0,1,0,1,0,0,0,0,2,0,0,2],
    ![0,0,0,0,0,1,0,1,0,0,0,0,0,2,2,0],
    ![0,0,0,0,0,1,0,1,0,0,0,0,0,3,0,1],
    ![0,0,0,0,0,4,0,0,2,0,0,0,3,0,9,0],
    ![0,0,0,0,0,2,0,0,1,0,0,0,3,0,0,3],
    ![0,0,0,0,0,2,0,0,1,0,0,0,0,3,3,0],
    ![0,0,0,0,0,4,0,0,2,0,0,0,0,9,0,3],
    ![0,0,0,0,0,3,0,0,0,1,0,0,2,0,6,0],
    ![0,0,0,0,0,3,0,0,0,1,0,0,4,0,0,4],
    ![0,0,0,0,0,3,0,0,0,1,0,0,0,4,4,0],
    ![0,0,0,0,0,3,0,0,0,1,0,0,0,6,0,2],
    ![0,0,0,0,0,2,0,0,0,0,1,0,1,0,4,0],
    ![0,0,0,0,0,6,0,0,0,0,3,0,7,0,0,8],
    ![0,0,0,0,0,2,0,0,0,0,1,0,0,2,3,0],
    ![0,0,0,0,0,4,0,0,0,0,2,0,0,7,0,3],
    ![0,0,0,0,0,3,0,0,0,0,0,3,2,0,0,4],
    ![0,0,0,0,0,1,0,0,0,0,0,1,0,1,0,1]]
set_option maxRecDepth 8192 in
private def slackZ : Fin 187 → Fin 3 → ℤ :=
  ![![1,2,0],
    ![2,3,1],
    ![3,4,2],
    ![1,2,0],
    ![1,2,0],
    ![0,1,0],
    ![0,2,1],
    ![0,3,1],
    ![0,1,1],
    ![0,1,1],
    ![0,0,1],
    ![1,0,2],
    ![3,0,6],
    ![1,0,1],
    ![3,0,4],
    ![1,0,2],
    ![3,0,6],
    ![0,1,1],
    ![0,0,1],
    ![0,3,1],
    ![0,1,1],
    ![0,5,1],
    ![0,2,1],
    ![0,2,0],
    ![0,5,1],
    ![1,3,0],
    ![1,4,0],
    ![2,4,0],
    ![3,6,0],
    ![0,1,0],
    ![0,2,0],
    ![0,2,0],
    ![0,1,0],
    ![0,1,0],
    ![0,0,0],
    ![0,0,0],
    ![1,0,0],
    ![1,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,1,0],
    ![0,1,0],
    ![0,2,0],
    ![0,2,0],
    ![0,3,0],
    ![0,3,0],
    ![0,2,0],
    ![0,0,1],
    ![0,0,3],
    ![0,0,1],
    ![0,0,2],
    ![0,0,1],
    ![0,0,3],
    ![0,2,0],
    ![0,3,0],
    ![0,2,0],
    ![0,0,2],
    ![0,0,2],
    ![0,0,1],
    ![0,0,3],
    ![0,0,2],
    ![0,0,2],
    ![0,3,0],
    ![0,5,0],
    ![0,4,0],
    ![0,2,0],
    ![0,2,0],
    ![0,4,0],
    ![0,0,1],
    ![0,0,2],
    ![0,0,1],
    ![0,2,0],
    ![0,4,0],
    ![0,2,0],
    ![0,1,0],
    ![0,1,0],
    ![0,2,0],
    ![0,0,1],
    ![0,0,2],
    ![0,0,2],
    ![0,0,3],
    ![0,0,3],
    ![0,0,2],
    ![0,0,6],
    ![0,1,0],
    ![0,0,1],
    ![0,3,0],
    ![0,0,3],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,2],
    ![0,0,1],
    ![0,0,3],
    ![0,0,4],
    ![0,0,2],
    ![0,0,2],
    ![0,0,7],
    ![0,0,0],
    ![0,2,0],
    ![0,0,1],
    ![2,0,0],
    ![3,0,0],
    ![1,0,0],
    ![1,0,0],
    ![0,0,1],
    ![0,0,2],
    ![0,0,2],
    ![0,0,3],
    ![0,0,3],
    ![0,0,2],
    ![0,0,6],
    ![0,1,0],
    ![0,0,1],
    ![0,3,0],
    ![0,0,3],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,2,0],
    ![0,4,0],
    ![0,2,0],
    ![0,1,0],
    ![0,1,0],
    ![0,2,0],
    ![0,3,0],
    ![0,5,0],
    ![0,4,0],
    ![0,2,0],
    ![0,2,0],
    ![0,4,0],
    ![0,4,0],
    ![0,6,0],
    ![0,6,0],
    ![0,3,0],
    ![0,3,0],
    ![0,6,0],
    ![0,3,0],
    ![0,6,0],
    ![0,4,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0],
    ![0,0,0]]
set_option maxRecDepth 8192 in
private def zZ : Fin 187 → Fin 19 → ℤ := fun t => Fin.append (gZ t) (slackZ t)
set_option maxRecDepth 8192 in
private def positiveSlot : Fin 187 → Fin 16 := ![13,14,15,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem gap_positive : ∀ t, 0 < gZ t (positiveSlot t) := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem catalog_slack : ∀ t, slackZ t = aZ *ᵥ gZ t := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem catalog_alignment : ∀ t, gZ t = originalGap t := by
  classical
  intro t
  rfl

set_option maxRecDepth 8192 in
private def CaseValid : (Fin 4 → Fin 19) → Witness → Prop := fun e w =>
  match w with
  | .inl (p,n) => 0 < cof4 e p ∧ cof4 e n < 0
  | .inr none => ∀ i, cof4 e i = 0
  | .inr (some (negative,d,t)) =>
    0 < d ∧ ∀ j : Fin 19,
      (if negative then (-1 : ℤ) else 1) * extend4 e (cof4 e) j =
        (d : ℤ) * zZ t j

/- Insert after 01-catalog and before 02-witness-blocks. CaseValid is a match
 on a variable witness, so supply its constructive decision procedure rather
 than asking typeclass synthesis to invent the dependent case split. -/
private instance caseValidDecidable : ∀ (e : Fin 4 → Fin 19) (w : Witness), Decidable (CaseValid e w) :=
  fun e w => by
    rcases w with ⟨p,n⟩ | (_ | ⟨negative,d,t⟩)
    · dsimp only [CaseValid]
      infer_instance
    · dsimp only [CaseValid]
      infer_instance
    · dsimp only [CaseValid]
      infer_instance

set_option maxRecDepth 8192 in
private def block00 : Fin 816 → Entry :=
  ![(![0,1,2,3], .inl (1,0)),
    (![0,1,2,4], .inl (1,0)),
    (![0,1,2,5], .inl (1,0)),
    (![0,1,2,6], .inl (1,0)),
    (![0,1,2,7], .inl (1,0)),
    (![0,1,2,8], .inr none),
    (![0,1,2,9], .inl (0,1)),
    (![0,1,2,10], .inl (0,1)),
    (![0,1,2,11], .inl (0,1)),
    (![0,1,2,12], .inl (0,1)),
    (![0,1,2,13], .inl (0,1)),
    (![0,1,2,14], .inl (0,1)),
    (![0,1,2,15], .inl (0,1)),
    (![0,1,2,16], .inl (0,1)),
    (![0,1,2,17], .inl (1,0)),
    (![0,1,2,18], .inr none),
    (![0,1,3,4], .inl (1,0)),
    (![0,1,3,5], .inl (1,0)),
    (![0,1,3,6], .inl (1,0)),
    (![0,1,3,7], .inl (3,2)),
    (![0,1,3,8], .inl (0,1)),
    (![0,1,3,9], .inl (0,1)),
    (![0,1,3,10], .inl (0,1)),
    (![0,1,3,11], .inl (2,1)),
    (![0,1,3,12], .inl (2,0)),
    (![0,1,3,13], .inl (2,1)),
    (![0,1,3,14], .inl (0,1)),
    (![0,1,3,15], .inl (0,1)),
    (![0,1,3,16], .inl (0,1)),
    (![0,1,3,17], .inl (1,0)),
    (![0,1,3,18], .inl (1,0)),
    (![0,1,4,5], .inl (1,0)),
    (![0,1,4,6], .inl (3,2)),
    (![0,1,4,7], .inl (0,1)),
    (![0,1,4,8], .inl (0,1)),
    (![0,1,4,9], .inl (0,1)),
    (![0,1,4,10], .inl (0,1)),
    (![0,1,4,11], .inl (2,0)),
    (![0,1,4,12], .inl (2,0)),
    (![0,1,4,13], .inl (2,0)),
    (![0,1,4,14], .inr (some (false,1,34))),
    (![0,1,4,15], .inr (some (false,1,35))),
    (![0,1,4,16], .inl (0,1)),
    (![0,1,4,17], .inl (1,0)),
    (![0,1,4,18], .inl (1,0)),
    (![0,1,5,6], .inl (0,1)),
    (![0,1,5,7], .inl (0,1)),
    (![0,1,5,8], .inl (0,1)),
    (![0,1,5,9], .inl (0,1)),
    (![0,1,5,10], .inl (0,1)),
    (![0,1,5,11], .inl (2,0)),
    (![0,1,5,12], .inl (1,0)),
    (![0,1,5,13], .inl (1,0)),
    (![0,1,5,14], .inr (some (false,1,142))),
    (![0,1,5,15], .inr (some (false,1,143))),
    (![0,1,5,16], .inl (0,1)),
    (![0,1,5,17], .inl (1,0)),
    (![0,1,5,18], .inl (1,0)),
    (![0,1,6,7], .inl (0,1)),
    (![0,1,6,8], .inl (0,1)),
    (![0,1,6,9], .inl (0,1)),
    (![0,1,6,10], .inl (0,1)),
    (![0,1,6,11], .inl (2,0)),
    (![0,1,6,12], .inl (2,0)),
    (![0,1,6,13], .inl (2,0)),
    (![0,1,6,14], .inr (some (false,1,38))),
    (![0,1,6,15], .inr (some (false,1,39))),
    (![0,1,6,16], .inl (0,1)),
    (![0,1,6,17], .inl (1,0)),
    (![0,1,6,18], .inl (1,0)),
    (![0,1,7,8], .inl (0,1)),
    (![0,1,7,9], .inl (0,1)),
    (![0,1,7,10], .inl (0,1)),
    (![0,1,7,11], .inl (2,1)),
    (![0,1,7,12], .inl (2,0)),
    (![0,1,7,13], .inl (2,1)),
    (![0,1,7,14], .inl (0,1)),
    (![0,1,7,15], .inl (0,1)),
    (![0,1,7,16], .inl (0,1)),
    (![0,1,7,17], .inl (1,0)),
    (![0,1,7,18], .inl (1,0)),
    (![0,1,8,9], .inl (0,1)),
    (![0,1,8,10], .inl (0,1)),
    (![0,1,8,11], .inl (0,1)),
    (![0,1,8,12], .inl (0,1)),
    (![0,1,8,13], .inl (0,1)),
    (![0,1,8,14], .inl (0,1)),
    (![0,1,8,15], .inl (0,1)),
    (![0,1,8,16], .inl (0,1)),
    (![0,1,8,17], .inl (1,0)),
    (![0,1,8,18], .inr none),
    (![0,1,9,10], .inl (0,1)),
    (![0,1,9,11], .inl (0,1)),
    (![0,1,9,12], .inl (0,1)),
    (![0,1,9,13], .inl (0,1)),
    (![0,1,9,14], .inl (0,1)),
    (![0,1,9,15], .inl (2,1)),
    (![0,1,9,16], .inl (2,1)),
    (![0,1,9,17], .inl (1,0)),
    (![0,1,9,18], .inl (0,1)),
    (![0,1,10,11], .inl (0,1)),
    (![0,1,10,12], .inl (0,1)),
    (![0,1,10,13], .inl (0,1)),
    (![0,1,10,14], .inl (2,1)),
    (![0,1,10,15], .inl (2,0)),
    (![0,1,10,16], .inl (2,0)),
    (![0,1,10,17], .inl (1,2)),
    (![0,1,10,18], .inl (0,1)),
    (![0,1,11,12], .inl (0,1)),
    (![0,1,11,13], .inl (2,1)),
    (![0,1,11,14], .inl (2,0)),
    (![0,1,11,15], .inl (2,0)),
    (![0,1,11,16], .inl (1,0)),
    (![0,1,11,17], .inl (0,2)),
    (![0,1,11,18], .inl (0,1)),
    (![0,1,12,13], .inl (2,0)),
    (![0,1,12,14], .inl (2,0)),
    (![0,1,12,15], .inl (2,0)),
    (![0,1,12,16], .inl (1,0)),
    (![0,1,12,17], .inl (0,1)),
    (![0,1,12,18], .inl (0,1)),
    (![0,1,13,14], .inl (2,0)),
    (![0,1,13,15], .inl (2,0)),
    (![0,1,13,16], .inl (1,0)),
    (![0,1,13,17], .inl (0,1)),
    (![0,1,13,18], .inl (0,1)),
    (![0,1,14,15], .inl (2,0)),
    (![0,1,14,16], .inl (1,0)),
    (![0,1,14,17], .inr (some (true,1,5))),
    (![0,1,14,18], .inl (0,1)),
    (![0,1,15,16], .inl (1,3)),
    (![0,1,15,17], .inr (some (true,1,29))),
    (![0,1,15,18], .inl (0,1)),
    (![0,1,16,17], .inl (1,0)),
    (![0,1,16,18], .inl (0,1)),
    (![0,1,17,18], .inl (1,0)),
    (![0,2,3,4], .inl (1,2)),
    (![0,2,3,5], .inl (1,2)),
    (![0,2,3,6], .inl (1,2)),
    (![0,2,3,7], .inl (3,2)),
    (![0,2,3,8], .inl (3,1)),
    (![0,2,3,9], .inl (2,1)),
    (![0,2,3,10], .inl (2,0)),
    (![0,2,3,11], .inl (2,0)),
    (![0,2,3,12], .inl (2,0)),
    (![0,2,3,13], .inl (2,0)),
    (![0,2,3,14], .inl (0,1)),
    (![0,2,3,15], .inl (0,1)),
    (![0,2,3,16], .inl (0,1)),
    (![0,2,3,17], .inl (1,2)),
    (![0,2,3,18], .inl (1,0)),
    (![0,2,4,5], .inl (1,2)),
    (![0,2,4,6], .inl (3,2)),
    (![0,2,4,7], .inl (3,1)),
    (![0,2,4,8], .inl (3,1)),
    (![0,2,4,9], .inl (2,1)),
    (![0,2,4,10], .inl (2,0)),
    (![0,2,4,11], .inl (2,0)),
    (![0,2,4,12], .inl (2,0)),
    (![0,2,4,13], .inl (2,0)),
    (![0,2,4,14], .inr (some (false,2,34))),
    (![0,2,4,15], .inr (some (false,2,35))),
    (![0,2,4,16], .inl (0,1)),
    (![0,2,4,17], .inl (1,2)),
    (![0,2,4,18], .inl (1,0)),
    (![0,2,5,6], .inl (3,1)),
    (![0,2,5,7], .inl (3,1)),
    (![0,2,5,8], .inl (3,1)),
    (![0,2,5,9], .inl (2,1)),
    (![0,2,5,10], .inl (2,0)),
    (![0,2,5,11], .inl (2,0)),
    (![0,2,5,12], .inl (1,0)),
    (![0,2,5,13], .inl (1,0)),
    (![0,2,5,14], .inr (some (false,1,144))),
    (![0,2,5,15], .inr (some (false,1,145))),
    (![0,2,5,16], .inl (0,1)),
    (![0,2,5,17], .inl (1,2)),
    (![0,2,5,18], .inl (1,0)),
    (![0,2,6,7], .inl (3,1)),
    (![0,2,6,8], .inl (3,1)),
    (![0,2,6,9], .inl (2,1)),
    (![0,2,6,10], .inl (2,0)),
    (![0,2,6,11], .inl (2,0)),
    (![0,2,6,12], .inl (2,0)),
    (![0,2,6,13], .inl (2,0)),
    (![0,2,6,14], .inr (some (false,2,38))),
    (![0,2,6,15], .inr (some (false,2,39))),
    (![0,2,6,16], .inl (0,1)),
    (![0,2,6,17], .inl (1,2)),
    (![0,2,6,18], .inl (1,0)),
    (![0,2,7,8], .inl (3,1)),
    (![0,2,7,9], .inl (2,1)),
    (![0,2,7,10], .inl (2,0)),
    (![0,2,7,11], .inl (2,0)),
    (![0,2,7,12], .inl (2,0)),
    (![0,2,7,13], .inl (2,0)),
    (![0,2,7,14], .inl (0,1)),
    (![0,2,7,15], .inl (0,1)),
    (![0,2,7,16], .inl (0,1)),
    (![0,2,7,17], .inl (1,2)),
    (![0,2,7,18], .inl (1,0)),
    (![0,2,8,9], .inl (2,1)),
    (![0,2,8,10], .inl (2,1)),
    (![0,2,8,11], .inl (2,1)),
    (![0,2,8,12], .inl (2,1)),
    (![0,2,8,13], .inl (2,1)),
    (![0,2,8,14], .inl (2,1)),
    (![0,2,8,15], .inl (2,1)),
    (![0,2,8,16], .inl (2,1)),
    (![0,2,8,17], .inl (1,2)),
    (![0,2,8,18], .inr none),
    (![0,2,9,10], .inl (0,1)),
    (![0,2,9,11], .inl (0,1)),
    (![0,2,9,12], .inl (0,1)),
    (![0,2,9,13], .inl (0,1)),
    (![0,2,9,14], .inl (2,0)),
    (![0,2,9,15], .inl (2,0)),
    (![0,2,9,16], .inl (2,0)),
    (![0,2,9,17], .inl (1,2)),
    (![0,2,9,18], .inl (0,1)),
    (![0,2,10,11], .inl (0,1)),
    (![0,2,10,12], .inl (0,1)),
    (![0,2,10,13], .inl (2,1)),
    (![0,2,10,14], .inl (2,0)),
    (![0,2,10,15], .inl (2,0)),
    (![0,2,10,16], .inl (2,0)),
    (![0,2,10,17], .inl (0,2)),
    (![0,2,10,18], .inl (0,1)),
    (![0,2,11,12], .inl (0,1)),
    (![0,2,11,13], .inl (2,0)),
    (![0,2,11,14], .inl (2,0)),
    (![0,2,11,15], .inl (2,0)),
    (![0,2,11,16], .inl (1,0)),
    (![0,2,11,17], .inl (0,2)),
    (![0,2,11,18], .inl (0,1)),
    (![0,2,12,13], .inl (2,0)),
    (![0,2,12,14], .inl (2,0)),
    (![0,2,12,15], .inl (2,0)),
    (![0,2,12,16], .inl (1,0)),
    (![0,2,12,17], .inl (0,1)),
    (![0,2,12,18], .inl (0,1)),
    (![0,2,13,14], .inl (2,0)),
    (![0,2,13,15], .inl (2,0)),
    (![0,2,13,16], .inl (1,0)),
    (![0,2,13,17], .inl (0,1)),
    (![0,2,13,18], .inl (0,1)),
    (![0,2,14,15], .inl (2,0)),
    (![0,2,14,16], .inl (1,3)),
    (![0,2,14,17], .inr (some (true,1,30))),
    (![0,2,14,18], .inl (0,1)),
    (![0,2,15,16], .inl (0,3)),
    (![0,2,15,17], .inr (some (true,1,31))),
    (![0,2,15,18], .inl (0,1)),
    (![0,2,16,17], .inl (1,0)),
    (![0,2,16,18], .inl (0,1)),
    (![0,2,17,18], .inl (1,0)),
    (![0,3,4,5], .inl (1,2)),
    (![0,3,4,6], .inl (3,2)),
    (![0,3,4,7], .inl (3,1)),
    (![0,3,4,8], .inl (2,1)),
    (![0,3,4,9], .inl (2,1)),
    (![0,3,4,10], .inl (2,0)),
    (![0,3,4,11], .inl (2,0)),
    (![0,3,4,12], .inl (2,0)),
    (![0,3,4,13], .inl (2,0)),
    (![0,3,4,14], .inr (some (false,1,34))),
    (![0,3,4,15], .inr (some (false,1,35))),
    (![0,3,4,16], .inl (0,1)),
    (![0,3,4,17], .inl (1,2)),
    (![0,3,4,18], .inl (1,0)),
    (![0,3,5,6], .inl (3,1)),
    (![0,3,5,7], .inl (3,1)),
    (![0,3,5,8], .inl (2,1)),
    (![0,3,5,9], .inl (2,1)),
    (![0,3,5,10], .inl (2,0)),
    (![0,3,5,11], .inl (2,0)),
    (![0,3,5,12], .inl (1,0)),
    (![0,3,5,13], .inl (1,0)),
    (![0,3,5,14], .inr (some (false,1,146))),
    (![0,3,5,15], .inr (some (false,1,147))),
    (![0,3,5,16], .inl (0,1)),
    (![0,3,5,17], .inl (1,2)),
    (![0,3,5,18], .inl (1,0)),
    (![0,3,6,7], .inl (3,1)),
    (![0,3,6,8], .inl (2,1)),
    (![0,3,6,9], .inl (2,1)),
    (![0,3,6,10], .inl (2,0)),
    (![0,3,6,11], .inl (2,0)),
    (![0,3,6,12], .inl (2,0)),
    (![0,3,6,13], .inl (2,0)),
    (![0,3,6,14], .inr (some (false,1,38))),
    (![0,3,6,15], .inr (some (false,1,39))),
    (![0,3,6,16], .inl (0,1)),
    (![0,3,6,17], .inl (1,2)),
    (![0,3,6,18], .inl (1,0)),
    (![0,3,7,8], .inl (2,1)),
    (![0,3,7,9], .inl (2,1)),
    (![0,3,7,10], .inl (2,1)),
    (![0,3,7,11], .inl (2,1)),
    (![0,3,7,12], .inl (2,1)),
    (![0,3,7,13], .inl (2,1)),
    (![0,3,7,14], .inl (2,1)),
    (![0,3,7,15], .inl (2,1)),
    (![0,3,7,16], .inl (2,1)),
    (![0,3,7,17], .inl (1,2)),
    (![0,3,7,18], .inl (1,2)),
    (![0,3,8,9], .inl (2,1)),
    (![0,3,8,10], .inl (0,1)),
    (![0,3,8,11], .inl (0,1)),
    (![0,3,8,12], .inl (0,1)),
    (![0,3,8,13], .inl (0,1)),
    (![0,3,8,14], .inl (2,0)),
    (![0,3,8,15], .inl (2,0)),
    (![0,3,8,16], .inl (2,0)),
    (![0,3,8,17], .inl (1,2)),
    (![0,3,8,18], .inl (0,2)),
    (![0,3,9,10], .inl (0,1)),
    (![0,3,9,11], .inl (0,1)),
    (![0,3,9,12], .inl (0,1)),
    (![0,3,9,13], .inl (0,1)),
    (![0,3,9,14], .inl (2,0)),
    (![0,3,9,15], .inl (2,0)),
    (![0,3,9,16], .inl (2,0)),
    (![0,3,9,17], .inl (1,2)),
    (![0,3,9,18], .inl (0,1)),
    (![0,3,10,11], .inl (0,1)),
    (![0,3,10,12], .inl (0,1)),
    (![0,3,10,13], .inl (0,1)),
    (![0,3,10,14], .inl (2,0)),
    (![0,3,10,15], .inl (2,0)),
    (![0,3,10,16], .inl (2,0)),
    (![0,3,10,17], .inl (0,2)),
    (![0,3,10,18], .inl (0,1)),
    (![0,3,11,12], .inl (0,1)),
    (![0,3,11,13], .inl (2,1)),
    (![0,3,11,14], .inl (2,0)),
    (![0,3,11,15], .inl (2,0)),
    (![0,3,11,16], .inl (1,0)),
    (![0,3,11,17], .inl (0,2)),
    (![0,3,11,18], .inl (0,1)),
    (![0,3,12,13], .inl (2,0)),
    (![0,3,12,14], .inl (2,0)),
    (![0,3,12,15], .inl (2,0)),
    (![0,3,12,16], .inl (1,0)),
    (![0,3,12,17], .inl (0,1)),
    (![0,3,12,18], .inl (0,1)),
    (![0,3,13,14], .inl (2,0)),
    (![0,3,13,15], .inl (2,0)),
    (![0,3,13,16], .inl (1,0)),
    (![0,3,13,17], .inl (0,1)),
    (![0,3,13,18], .inl (0,1)),
    (![0,3,14,15], .inl (2,0)),
    (![0,3,14,16], .inl (0,3)),
    (![0,3,14,17], .inr (some (true,1,32))),
    (![0,3,14,18], .inl (0,1)),
    (![0,3,15,16], .inl (0,3)),
    (![0,3,15,17], .inr (some (true,1,33))),
    (![0,3,15,18], .inr (some (true,1,10))),
    (![0,3,16,17], .inl (1,0)),
    (![0,3,16,18], .inl (0,1)),
    (![0,3,17,18], .inl (1,0)),
    (![0,4,5,6], .inl (3,1)),
    (![0,4,5,7], .inl (2,1)),
    (![0,4,5,8], .inl (2,1)),
    (![0,4,5,9], .inl (2,1)),
    (![0,4,5,10], .inl (2,0)),
    (![0,4,5,11], .inl (2,0)),
    (![0,4,5,12], .inl (1,0)),
    (![0,4,5,13], .inl (1,0)),
    (![0,4,5,14], .inr (some (false,1,34))),
    (![0,4,5,15], .inr (some (false,1,35))),
    (![0,4,5,16], .inl (0,1)),
    (![0,4,5,17], .inl (1,2)),
    (![0,4,5,18], .inl (1,0)),
    (![0,4,6,7], .inl (2,1)),
    (![0,4,6,8], .inl (2,1)),
    (![0,4,6,9], .inl (2,1)),
    (![0,4,6,10], .inl (2,1)),
    (![0,4,6,11], .inl (2,1)),
    (![0,4,6,12], .inr none),
    (![0,4,6,13], .inr none),
    (![0,4,6,14], .inr none),
    (![0,4,6,15], .inr none),
    (![0,4,6,16], .inl (2,1)),
    (![0,4,6,17], .inl (1,2)),
    (![0,4,6,18], .inl (1,2)),
    (![0,4,7,8], .inl (2,1)),
    (![0,4,7,9], .inl (2,1)),
    (![0,4,7,10], .inl (0,1)),
    (![0,4,7,11], .inl (0,1)),
    (![0,4,7,12], .inl (0,1)),
    (![0,4,7,13], .inl (0,1)),
    (![0,4,7,14], .inr (some (true,1,34))),
    (![0,4,7,15], .inr (some (true,1,35))),
    (![0,4,7,16], .inl (2,0)),
    (![0,4,7,17], .inl (1,2)),
    (![0,4,7,18], .inl (0,2)),
    (![0,4,8,9], .inl (2,1)),
    (![0,4,8,10], .inl (0,1)),
    (![0,4,8,11], .inl (0,1)),
    (![0,4,8,12], .inl (0,1)),
    (![0,4,8,13], .inl (0,1)),
    (![0,4,8,14], .inr (some (true,2,34))),
    (![0,4,8,15], .inr (some (true,2,35))),
    (![0,4,8,16], .inl (2,0)),
    (![0,4,8,17], .inl (1,2)),
    (![0,4,8,18], .inl (0,2)),
    (![0,4,9,10], .inl (0,1)),
    (![0,4,9,11], .inl (0,1)),
    (![0,4,9,12], .inl (0,1)),
    (![0,4,9,13], .inl (0,1)),
    (![0,4,9,14], .inr (some (true,3,34))),
    (![0,4,9,15], .inr (some (true,3,35))),
    (![0,4,9,16], .inl (2,0)),
    (![0,4,9,17], .inl (1,2)),
    (![0,4,9,18], .inl (0,1)),
    (![0,4,10,11], .inl (0,1)),
    (![0,4,10,12], .inl (0,1)),
    (![0,4,10,13], .inl (0,1)),
    (![0,4,10,14], .inr (some (true,2,34))),
    (![0,4,10,15], .inr (some (true,2,35))),
    (![0,4,10,16], .inl (2,0)),
    (![0,4,10,17], .inl (0,2)),
    (![0,4,10,18], .inl (0,1)),
    (![0,4,11,12], .inl (0,1)),
    (![0,4,11,13], .inl (0,1)),
    (![0,4,11,14], .inr (some (true,1,34))),
    (![0,4,11,15], .inr (some (true,1,35))),
    (![0,4,11,16], .inl (1,0)),
    (![0,4,11,17], .inl (0,2)),
    (![0,4,11,18], .inl (0,1)),
    (![0,4,12,13], .inr none),
    (![0,4,12,14], .inr none),
    (![0,4,12,15], .inr none),
    (![0,4,12,16], .inl (1,0)),
    (![0,4,12,17], .inl (0,1)),
    (![0,4,12,18], .inl (0,1)),
    (![0,4,13,14], .inr none),
    (![0,4,13,15], .inr none),
    (![0,4,13,16], .inl (1,0)),
    (![0,4,13,17], .inl (0,1)),
    (![0,4,13,18], .inl (0,1)),
    (![0,4,14,15], .inr none),
    (![0,4,14,16], .inr (some (false,2,34))),
    (![0,4,14,17], .inr (some (true,1,34))),
    (![0,4,14,18], .inr (some (true,1,34))),
    (![0,4,15,16], .inr (some (false,2,35))),
    (![0,4,15,17], .inr (some (true,1,35))),
    (![0,4,15,18], .inr (some (true,1,35))),
    (![0,4,16,17], .inl (1,0)),
    (![0,4,16,18], .inl (0,1)),
    (![0,4,17,18], .inl (1,0)),
    (![0,5,6,7], .inl (2,1)),
    (![0,5,6,8], .inl (2,1)),
    (![0,5,6,9], .inl (2,1)),
    (![0,5,6,10], .inl (0,1)),
    (![0,5,6,11], .inl (0,1)),
    (![0,5,6,12], .inl (0,2)),
    (![0,5,6,13], .inl (0,2)),
    (![0,5,6,14], .inr (some (true,1,38))),
    (![0,5,6,15], .inr (some (true,1,39))),
    (![0,5,6,16], .inl (2,0)),
    (![0,5,6,17], .inl (1,2)),
    (![0,5,6,18], .inl (0,2)),
    (![0,5,7,8], .inl (2,1)),
    (![0,5,7,9], .inl (2,1)),
    (![0,5,7,10], .inl (0,1)),
    (![0,5,7,11], .inl (0,1)),
    (![0,5,7,12], .inl (0,1)),
    (![0,5,7,13], .inl (0,1)),
    (![0,5,7,14], .inr (some (true,1,148))),
    (![0,5,7,15], .inr (some (true,1,149))),
    (![0,5,7,16], .inl (2,0)),
    (![0,5,7,17], .inl (1,2)),
    (![0,5,7,18], .inl (0,2)),
    (![0,5,8,9], .inl (2,1)),
    (![0,5,8,10], .inl (0,1)),
    (![0,5,8,11], .inl (0,1)),
    (![0,5,8,12], .inl (0,1)),
    (![0,5,8,13], .inl (0,1)),
    (![0,5,8,14], .inr (some (true,1,150))),
    (![0,5,8,15], .inr (some (true,1,151))),
    (![0,5,8,16], .inl (2,0)),
    (![0,5,8,17], .inl (1,2)),
    (![0,5,8,18], .inl (0,2)),
    (![0,5,9,10], .inl (0,1)),
    (![0,5,9,11], .inl (0,1)),
    (![0,5,9,12], .inl (0,1)),
    (![0,5,9,13], .inl (0,1)),
    (![0,5,9,14], .inr (some (true,1,152))),
    (![0,5,9,15], .inr (some (true,1,153))),
    (![0,5,9,16], .inl (2,0)),
    (![0,5,9,17], .inl (1,2)),
    (![0,5,9,18], .inl (0,1)),
    (![0,5,10,11], .inl (0,1)),
    (![0,5,10,12], .inl (0,1)),
    (![0,5,10,13], .inl (0,1)),
    (![0,5,10,14], .inr (some (true,1,154))),
    (![0,5,10,15], .inr (some (true,1,155))),
    (![0,5,10,16], .inl (2,0)),
    (![0,5,10,17], .inl (0,2)),
    (![0,5,10,18], .inl (0,1)),
    (![0,5,11,12], .inl (0,1)),
    (![0,5,11,13], .inl (0,1)),
    (![0,5,11,14], .inr (some (true,1,99))),
    (![0,5,11,15], .inr (some (true,1,156))),
    (![0,5,11,16], .inl (1,0)),
    (![0,5,11,17], .inl (0,2)),
    (![0,5,11,18], .inl (0,1)),
    (![0,5,12,13], .inl (0,2)),
    (![0,5,12,14], .inl (0,2)),
    (![0,5,12,15], .inl (0,2)),
    (![0,5,12,16], .inl (1,0)),
    (![0,5,12,17], .inl (0,1)),
    (![0,5,12,18], .inl (0,1)),
    (![0,5,13,14], .inl (0,2)),
    (![0,5,13,15], .inl (0,2)),
    (![0,5,13,16], .inl (1,0)),
    (![0,5,13,17], .inl (0,1)),
    (![0,5,13,18], .inl (3,1)),
    (![0,5,14,15], .inl (0,2)),
    (![0,5,14,16], .inr (some (false,1,36))),
    (![0,5,14,17], .inl (3,0)),
    (![0,5,14,18], .inl (3,0)),
    (![0,5,15,16], .inr (some (false,1,37))),
    (![0,5,15,17], .inl (3,0)),
    (![0,5,15,18], .inl (3,0)),
    (![0,5,16,17], .inl (1,0)),
    (![0,5,16,18], .inl (0,1)),
    (![0,5,17,18], .inl (1,0)),
    (![0,6,7,8], .inl (2,1)),
    (![0,6,7,9], .inl (2,1)),
    (![0,6,7,10], .inl (0,1)),
    (![0,6,7,11], .inl (0,1)),
    (![0,6,7,12], .inl (0,1)),
    (![0,6,7,13], .inl (0,1)),
    (![0,6,7,14], .inr (some (true,1,38))),
    (![0,6,7,15], .inr (some (true,1,39))),
    (![0,6,7,16], .inl (2,0)),
    (![0,6,7,17], .inl (1,2)),
    (![0,6,7,18], .inl (0,2)),
    (![0,6,8,9], .inl (2,1)),
    (![0,6,8,10], .inl (0,1)),
    (![0,6,8,11], .inl (0,1)),
    (![0,6,8,12], .inl (0,1)),
    (![0,6,8,13], .inl (0,1)),
    (![0,6,8,14], .inr (some (true,2,38))),
    (![0,6,8,15], .inr (some (true,2,39))),
    (![0,6,8,16], .inl (2,0)),
    (![0,6,8,17], .inl (1,2)),
    (![0,6,8,18], .inl (0,2)),
    (![0,6,9,10], .inl (0,1)),
    (![0,6,9,11], .inl (0,1)),
    (![0,6,9,12], .inl (0,1)),
    (![0,6,9,13], .inl (0,1)),
    (![0,6,9,14], .inr (some (true,3,38))),
    (![0,6,9,15], .inr (some (true,3,39))),
    (![0,6,9,16], .inl (2,0)),
    (![0,6,9,17], .inl (1,2)),
    (![0,6,9,18], .inl (0,1)),
    (![0,6,10,11], .inl (0,1)),
    (![0,6,10,12], .inl (0,1)),
    (![0,6,10,13], .inl (0,1)),
    (![0,6,10,14], .inr (some (true,2,38))),
    (![0,6,10,15], .inr (some (true,2,39))),
    (![0,6,10,16], .inl (2,0)),
    (![0,6,10,17], .inl (0,2)),
    (![0,6,10,18], .inl (0,1)),
    (![0,6,11,12], .inl (0,1)),
    (![0,6,11,13], .inl (0,1)),
    (![0,6,11,14], .inr (some (true,1,38))),
    (![0,6,11,15], .inr (some (true,1,39))),
    (![0,6,11,16], .inl (1,0)),
    (![0,6,11,17], .inl (0,2)),
    (![0,6,11,18], .inl (0,1)),
    (![0,6,12,13], .inr none),
    (![0,6,12,14], .inr none),
    (![0,6,12,15], .inr none),
    (![0,6,12,16], .inl (1,0)),
    (![0,6,12,17], .inl (0,1)),
    (![0,6,12,18], .inl (0,1)),
    (![0,6,13,14], .inr none),
    (![0,6,13,15], .inr none),
    (![0,6,13,16], .inl (1,0)),
    (![0,6,13,17], .inl (0,1)),
    (![0,6,13,18], .inl (0,1)),
    (![0,6,14,15], .inr none),
    (![0,6,14,16], .inr (some (false,2,38))),
    (![0,6,14,17], .inr (some (true,1,38))),
    (![0,6,14,18], .inr (some (true,1,38))),
    (![0,6,15,16], .inr (some (false,2,39))),
    (![0,6,15,17], .inr (some (true,1,39))),
    (![0,6,15,18], .inr (some (true,1,39))),
    (![0,6,16,17], .inl (1,0)),
    (![0,6,16,18], .inl (0,1)),
    (![0,6,17,18], .inl (1,0)),
    (![0,7,8,9], .inl (2,1)),
    (![0,7,8,10], .inl (0,1)),
    (![0,7,8,11], .inl (0,1)),
    (![0,7,8,12], .inl (0,1)),
    (![0,7,8,13], .inl (0,1)),
    (![0,7,8,14], .inl (2,0)),
    (![0,7,8,15], .inl (2,0)),
    (![0,7,8,16], .inl (2,0)),
    (![0,7,8,17], .inl (1,2)),
    (![0,7,8,18], .inl (0,2)),
    (![0,7,9,10], .inl (0,1)),
    (![0,7,9,11], .inl (0,1)),
    (![0,7,9,12], .inl (0,1)),
    (![0,7,9,13], .inl (0,1)),
    (![0,7,9,14], .inl (2,0)),
    (![0,7,9,15], .inl (2,0)),
    (![0,7,9,16], .inl (2,0)),
    (![0,7,9,17], .inl (1,2)),
    (![0,7,9,18], .inl (0,1)),
    (![0,7,10,11], .inl (0,1)),
    (![0,7,10,12], .inl (0,1)),
    (![0,7,10,13], .inl (0,1)),
    (![0,7,10,14], .inl (2,0)),
    (![0,7,10,15], .inl (2,0)),
    (![0,7,10,16], .inl (2,0)),
    (![0,7,10,17], .inl (0,2)),
    (![0,7,10,18], .inl (0,1)),
    (![0,7,11,12], .inl (0,1)),
    (![0,7,11,13], .inl (2,1)),
    (![0,7,11,14], .inl (2,0)),
    (![0,7,11,15], .inl (2,0)),
    (![0,7,11,16], .inl (1,0)),
    (![0,7,11,17], .inl (0,2)),
    (![0,7,11,18], .inl (0,1)),
    (![0,7,12,13], .inl (2,0)),
    (![0,7,12,14], .inl (2,0)),
    (![0,7,12,15], .inl (2,0)),
    (![0,7,12,16], .inl (1,0)),
    (![0,7,12,17], .inl (0,1)),
    (![0,7,12,18], .inl (0,1)),
    (![0,7,13,14], .inl (2,0)),
    (![0,7,13,15], .inl (2,0)),
    (![0,7,13,16], .inl (1,0)),
    (![0,7,13,17], .inl (0,1)),
    (![0,7,13,18], .inl (0,1)),
    (![0,7,14,15], .inl (2,0)),
    (![0,7,14,16], .inl (0,3)),
    (![0,7,14,17], .inr (some (true,1,40))),
    (![0,7,14,18], .inl (0,1)),
    (![0,7,15,16], .inl (0,3)),
    (![0,7,15,17], .inr (some (true,1,41))),
    (![0,7,15,18], .inr (some (true,1,18))),
    (![0,7,16,17], .inl (1,0)),
    (![0,7,16,18], .inl (0,1)),
    (![0,7,17,18], .inl (1,0)),
    (![0,8,9,10], .inl (0,1)),
    (![0,8,9,11], .inl (0,1)),
    (![0,8,9,12], .inl (0,1)),
    (![0,8,9,13], .inl (0,1)),
    (![0,8,9,14], .inl (2,0)),
    (![0,8,9,15], .inl (2,0)),
    (![0,8,9,16], .inl (2,0)),
    (![0,8,9,17], .inl (1,2)),
    (![0,8,9,18], .inl (0,1)),
    (![0,8,10,11], .inl (0,1)),
    (![0,8,10,12], .inl (0,1)),
    (![0,8,10,13], .inl (2,1)),
    (![0,8,10,14], .inl (2,0)),
    (![0,8,10,15], .inl (2,0)),
    (![0,8,10,16], .inl (2,0)),
    (![0,8,10,17], .inl (0,2)),
    (![0,8,10,18], .inl (0,1)),
    (![0,8,11,12], .inl (0,1)),
    (![0,8,11,13], .inl (2,0)),
    (![0,8,11,14], .inl (2,0)),
    (![0,8,11,15], .inl (2,0)),
    (![0,8,11,16], .inl (1,0)),
    (![0,8,11,17], .inl (0,2)),
    (![0,8,11,18], .inl (0,1)),
    (![0,8,12,13], .inl (2,0)),
    (![0,8,12,14], .inl (2,0)),
    (![0,8,12,15], .inl (2,0)),
    (![0,8,12,16], .inl (1,0)),
    (![0,8,12,17], .inl (0,1)),
    (![0,8,12,18], .inl (0,1)),
    (![0,8,13,14], .inl (2,0)),
    (![0,8,13,15], .inl (2,0)),
    (![0,8,13,16], .inl (1,0)),
    (![0,8,13,17], .inl (0,1)),
    (![0,8,13,18], .inl (0,1)),
    (![0,8,14,15], .inl (2,0)),
    (![0,8,14,16], .inl (1,3)),
    (![0,8,14,17], .inr (some (true,1,42))),
    (![0,8,14,18], .inl (0,1)),
    (![0,8,15,16], .inl (0,3)),
    (![0,8,15,17], .inr (some (true,1,43))),
    (![0,8,15,18], .inl (0,1)),
    (![0,8,16,17], .inl (1,0)),
    (![0,8,16,18], .inl (0,1)),
    (![0,8,17,18], .inl (1,0)),
    (![0,9,10,11], .inl (2,1)),
    (![0,9,10,12], .inl (2,1)),
    (![0,9,10,13], .inl (2,0)),
    (![0,9,10,14], .inl (2,0)),
    (![0,9,10,15], .inl (2,0)),
    (![0,9,10,16], .inl (2,0)),
    (![0,9,10,17], .inl (0,2)),
    (![0,9,10,18], .inl (0,1)),
    (![0,9,11,12], .inl (2,1)),
    (![0,9,11,13], .inl (2,0)),
    (![0,9,11,14], .inl (2,0)),
    (![0,9,11,15], .inl (2,0)),
    (![0,9,11,16], .inl (1,0)),
    (![0,9,11,17], .inl (0,2)),
    (![0,9,11,18], .inl (0,1)),
    (![0,9,12,13], .inl (2,0)),
    (![0,9,12,14], .inl (2,0)),
    (![0,9,12,15], .inl (2,0)),
    (![0,9,12,16], .inl (1,0)),
    (![0,9,12,17], .inl (0,1)),
    (![0,9,12,18], .inl (0,1)),
    (![0,9,13,14], .inl (2,0)),
    (![0,9,13,15], .inl (2,0)),
    (![0,9,13,16], .inl (1,0)),
    (![0,9,13,17], .inl (0,1)),
    (![0,9,13,18], .inl (0,1)),
    (![0,9,14,15], .inl (2,0)),
    (![0,9,14,16], .inl (1,0)),
    (![0,9,14,17], .inr (some (true,1,44))),
    (![0,9,14,18], .inl (0,1)),
    (![0,9,15,16], .inl (1,3)),
    (![0,9,15,17], .inr (some (true,1,45))),
    (![0,9,15,18], .inl (0,1)),
    (![0,9,16,17], .inl (1,0)),
    (![0,9,16,18], .inl (0,1)),
    (![0,9,17,18], .inl (1,0)),
    (![0,10,11,12], .inl (2,1)),
    (![0,10,11,13], .inl (2,0)),
    (![0,10,11,14], .inl (2,0)),
    (![0,10,11,15], .inl (2,0)),
    (![0,10,11,16], .inl (1,0)),
    (![0,10,11,17], .inl (0,2)),
    (![0,10,11,18], .inl (0,1)),
    (![0,10,12,13], .inl (2,0)),
    (![0,10,12,14], .inl (2,0)),
    (![0,10,12,15], .inl (2,0)),
    (![0,10,12,16], .inl (1,0)),
    (![0,10,12,17], .inl (0,1)),
    (![0,10,12,18], .inl (0,1)),
    (![0,10,13,14], .inl (2,0)),
    (![0,10,13,15], .inl (2,0)),
    (![0,10,13,16], .inl (1,0)),
    (![0,10,13,17], .inl (0,1)),
    (![0,10,13,18], .inl (0,1)),
    (![0,10,14,15], .inl (2,0)),
    (![0,10,14,16], .inl (1,0)),
    (![0,10,14,17], .inr (some (true,1,23))),
    (![0,10,14,18], .inl (0,1)),
    (![0,10,15,16], .inl (1,0)),
    (![0,10,15,17], .inr (some (true,1,46))),
    (![0,10,15,18], .inl (0,1)),
    (![0,10,16,17], .inl (1,0)),
    (![0,10,16,18], .inl (0,1)),
    (![0,10,17,18], .inl (1,0)),
    (![0,11,12,13], .inl (2,0)),
    (![0,11,12,14], .inl (2,0)),
    (![0,11,12,15], .inl (2,0)),
    (![0,11,12,16], .inl (1,0)),
    (![0,11,12,17], .inl (0,1)),
    (![0,11,12,18], .inl (0,1)),
    (![0,11,13,14], .inl (2,0)),
    (![0,11,13,15], .inl (2,0)),
    (![0,11,13,16], .inl (1,0)),
    (![0,11,13,17], .inl (0,1)),
    (![0,11,13,18], .inl (0,1)),
    (![0,11,14,15], .inl (2,0)),
    (![0,11,14,16], .inl (1,0)),
    (![0,11,14,17], .inl (0,1)),
    (![0,11,14,18], .inl (0,1)),
    (![0,11,15,16], .inl (1,0)),
    (![0,11,15,17], .inl (0,1)),
    (![0,11,15,18], .inl (0,1)),
    (![0,11,16,17], .inl (1,0)),
    (![0,11,16,18], .inl (2,1)),
    (![0,11,17,18], .inl (1,0)),
    (![0,12,13,14], .inr none),
    (![0,12,13,15], .inr none),
    (![0,12,13,16], .inl (1,0)),
    (![0,12,13,17], .inl (0,1)),
    (![0,12,13,18], .inl (0,1)),
    (![0,12,14,15], .inr none),
    (![0,12,14,16], .inl (1,0)),
    (![0,12,14,17], .inl (0,1)),
    (![0,12,14,18], .inl (0,1)),
    (![0,12,15,16], .inl (1,0)),
    (![0,12,15,17], .inl (0,1)),
    (![0,12,15,18], .inl (0,1)),
    (![0,12,16,17], .inl (1,0)),
    (![0,12,16,18], .inl (2,0)),
    (![0,12,17,18], .inl (1,3)),
    (![0,13,14,15], .inr none),
    (![0,13,14,16], .inl (1,0)),
    (![0,13,14,17], .inl (0,1)),
    (![0,13,14,18], .inl (0,1)),
    (![0,13,15,16], .inl (1,0)),
    (![0,13,15,17], .inl (0,1)),
    (![0,13,15,18], .inl (0,1)),
    (![0,13,16,17], .inr (some (false,1,0))),
    (![0,13,16,18], .inl (2,0)),
    (![0,13,17,18], .inl (0,3)),
    (![0,14,15,16], .inl (1,0)),
    (![0,14,15,17], .inl (0,1)),
    (![0,14,15,18], .inl (0,1)),
    (![0,14,16,17], .inr (some (false,1,3))),
    (![0,14,16,18], .inl (2,0)),
    (![0,14,17,18], .inl (0,3)),
    (![0,15,16,17], .inr (some (false,1,4))),
    (![0,15,16,18], .inl (2,0)),
    (![0,15,17,18], .inl (0,3)),
    (![0,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid00 : ∀ k : Fin 816, CaseValid (block00 k).1 (block00 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align00 : (List.finRange 816).map (fun k => (block00 k).1) = fourTuples 0 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block01 : Fin 680 → Entry :=
  ![(![1,2,3,4], .inl (1,2)),
    (![1,2,3,5], .inl (1,2)),
    (![1,2,3,6], .inl (1,2)),
    (![1,2,3,7], .inl (3,2)),
    (![1,2,3,8], .inl (3,1)),
    (![1,2,3,9], .inl (2,1)),
    (![1,2,3,10], .inl (2,0)),
    (![1,2,3,11], .inl (2,0)),
    (![1,2,3,12], .inl (1,0)),
    (![1,2,3,13], .inl (2,0)),
    (![1,2,3,14], .inl (0,1)),
    (![1,2,3,15], .inl (0,1)),
    (![1,2,3,16], .inl (0,1)),
    (![1,2,3,17], .inl (1,2)),
    (![1,2,3,18], .inl (1,0)),
    (![1,2,4,5], .inl (1,2)),
    (![1,2,4,6], .inl (3,2)),
    (![1,2,4,7], .inl (3,1)),
    (![1,2,4,8], .inl (3,1)),
    (![1,2,4,9], .inl (2,1)),
    (![1,2,4,10], .inl (2,0)),
    (![1,2,4,11], .inl (1,0)),
    (![1,2,4,12], .inl (1,0)),
    (![1,2,4,13], .inl (1,0)),
    (![1,2,4,14], .inl (0,1)),
    (![1,2,4,15], .inl (0,1)),
    (![1,2,4,16], .inl (0,1)),
    (![1,2,4,17], .inl (1,2)),
    (![1,2,4,18], .inl (1,0)),
    (![1,2,5,6], .inl (3,1)),
    (![1,2,5,7], .inl (3,1)),
    (![1,2,5,8], .inl (3,1)),
    (![1,2,5,9], .inl (2,1)),
    (![1,2,5,10], .inl (2,0)),
    (![1,2,5,11], .inl (1,0)),
    (![1,2,5,12], .inl (1,0)),
    (![1,2,5,13], .inl (1,0)),
    (![1,2,5,14], .inl (0,1)),
    (![1,2,5,15], .inl (0,1)),
    (![1,2,5,16], .inl (0,1)),
    (![1,2,5,17], .inl (1,2)),
    (![1,2,5,18], .inl (1,0)),
    (![1,2,6,7], .inl (3,1)),
    (![1,2,6,8], .inl (3,1)),
    (![1,2,6,9], .inl (2,1)),
    (![1,2,6,10], .inl (2,0)),
    (![1,2,6,11], .inl (1,0)),
    (![1,2,6,12], .inl (1,0)),
    (![1,2,6,13], .inl (1,0)),
    (![1,2,6,14], .inl (0,1)),
    (![1,2,6,15], .inl (0,1)),
    (![1,2,6,16], .inl (0,1)),
    (![1,2,6,17], .inl (1,2)),
    (![1,2,6,18], .inl (1,0)),
    (![1,2,7,8], .inl (3,1)),
    (![1,2,7,9], .inl (2,1)),
    (![1,2,7,10], .inl (2,0)),
    (![1,2,7,11], .inl (2,0)),
    (![1,2,7,12], .inl (1,0)),
    (![1,2,7,13], .inl (2,0)),
    (![1,2,7,14], .inl (0,1)),
    (![1,2,7,15], .inl (0,1)),
    (![1,2,7,16], .inl (0,1)),
    (![1,2,7,17], .inl (1,2)),
    (![1,2,7,18], .inl (1,0)),
    (![1,2,8,9], .inl (2,1)),
    (![1,2,8,10], .inl (2,1)),
    (![1,2,8,11], .inl (2,1)),
    (![1,2,8,12], .inl (2,1)),
    (![1,2,8,13], .inl (2,1)),
    (![1,2,8,14], .inl (2,1)),
    (![1,2,8,15], .inl (2,1)),
    (![1,2,8,16], .inl (2,1)),
    (![1,2,8,17], .inl (1,2)),
    (![1,2,8,18], .inr none),
    (![1,2,9,10], .inl (0,1)),
    (![1,2,9,11], .inl (0,1)),
    (![1,2,9,12], .inl (0,1)),
    (![1,2,9,13], .inl (0,1)),
    (![1,2,9,14], .inl (2,0)),
    (![1,2,9,15], .inl (2,0)),
    (![1,2,9,16], .inl (2,0)),
    (![1,2,9,17], .inl (1,2)),
    (![1,2,9,18], .inl (0,1)),
    (![1,2,10,11], .inl (0,1)),
    (![1,2,10,12], .inl (0,1)),
    (![1,2,10,13], .inl (2,1)),
    (![1,2,10,14], .inl (2,0)),
    (![1,2,10,15], .inl (1,0)),
    (![1,2,10,16], .inl (1,0)),
    (![1,2,10,17], .inl (0,2)),
    (![1,2,10,18], .inl (0,1)),
    (![1,2,11,12], .inl (0,1)),
    (![1,2,11,13], .inl (2,0)),
    (![1,2,11,14], .inl (1,0)),
    (![1,2,11,15], .inl (1,0)),
    (![1,2,11,16], .inl (1,0)),
    (![1,2,11,17], .inl (0,1)),
    (![1,2,11,18], .inl (0,1)),
    (![1,2,12,13], .inl (1,0)),
    (![1,2,12,14], .inl (1,0)),
    (![1,2,12,15], .inl (1,0)),
    (![1,2,12,16], .inl (1,0)),
    (![1,2,12,17], .inl (0,1)),
    (![1,2,12,18], .inl (0,1)),
    (![1,2,13,14], .inl (1,0)),
    (![1,2,13,15], .inl (1,0)),
    (![1,2,13,16], .inl (1,0)),
    (![1,2,13,17], .inl (0,1)),
    (![1,2,13,18], .inl (0,1)),
    (![1,2,14,15], .inl (1,0)),
    (![1,2,14,16], .inl (1,3)),
    (![1,2,14,17], .inr (some (true,1,5))),
    (![1,2,14,18], .inl (0,1)),
    (![1,2,15,16], .inl (0,3)),
    (![1,2,15,17], .inl (1,0)),
    (![1,2,15,18], .inl (0,1)),
    (![1,2,16,17], .inl (1,0)),
    (![1,2,16,18], .inl (0,1)),
    (![1,2,17,18], .inl (1,0)),
    (![1,3,4,5], .inl (1,2)),
    (![1,3,4,6], .inl (3,2)),
    (![1,3,4,7], .inl (3,1)),
    (![1,3,4,8], .inl (2,1)),
    (![1,3,4,9], .inl (2,1)),
    (![1,3,4,10], .inl (2,0)),
    (![1,3,4,11], .inl (1,0)),
    (![1,3,4,12], .inl (1,0)),
    (![1,3,4,13], .inl (1,0)),
    (![1,3,4,14], .inl (0,1)),
    (![1,3,4,15], .inl (0,1)),
    (![1,3,4,16], .inl (0,1)),
    (![1,3,4,17], .inl (1,2)),
    (![1,3,4,18], .inl (1,0)),
    (![1,3,5,6], .inl (3,1)),
    (![1,3,5,7], .inl (3,1)),
    (![1,3,5,8], .inl (2,1)),
    (![1,3,5,9], .inl (2,1)),
    (![1,3,5,10], .inl (2,0)),
    (![1,3,5,11], .inl (1,0)),
    (![1,3,5,12], .inl (1,0)),
    (![1,3,5,13], .inl (1,0)),
    (![1,3,5,14], .inl (0,1)),
    (![1,3,5,15], .inl (0,1)),
    (![1,3,5,16], .inl (0,1)),
    (![1,3,5,17], .inl (1,2)),
    (![1,3,5,18], .inl (1,0)),
    (![1,3,6,7], .inl (3,1)),
    (![1,3,6,8], .inl (2,1)),
    (![1,3,6,9], .inl (2,1)),
    (![1,3,6,10], .inl (2,0)),
    (![1,3,6,11], .inl (1,0)),
    (![1,3,6,12], .inl (1,0)),
    (![1,3,6,13], .inl (1,0)),
    (![1,3,6,14], .inl (0,1)),
    (![1,3,6,15], .inl (0,1)),
    (![1,3,6,16], .inl (0,1)),
    (![1,3,6,17], .inl (1,2)),
    (![1,3,6,18], .inl (1,0)),
    (![1,3,7,8], .inl (2,1)),
    (![1,3,7,9], .inl (2,1)),
    (![1,3,7,10], .inl (2,1)),
    (![1,3,7,11], .inr none),
    (![1,3,7,12], .inl (1,2)),
    (![1,3,7,13], .inr none),
    (![1,3,7,14], .inl (2,1)),
    (![1,3,7,15], .inl (2,1)),
    (![1,3,7,16], .inl (2,1)),
    (![1,3,7,17], .inl (1,2)),
    (![1,3,7,18], .inl (1,2)),
    (![1,3,8,9], .inl (2,1)),
    (![1,3,8,10], .inl (0,1)),
    (![1,3,8,11], .inl (0,1)),
    (![1,3,8,12], .inl (0,1)),
    (![1,3,8,13], .inl (0,1)),
    (![1,3,8,14], .inl (2,0)),
    (![1,3,8,15], .inl (2,0)),
    (![1,3,8,16], .inl (2,0)),
    (![1,3,8,17], .inl (1,2)),
    (![1,3,8,18], .inl (0,2)),
    (![1,3,9,10], .inl (0,1)),
    (![1,3,9,11], .inl (0,1)),
    (![1,3,9,12], .inl (0,1)),
    (![1,3,9,13], .inl (0,1)),
    (![1,3,9,14], .inl (2,0)),
    (![1,3,9,15], .inl (2,0)),
    (![1,3,9,16], .inl (2,0)),
    (![1,3,9,17], .inl (1,2)),
    (![1,3,9,18], .inl (0,1)),
    (![1,3,10,11], .inl (0,1)),
    (![1,3,10,12], .inl (0,1)),
    (![1,3,10,13], .inl (0,1)),
    (![1,3,10,14], .inl (2,0)),
    (![1,3,10,15], .inl (1,0)),
    (![1,3,10,16], .inl (1,0)),
    (![1,3,10,17], .inl (0,2)),
    (![1,3,10,18], .inl (0,1)),
    (![1,3,11,12], .inl (0,1)),
    (![1,3,11,13], .inr none),
    (![1,3,11,14], .inl (1,0)),
    (![1,3,11,15], .inl (1,0)),
    (![1,3,11,16], .inl (1,0)),
    (![1,3,11,17], .inl (0,1)),
    (![1,3,11,18], .inl (0,1)),
    (![1,3,12,13], .inl (1,0)),
    (![1,3,12,14], .inl (1,0)),
    (![1,3,12,15], .inl (1,0)),
    (![1,3,12,16], .inl (1,0)),
    (![1,3,12,17], .inl (0,1)),
    (![1,3,12,18], .inl (0,1)),
    (![1,3,13,14], .inl (1,0)),
    (![1,3,13,15], .inl (1,0)),
    (![1,3,13,16], .inl (1,0)),
    (![1,3,13,17], .inl (0,1)),
    (![1,3,13,18], .inl (0,1)),
    (![1,3,14,15], .inl (1,0)),
    (![1,3,14,16], .inl (0,3)),
    (![1,3,14,17], .inr (some (true,1,5))),
    (![1,3,14,18], .inl (0,1)),
    (![1,3,15,16], .inl (0,3)),
    (![1,3,15,17], .inl (1,0)),
    (![1,3,15,18], .inr (some (true,2,10))),
    (![1,3,16,17], .inl (1,0)),
    (![1,3,16,18], .inl (0,1)),
    (![1,3,17,18], .inl (1,0)),
    (![1,4,5,6], .inl (3,1)),
    (![1,4,5,7], .inl (2,1)),
    (![1,4,5,8], .inl (2,1)),
    (![1,4,5,9], .inl (2,1)),
    (![1,4,5,10], .inl (2,0)),
    (![1,4,5,11], .inl (1,0)),
    (![1,4,5,12], .inl (1,0)),
    (![1,4,5,13], .inl (1,0)),
    (![1,4,5,14], .inl (0,1)),
    (![1,4,5,15], .inl (0,1)),
    (![1,4,5,16], .inl (0,1)),
    (![1,4,5,17], .inl (1,2)),
    (![1,4,5,18], .inl (1,0)),
    (![1,4,6,7], .inl (2,1)),
    (![1,4,6,8], .inl (2,1)),
    (![1,4,6,9], .inl (2,1)),
    (![1,4,6,10], .inl (2,1)),
    (![1,4,6,11], .inl (1,2)),
    (![1,4,6,12], .inl (1,2)),
    (![1,4,6,13], .inl (1,2)),
    (![1,4,6,14], .inl (2,1)),
    (![1,4,6,15], .inl (2,1)),
    (![1,4,6,16], .inl (2,1)),
    (![1,4,6,17], .inl (1,2)),
    (![1,4,6,18], .inl (1,2)),
    (![1,4,7,8], .inl (2,1)),
    (![1,4,7,9], .inl (2,1)),
    (![1,4,7,10], .inl (0,1)),
    (![1,4,7,11], .inl (0,2)),
    (![1,4,7,12], .inl (0,2)),
    (![1,4,7,13], .inl (0,2)),
    (![1,4,7,14], .inl (2,0)),
    (![1,4,7,15], .inl (2,0)),
    (![1,4,7,16], .inl (2,0)),
    (![1,4,7,17], .inl (1,2)),
    (![1,4,7,18], .inl (0,2)),
    (![1,4,8,9], .inl (2,1)),
    (![1,4,8,10], .inl (0,1)),
    (![1,4,8,11], .inl (0,1)),
    (![1,4,8,12], .inl (0,1)),
    (![1,4,8,13], .inl (0,1)),
    (![1,4,8,14], .inl (2,0)),
    (![1,4,8,15], .inl (2,0)),
    (![1,4,8,16], .inl (2,0)),
    (![1,4,8,17], .inl (1,2)),
    (![1,4,8,18], .inl (0,2)),
    (![1,4,9,10], .inl (0,1)),
    (![1,4,9,11], .inl (0,1)),
    (![1,4,9,12], .inl (0,1)),
    (![1,4,9,13], .inl (0,1)),
    (![1,4,9,14], .inl (2,0)),
    (![1,4,9,15], .inl (2,0)),
    (![1,4,9,16], .inl (2,0)),
    (![1,4,9,17], .inl (1,2)),
    (![1,4,9,18], .inl (0,1)),
    (![1,4,10,11], .inl (0,1)),
    (![1,4,10,12], .inl (0,1)),
    (![1,4,10,13], .inl (0,1)),
    (![1,4,10,14], .inl (2,0)),
    (![1,4,10,15], .inl (1,0)),
    (![1,4,10,16], .inl (1,0)),
    (![1,4,10,17], .inl (0,2)),
    (![1,4,10,18], .inl (0,1)),
    (![1,4,11,12], .inl (0,1)),
    (![1,4,11,13], .inl (0,2)),
    (![1,4,11,14], .inl (1,0)),
    (![1,4,11,15], .inl (1,0)),
    (![1,4,11,16], .inl (1,0)),
    (![1,4,11,17], .inl (0,1)),
    (![1,4,11,18], .inl (0,1)),
    (![1,4,12,13], .inl (1,2)),
    (![1,4,12,14], .inr (some (false,1,88))),
    (![1,4,12,15], .inr (some (false,3,89))),
    (![1,4,12,16], .inl (1,0)),
    (![1,4,12,17], .inl (0,1)),
    (![1,4,12,18], .inl (0,1)),
    (![1,4,13,14], .inr (some (false,1,90))),
    (![1,4,13,15], .inr (some (false,1,91))),
    (![1,4,13,16], .inl (1,0)),
    (![1,4,13,17], .inl (0,1)),
    (![1,4,13,18], .inl (0,1)),
    (![1,4,14,15], .inl (1,3)),
    (![1,4,14,16], .inl (0,3)),
    (![1,4,14,17], .inr (some (true,1,5))),
    (![1,4,14,18], .inr (some (true,1,47))),
    (![1,4,15,16], .inl (0,3)),
    (![1,4,15,17], .inl (1,0)),
    (![1,4,15,18], .inr (some (true,1,48))),
    (![1,4,16,17], .inl (1,0)),
    (![1,4,16,18], .inl (0,1)),
    (![1,4,17,18], .inl (1,0)),
    (![1,5,6,7], .inl (2,1)),
    (![1,5,6,8], .inl (2,1)),
    (![1,5,6,9], .inl (2,1)),
    (![1,5,6,10], .inl (0,1)),
    (![1,5,6,11], .inl (0,2)),
    (![1,5,6,12], .inl (0,2)),
    (![1,5,6,13], .inl (0,2)),
    (![1,5,6,14], .inl (2,0)),
    (![1,5,6,15], .inl (2,0)),
    (![1,5,6,16], .inl (2,0)),
    (![1,5,6,17], .inl (1,2)),
    (![1,5,6,18], .inl (0,2)),
    (![1,5,7,8], .inl (2,1)),
    (![1,5,7,9], .inl (2,1)),
    (![1,5,7,10], .inl (0,1)),
    (![1,5,7,11], .inl (0,2)),
    (![1,5,7,12], .inl (0,2)),
    (![1,5,7,13], .inl (0,2)),
    (![1,5,7,14], .inl (2,0)),
    (![1,5,7,15], .inl (2,0)),
    (![1,5,7,16], .inl (2,0)),
    (![1,5,7,17], .inl (1,2)),
    (![1,5,7,18], .inl (0,2)),
    (![1,5,8,9], .inl (2,1)),
    (![1,5,8,10], .inl (0,1)),
    (![1,5,8,11], .inl (0,1)),
    (![1,5,8,12], .inl (0,1)),
    (![1,5,8,13], .inl (0,1)),
    (![1,5,8,14], .inl (2,0)),
    (![1,5,8,15], .inl (2,0)),
    (![1,5,8,16], .inl (2,0)),
    (![1,5,8,17], .inl (1,2)),
    (![1,5,8,18], .inl (0,2)),
    (![1,5,9,10], .inl (0,1)),
    (![1,5,9,11], .inl (0,1)),
    (![1,5,9,12], .inl (0,1)),
    (![1,5,9,13], .inl (0,1)),
    (![1,5,9,14], .inl (2,0)),
    (![1,5,9,15], .inl (2,0)),
    (![1,5,9,16], .inl (2,0)),
    (![1,5,9,17], .inl (1,2)),
    (![1,5,9,18], .inl (0,1)),
    (![1,5,10,11], .inl (0,1)),
    (![1,5,10,12], .inl (0,1)),
    (![1,5,10,13], .inl (0,1)),
    (![1,5,10,14], .inl (2,0)),
    (![1,5,10,15], .inl (1,0)),
    (![1,5,10,16], .inl (1,0)),
    (![1,5,10,17], .inl (0,2)),
    (![1,5,10,18], .inl (0,1)),
    (![1,5,11,12], .inl (0,1)),
    (![1,5,11,13], .inl (0,2)),
    (![1,5,11,14], .inr (some (false,1,99))),
    (![1,5,11,15], .inl (1,0)),
    (![1,5,11,16], .inl (1,0)),
    (![1,5,11,17], .inl (0,1)),
    (![1,5,11,18], .inl (0,1)),
    (![1,5,12,13], .inl (0,2)),
    (![1,5,12,14], .inr (some (false,1,157))),
    (![1,5,12,15], .inr (some (false,1,158))),
    (![1,5,12,16], .inl (1,0)),
    (![1,5,12,17], .inl (0,1)),
    (![1,5,12,18], .inl (0,1)),
    (![1,5,13,14], .inr (some (false,1,159))),
    (![1,5,13,15], .inr (some (false,2,160))),
    (![1,5,13,16], .inl (1,0)),
    (![1,5,13,17], .inl (0,1)),
    (![1,5,13,18], .inl (3,1)),
    (![1,5,14,15], .inl (0,3)),
    (![1,5,14,16], .inl (0,3)),
    (![1,5,14,17], .inr (some (true,1,5))),
    (![1,5,14,18], .inr (some (true,1,49))),
    (![1,5,15,16], .inl (0,3)),
    (![1,5,15,17], .inl (1,0)),
    (![1,5,15,18], .inr (some (true,2,50))),
    (![1,5,16,17], .inl (1,0)),
    (![1,5,16,18], .inl (0,1)),
    (![1,5,17,18], .inl (1,0)),
    (![1,6,7,8], .inl (2,1)),
    (![1,6,7,9], .inl (2,1)),
    (![1,6,7,10], .inl (0,1)),
    (![1,6,7,11], .inl (0,2)),
    (![1,6,7,12], .inl (0,2)),
    (![1,6,7,13], .inl (0,2)),
    (![1,6,7,14], .inl (2,0)),
    (![1,6,7,15], .inl (2,0)),
    (![1,6,7,16], .inl (2,0)),
    (![1,6,7,17], .inl (1,2)),
    (![1,6,7,18], .inl (0,2)),
    (![1,6,8,9], .inl (2,1)),
    (![1,6,8,10], .inl (0,1)),
    (![1,6,8,11], .inl (0,1)),
    (![1,6,8,12], .inl (0,1)),
    (![1,6,8,13], .inl (0,1)),
    (![1,6,8,14], .inl (2,0)),
    (![1,6,8,15], .inl (2,0)),
    (![1,6,8,16], .inl (2,0)),
    (![1,6,8,17], .inl (1,2)),
    (![1,6,8,18], .inl (0,2)),
    (![1,6,9,10], .inl (0,1)),
    (![1,6,9,11], .inl (0,1)),
    (![1,6,9,12], .inl (0,1)),
    (![1,6,9,13], .inl (0,1)),
    (![1,6,9,14], .inl (2,0)),
    (![1,6,9,15], .inl (2,0)),
    (![1,6,9,16], .inl (2,0)),
    (![1,6,9,17], .inl (1,2)),
    (![1,6,9,18], .inl (0,1)),
    (![1,6,10,11], .inl (0,1)),
    (![1,6,10,12], .inl (0,1)),
    (![1,6,10,13], .inl (0,1)),
    (![1,6,10,14], .inl (2,0)),
    (![1,6,10,15], .inl (1,0)),
    (![1,6,10,16], .inl (1,0)),
    (![1,6,10,17], .inl (0,2)),
    (![1,6,10,18], .inl (0,1)),
    (![1,6,11,12], .inl (0,1)),
    (![1,6,11,13], .inl (0,2)),
    (![1,6,11,14], .inl (1,0)),
    (![1,6,11,15], .inl (1,0)),
    (![1,6,11,16], .inl (1,0)),
    (![1,6,11,17], .inl (0,1)),
    (![1,6,11,18], .inl (0,1)),
    (![1,6,12,13], .inl (1,2)),
    (![1,6,12,14], .inr (some (false,1,117))),
    (![1,6,12,15], .inr (some (false,3,118))),
    (![1,6,12,16], .inl (1,0)),
    (![1,6,12,17], .inl (0,1)),
    (![1,6,12,18], .inl (0,1)),
    (![1,6,13,14], .inr (some (false,1,119))),
    (![1,6,13,15], .inr (some (false,1,120))),
    (![1,6,13,16], .inl (1,0)),
    (![1,6,13,17], .inl (0,1)),
    (![1,6,13,18], .inl (0,1)),
    (![1,6,14,15], .inl (1,3)),
    (![1,6,14,16], .inl (0,3)),
    (![1,6,14,17], .inr (some (true,1,5))),
    (![1,6,14,18], .inr (some (true,1,51))),
    (![1,6,15,16], .inl (0,3)),
    (![1,6,15,17], .inl (1,0)),
    (![1,6,15,18], .inr (some (true,1,52))),
    (![1,6,16,17], .inl (1,0)),
    (![1,6,16,18], .inl (0,1)),
    (![1,6,17,18], .inl (1,0)),
    (![1,7,8,9], .inl (2,1)),
    (![1,7,8,10], .inl (0,1)),
    (![1,7,8,11], .inl (0,1)),
    (![1,7,8,12], .inl (0,1)),
    (![1,7,8,13], .inl (0,1)),
    (![1,7,8,14], .inl (2,0)),
    (![1,7,8,15], .inl (2,0)),
    (![1,7,8,16], .inl (2,0)),
    (![1,7,8,17], .inl (1,2)),
    (![1,7,8,18], .inl (0,2)),
    (![1,7,9,10], .inl (0,1)),
    (![1,7,9,11], .inl (0,1)),
    (![1,7,9,12], .inl (0,1)),
    (![1,7,9,13], .inl (0,1)),
    (![1,7,9,14], .inl (2,0)),
    (![1,7,9,15], .inl (2,0)),
    (![1,7,9,16], .inl (2,0)),
    (![1,7,9,17], .inl (1,2)),
    (![1,7,9,18], .inl (0,1)),
    (![1,7,10,11], .inl (0,1)),
    (![1,7,10,12], .inl (0,1)),
    (![1,7,10,13], .inl (0,1)),
    (![1,7,10,14], .inl (2,0)),
    (![1,7,10,15], .inl (1,0)),
    (![1,7,10,16], .inl (1,0)),
    (![1,7,10,17], .inl (0,2)),
    (![1,7,10,18], .inl (0,1)),
    (![1,7,11,12], .inl (0,1)),
    (![1,7,11,13], .inr none),
    (![1,7,11,14], .inl (1,0)),
    (![1,7,11,15], .inl (1,0)),
    (![1,7,11,16], .inl (1,0)),
    (![1,7,11,17], .inl (0,1)),
    (![1,7,11,18], .inl (0,1)),
    (![1,7,12,13], .inl (1,0)),
    (![1,7,12,14], .inl (1,0)),
    (![1,7,12,15], .inl (1,0)),
    (![1,7,12,16], .inl (1,0)),
    (![1,7,12,17], .inl (0,1)),
    (![1,7,12,18], .inl (0,1)),
    (![1,7,13,14], .inl (1,0)),
    (![1,7,13,15], .inl (1,0)),
    (![1,7,13,16], .inl (1,0)),
    (![1,7,13,17], .inl (0,1)),
    (![1,7,13,18], .inl (0,1)),
    (![1,7,14,15], .inl (1,0)),
    (![1,7,14,16], .inl (0,3)),
    (![1,7,14,17], .inr (some (true,1,5))),
    (![1,7,14,18], .inl (0,1)),
    (![1,7,15,16], .inl (0,3)),
    (![1,7,15,17], .inl (1,0)),
    (![1,7,15,18], .inr (some (true,2,18))),
    (![1,7,16,17], .inl (1,0)),
    (![1,7,16,18], .inl (0,1)),
    (![1,7,17,18], .inl (1,0)),
    (![1,8,9,10], .inl (0,1)),
    (![1,8,9,11], .inl (0,1)),
    (![1,8,9,12], .inl (0,1)),
    (![1,8,9,13], .inl (0,1)),
    (![1,8,9,14], .inl (2,0)),
    (![1,8,9,15], .inl (2,0)),
    (![1,8,9,16], .inl (2,0)),
    (![1,8,9,17], .inl (1,2)),
    (![1,8,9,18], .inl (0,1)),
    (![1,8,10,11], .inl (0,1)),
    (![1,8,10,12], .inl (0,1)),
    (![1,8,10,13], .inl (2,1)),
    (![1,8,10,14], .inl (2,0)),
    (![1,8,10,15], .inl (1,0)),
    (![1,8,10,16], .inl (1,0)),
    (![1,8,10,17], .inl (0,2)),
    (![1,8,10,18], .inl (0,1)),
    (![1,8,11,12], .inl (0,1)),
    (![1,8,11,13], .inl (2,0)),
    (![1,8,11,14], .inl (1,0)),
    (![1,8,11,15], .inl (1,0)),
    (![1,8,11,16], .inl (1,0)),
    (![1,8,11,17], .inl (0,1)),
    (![1,8,11,18], .inl (0,1)),
    (![1,8,12,13], .inl (1,0)),
    (![1,8,12,14], .inl (1,0)),
    (![1,8,12,15], .inl (1,0)),
    (![1,8,12,16], .inl (1,0)),
    (![1,8,12,17], .inl (0,1)),
    (![1,8,12,18], .inl (0,1)),
    (![1,8,13,14], .inl (1,0)),
    (![1,8,13,15], .inl (1,0)),
    (![1,8,13,16], .inl (1,0)),
    (![1,8,13,17], .inl (0,1)),
    (![1,8,13,18], .inl (0,1)),
    (![1,8,14,15], .inl (1,0)),
    (![1,8,14,16], .inl (1,3)),
    (![1,8,14,17], .inr (some (true,1,5))),
    (![1,8,14,18], .inl (0,1)),
    (![1,8,15,16], .inl (0,3)),
    (![1,8,15,17], .inl (1,0)),
    (![1,8,15,18], .inl (0,1)),
    (![1,8,16,17], .inl (1,0)),
    (![1,8,16,18], .inl (0,1)),
    (![1,8,17,18], .inl (1,0)),
    (![1,9,10,11], .inl (2,1)),
    (![1,9,10,12], .inl (2,1)),
    (![1,9,10,13], .inl (2,0)),
    (![1,9,10,14], .inl (2,0)),
    (![1,9,10,15], .inl (1,0)),
    (![1,9,10,16], .inl (1,0)),
    (![1,9,10,17], .inl (0,2)),
    (![1,9,10,18], .inl (0,1)),
    (![1,9,11,12], .inl (2,1)),
    (![1,9,11,13], .inl (2,0)),
    (![1,9,11,14], .inl (1,0)),
    (![1,9,11,15], .inl (1,0)),
    (![1,9,11,16], .inl (1,0)),
    (![1,9,11,17], .inl (0,1)),
    (![1,9,11,18], .inl (0,1)),
    (![1,9,12,13], .inl (1,0)),
    (![1,9,12,14], .inl (1,0)),
    (![1,9,12,15], .inl (1,0)),
    (![1,9,12,16], .inl (1,0)),
    (![1,9,12,17], .inl (0,1)),
    (![1,9,12,18], .inl (0,1)),
    (![1,9,13,14], .inl (1,0)),
    (![1,9,13,15], .inl (1,0)),
    (![1,9,13,16], .inl (1,0)),
    (![1,9,13,17], .inl (0,1)),
    (![1,9,13,18], .inl (0,1)),
    (![1,9,14,15], .inl (1,0)),
    (![1,9,14,16], .inl (1,0)),
    (![1,9,14,17], .inr (some (true,1,5))),
    (![1,9,14,18], .inl (0,1)),
    (![1,9,15,16], .inr none),
    (![1,9,15,17], .inl (1,0)),
    (![1,9,15,18], .inl (0,1)),
    (![1,9,16,17], .inl (1,0)),
    (![1,9,16,18], .inl (0,1)),
    (![1,9,17,18], .inl (1,0)),
    (![1,10,11,12], .inl (2,1)),
    (![1,10,11,13], .inl (2,0)),
    (![1,10,11,14], .inl (1,0)),
    (![1,10,11,15], .inl (1,0)),
    (![1,10,11,16], .inl (1,0)),
    (![1,10,11,17], .inl (0,1)),
    (![1,10,11,18], .inl (0,1)),
    (![1,10,12,13], .inl (1,0)),
    (![1,10,12,14], .inl (1,0)),
    (![1,10,12,15], .inl (1,0)),
    (![1,10,12,16], .inl (1,0)),
    (![1,10,12,17], .inl (0,1)),
    (![1,10,12,18], .inl (0,1)),
    (![1,10,13,14], .inl (1,0)),
    (![1,10,13,15], .inl (1,0)),
    (![1,10,13,16], .inl (1,0)),
    (![1,10,13,17], .inl (0,1)),
    (![1,10,13,18], .inl (0,1)),
    (![1,10,14,15], .inl (1,0)),
    (![1,10,14,16], .inl (1,0)),
    (![1,10,14,17], .inr none),
    (![1,10,14,18], .inl (0,1)),
    (![1,10,15,16], .inl (3,0)),
    (![1,10,15,17], .inl (1,0)),
    (![1,10,15,18], .inl (0,1)),
    (![1,10,16,17], .inl (1,0)),
    (![1,10,16,18], .inl (0,1)),
    (![1,10,17,18], .inl (1,0)),
    (![1,11,12,13], .inl (1,0)),
    (![1,11,12,14], .inl (1,0)),
    (![1,11,12,15], .inl (1,0)),
    (![1,11,12,16], .inl (1,0)),
    (![1,11,12,17], .inl (0,1)),
    (![1,11,12,18], .inl (0,1)),
    (![1,11,13,14], .inl (1,0)),
    (![1,11,13,15], .inl (1,0)),
    (![1,11,13,16], .inl (1,0)),
    (![1,11,13,17], .inl (0,1)),
    (![1,11,13,18], .inl (0,1)),
    (![1,11,14,15], .inl (1,0)),
    (![1,11,14,16], .inl (1,0)),
    (![1,11,14,17], .inr (some (false,1,5))),
    (![1,11,14,18], .inl (0,1)),
    (![1,11,15,16], .inl (3,0)),
    (![1,11,15,17], .inr (some (false,1,53))),
    (![1,11,15,18], .inl (0,1)),
    (![1,11,16,17], .inl (1,0)),
    (![1,11,16,18], .inl (2,1)),
    (![1,11,17,18], .inl (1,0)),
    (![1,12,13,14], .inl (1,2)),
    (![1,12,13,15], .inl (1,2)),
    (![1,12,13,16], .inl (1,0)),
    (![1,12,13,17], .inl (0,1)),
    (![1,12,13,18], .inl (0,1)),
    (![1,12,14,15], .inl (1,2)),
    (![1,12,14,16], .inl (1,0)),
    (![1,12,14,17], .inr (some (false,2,5))),
    (![1,12,14,18], .inl (0,1)),
    (![1,12,15,16], .inl (3,0)),
    (![1,12,15,17], .inr (some (false,1,54))),
    (![1,12,15,18], .inl (0,1)),
    (![1,12,16,17], .inl (1,0)),
    (![1,12,16,18], .inl (2,0)),
    (![1,12,17,18], .inl (1,3)),
    (![1,13,14,15], .inl (1,2)),
    (![1,13,14,16], .inl (1,0)),
    (![1,13,14,17], .inr (some (false,1,5))),
    (![1,13,14,18], .inl (0,1)),
    (![1,13,15,16], .inl (3,0)),
    (![1,13,15,17], .inr (some (false,1,55))),
    (![1,13,15,18], .inl (0,1)),
    (![1,13,16,17], .inr (some (false,1,0))),
    (![1,13,16,18], .inl (2,0)),
    (![1,13,17,18], .inl (0,3)),
    (![1,14,15,16], .inl (3,0)),
    (![1,14,15,17], .inr (some (false,1,5))),
    (![1,14,15,18], .inl (0,1)),
    (![1,14,16,17], .inr (some (false,1,5))),
    (![1,14,16,18], .inl (2,0)),
    (![1,14,17,18], .inr (some (false,2,5))),
    (![1,15,16,17], .inl (0,2)),
    (![1,15,16,18], .inl (2,0)),
    (![1,15,17,18], .inr (some (false,1,6))),
    (![1,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid01 : ∀ k : Fin 680, CaseValid (block01 k).1 (block01 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align01 : (List.finRange 680).map (fun k => (block01 k).1) = fourTuples 1 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block02 : Fin 560 → Entry :=
  ![(![2,3,4,5], .inr none),
    (![2,3,4,6], .inr none),
    (![2,3,4,7], .inr none),
    (![2,3,4,8], .inr none),
    (![2,3,4,9], .inr none),
    (![2,3,4,10], .inl (1,0)),
    (![2,3,4,11], .inl (1,0)),
    (![2,3,4,12], .inl (1,0)),
    (![2,3,4,13], .inl (1,0)),
    (![2,3,4,14], .inl (0,1)),
    (![2,3,4,15], .inl (0,1)),
    (![2,3,4,16], .inl (0,1)),
    (![2,3,4,17], .inr none),
    (![2,3,4,18], .inl (1,0)),
    (![2,3,5,6], .inr none),
    (![2,3,5,7], .inr none),
    (![2,3,5,8], .inr none),
    (![2,3,5,9], .inr none),
    (![2,3,5,10], .inl (1,0)),
    (![2,3,5,11], .inl (1,0)),
    (![2,3,5,12], .inl (1,0)),
    (![2,3,5,13], .inl (1,0)),
    (![2,3,5,14], .inl (0,1)),
    (![2,3,5,15], .inl (0,1)),
    (![2,3,5,16], .inl (0,1)),
    (![2,3,5,17], .inr none),
    (![2,3,5,18], .inl (1,0)),
    (![2,3,6,7], .inr none),
    (![2,3,6,8], .inr none),
    (![2,3,6,9], .inr none),
    (![2,3,6,10], .inl (1,0)),
    (![2,3,6,11], .inl (1,0)),
    (![2,3,6,12], .inl (1,0)),
    (![2,3,6,13], .inl (1,0)),
    (![2,3,6,14], .inl (0,1)),
    (![2,3,6,15], .inl (0,1)),
    (![2,3,6,16], .inl (0,1)),
    (![2,3,6,17], .inr none),
    (![2,3,6,18], .inl (1,0)),
    (![2,3,7,8], .inr none),
    (![2,3,7,9], .inr none),
    (![2,3,7,10], .inl (1,2)),
    (![2,3,7,11], .inl (1,2)),
    (![2,3,7,12], .inl (1,2)),
    (![2,3,7,13], .inl (1,2)),
    (![2,3,7,14], .inl (2,1)),
    (![2,3,7,15], .inl (2,1)),
    (![2,3,7,16], .inl (2,1)),
    (![2,3,7,17], .inr none),
    (![2,3,7,18], .inl (1,2)),
    (![2,3,8,9], .inr none),
    (![2,3,8,10], .inl (0,2)),
    (![2,3,8,11], .inl (0,2)),
    (![2,3,8,12], .inl (0,2)),
    (![2,3,8,13], .inl (0,2)),
    (![2,3,8,14], .inl (2,0)),
    (![2,3,8,15], .inl (2,0)),
    (![2,3,8,16], .inl (2,0)),
    (![2,3,8,17], .inr none),
    (![2,3,8,18], .inl (0,2)),
    (![2,3,9,10], .inl (0,1)),
    (![2,3,9,11], .inl (0,1)),
    (![2,3,9,12], .inl (0,1)),
    (![2,3,9,13], .inl (0,1)),
    (![2,3,9,14], .inl (1,0)),
    (![2,3,9,15], .inl (1,0)),
    (![2,3,9,16], .inl (1,0)),
    (![2,3,9,17], .inr none),
    (![2,3,9,18], .inl (0,1)),
    (![2,3,10,11], .inl (0,1)),
    (![2,3,10,12], .inl (0,1)),
    (![2,3,10,13], .inl (0,2)),
    (![2,3,10,14], .inl (1,0)),
    (![2,3,10,15], .inl (1,0)),
    (![2,3,10,16], .inl (1,0)),
    (![2,3,10,17], .inl (0,1)),
    (![2,3,10,18], .inl (0,1)),
    (![2,3,11,12], .inl (0,1)),
    (![2,3,11,13], .inl (1,2)),
    (![2,3,11,14], .inl (1,0)),
    (![2,3,11,15], .inl (1,0)),
    (![2,3,11,16], .inl (1,0)),
    (![2,3,11,17], .inl (0,1)),
    (![2,3,11,18], .inl (0,1)),
    (![2,3,12,13], .inl (1,0)),
    (![2,3,12,14], .inl (1,0)),
    (![2,3,12,15], .inl (1,0)),
    (![2,3,12,16], .inl (1,0)),
    (![2,3,12,17], .inl (0,1)),
    (![2,3,12,18], .inl (0,1)),
    (![2,3,13,14], .inl (1,0)),
    (![2,3,13,15], .inl (1,0)),
    (![2,3,13,16], .inl (1,0)),
    (![2,3,13,17], .inl (0,1)),
    (![2,3,13,18], .inl (0,1)),
    (![2,3,14,15], .inl (1,0)),
    (![2,3,14,16], .inl (0,3)),
    (![2,3,14,17], .inl (1,0)),
    (![2,3,14,18], .inl (0,1)),
    (![2,3,15,16], .inl (0,1)),
    (![2,3,15,17], .inl (1,0)),
    (![2,3,15,18], .inr (some (true,3,10))),
    (![2,3,16,17], .inl (1,0)),
    (![2,3,16,18], .inl (0,1)),
    (![2,3,17,18], .inl (1,0)),
    (![2,4,5,6], .inr none),
    (![2,4,5,7], .inr none),
    (![2,4,5,8], .inr none),
    (![2,4,5,9], .inr none),
    (![2,4,5,10], .inl (1,0)),
    (![2,4,5,11], .inl (1,0)),
    (![2,4,5,12], .inl (1,0)),
    (![2,4,5,13], .inl (1,0)),
    (![2,4,5,14], .inl (0,1)),
    (![2,4,5,15], .inl (0,1)),
    (![2,4,5,16], .inl (0,1)),
    (![2,4,5,17], .inr none),
    (![2,4,5,18], .inl (1,0)),
    (![2,4,6,7], .inr none),
    (![2,4,6,8], .inr none),
    (![2,4,6,9], .inr none),
    (![2,4,6,10], .inl (1,2)),
    (![2,4,6,11], .inl (1,2)),
    (![2,4,6,12], .inl (1,2)),
    (![2,4,6,13], .inl (1,2)),
    (![2,4,6,14], .inl (2,1)),
    (![2,4,6,15], .inl (2,1)),
    (![2,4,6,16], .inl (2,1)),
    (![2,4,6,17], .inr none),
    (![2,4,6,18], .inl (1,2)),
    (![2,4,7,8], .inr none),
    (![2,4,7,9], .inr none),
    (![2,4,7,10], .inl (0,2)),
    (![2,4,7,11], .inl (0,2)),
    (![2,4,7,12], .inl (0,2)),
    (![2,4,7,13], .inl (0,2)),
    (![2,4,7,14], .inl (2,0)),
    (![2,4,7,15], .inl (2,0)),
    (![2,4,7,16], .inl (2,0)),
    (![2,4,7,17], .inr none),
    (![2,4,7,18], .inl (0,2)),
    (![2,4,8,9], .inr none),
    (![2,4,8,10], .inl (0,2)),
    (![2,4,8,11], .inl (0,2)),
    (![2,4,8,12], .inl (0,2)),
    (![2,4,8,13], .inl (0,2)),
    (![2,4,8,14], .inl (2,0)),
    (![2,4,8,15], .inl (2,0)),
    (![2,4,8,16], .inl (2,0)),
    (![2,4,8,17], .inr none),
    (![2,4,8,18], .inl (0,2)),
    (![2,4,9,10], .inl (0,1)),
    (![2,4,9,11], .inl (0,1)),
    (![2,4,9,12], .inl (0,1)),
    (![2,4,9,13], .inl (0,1)),
    (![2,4,9,14], .inl (1,0)),
    (![2,4,9,15], .inl (1,0)),
    (![2,4,9,16], .inl (1,0)),
    (![2,4,9,17], .inr none),
    (![2,4,9,18], .inl (0,1)),
    (![2,4,10,11], .inl (0,1)),
    (![2,4,10,12], .inl (0,1)),
    (![2,4,10,13], .inl (0,2)),
    (![2,4,10,14], .inl (1,0)),
    (![2,4,10,15], .inl (1,0)),
    (![2,4,10,16], .inl (1,0)),
    (![2,4,10,17], .inl (0,1)),
    (![2,4,10,18], .inl (0,1)),
    (![2,4,11,12], .inl (0,1)),
    (![2,4,11,13], .inl (0,2)),
    (![2,4,11,14], .inl (1,0)),
    (![2,4,11,15], .inl (1,0)),
    (![2,4,11,16], .inl (1,0)),
    (![2,4,11,17], .inl (0,1)),
    (![2,4,11,18], .inl (0,1)),
    (![2,4,12,13], .inl (1,2)),
    (![2,4,12,14], .inr (some (false,2,88))),
    (![2,4,12,15], .inr (some (false,6,89))),
    (![2,4,12,16], .inl (1,0)),
    (![2,4,12,17], .inl (0,1)),
    (![2,4,12,18], .inl (0,1)),
    (![2,4,13,14], .inr (some (false,2,90))),
    (![2,4,13,15], .inr (some (false,2,91))),
    (![2,4,13,16], .inl (1,0)),
    (![2,4,13,17], .inl (0,1)),
    (![2,4,13,18], .inl (0,1)),
    (![2,4,14,15], .inl (1,3)),
    (![2,4,14,16], .inl (0,3)),
    (![2,4,14,17], .inl (1,0)),
    (![2,4,14,18], .inr (some (true,1,56))),
    (![2,4,15,16], .inl (0,1)),
    (![2,4,15,17], .inl (1,0)),
    (![2,4,15,18], .inr (some (true,3,57))),
    (![2,4,16,17], .inl (1,0)),
    (![2,4,16,18], .inl (0,1)),
    (![2,4,17,18], .inl (1,0)),
    (![2,5,6,7], .inr none),
    (![2,5,6,8], .inr none),
    (![2,5,6,9], .inr none),
    (![2,5,6,10], .inl (0,2)),
    (![2,5,6,11], .inl (0,2)),
    (![2,5,6,12], .inl (0,2)),
    (![2,5,6,13], .inl (0,2)),
    (![2,5,6,14], .inl (2,0)),
    (![2,5,6,15], .inl (2,0)),
    (![2,5,6,16], .inl (2,0)),
    (![2,5,6,17], .inr none),
    (![2,5,6,18], .inl (0,2)),
    (![2,5,7,8], .inr none),
    (![2,5,7,9], .inr none),
    (![2,5,7,10], .inl (0,2)),
    (![2,5,7,11], .inl (0,2)),
    (![2,5,7,12], .inl (0,2)),
    (![2,5,7,13], .inl (0,2)),
    (![2,5,7,14], .inl (2,0)),
    (![2,5,7,15], .inl (2,0)),
    (![2,5,7,16], .inl (2,0)),
    (![2,5,7,17], .inr none),
    (![2,5,7,18], .inl (0,2)),
    (![2,5,8,9], .inr none),
    (![2,5,8,10], .inl (0,2)),
    (![2,5,8,11], .inl (0,2)),
    (![2,5,8,12], .inl (0,2)),
    (![2,5,8,13], .inl (0,2)),
    (![2,5,8,14], .inl (2,0)),
    (![2,5,8,15], .inl (2,0)),
    (![2,5,8,16], .inl (2,0)),
    (![2,5,8,17], .inr none),
    (![2,5,8,18], .inl (0,2)),
    (![2,5,9,10], .inl (0,1)),
    (![2,5,9,11], .inl (0,1)),
    (![2,5,9,12], .inl (0,1)),
    (![2,5,9,13], .inl (0,1)),
    (![2,5,9,14], .inl (1,0)),
    (![2,5,9,15], .inl (1,0)),
    (![2,5,9,16], .inl (1,0)),
    (![2,5,9,17], .inr none),
    (![2,5,9,18], .inl (0,1)),
    (![2,5,10,11], .inl (0,1)),
    (![2,5,10,12], .inl (0,1)),
    (![2,5,10,13], .inl (0,2)),
    (![2,5,10,14], .inl (1,0)),
    (![2,5,10,15], .inl (1,0)),
    (![2,5,10,16], .inl (1,0)),
    (![2,5,10,17], .inl (0,1)),
    (![2,5,10,18], .inl (0,1)),
    (![2,5,11,12], .inl (0,1)),
    (![2,5,11,13], .inl (0,2)),
    (![2,5,11,14], .inr (some (false,3,99))),
    (![2,5,11,15], .inl (1,0)),
    (![2,5,11,16], .inl (1,0)),
    (![2,5,11,17], .inl (0,1)),
    (![2,5,11,18], .inl (0,1)),
    (![2,5,12,13], .inl (0,2)),
    (![2,5,12,14], .inr (some (false,1,161))),
    (![2,5,12,15], .inr (some (false,3,162))),
    (![2,5,12,16], .inl (1,0)),
    (![2,5,12,17], .inl (0,1)),
    (![2,5,12,18], .inl (0,1)),
    (![2,5,13,14], .inr (some (false,1,163))),
    (![2,5,13,15], .inr (some (false,1,164))),
    (![2,5,13,16], .inl (1,0)),
    (![2,5,13,17], .inl (0,1)),
    (![2,5,13,18], .inl (3,1)),
    (![2,5,14,15], .inl (0,3)),
    (![2,5,14,16], .inl (0,3)),
    (![2,5,14,17], .inl (1,0)),
    (![2,5,14,18], .inr (some (true,3,58))),
    (![2,5,15,16], .inl (0,1)),
    (![2,5,15,17], .inl (1,0)),
    (![2,5,15,18], .inr (some (true,3,59))),
    (![2,5,16,17], .inl (1,0)),
    (![2,5,16,18], .inl (0,1)),
    (![2,5,17,18], .inl (1,0)),
    (![2,6,7,8], .inr none),
    (![2,6,7,9], .inr none),
    (![2,6,7,10], .inl (0,2)),
    (![2,6,7,11], .inl (0,2)),
    (![2,6,7,12], .inl (0,2)),
    (![2,6,7,13], .inl (0,2)),
    (![2,6,7,14], .inl (2,0)),
    (![2,6,7,15], .inl (2,0)),
    (![2,6,7,16], .inl (2,0)),
    (![2,6,7,17], .inr none),
    (![2,6,7,18], .inl (0,2)),
    (![2,6,8,9], .inr none),
    (![2,6,8,10], .inl (0,2)),
    (![2,6,8,11], .inl (0,2)),
    (![2,6,8,12], .inl (0,2)),
    (![2,6,8,13], .inl (0,2)),
    (![2,6,8,14], .inl (2,0)),
    (![2,6,8,15], .inl (2,0)),
    (![2,6,8,16], .inl (2,0)),
    (![2,6,8,17], .inr none),
    (![2,6,8,18], .inl (0,2)),
    (![2,6,9,10], .inl (0,1)),
    (![2,6,9,11], .inl (0,1)),
    (![2,6,9,12], .inl (0,1)),
    (![2,6,9,13], .inl (0,1)),
    (![2,6,9,14], .inl (1,0)),
    (![2,6,9,15], .inl (1,0)),
    (![2,6,9,16], .inl (1,0)),
    (![2,6,9,17], .inr none),
    (![2,6,9,18], .inl (0,1)),
    (![2,6,10,11], .inl (0,1)),
    (![2,6,10,12], .inl (0,1)),
    (![2,6,10,13], .inl (0,2)),
    (![2,6,10,14], .inl (1,0)),
    (![2,6,10,15], .inl (1,0)),
    (![2,6,10,16], .inl (1,0)),
    (![2,6,10,17], .inl (0,1)),
    (![2,6,10,18], .inl (0,1)),
    (![2,6,11,12], .inl (0,1)),
    (![2,6,11,13], .inl (0,2)),
    (![2,6,11,14], .inl (1,0)),
    (![2,6,11,15], .inl (1,0)),
    (![2,6,11,16], .inl (1,0)),
    (![2,6,11,17], .inl (0,1)),
    (![2,6,11,18], .inl (0,1)),
    (![2,6,12,13], .inl (1,2)),
    (![2,6,12,14], .inr (some (false,2,117))),
    (![2,6,12,15], .inr (some (false,6,118))),
    (![2,6,12,16], .inl (1,0)),
    (![2,6,12,17], .inl (0,1)),
    (![2,6,12,18], .inl (0,1)),
    (![2,6,13,14], .inr (some (false,2,119))),
    (![2,6,13,15], .inr (some (false,2,120))),
    (![2,6,13,16], .inl (1,0)),
    (![2,6,13,17], .inl (0,1)),
    (![2,6,13,18], .inl (0,1)),
    (![2,6,14,15], .inl (1,3)),
    (![2,6,14,16], .inl (0,3)),
    (![2,6,14,17], .inl (1,0)),
    (![2,6,14,18], .inr (some (true,1,60))),
    (![2,6,15,16], .inl (0,1)),
    (![2,6,15,17], .inl (1,0)),
    (![2,6,15,18], .inr (some (true,3,61))),
    (![2,6,16,17], .inl (1,0)),
    (![2,6,16,18], .inl (0,1)),
    (![2,6,17,18], .inl (1,0)),
    (![2,7,8,9], .inr none),
    (![2,7,8,10], .inl (0,2)),
    (![2,7,8,11], .inl (0,2)),
    (![2,7,8,12], .inl (0,2)),
    (![2,7,8,13], .inl (0,2)),
    (![2,7,8,14], .inl (2,0)),
    (![2,7,8,15], .inl (2,0)),
    (![2,7,8,16], .inl (2,0)),
    (![2,7,8,17], .inr none),
    (![2,7,8,18], .inl (0,2)),
    (![2,7,9,10], .inl (0,1)),
    (![2,7,9,11], .inl (0,1)),
    (![2,7,9,12], .inl (0,1)),
    (![2,7,9,13], .inl (0,1)),
    (![2,7,9,14], .inl (1,0)),
    (![2,7,9,15], .inl (1,0)),
    (![2,7,9,16], .inl (1,0)),
    (![2,7,9,17], .inr none),
    (![2,7,9,18], .inl (0,1)),
    (![2,7,10,11], .inl (0,1)),
    (![2,7,10,12], .inl (0,1)),
    (![2,7,10,13], .inl (0,2)),
    (![2,7,10,14], .inl (1,0)),
    (![2,7,10,15], .inl (1,0)),
    (![2,7,10,16], .inl (1,0)),
    (![2,7,10,17], .inl (0,1)),
    (![2,7,10,18], .inl (0,1)),
    (![2,7,11,12], .inl (0,1)),
    (![2,7,11,13], .inl (1,2)),
    (![2,7,11,14], .inl (1,0)),
    (![2,7,11,15], .inl (1,0)),
    (![2,7,11,16], .inl (1,0)),
    (![2,7,11,17], .inl (0,1)),
    (![2,7,11,18], .inl (0,1)),
    (![2,7,12,13], .inl (1,0)),
    (![2,7,12,14], .inl (1,0)),
    (![2,7,12,15], .inl (1,0)),
    (![2,7,12,16], .inl (1,0)),
    (![2,7,12,17], .inl (0,1)),
    (![2,7,12,18], .inl (0,1)),
    (![2,7,13,14], .inl (1,0)),
    (![2,7,13,15], .inl (1,0)),
    (![2,7,13,16], .inl (1,0)),
    (![2,7,13,17], .inl (0,1)),
    (![2,7,13,18], .inl (0,1)),
    (![2,7,14,15], .inl (1,0)),
    (![2,7,14,16], .inl (0,3)),
    (![2,7,14,17], .inl (1,0)),
    (![2,7,14,18], .inl (0,1)),
    (![2,7,15,16], .inl (0,1)),
    (![2,7,15,17], .inl (1,0)),
    (![2,7,15,18], .inr (some (true,3,18))),
    (![2,7,16,17], .inl (1,0)),
    (![2,7,16,18], .inl (0,1)),
    (![2,7,17,18], .inl (1,0)),
    (![2,8,9,10], .inl (0,1)),
    (![2,8,9,11], .inl (0,1)),
    (![2,8,9,12], .inl (0,1)),
    (![2,8,9,13], .inl (0,1)),
    (![2,8,9,14], .inl (1,0)),
    (![2,8,9,15], .inl (1,0)),
    (![2,8,9,16], .inl (1,0)),
    (![2,8,9,17], .inr none),
    (![2,8,9,18], .inl (0,1)),
    (![2,8,10,11], .inl (0,1)),
    (![2,8,10,12], .inl (0,1)),
    (![2,8,10,13], .inr none),
    (![2,8,10,14], .inl (1,0)),
    (![2,8,10,15], .inl (1,0)),
    (![2,8,10,16], .inl (1,0)),
    (![2,8,10,17], .inl (0,1)),
    (![2,8,10,18], .inl (0,1)),
    (![2,8,11,12], .inl (0,1)),
    (![2,8,11,13], .inl (1,0)),
    (![2,8,11,14], .inl (1,0)),
    (![2,8,11,15], .inl (1,0)),
    (![2,8,11,16], .inl (1,0)),
    (![2,8,11,17], .inl (0,1)),
    (![2,8,11,18], .inl (0,1)),
    (![2,8,12,13], .inl (1,0)),
    (![2,8,12,14], .inl (1,0)),
    (![2,8,12,15], .inl (1,0)),
    (![2,8,12,16], .inl (1,0)),
    (![2,8,12,17], .inl (0,1)),
    (![2,8,12,18], .inl (0,1)),
    (![2,8,13,14], .inl (1,0)),
    (![2,8,13,15], .inl (1,0)),
    (![2,8,13,16], .inl (1,0)),
    (![2,8,13,17], .inl (0,1)),
    (![2,8,13,18], .inl (0,1)),
    (![2,8,14,15], .inl (1,0)),
    (![2,8,14,16], .inr none),
    (![2,8,14,17], .inl (1,0)),
    (![2,8,14,18], .inl (0,1)),
    (![2,8,15,16], .inl (0,1)),
    (![2,8,15,17], .inl (1,0)),
    (![2,8,15,18], .inl (0,1)),
    (![2,8,16,17], .inl (1,0)),
    (![2,8,16,18], .inl (0,1)),
    (![2,8,17,18], .inl (1,0)),
    (![2,9,10,11], .inl (2,1)),
    (![2,9,10,12], .inl (2,1)),
    (![2,9,10,13], .inl (2,0)),
    (![2,9,10,14], .inl (1,0)),
    (![2,9,10,15], .inl (1,0)),
    (![2,9,10,16], .inl (1,0)),
    (![2,9,10,17], .inl (0,1)),
    (![2,9,10,18], .inl (0,1)),
    (![2,9,11,12], .inl (2,1)),
    (![2,9,11,13], .inl (1,0)),
    (![2,9,11,14], .inl (1,0)),
    (![2,9,11,15], .inl (1,0)),
    (![2,9,11,16], .inl (1,0)),
    (![2,9,11,17], .inl (0,1)),
    (![2,9,11,18], .inl (0,1)),
    (![2,9,12,13], .inl (1,0)),
    (![2,9,12,14], .inl (1,0)),
    (![2,9,12,15], .inl (1,0)),
    (![2,9,12,16], .inl (1,0)),
    (![2,9,12,17], .inl (0,1)),
    (![2,9,12,18], .inl (0,1)),
    (![2,9,13,14], .inl (1,0)),
    (![2,9,13,15], .inl (1,0)),
    (![2,9,13,16], .inl (1,0)),
    (![2,9,13,17], .inl (0,1)),
    (![2,9,13,18], .inl (0,1)),
    (![2,9,14,15], .inl (1,0)),
    (![2,9,14,16], .inl (3,0)),
    (![2,9,14,17], .inl (1,0)),
    (![2,9,14,18], .inl (0,1)),
    (![2,9,15,16], .inl (3,1)),
    (![2,9,15,17], .inl (1,0)),
    (![2,9,15,18], .inl (0,1)),
    (![2,9,16,17], .inl (1,0)),
    (![2,9,16,18], .inl (0,1)),
    (![2,9,17,18], .inl (1,0)),
    (![2,10,11,12], .inl (2,1)),
    (![2,10,11,13], .inl (1,0)),
    (![2,10,11,14], .inl (1,0)),
    (![2,10,11,15], .inl (1,0)),
    (![2,10,11,16], .inl (1,0)),
    (![2,10,11,17], .inl (0,1)),
    (![2,10,11,18], .inl (0,1)),
    (![2,10,12,13], .inl (1,0)),
    (![2,10,12,14], .inl (1,0)),
    (![2,10,12,15], .inl (1,0)),
    (![2,10,12,16], .inl (1,0)),
    (![2,10,12,17], .inl (0,1)),
    (![2,10,12,18], .inl (0,1)),
    (![2,10,13,14], .inl (1,0)),
    (![2,10,13,15], .inl (1,0)),
    (![2,10,13,16], .inl (1,0)),
    (![2,10,13,17], .inl (0,1)),
    (![2,10,13,18], .inl (0,1)),
    (![2,10,14,15], .inl (1,0)),
    (![2,10,14,16], .inl (3,0)),
    (![2,10,14,17], .inr (some (false,1,23))),
    (![2,10,14,18], .inl (0,1)),
    (![2,10,15,16], .inl (3,0)),
    (![2,10,15,17], .inl (1,0)),
    (![2,10,15,18], .inl (0,1)),
    (![2,10,16,17], .inl (1,0)),
    (![2,10,16,18], .inl (0,1)),
    (![2,10,17,18], .inl (1,0)),
    (![2,11,12,13], .inl (1,0)),
    (![2,11,12,14], .inl (1,0)),
    (![2,11,12,15], .inl (1,0)),
    (![2,11,12,16], .inl (1,0)),
    (![2,11,12,17], .inl (0,1)),
    (![2,11,12,18], .inl (0,1)),
    (![2,11,13,14], .inl (1,0)),
    (![2,11,13,15], .inl (1,0)),
    (![2,11,13,16], .inl (1,0)),
    (![2,11,13,17], .inl (0,1)),
    (![2,11,13,18], .inl (0,1)),
    (![2,11,14,15], .inl (1,0)),
    (![2,11,14,16], .inl (3,0)),
    (![2,11,14,17], .inr (some (false,1,62))),
    (![2,11,14,18], .inl (0,1)),
    (![2,11,15,16], .inl (3,0)),
    (![2,11,15,17], .inr (some (false,1,63))),
    (![2,11,15,18], .inl (0,1)),
    (![2,11,16,17], .inl (1,0)),
    (![2,11,16,18], .inl (2,1)),
    (![2,11,17,18], .inl (1,0)),
    (![2,12,13,14], .inl (1,2)),
    (![2,12,13,15], .inl (1,2)),
    (![2,12,13,16], .inl (1,0)),
    (![2,12,13,17], .inl (0,1)),
    (![2,12,13,18], .inl (0,1)),
    (![2,12,14,15], .inl (1,2)),
    (![2,12,14,16], .inl (3,0)),
    (![2,12,14,17], .inr (some (false,1,64))),
    (![2,12,14,18], .inl (0,1)),
    (![2,12,15,16], .inl (3,0)),
    (![2,12,15,17], .inr (some (false,3,65))),
    (![2,12,15,18], .inl (0,1)),
    (![2,12,16,17], .inl (1,0)),
    (![2,12,16,18], .inl (2,0)),
    (![2,12,17,18], .inl (1,3)),
    (![2,13,14,15], .inl (1,2)),
    (![2,13,14,16], .inl (3,0)),
    (![2,13,14,17], .inr (some (false,1,66))),
    (![2,13,14,18], .inl (0,1)),
    (![2,13,15,16], .inl (3,0)),
    (![2,13,15,17], .inr (some (false,1,67))),
    (![2,13,15,18], .inl (0,1)),
    (![2,13,16,17], .inr (some (false,1,0))),
    (![2,13,16,18], .inl (2,0)),
    (![2,13,17,18], .inl (0,3)),
    (![2,14,15,16], .inl (3,0)),
    (![2,14,15,17], .inl (0,2)),
    (![2,14,15,18], .inl (0,1)),
    (![2,14,16,17], .inl (0,2)),
    (![2,14,16,18], .inl (2,0)),
    (![2,14,17,18], .inr (some (false,1,7))),
    (![2,15,16,17], .inl (0,2)),
    (![2,15,16,18], .inl (2,0)),
    (![2,15,17,18], .inr (some (false,3,8))),
    (![2,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid02 : ∀ k : Fin 560, CaseValid (block02 k).1 (block02 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align02 : (List.finRange 560).map (fun k => (block02 k).1) = fourTuples 2 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block03 : Fin 455 → Entry :=
  ![(![3,4,5,6], .inr none),
    (![3,4,5,7], .inr none),
    (![3,4,5,8], .inr none),
    (![3,4,5,9], .inr none),
    (![3,4,5,10], .inl (1,0)),
    (![3,4,5,11], .inl (1,0)),
    (![3,4,5,12], .inl (1,0)),
    (![3,4,5,13], .inl (1,0)),
    (![3,4,5,14], .inl (0,1)),
    (![3,4,5,15], .inl (0,1)),
    (![3,4,5,16], .inl (0,1)),
    (![3,4,5,17], .inr none),
    (![3,4,5,18], .inl (1,0)),
    (![3,4,6,7], .inr none),
    (![3,4,6,8], .inr none),
    (![3,4,6,9], .inr none),
    (![3,4,6,10], .inl (1,2)),
    (![3,4,6,11], .inl (1,2)),
    (![3,4,6,12], .inl (1,2)),
    (![3,4,6,13], .inl (1,2)),
    (![3,4,6,14], .inl (2,1)),
    (![3,4,6,15], .inl (2,1)),
    (![3,4,6,16], .inl (2,1)),
    (![3,4,6,17], .inr none),
    (![3,4,6,18], .inl (1,2)),
    (![3,4,7,8], .inr none),
    (![3,4,7,9], .inr none),
    (![3,4,7,10], .inl (0,2)),
    (![3,4,7,11], .inl (0,2)),
    (![3,4,7,12], .inl (0,2)),
    (![3,4,7,13], .inl (0,2)),
    (![3,4,7,14], .inl (2,0)),
    (![3,4,7,15], .inl (2,0)),
    (![3,4,7,16], .inl (2,0)),
    (![3,4,7,17], .inr none),
    (![3,4,7,18], .inl (0,2)),
    (![3,4,8,9], .inr none),
    (![3,4,8,10], .inl (0,1)),
    (![3,4,8,11], .inl (0,1)),
    (![3,4,8,12], .inl (0,1)),
    (![3,4,8,13], .inl (0,1)),
    (![3,4,8,14], .inl (1,0)),
    (![3,4,8,15], .inl (1,0)),
    (![3,4,8,16], .inl (1,0)),
    (![3,4,8,17], .inr none),
    (![3,4,8,18], .inl (0,1)),
    (![3,4,9,10], .inl (0,1)),
    (![3,4,9,11], .inl (0,1)),
    (![3,4,9,12], .inl (0,1)),
    (![3,4,9,13], .inl (0,1)),
    (![3,4,9,14], .inl (1,0)),
    (![3,4,9,15], .inl (1,0)),
    (![3,4,9,16], .inl (1,0)),
    (![3,4,9,17], .inr none),
    (![3,4,9,18], .inl (0,1)),
    (![3,4,10,11], .inl (0,1)),
    (![3,4,10,12], .inl (0,1)),
    (![3,4,10,13], .inl (0,1)),
    (![3,4,10,14], .inl (1,0)),
    (![3,4,10,15], .inl (1,0)),
    (![3,4,10,16], .inl (1,0)),
    (![3,4,10,17], .inl (0,1)),
    (![3,4,10,18], .inl (0,1)),
    (![3,4,11,12], .inl (0,1)),
    (![3,4,11,13], .inl (0,2)),
    (![3,4,11,14], .inl (1,0)),
    (![3,4,11,15], .inl (1,0)),
    (![3,4,11,16], .inl (1,0)),
    (![3,4,11,17], .inl (0,1)),
    (![3,4,11,18], .inl (0,1)),
    (![3,4,12,13], .inl (1,2)),
    (![3,4,12,14], .inr (some (false,1,88))),
    (![3,4,12,15], .inr (some (false,3,89))),
    (![3,4,12,16], .inl (1,0)),
    (![3,4,12,17], .inl (0,1)),
    (![3,4,12,18], .inl (0,1)),
    (![3,4,13,14], .inr (some (false,1,90))),
    (![3,4,13,15], .inr (some (false,1,91))),
    (![3,4,13,16], .inl (1,0)),
    (![3,4,13,17], .inl (0,1)),
    (![3,4,13,18], .inl (0,1)),
    (![3,4,14,15], .inl (1,3)),
    (![3,4,14,16], .inl (0,1)),
    (![3,4,14,17], .inl (1,0)),
    (![3,4,14,18], .inr (some (true,1,68))),
    (![3,4,15,16], .inl (0,1)),
    (![3,4,15,17], .inl (1,0)),
    (![3,4,15,18], .inr (some (true,3,10))),
    (![3,4,16,17], .inl (1,0)),
    (![3,4,16,18], .inl (0,1)),
    (![3,4,17,18], .inl (1,0)),
    (![3,5,6,7], .inr none),
    (![3,5,6,8], .inr none),
    (![3,5,6,9], .inr none),
    (![3,5,6,10], .inl (0,2)),
    (![3,5,6,11], .inl (0,2)),
    (![3,5,6,12], .inl (0,2)),
    (![3,5,6,13], .inl (0,2)),
    (![3,5,6,14], .inl (2,0)),
    (![3,5,6,15], .inl (2,0)),
    (![3,5,6,16], .inl (2,0)),
    (![3,5,6,17], .inr none),
    (![3,5,6,18], .inl (0,2)),
    (![3,5,7,8], .inr none),
    (![3,5,7,9], .inr none),
    (![3,5,7,10], .inl (0,2)),
    (![3,5,7,11], .inl (0,2)),
    (![3,5,7,12], .inl (0,2)),
    (![3,5,7,13], .inl (0,2)),
    (![3,5,7,14], .inl (2,0)),
    (![3,5,7,15], .inl (2,0)),
    (![3,5,7,16], .inl (2,0)),
    (![3,5,7,17], .inr none),
    (![3,5,7,18], .inl (0,2)),
    (![3,5,8,9], .inr none),
    (![3,5,8,10], .inl (0,1)),
    (![3,5,8,11], .inl (0,1)),
    (![3,5,8,12], .inl (0,1)),
    (![3,5,8,13], .inl (0,1)),
    (![3,5,8,14], .inl (1,0)),
    (![3,5,8,15], .inl (1,0)),
    (![3,5,8,16], .inl (1,0)),
    (![3,5,8,17], .inr none),
    (![3,5,8,18], .inl (0,1)),
    (![3,5,9,10], .inl (0,1)),
    (![3,5,9,11], .inl (0,1)),
    (![3,5,9,12], .inl (0,1)),
    (![3,5,9,13], .inl (0,1)),
    (![3,5,9,14], .inl (1,0)),
    (![3,5,9,15], .inl (1,0)),
    (![3,5,9,16], .inl (1,0)),
    (![3,5,9,17], .inr none),
    (![3,5,9,18], .inl (0,1)),
    (![3,5,10,11], .inl (0,1)),
    (![3,5,10,12], .inl (0,1)),
    (![3,5,10,13], .inl (0,1)),
    (![3,5,10,14], .inl (1,0)),
    (![3,5,10,15], .inl (1,0)),
    (![3,5,10,16], .inl (1,0)),
    (![3,5,10,17], .inl (0,1)),
    (![3,5,10,18], .inl (0,1)),
    (![3,5,11,12], .inl (0,1)),
    (![3,5,11,13], .inl (0,2)),
    (![3,5,11,14], .inr (some (false,2,99))),
    (![3,5,11,15], .inl (1,0)),
    (![3,5,11,16], .inl (1,0)),
    (![3,5,11,17], .inl (0,1)),
    (![3,5,11,18], .inl (0,1)),
    (![3,5,12,13], .inl (0,2)),
    (![3,5,12,14], .inr (some (false,2,165))),
    (![3,5,12,15], .inr (some (false,3,166))),
    (![3,5,12,16], .inl (1,0)),
    (![3,5,12,17], .inl (0,1)),
    (![3,5,12,18], .inl (0,1)),
    (![3,5,13,14], .inr (some (false,1,167))),
    (![3,5,13,15], .inr (some (false,2,168))),
    (![3,5,13,16], .inl (1,0)),
    (![3,5,13,17], .inl (0,1)),
    (![3,5,13,18], .inl (3,1)),
    (![3,5,14,15], .inl (0,3)),
    (![3,5,14,16], .inl (0,1)),
    (![3,5,14,17], .inl (1,0)),
    (![3,5,14,18], .inr (some (true,1,69))),
    (![3,5,15,16], .inl (0,1)),
    (![3,5,15,17], .inl (1,0)),
    (![3,5,15,18], .inr (some (true,6,10))),
    (![3,5,16,17], .inl (1,0)),
    (![3,5,16,18], .inl (0,1)),
    (![3,5,17,18], .inl (1,0)),
    (![3,6,7,8], .inr none),
    (![3,6,7,9], .inr none),
    (![3,6,7,10], .inl (0,2)),
    (![3,6,7,11], .inl (0,2)),
    (![3,6,7,12], .inl (0,2)),
    (![3,6,7,13], .inl (0,2)),
    (![3,6,7,14], .inl (2,0)),
    (![3,6,7,15], .inl (2,0)),
    (![3,6,7,16], .inl (2,0)),
    (![3,6,7,17], .inr none),
    (![3,6,7,18], .inl (0,2)),
    (![3,6,8,9], .inr none),
    (![3,6,8,10], .inl (0,1)),
    (![3,6,8,11], .inl (0,1)),
    (![3,6,8,12], .inl (0,1)),
    (![3,6,8,13], .inl (0,1)),
    (![3,6,8,14], .inl (1,0)),
    (![3,6,8,15], .inl (1,0)),
    (![3,6,8,16], .inl (1,0)),
    (![3,6,8,17], .inr none),
    (![3,6,8,18], .inl (0,1)),
    (![3,6,9,10], .inl (0,1)),
    (![3,6,9,11], .inl (0,1)),
    (![3,6,9,12], .inl (0,1)),
    (![3,6,9,13], .inl (0,1)),
    (![3,6,9,14], .inl (1,0)),
    (![3,6,9,15], .inl (1,0)),
    (![3,6,9,16], .inl (1,0)),
    (![3,6,9,17], .inr none),
    (![3,6,9,18], .inl (0,1)),
    (![3,6,10,11], .inl (0,1)),
    (![3,6,10,12], .inl (0,1)),
    (![3,6,10,13], .inl (0,1)),
    (![3,6,10,14], .inl (1,0)),
    (![3,6,10,15], .inl (1,0)),
    (![3,6,10,16], .inl (1,0)),
    (![3,6,10,17], .inl (0,1)),
    (![3,6,10,18], .inl (0,1)),
    (![3,6,11,12], .inl (0,1)),
    (![3,6,11,13], .inl (0,2)),
    (![3,6,11,14], .inl (1,0)),
    (![3,6,11,15], .inl (1,0)),
    (![3,6,11,16], .inl (1,0)),
    (![3,6,11,17], .inl (0,1)),
    (![3,6,11,18], .inl (0,1)),
    (![3,6,12,13], .inl (1,2)),
    (![3,6,12,14], .inr (some (false,1,117))),
    (![3,6,12,15], .inr (some (false,3,118))),
    (![3,6,12,16], .inl (1,0)),
    (![3,6,12,17], .inl (0,1)),
    (![3,6,12,18], .inl (0,1)),
    (![3,6,13,14], .inr (some (false,1,119))),
    (![3,6,13,15], .inr (some (false,1,120))),
    (![3,6,13,16], .inl (1,0)),
    (![3,6,13,17], .inl (0,1)),
    (![3,6,13,18], .inl (0,1)),
    (![3,6,14,15], .inl (1,3)),
    (![3,6,14,16], .inl (0,1)),
    (![3,6,14,17], .inl (1,0)),
    (![3,6,14,18], .inr (some (true,1,70))),
    (![3,6,15,16], .inl (0,1)),
    (![3,6,15,17], .inl (1,0)),
    (![3,6,15,18], .inr (some (true,3,10))),
    (![3,6,16,17], .inl (1,0)),
    (![3,6,16,18], .inl (0,1)),
    (![3,6,17,18], .inl (1,0)),
    (![3,7,8,9], .inr none),
    (![3,7,8,10], .inl (0,1)),
    (![3,7,8,11], .inl (0,1)),
    (![3,7,8,12], .inl (0,1)),
    (![3,7,8,13], .inl (0,1)),
    (![3,7,8,14], .inl (1,0)),
    (![3,7,8,15], .inl (1,0)),
    (![3,7,8,16], .inl (1,0)),
    (![3,7,8,17], .inr none),
    (![3,7,8,18], .inl (0,1)),
    (![3,7,9,10], .inl (0,1)),
    (![3,7,9,11], .inl (0,1)),
    (![3,7,9,12], .inl (0,1)),
    (![3,7,9,13], .inl (0,1)),
    (![3,7,9,14], .inl (1,0)),
    (![3,7,9,15], .inl (1,0)),
    (![3,7,9,16], .inl (1,0)),
    (![3,7,9,17], .inr none),
    (![3,7,9,18], .inl (0,1)),
    (![3,7,10,11], .inl (0,1)),
    (![3,7,10,12], .inl (0,1)),
    (![3,7,10,13], .inl (0,1)),
    (![3,7,10,14], .inl (1,0)),
    (![3,7,10,15], .inl (1,0)),
    (![3,7,10,16], .inl (1,0)),
    (![3,7,10,17], .inl (0,1)),
    (![3,7,10,18], .inl (0,1)),
    (![3,7,11,12], .inl (0,1)),
    (![3,7,11,13], .inr none),
    (![3,7,11,14], .inl (1,0)),
    (![3,7,11,15], .inl (1,0)),
    (![3,7,11,16], .inl (1,0)),
    (![3,7,11,17], .inl (0,1)),
    (![3,7,11,18], .inl (0,1)),
    (![3,7,12,13], .inl (1,0)),
    (![3,7,12,14], .inl (1,0)),
    (![3,7,12,15], .inl (1,0)),
    (![3,7,12,16], .inl (1,0)),
    (![3,7,12,17], .inl (0,1)),
    (![3,7,12,18], .inl (0,1)),
    (![3,7,13,14], .inl (1,0)),
    (![3,7,13,15], .inl (1,0)),
    (![3,7,13,16], .inl (1,0)),
    (![3,7,13,17], .inl (0,1)),
    (![3,7,13,18], .inl (0,1)),
    (![3,7,14,15], .inl (1,0)),
    (![3,7,14,16], .inl (0,1)),
    (![3,7,14,17], .inl (1,0)),
    (![3,7,14,18], .inl (0,1)),
    (![3,7,15,16], .inl (0,1)),
    (![3,7,15,17], .inl (1,0)),
    (![3,7,15,18], .inr none),
    (![3,7,16,17], .inl (1,0)),
    (![3,7,16,18], .inl (0,1)),
    (![3,7,17,18], .inl (1,0)),
    (![3,8,9,10], .inl (0,1)),
    (![3,8,9,11], .inl (0,1)),
    (![3,8,9,12], .inl (0,1)),
    (![3,8,9,13], .inl (0,1)),
    (![3,8,9,14], .inl (1,0)),
    (![3,8,9,15], .inl (1,0)),
    (![3,8,9,16], .inl (1,0)),
    (![3,8,9,17], .inr none),
    (![3,8,9,18], .inl (0,1)),
    (![3,8,10,11], .inl (0,1)),
    (![3,8,10,12], .inl (0,1)),
    (![3,8,10,13], .inl (2,1)),
    (![3,8,10,14], .inl (1,0)),
    (![3,8,10,15], .inl (1,0)),
    (![3,8,10,16], .inl (1,0)),
    (![3,8,10,17], .inl (0,1)),
    (![3,8,10,18], .inl (0,1)),
    (![3,8,11,12], .inl (0,1)),
    (![3,8,11,13], .inl (2,0)),
    (![3,8,11,14], .inl (1,0)),
    (![3,8,11,15], .inl (1,0)),
    (![3,8,11,16], .inl (1,0)),
    (![3,8,11,17], .inl (0,1)),
    (![3,8,11,18], .inl (0,1)),
    (![3,8,12,13], .inl (1,0)),
    (![3,8,12,14], .inl (1,0)),
    (![3,8,12,15], .inl (1,0)),
    (![3,8,12,16], .inl (1,0)),
    (![3,8,12,17], .inl (0,1)),
    (![3,8,12,18], .inl (0,1)),
    (![3,8,13,14], .inl (1,0)),
    (![3,8,13,15], .inl (1,0)),
    (![3,8,13,16], .inl (1,0)),
    (![3,8,13,17], .inl (0,1)),
    (![3,8,13,18], .inl (0,1)),
    (![3,8,14,15], .inl (1,0)),
    (![3,8,14,16], .inl (3,1)),
    (![3,8,14,17], .inl (1,0)),
    (![3,8,14,18], .inl (0,1)),
    (![3,8,15,16], .inl (0,1)),
    (![3,8,15,17], .inl (1,0)),
    (![3,8,15,18], .inr (some (false,3,10))),
    (![3,8,16,17], .inl (1,0)),
    (![3,8,16,18], .inl (0,1)),
    (![3,8,17,18], .inl (1,0)),
    (![3,9,10,11], .inl (2,1)),
    (![3,9,10,12], .inl (2,1)),
    (![3,9,10,13], .inl (2,0)),
    (![3,9,10,14], .inl (1,0)),
    (![3,9,10,15], .inl (1,0)),
    (![3,9,10,16], .inl (1,0)),
    (![3,9,10,17], .inl (0,1)),
    (![3,9,10,18], .inl (0,1)),
    (![3,9,11,12], .inl (2,1)),
    (![3,9,11,13], .inl (2,0)),
    (![3,9,11,14], .inl (1,0)),
    (![3,9,11,15], .inl (1,0)),
    (![3,9,11,16], .inl (1,0)),
    (![3,9,11,17], .inl (0,1)),
    (![3,9,11,18], .inl (0,1)),
    (![3,9,12,13], .inl (1,0)),
    (![3,9,12,14], .inl (1,0)),
    (![3,9,12,15], .inl (1,0)),
    (![3,9,12,16], .inl (1,0)),
    (![3,9,12,17], .inl (0,1)),
    (![3,9,12,18], .inl (0,1)),
    (![3,9,13,14], .inl (1,0)),
    (![3,9,13,15], .inl (1,0)),
    (![3,9,13,16], .inl (1,0)),
    (![3,9,13,17], .inl (0,1)),
    (![3,9,13,18], .inl (0,1)),
    (![3,9,14,15], .inl (1,0)),
    (![3,9,14,16], .inl (3,0)),
    (![3,9,14,17], .inl (1,0)),
    (![3,9,14,18], .inl (0,1)),
    (![3,9,15,16], .inl (3,1)),
    (![3,9,15,17], .inl (1,0)),
    (![3,9,15,18], .inr (some (false,6,10))),
    (![3,9,16,17], .inl (1,0)),
    (![3,9,16,18], .inl (0,1)),
    (![3,9,17,18], .inl (1,0)),
    (![3,10,11,12], .inl (2,1)),
    (![3,10,11,13], .inl (2,0)),
    (![3,10,11,14], .inl (1,0)),
    (![3,10,11,15], .inl (1,0)),
    (![3,10,11,16], .inl (1,0)),
    (![3,10,11,17], .inl (0,1)),
    (![3,10,11,18], .inl (0,1)),
    (![3,10,12,13], .inl (1,0)),
    (![3,10,12,14], .inl (1,0)),
    (![3,10,12,15], .inl (1,0)),
    (![3,10,12,16], .inl (1,0)),
    (![3,10,12,17], .inl (0,1)),
    (![3,10,12,18], .inl (0,1)),
    (![3,10,13,14], .inl (1,0)),
    (![3,10,13,15], .inl (1,0)),
    (![3,10,13,16], .inl (1,0)),
    (![3,10,13,17], .inl (0,1)),
    (![3,10,13,18], .inl (0,1)),
    (![3,10,14,15], .inl (1,0)),
    (![3,10,14,16], .inl (3,0)),
    (![3,10,14,17], .inr (some (false,1,23))),
    (![3,10,14,18], .inl (0,1)),
    (![3,10,15,16], .inl (3,0)),
    (![3,10,15,17], .inl (1,0)),
    (![3,10,15,18], .inr (some (false,5,10))),
    (![3,10,16,17], .inl (1,0)),
    (![3,10,16,18], .inl (0,1)),
    (![3,10,17,18], .inl (1,0)),
    (![3,11,12,13], .inl (1,0)),
    (![3,11,12,14], .inl (1,0)),
    (![3,11,12,15], .inl (1,0)),
    (![3,11,12,16], .inl (1,0)),
    (![3,11,12,17], .inl (0,1)),
    (![3,11,12,18], .inl (0,1)),
    (![3,11,13,14], .inl (1,0)),
    (![3,11,13,15], .inl (1,0)),
    (![3,11,13,16], .inl (1,0)),
    (![3,11,13,17], .inl (0,1)),
    (![3,11,13,18], .inl (0,1)),
    (![3,11,14,15], .inl (1,0)),
    (![3,11,14,16], .inl (3,0)),
    (![3,11,14,17], .inr (some (false,1,71))),
    (![3,11,14,18], .inl (0,1)),
    (![3,11,15,16], .inl (3,0)),
    (![3,11,15,17], .inr (some (false,1,72))),
    (![3,11,15,18], .inr (some (false,4,10))),
    (![3,11,16,17], .inl (1,0)),
    (![3,11,16,18], .inl (2,1)),
    (![3,11,17,18], .inl (1,0)),
    (![3,12,13,14], .inl (1,2)),
    (![3,12,13,15], .inl (1,2)),
    (![3,12,13,16], .inl (1,0)),
    (![3,12,13,17], .inl (0,1)),
    (![3,12,13,18], .inl (0,1)),
    (![3,12,14,15], .inl (1,2)),
    (![3,12,14,16], .inl (3,0)),
    (![3,12,14,17], .inr (some (false,1,73))),
    (![3,12,14,18], .inl (0,1)),
    (![3,12,15,16], .inl (3,0)),
    (![3,12,15,17], .inr (some (false,3,74))),
    (![3,12,15,18], .inr (some (false,3,10))),
    (![3,12,16,17], .inl (1,0)),
    (![3,12,16,18], .inl (2,0)),
    (![3,12,17,18], .inl (1,3)),
    (![3,13,14,15], .inl (1,2)),
    (![3,13,14,16], .inl (3,0)),
    (![3,13,14,17], .inr (some (false,1,75))),
    (![3,13,14,18], .inl (0,1)),
    (![3,13,15,16], .inl (3,0)),
    (![3,13,15,17], .inr (some (false,1,76))),
    (![3,13,15,18], .inr (some (false,2,10))),
    (![3,13,16,17], .inr (some (false,1,0))),
    (![3,13,16,18], .inl (2,0)),
    (![3,13,17,18], .inl (0,3)),
    (![3,14,15,16], .inl (2,0)),
    (![3,14,15,17], .inl (0,2)),
    (![3,14,15,18], .inr (some (false,1,10))),
    (![3,14,16,17], .inl (0,2)),
    (![3,14,16,18], .inl (2,0)),
    (![3,14,17,18], .inr (some (false,1,9))),
    (![3,15,16,17], .inl (0,2)),
    (![3,15,16,18], .inr (some (true,4,10))),
    (![3,15,17,18], .inr (some (false,3,10))),
    (![3,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid03 : ∀ k : Fin 455, CaseValid (block03 k).1 (block03 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align03 : (List.finRange 455).map (fun k => (block03 k).1) = fourTuples 3 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block04 : Fin 364 → Entry :=
  ![(![4,5,6,7], .inr none),
    (![4,5,6,8], .inr none),
    (![4,5,6,9], .inr none),
    (![4,5,6,10], .inl (0,2)),
    (![4,5,6,11], .inl (0,2)),
    (![4,5,6,12], .inl (0,2)),
    (![4,5,6,13], .inl (0,2)),
    (![4,5,6,14], .inl (2,0)),
    (![4,5,6,15], .inl (2,0)),
    (![4,5,6,16], .inl (2,0)),
    (![4,5,6,17], .inr none),
    (![4,5,6,18], .inl (0,2)),
    (![4,5,7,8], .inr none),
    (![4,5,7,9], .inr none),
    (![4,5,7,10], .inl (0,1)),
    (![4,5,7,11], .inl (0,1)),
    (![4,5,7,12], .inl (0,1)),
    (![4,5,7,13], .inl (0,1)),
    (![4,5,7,14], .inl (1,0)),
    (![4,5,7,15], .inl (1,0)),
    (![4,5,7,16], .inl (1,0)),
    (![4,5,7,17], .inr none),
    (![4,5,7,18], .inl (0,1)),
    (![4,5,8,9], .inr none),
    (![4,5,8,10], .inl (0,1)),
    (![4,5,8,11], .inl (0,1)),
    (![4,5,8,12], .inl (0,1)),
    (![4,5,8,13], .inl (0,1)),
    (![4,5,8,14], .inl (1,0)),
    (![4,5,8,15], .inl (1,0)),
    (![4,5,8,16], .inl (1,0)),
    (![4,5,8,17], .inr none),
    (![4,5,8,18], .inl (0,1)),
    (![4,5,9,10], .inl (0,1)),
    (![4,5,9,11], .inl (0,1)),
    (![4,5,9,12], .inl (0,1)),
    (![4,5,9,13], .inl (0,1)),
    (![4,5,9,14], .inl (1,0)),
    (![4,5,9,15], .inl (1,0)),
    (![4,5,9,16], .inl (1,0)),
    (![4,5,9,17], .inr none),
    (![4,5,9,18], .inl (0,1)),
    (![4,5,10,11], .inl (0,1)),
    (![4,5,10,12], .inl (0,1)),
    (![4,5,10,13], .inl (0,1)),
    (![4,5,10,14], .inl (1,0)),
    (![4,5,10,15], .inl (1,0)),
    (![4,5,10,16], .inl (1,0)),
    (![4,5,10,17], .inl (0,1)),
    (![4,5,10,18], .inl (0,1)),
    (![4,5,11,12], .inl (0,1)),
    (![4,5,11,13], .inl (0,1)),
    (![4,5,11,14], .inr (some (false,1,99))),
    (![4,5,11,15], .inl (1,0)),
    (![4,5,11,16], .inl (1,0)),
    (![4,5,11,17], .inl (0,1)),
    (![4,5,11,18], .inl (0,1)),
    (![4,5,12,13], .inl (0,2)),
    (![4,5,12,14], .inr (some (false,1,88))),
    (![4,5,12,15], .inr (some (false,3,89))),
    (![4,5,12,16], .inl (1,0)),
    (![4,5,12,17], .inl (0,1)),
    (![4,5,12,18], .inl (0,1)),
    (![4,5,13,14], .inr (some (false,1,90))),
    (![4,5,13,15], .inr (some (false,1,91))),
    (![4,5,13,16], .inl (1,0)),
    (![4,5,13,17], .inl (0,1)),
    (![4,5,13,18], .inl (3,1)),
    (![4,5,14,15], .inl (0,3)),
    (![4,5,14,16], .inl (0,1)),
    (![4,5,14,17], .inl (1,0)),
    (![4,5,14,18], .inl (1,0)),
    (![4,5,15,16], .inl (0,1)),
    (![4,5,15,17], .inl (1,0)),
    (![4,5,15,18], .inl (1,0)),
    (![4,5,16,17], .inl (1,0)),
    (![4,5,16,18], .inl (0,1)),
    (![4,5,17,18], .inl (1,0)),
    (![4,6,7,8], .inr none),
    (![4,6,7,9], .inr none),
    (![4,6,7,10], .inl (0,1)),
    (![4,6,7,11], .inl (0,1)),
    (![4,6,7,12], .inl (0,1)),
    (![4,6,7,13], .inl (0,1)),
    (![4,6,7,14], .inl (1,0)),
    (![4,6,7,15], .inl (1,0)),
    (![4,6,7,16], .inl (1,0)),
    (![4,6,7,17], .inr none),
    (![4,6,7,18], .inl (0,1)),
    (![4,6,8,9], .inr none),
    (![4,6,8,10], .inl (0,1)),
    (![4,6,8,11], .inl (0,1)),
    (![4,6,8,12], .inl (0,1)),
    (![4,6,8,13], .inl (0,1)),
    (![4,6,8,14], .inl (1,0)),
    (![4,6,8,15], .inl (1,0)),
    (![4,6,8,16], .inl (1,0)),
    (![4,6,8,17], .inr none),
    (![4,6,8,18], .inl (0,1)),
    (![4,6,9,10], .inl (0,1)),
    (![4,6,9,11], .inl (0,1)),
    (![4,6,9,12], .inl (0,1)),
    (![4,6,9,13], .inl (0,1)),
    (![4,6,9,14], .inl (1,0)),
    (![4,6,9,15], .inl (1,0)),
    (![4,6,9,16], .inl (1,0)),
    (![4,6,9,17], .inr none),
    (![4,6,9,18], .inl (0,1)),
    (![4,6,10,11], .inl (0,1)),
    (![4,6,10,12], .inl (0,1)),
    (![4,6,10,13], .inl (0,1)),
    (![4,6,10,14], .inl (1,0)),
    (![4,6,10,15], .inl (1,0)),
    (![4,6,10,16], .inl (1,0)),
    (![4,6,10,17], .inl (0,1)),
    (![4,6,10,18], .inl (0,1)),
    (![4,6,11,12], .inl (0,1)),
    (![4,6,11,13], .inl (0,1)),
    (![4,6,11,14], .inl (1,0)),
    (![4,6,11,15], .inl (1,0)),
    (![4,6,11,16], .inl (1,0)),
    (![4,6,11,17], .inl (0,1)),
    (![4,6,11,18], .inl (0,1)),
    (![4,6,12,13], .inr none),
    (![4,6,12,14], .inr none),
    (![4,6,12,15], .inr none),
    (![4,6,12,16], .inl (1,0)),
    (![4,6,12,17], .inl (0,1)),
    (![4,6,12,18], .inl (0,1)),
    (![4,6,13,14], .inr none),
    (![4,6,13,15], .inr none),
    (![4,6,13,16], .inl (1,0)),
    (![4,6,13,17], .inl (0,1)),
    (![4,6,13,18], .inl (0,1)),
    (![4,6,14,15], .inr none),
    (![4,6,14,16], .inl (0,1)),
    (![4,6,14,17], .inl (1,0)),
    (![4,6,14,18], .inl (1,0)),
    (![4,6,15,16], .inl (0,1)),
    (![4,6,15,17], .inl (1,0)),
    (![4,6,15,18], .inl (1,0)),
    (![4,6,16,17], .inl (1,0)),
    (![4,6,16,18], .inl (0,1)),
    (![4,6,17,18], .inl (1,0)),
    (![4,7,8,9], .inr none),
    (![4,7,8,10], .inl (0,1)),
    (![4,7,8,11], .inl (0,1)),
    (![4,7,8,12], .inl (0,1)),
    (![4,7,8,13], .inl (0,1)),
    (![4,7,8,14], .inl (1,0)),
    (![4,7,8,15], .inl (1,0)),
    (![4,7,8,16], .inl (1,0)),
    (![4,7,8,17], .inr none),
    (![4,7,8,18], .inl (0,1)),
    (![4,7,9,10], .inl (0,1)),
    (![4,7,9,11], .inl (0,1)),
    (![4,7,9,12], .inl (0,1)),
    (![4,7,9,13], .inl (0,1)),
    (![4,7,9,14], .inl (1,0)),
    (![4,7,9,15], .inl (1,0)),
    (![4,7,9,16], .inl (1,0)),
    (![4,7,9,17], .inr none),
    (![4,7,9,18], .inl (0,1)),
    (![4,7,10,11], .inl (0,1)),
    (![4,7,10,12], .inl (0,1)),
    (![4,7,10,13], .inl (0,1)),
    (![4,7,10,14], .inl (1,0)),
    (![4,7,10,15], .inl (1,0)),
    (![4,7,10,16], .inl (1,0)),
    (![4,7,10,17], .inl (0,1)),
    (![4,7,10,18], .inl (0,1)),
    (![4,7,11,12], .inl (0,1)),
    (![4,7,11,13], .inl (2,1)),
    (![4,7,11,14], .inl (1,0)),
    (![4,7,11,15], .inl (1,0)),
    (![4,7,11,16], .inl (1,0)),
    (![4,7,11,17], .inl (0,1)),
    (![4,7,11,18], .inl (0,1)),
    (![4,7,12,13], .inl (2,0)),
    (![4,7,12,14], .inr (some (true,1,88))),
    (![4,7,12,15], .inr (some (true,3,89))),
    (![4,7,12,16], .inl (1,0)),
    (![4,7,12,17], .inl (0,1)),
    (![4,7,12,18], .inl (0,1)),
    (![4,7,13,14], .inr (some (true,1,90))),
    (![4,7,13,15], .inr (some (true,1,91))),
    (![4,7,13,16], .inl (1,0)),
    (![4,7,13,17], .inl (0,1)),
    (![4,7,13,18], .inl (0,1)),
    (![4,7,14,15], .inl (3,0)),
    (![4,7,14,16], .inl (0,1)),
    (![4,7,14,17], .inl (1,0)),
    (![4,7,14,18], .inr (some (false,1,77))),
    (![4,7,15,16], .inl (0,1)),
    (![4,7,15,17], .inl (1,0)),
    (![4,7,15,18], .inr (some (false,3,18))),
    (![4,7,16,17], .inl (1,0)),
    (![4,7,16,18], .inl (0,1)),
    (![4,7,17,18], .inl (1,0)),
    (![4,8,9,10], .inl (0,1)),
    (![4,8,9,11], .inl (0,1)),
    (![4,8,9,12], .inl (0,1)),
    (![4,8,9,13], .inl (0,1)),
    (![4,8,9,14], .inl (1,0)),
    (![4,8,9,15], .inl (1,0)),
    (![4,8,9,16], .inl (1,0)),
    (![4,8,9,17], .inr none),
    (![4,8,9,18], .inl (0,1)),
    (![4,8,10,11], .inl (0,1)),
    (![4,8,10,12], .inl (0,1)),
    (![4,8,10,13], .inl (2,1)),
    (![4,8,10,14], .inl (1,0)),
    (![4,8,10,15], .inl (1,0)),
    (![4,8,10,16], .inl (1,0)),
    (![4,8,10,17], .inl (0,1)),
    (![4,8,10,18], .inl (0,1)),
    (![4,8,11,12], .inl (0,1)),
    (![4,8,11,13], .inl (2,0)),
    (![4,8,11,14], .inl (1,0)),
    (![4,8,11,15], .inl (1,0)),
    (![4,8,11,16], .inl (1,0)),
    (![4,8,11,17], .inl (0,1)),
    (![4,8,11,18], .inl (0,1)),
    (![4,8,12,13], .inl (2,0)),
    (![4,8,12,14], .inr (some (true,2,88))),
    (![4,8,12,15], .inr (some (true,6,89))),
    (![4,8,12,16], .inl (1,0)),
    (![4,8,12,17], .inl (0,1)),
    (![4,8,12,18], .inl (0,1)),
    (![4,8,13,14], .inr (some (true,2,90))),
    (![4,8,13,15], .inr (some (true,2,91))),
    (![4,8,13,16], .inl (1,0)),
    (![4,8,13,17], .inl (0,1)),
    (![4,8,13,18], .inl (0,1)),
    (![4,8,14,15], .inl (3,0)),
    (![4,8,14,16], .inl (3,1)),
    (![4,8,14,17], .inl (1,0)),
    (![4,8,14,18], .inr (some (false,1,78))),
    (![4,8,15,16], .inl (0,1)),
    (![4,8,15,17], .inl (1,0)),
    (![4,8,15,18], .inr (some (false,3,79))),
    (![4,8,16,17], .inl (1,0)),
    (![4,8,16,18], .inl (0,1)),
    (![4,8,17,18], .inl (1,0)),
    (![4,9,10,11], .inl (2,1)),
    (![4,9,10,12], .inl (2,1)),
    (![4,9,10,13], .inl (2,0)),
    (![4,9,10,14], .inl (1,0)),
    (![4,9,10,15], .inl (1,0)),
    (![4,9,10,16], .inl (1,0)),
    (![4,9,10,17], .inl (0,1)),
    (![4,9,10,18], .inl (0,1)),
    (![4,9,11,12], .inl (2,1)),
    (![4,9,11,13], .inl (2,0)),
    (![4,9,11,14], .inl (1,0)),
    (![4,9,11,15], .inl (1,0)),
    (![4,9,11,16], .inl (1,0)),
    (![4,9,11,17], .inl (0,1)),
    (![4,9,11,18], .inl (0,1)),
    (![4,9,12,13], .inl (2,0)),
    (![4,9,12,14], .inr (some (true,3,88))),
    (![4,9,12,15], .inr (some (true,9,89))),
    (![4,9,12,16], .inl (1,0)),
    (![4,9,12,17], .inl (0,1)),
    (![4,9,12,18], .inl (0,1)),
    (![4,9,13,14], .inr (some (true,3,90))),
    (![4,9,13,15], .inr (some (true,3,91))),
    (![4,9,13,16], .inl (1,0)),
    (![4,9,13,17], .inl (0,1)),
    (![4,9,13,18], .inl (0,1)),
    (![4,9,14,15], .inl (3,0)),
    (![4,9,14,16], .inl (3,0)),
    (![4,9,14,17], .inl (1,0)),
    (![4,9,14,18], .inr (some (false,1,80))),
    (![4,9,15,16], .inl (3,1)),
    (![4,9,15,17], .inl (1,0)),
    (![4,9,15,18], .inr (some (false,3,81))),
    (![4,9,16,17], .inl (1,0)),
    (![4,9,16,18], .inl (0,1)),
    (![4,9,17,18], .inl (1,0)),
    (![4,10,11,12], .inl (2,1)),
    (![4,10,11,13], .inl (2,0)),
    (![4,10,11,14], .inl (1,0)),
    (![4,10,11,15], .inl (1,0)),
    (![4,10,11,16], .inl (1,0)),
    (![4,10,11,17], .inl (0,1)),
    (![4,10,11,18], .inl (0,1)),
    (![4,10,12,13], .inl (2,0)),
    (![4,10,12,14], .inr (some (true,2,88))),
    (![4,10,12,15], .inr (some (true,6,89))),
    (![4,10,12,16], .inl (1,0)),
    (![4,10,12,17], .inl (0,1)),
    (![4,10,12,18], .inl (0,1)),
    (![4,10,13,14], .inr (some (true,2,90))),
    (![4,10,13,15], .inr (some (true,2,91))),
    (![4,10,13,16], .inl (1,0)),
    (![4,10,13,17], .inl (0,1)),
    (![4,10,13,18], .inl (0,1)),
    (![4,10,14,15], .inl (3,0)),
    (![4,10,14,16], .inl (3,0)),
    (![4,10,14,17], .inr (some (false,1,23))),
    (![4,10,14,18], .inr (some (false,1,82))),
    (![4,10,15,16], .inl (3,0)),
    (![4,10,15,17], .inl (1,0)),
    (![4,10,15,18], .inr (some (false,1,83))),
    (![4,10,16,17], .inl (1,0)),
    (![4,10,16,18], .inl (0,1)),
    (![4,10,17,18], .inl (1,0)),
    (![4,11,12,13], .inl (2,0)),
    (![4,11,12,14], .inr (some (true,1,88))),
    (![4,11,12,15], .inr (some (true,3,89))),
    (![4,11,12,16], .inl (1,0)),
    (![4,11,12,17], .inl (0,1)),
    (![4,11,12,18], .inl (0,1)),
    (![4,11,13,14], .inr (some (true,1,90))),
    (![4,11,13,15], .inr (some (true,1,91))),
    (![4,11,13,16], .inl (1,0)),
    (![4,11,13,17], .inl (0,1)),
    (![4,11,13,18], .inl (0,1)),
    (![4,11,14,15], .inl (3,0)),
    (![4,11,14,16], .inl (3,0)),
    (![4,11,14,17], .inr (some (false,1,84))),
    (![4,11,14,18], .inr (some (false,1,85))),
    (![4,11,15,16], .inl (3,0)),
    (![4,11,15,17], .inr (some (false,1,86))),
    (![4,11,15,18], .inr (some (false,1,87))),
    (![4,11,16,17], .inl (1,0)),
    (![4,11,16,18], .inl (2,1)),
    (![4,11,17,18], .inl (1,0)),
    (![4,12,13,14], .inr none),
    (![4,12,13,15], .inr none),
    (![4,12,13,16], .inl (1,0)),
    (![4,12,13,17], .inl (0,1)),
    (![4,12,13,18], .inl (0,1)),
    (![4,12,14,15], .inr none),
    (![4,12,14,16], .inr (some (true,2,88))),
    (![4,12,14,17], .inr (some (false,1,88))),
    (![4,12,14,18], .inr (some (false,1,88))),
    (![4,12,15,16], .inr (some (true,6,89))),
    (![4,12,15,17], .inr (some (false,3,89))),
    (![4,12,15,18], .inr (some (false,3,89))),
    (![4,12,16,17], .inl (1,0)),
    (![4,12,16,18], .inl (2,0)),
    (![4,12,17,18], .inl (1,3)),
    (![4,13,14,15], .inr none),
    (![4,13,14,16], .inr (some (true,2,90))),
    (![4,13,14,17], .inr (some (false,1,90))),
    (![4,13,14,18], .inr (some (false,1,90))),
    (![4,13,15,16], .inr (some (true,2,91))),
    (![4,13,15,17], .inr (some (false,1,91))),
    (![4,13,15,18], .inr (some (false,1,91))),
    (![4,13,16,17], .inr (some (false,1,0))),
    (![4,13,16,18], .inl (2,0)),
    (![4,13,17,18], .inl (0,3)),
    (![4,14,15,16], .inl (2,0)),
    (![4,14,15,17], .inl (0,2)),
    (![4,14,15,18], .inl (0,2)),
    (![4,14,16,17], .inl (0,2)),
    (![4,14,16,18], .inr (some (true,1,11))),
    (![4,14,17,18], .inl (0,2)),
    (![4,15,16,17], .inl (0,2)),
    (![4,15,16,18], .inr (some (true,1,12))),
    (![4,15,17,18], .inl (0,2)),
    (![4,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid04 : ∀ k : Fin 364, CaseValid (block04 k).1 (block04 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align04 : (List.finRange 364).map (fun k => (block04 k).1) = fourTuples 4 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block05 : Fin 286 → Entry :=
  ![(![5,6,7,8], .inr none),
    (![5,6,7,9], .inr none),
    (![5,6,7,10], .inl (0,1)),
    (![5,6,7,11], .inl (0,1)),
    (![5,6,7,12], .inl (0,1)),
    (![5,6,7,13], .inl (0,1)),
    (![5,6,7,14], .inl (1,0)),
    (![5,6,7,15], .inl (1,0)),
    (![5,6,7,16], .inl (1,0)),
    (![5,6,7,17], .inr none),
    (![5,6,7,18], .inl (0,1)),
    (![5,6,8,9], .inr none),
    (![5,6,8,10], .inl (0,1)),
    (![5,6,8,11], .inl (0,1)),
    (![5,6,8,12], .inl (0,1)),
    (![5,6,8,13], .inl (0,1)),
    (![5,6,8,14], .inl (1,0)),
    (![5,6,8,15], .inl (1,0)),
    (![5,6,8,16], .inl (1,0)),
    (![5,6,8,17], .inr none),
    (![5,6,8,18], .inl (0,1)),
    (![5,6,9,10], .inl (0,1)),
    (![5,6,9,11], .inl (0,1)),
    (![5,6,9,12], .inl (0,1)),
    (![5,6,9,13], .inl (0,1)),
    (![5,6,9,14], .inl (1,0)),
    (![5,6,9,15], .inl (1,0)),
    (![5,6,9,16], .inl (1,0)),
    (![5,6,9,17], .inr none),
    (![5,6,9,18], .inl (0,1)),
    (![5,6,10,11], .inl (0,1)),
    (![5,6,10,12], .inl (0,1)),
    (![5,6,10,13], .inl (0,1)),
    (![5,6,10,14], .inl (1,0)),
    (![5,6,10,15], .inl (1,0)),
    (![5,6,10,16], .inl (1,0)),
    (![5,6,10,17], .inl (0,1)),
    (![5,6,10,18], .inl (0,1)),
    (![5,6,11,12], .inl (0,1)),
    (![5,6,11,13], .inl (0,1)),
    (![5,6,11,14], .inr (some (true,1,99))),
    (![5,6,11,15], .inl (1,0)),
    (![5,6,11,16], .inl (1,0)),
    (![5,6,11,17], .inl (0,1)),
    (![5,6,11,18], .inl (0,1)),
    (![5,6,12,13], .inl (2,1)),
    (![5,6,12,14], .inr (some (true,1,117))),
    (![5,6,12,15], .inr (some (true,3,118))),
    (![5,6,12,16], .inl (1,0)),
    (![5,6,12,17], .inl (0,1)),
    (![5,6,12,18], .inl (0,1)),
    (![5,6,13,14], .inr (some (true,1,119))),
    (![5,6,13,15], .inr (some (true,1,120))),
    (![5,6,13,16], .inl (1,0)),
    (![5,6,13,17], .inl (0,1)),
    (![5,6,13,18], .inl (0,3)),
    (![5,6,14,15], .inl (3,1)),
    (![5,6,14,16], .inl (0,1)),
    (![5,6,14,17], .inl (1,0)),
    (![5,6,14,18], .inl (1,0)),
    (![5,6,15,16], .inl (0,1)),
    (![5,6,15,17], .inl (1,0)),
    (![5,6,15,18], .inl (1,0)),
    (![5,6,16,17], .inl (1,0)),
    (![5,6,16,18], .inl (0,1)),
    (![5,6,17,18], .inl (1,0)),
    (![5,7,8,9], .inr none),
    (![5,7,8,10], .inl (0,1)),
    (![5,7,8,11], .inl (0,1)),
    (![5,7,8,12], .inl (0,1)),
    (![5,7,8,13], .inl (0,1)),
    (![5,7,8,14], .inl (1,0)),
    (![5,7,8,15], .inl (1,0)),
    (![5,7,8,16], .inl (1,0)),
    (![5,7,8,17], .inr none),
    (![5,7,8,18], .inl (0,1)),
    (![5,7,9,10], .inl (0,1)),
    (![5,7,9,11], .inl (0,1)),
    (![5,7,9,12], .inl (0,1)),
    (![5,7,9,13], .inl (0,1)),
    (![5,7,9,14], .inl (1,0)),
    (![5,7,9,15], .inl (1,0)),
    (![5,7,9,16], .inl (1,0)),
    (![5,7,9,17], .inr none),
    (![5,7,9,18], .inl (0,1)),
    (![5,7,10,11], .inl (0,1)),
    (![5,7,10,12], .inl (0,1)),
    (![5,7,10,13], .inl (0,1)),
    (![5,7,10,14], .inl (1,0)),
    (![5,7,10,15], .inl (1,0)),
    (![5,7,10,16], .inl (1,0)),
    (![5,7,10,17], .inl (0,1)),
    (![5,7,10,18], .inl (0,1)),
    (![5,7,11,12], .inl (0,1)),
    (![5,7,11,13], .inl (2,1)),
    (![5,7,11,14], .inr (some (true,2,99))),
    (![5,7,11,15], .inl (1,0)),
    (![5,7,11,16], .inl (1,0)),
    (![5,7,11,17], .inl (0,1)),
    (![5,7,11,18], .inl (0,1)),
    (![5,7,12,13], .inl (2,0)),
    (![5,7,12,14], .inr (some (true,2,169))),
    (![5,7,12,15], .inr (some (true,3,170))),
    (![5,7,12,16], .inl (1,0)),
    (![5,7,12,17], .inl (0,1)),
    (![5,7,12,18], .inl (0,1)),
    (![5,7,13,14], .inr (some (true,1,171))),
    (![5,7,13,15], .inr (some (true,2,172))),
    (![5,7,13,16], .inl (1,0)),
    (![5,7,13,17], .inl (0,1)),
    (![5,7,13,18], .inl (0,3)),
    (![5,7,14,15], .inl (3,0)),
    (![5,7,14,16], .inl (0,1)),
    (![5,7,14,17], .inl (1,0)),
    (![5,7,14,18], .inr (some (false,1,92))),
    (![5,7,15,16], .inl (0,1)),
    (![5,7,15,17], .inl (1,0)),
    (![5,7,15,18], .inr (some (false,6,18))),
    (![5,7,16,17], .inl (1,0)),
    (![5,7,16,18], .inl (0,1)),
    (![5,7,17,18], .inl (1,0)),
    (![5,8,9,10], .inl (0,1)),
    (![5,8,9,11], .inl (0,1)),
    (![5,8,9,12], .inl (0,1)),
    (![5,8,9,13], .inl (0,1)),
    (![5,8,9,14], .inl (1,0)),
    (![5,8,9,15], .inl (1,0)),
    (![5,8,9,16], .inl (1,0)),
    (![5,8,9,17], .inr none),
    (![5,8,9,18], .inl (0,1)),
    (![5,8,10,11], .inl (0,1)),
    (![5,8,10,12], .inl (0,1)),
    (![5,8,10,13], .inl (2,1)),
    (![5,8,10,14], .inl (1,0)),
    (![5,8,10,15], .inl (1,0)),
    (![5,8,10,16], .inl (1,0)),
    (![5,8,10,17], .inl (0,1)),
    (![5,8,10,18], .inl (0,1)),
    (![5,8,11,12], .inl (0,1)),
    (![5,8,11,13], .inl (2,0)),
    (![5,8,11,14], .inr (some (true,3,99))),
    (![5,8,11,15], .inl (1,0)),
    (![5,8,11,16], .inl (1,0)),
    (![5,8,11,17], .inl (0,1)),
    (![5,8,11,18], .inl (0,1)),
    (![5,8,12,13], .inl (2,0)),
    (![5,8,12,14], .inr (some (true,1,173))),
    (![5,8,12,15], .inr (some (true,3,174))),
    (![5,8,12,16], .inl (1,0)),
    (![5,8,12,17], .inl (0,1)),
    (![5,8,12,18], .inl (0,1)),
    (![5,8,13,14], .inr (some (true,1,175))),
    (![5,8,13,15], .inr (some (true,1,176))),
    (![5,8,13,16], .inl (1,0)),
    (![5,8,13,17], .inl (0,1)),
    (![5,8,13,18], .inl (0,3)),
    (![5,8,14,15], .inl (3,0)),
    (![5,8,14,16], .inl (3,1)),
    (![5,8,14,17], .inl (1,0)),
    (![5,8,14,18], .inr (some (false,3,93))),
    (![5,8,15,16], .inl (0,1)),
    (![5,8,15,17], .inl (1,0)),
    (![5,8,15,18], .inr (some (false,3,94))),
    (![5,8,16,17], .inl (1,0)),
    (![5,8,16,18], .inl (0,1)),
    (![5,8,17,18], .inl (1,0)),
    (![5,9,10,11], .inl (2,1)),
    (![5,9,10,12], .inl (2,1)),
    (![5,9,10,13], .inl (2,0)),
    (![5,9,10,14], .inl (1,0)),
    (![5,9,10,15], .inl (1,0)),
    (![5,9,10,16], .inl (1,0)),
    (![5,9,10,17], .inl (0,1)),
    (![5,9,10,18], .inl (0,1)),
    (![5,9,11,12], .inl (2,1)),
    (![5,9,11,13], .inl (2,0)),
    (![5,9,11,14], .inr (some (true,4,99))),
    (![5,9,11,15], .inl (1,0)),
    (![5,9,11,16], .inl (1,0)),
    (![5,9,11,17], .inl (0,1)),
    (![5,9,11,18], .inl (0,1)),
    (![5,9,12,13], .inl (2,0)),
    (![5,9,12,14], .inr (some (true,2,177))),
    (![5,9,12,15], .inr (some (true,3,178))),
    (![5,9,12,16], .inl (1,0)),
    (![5,9,12,17], .inl (0,1)),
    (![5,9,12,18], .inl (0,1)),
    (![5,9,13,14], .inr (some (true,1,179))),
    (![5,9,13,15], .inr (some (true,2,180))),
    (![5,9,13,16], .inl (1,0)),
    (![5,9,13,17], .inl (0,1)),
    (![5,9,13,18], .inl (0,3)),
    (![5,9,14,15], .inl (3,0)),
    (![5,9,14,16], .inl (3,0)),
    (![5,9,14,17], .inl (1,0)),
    (![5,9,14,18], .inr (some (false,1,95))),
    (![5,9,15,16], .inl (3,1)),
    (![5,9,15,17], .inl (1,0)),
    (![5,9,15,18], .inr (some (false,6,96))),
    (![5,9,16,17], .inl (1,0)),
    (![5,9,16,18], .inl (0,1)),
    (![5,9,17,18], .inl (1,0)),
    (![5,10,11,12], .inl (2,1)),
    (![5,10,11,13], .inl (2,0)),
    (![5,10,11,14], .inr (some (true,2,99))),
    (![5,10,11,15], .inl (1,0)),
    (![5,10,11,16], .inl (1,0)),
    (![5,10,11,17], .inl (0,1)),
    (![5,10,11,18], .inl (0,1)),
    (![5,10,12,13], .inl (2,0)),
    (![5,10,12,14], .inr (some (true,2,181))),
    (![5,10,12,15], .inr (some (true,1,182))),
    (![5,10,12,16], .inl (1,0)),
    (![5,10,12,17], .inl (0,1)),
    (![5,10,12,18], .inl (0,1)),
    (![5,10,13,14], .inr (some (true,1,183))),
    (![5,10,13,15], .inr (some (true,1,184))),
    (![5,10,13,16], .inl (1,0)),
    (![5,10,13,17], .inl (0,1)),
    (![5,10,13,18], .inl (0,3)),
    (![5,10,14,15], .inl (3,0)),
    (![5,10,14,16], .inl (3,0)),
    (![5,10,14,17], .inr (some (false,1,23))),
    (![5,10,14,18], .inr (some (false,1,97))),
    (![5,10,15,16], .inl (3,0)),
    (![5,10,15,17], .inl (1,0)),
    (![5,10,15,18], .inr (some (false,1,98))),
    (![5,10,16,17], .inl (1,0)),
    (![5,10,16,18], .inl (0,1)),
    (![5,10,17,18], .inl (1,0)),
    (![5,11,12,13], .inl (2,0)),
    (![5,11,12,14], .inr (some (true,2,99))),
    (![5,11,12,15], .inr (some (true,1,185))),
    (![5,11,12,16], .inl (1,0)),
    (![5,11,12,17], .inl (0,1)),
    (![5,11,12,18], .inl (0,1)),
    (![5,11,13,14], .inr (some (true,1,99))),
    (![5,11,13,15], .inr (some (true,2,186))),
    (![5,11,13,16], .inl (1,0)),
    (![5,11,13,17], .inl (0,1)),
    (![5,11,13,18], .inl (0,3)),
    (![5,11,14,15], .inr (some (true,1,99))),
    (![5,11,14,16], .inr (some (true,3,99))),
    (![5,11,14,17], .inr (some (false,1,99))),
    (![5,11,14,18], .inr (some (false,3,99))),
    (![5,11,15,16], .inl (3,0)),
    (![5,11,15,17], .inr (some (false,1,100))),
    (![5,11,15,18], .inr (some (false,2,101))),
    (![5,11,16,17], .inl (1,0)),
    (![5,11,16,18], .inl (2,1)),
    (![5,11,17,18], .inl (1,0)),
    (![5,12,13,14], .inl (2,1)),
    (![5,12,13,15], .inl (2,1)),
    (![5,12,13,16], .inl (1,0)),
    (![5,12,13,17], .inl (0,1)),
    (![5,12,13,18], .inl (0,3)),
    (![5,12,14,15], .inl (2,1)),
    (![5,12,14,16], .inr (some (true,1,102))),
    (![5,12,14,17], .inl (0,3)),
    (![5,12,14,18], .inl (0,3)),
    (![5,12,15,16], .inr (some (true,1,103))),
    (![5,12,15,17], .inl (0,3)),
    (![5,12,15,18], .inl (0,3)),
    (![5,12,16,17], .inl (1,0)),
    (![5,12,16,18], .inl (2,0)),
    (![5,12,17,18], .inl (1,3)),
    (![5,13,14,15], .inl (2,1)),
    (![5,13,14,16], .inr (some (true,1,104))),
    (![5,13,14,17], .inl (0,3)),
    (![5,13,14,18], .inl (0,3)),
    (![5,13,15,16], .inr (some (true,2,105))),
    (![5,13,15,17], .inl (0,3)),
    (![5,13,15,18], .inl (0,3)),
    (![5,13,16,17], .inr (some (false,1,0))),
    (![5,13,16,18], .inl (3,0)),
    (![5,13,17,18], .inl (0,3)),
    (![5,14,15,16], .inl (2,0)),
    (![5,14,15,17], .inl (0,2)),
    (![5,14,15,18], .inl (0,2)),
    (![5,14,16,17], .inl (0,2)),
    (![5,14,16,18], .inr (some (true,3,13))),
    (![5,14,17,18], .inl (0,2)),
    (![5,15,16,17], .inl (0,2)),
    (![5,15,16,18], .inr (some (true,2,14))),
    (![5,15,17,18], .inl (0,2)),
    (![5,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid05 : ∀ k : Fin 286, CaseValid (block05 k).1 (block05 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align05 : (List.finRange 286).map (fun k => (block05 k).1) = fourTuples 5 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block06 : Fin 220 → Entry :=
  ![(![6,7,8,9], .inr none),
    (![6,7,8,10], .inl (0,1)),
    (![6,7,8,11], .inl (0,1)),
    (![6,7,8,12], .inl (0,1)),
    (![6,7,8,13], .inl (0,1)),
    (![6,7,8,14], .inl (1,0)),
    (![6,7,8,15], .inl (1,0)),
    (![6,7,8,16], .inl (1,0)),
    (![6,7,8,17], .inr none),
    (![6,7,8,18], .inl (0,1)),
    (![6,7,9,10], .inl (0,1)),
    (![6,7,9,11], .inl (0,1)),
    (![6,7,9,12], .inl (0,1)),
    (![6,7,9,13], .inl (0,1)),
    (![6,7,9,14], .inl (1,0)),
    (![6,7,9,15], .inl (1,0)),
    (![6,7,9,16], .inl (1,0)),
    (![6,7,9,17], .inr none),
    (![6,7,9,18], .inl (0,1)),
    (![6,7,10,11], .inl (0,1)),
    (![6,7,10,12], .inl (0,1)),
    (![6,7,10,13], .inl (0,1)),
    (![6,7,10,14], .inl (1,0)),
    (![6,7,10,15], .inl (1,0)),
    (![6,7,10,16], .inl (1,0)),
    (![6,7,10,17], .inl (0,1)),
    (![6,7,10,18], .inl (0,1)),
    (![6,7,11,12], .inl (0,1)),
    (![6,7,11,13], .inl (2,1)),
    (![6,7,11,14], .inl (1,0)),
    (![6,7,11,15], .inl (1,0)),
    (![6,7,11,16], .inl (1,0)),
    (![6,7,11,17], .inl (0,1)),
    (![6,7,11,18], .inl (0,1)),
    (![6,7,12,13], .inl (2,0)),
    (![6,7,12,14], .inr (some (true,1,117))),
    (![6,7,12,15], .inr (some (true,3,118))),
    (![6,7,12,16], .inl (1,0)),
    (![6,7,12,17], .inl (0,1)),
    (![6,7,12,18], .inl (0,1)),
    (![6,7,13,14], .inr (some (true,1,119))),
    (![6,7,13,15], .inr (some (true,1,120))),
    (![6,7,13,16], .inl (1,0)),
    (![6,7,13,17], .inl (0,1)),
    (![6,7,13,18], .inl (0,1)),
    (![6,7,14,15], .inl (3,0)),
    (![6,7,14,16], .inl (0,1)),
    (![6,7,14,17], .inl (1,0)),
    (![6,7,14,18], .inr (some (false,1,106))),
    (![6,7,15,16], .inl (0,1)),
    (![6,7,15,17], .inl (1,0)),
    (![6,7,15,18], .inr (some (false,3,18))),
    (![6,7,16,17], .inl (1,0)),
    (![6,7,16,18], .inl (0,1)),
    (![6,7,17,18], .inl (1,0)),
    (![6,8,9,10], .inl (0,1)),
    (![6,8,9,11], .inl (0,1)),
    (![6,8,9,12], .inl (0,1)),
    (![6,8,9,13], .inl (0,1)),
    (![6,8,9,14], .inl (1,0)),
    (![6,8,9,15], .inl (1,0)),
    (![6,8,9,16], .inl (1,0)),
    (![6,8,9,17], .inr none),
    (![6,8,9,18], .inl (0,1)),
    (![6,8,10,11], .inl (0,1)),
    (![6,8,10,12], .inl (0,1)),
    (![6,8,10,13], .inl (2,1)),
    (![6,8,10,14], .inl (1,0)),
    (![6,8,10,15], .inl (1,0)),
    (![6,8,10,16], .inl (1,0)),
    (![6,8,10,17], .inl (0,1)),
    (![6,8,10,18], .inl (0,1)),
    (![6,8,11,12], .inl (0,1)),
    (![6,8,11,13], .inl (2,0)),
    (![6,8,11,14], .inl (1,0)),
    (![6,8,11,15], .inl (1,0)),
    (![6,8,11,16], .inl (1,0)),
    (![6,8,11,17], .inl (0,1)),
    (![6,8,11,18], .inl (0,1)),
    (![6,8,12,13], .inl (2,0)),
    (![6,8,12,14], .inr (some (true,2,117))),
    (![6,8,12,15], .inr (some (true,6,118))),
    (![6,8,12,16], .inl (1,0)),
    (![6,8,12,17], .inl (0,1)),
    (![6,8,12,18], .inl (0,1)),
    (![6,8,13,14], .inr (some (true,2,119))),
    (![6,8,13,15], .inr (some (true,2,120))),
    (![6,8,13,16], .inl (1,0)),
    (![6,8,13,17], .inl (0,1)),
    (![6,8,13,18], .inl (0,1)),
    (![6,8,14,15], .inl (3,0)),
    (![6,8,14,16], .inl (3,1)),
    (![6,8,14,17], .inl (1,0)),
    (![6,8,14,18], .inr (some (false,1,107))),
    (![6,8,15,16], .inl (0,1)),
    (![6,8,15,17], .inl (1,0)),
    (![6,8,15,18], .inr (some (false,3,108))),
    (![6,8,16,17], .inl (1,0)),
    (![6,8,16,18], .inl (0,1)),
    (![6,8,17,18], .inl (1,0)),
    (![6,9,10,11], .inl (2,1)),
    (![6,9,10,12], .inl (2,1)),
    (![6,9,10,13], .inl (2,0)),
    (![6,9,10,14], .inl (1,0)),
    (![6,9,10,15], .inl (1,0)),
    (![6,9,10,16], .inl (1,0)),
    (![6,9,10,17], .inl (0,1)),
    (![6,9,10,18], .inl (0,1)),
    (![6,9,11,12], .inl (2,1)),
    (![6,9,11,13], .inl (2,0)),
    (![6,9,11,14], .inl (1,0)),
    (![6,9,11,15], .inl (1,0)),
    (![6,9,11,16], .inl (1,0)),
    (![6,9,11,17], .inl (0,1)),
    (![6,9,11,18], .inl (0,1)),
    (![6,9,12,13], .inl (2,0)),
    (![6,9,12,14], .inr (some (true,3,117))),
    (![6,9,12,15], .inr (some (true,9,118))),
    (![6,9,12,16], .inl (1,0)),
    (![6,9,12,17], .inl (0,1)),
    (![6,9,12,18], .inl (0,1)),
    (![6,9,13,14], .inr (some (true,3,119))),
    (![6,9,13,15], .inr (some (true,3,120))),
    (![6,9,13,16], .inl (1,0)),
    (![6,9,13,17], .inl (0,1)),
    (![6,9,13,18], .inl (0,1)),
    (![6,9,14,15], .inl (3,0)),
    (![6,9,14,16], .inl (3,0)),
    (![6,9,14,17], .inl (1,0)),
    (![6,9,14,18], .inr (some (false,1,109))),
    (![6,9,15,16], .inl (3,1)),
    (![6,9,15,17], .inl (1,0)),
    (![6,9,15,18], .inr (some (false,3,110))),
    (![6,9,16,17], .inl (1,0)),
    (![6,9,16,18], .inl (0,1)),
    (![6,9,17,18], .inl (1,0)),
    (![6,10,11,12], .inl (2,1)),
    (![6,10,11,13], .inl (2,0)),
    (![6,10,11,14], .inl (1,0)),
    (![6,10,11,15], .inl (1,0)),
    (![6,10,11,16], .inl (1,0)),
    (![6,10,11,17], .inl (0,1)),
    (![6,10,11,18], .inl (0,1)),
    (![6,10,12,13], .inl (2,0)),
    (![6,10,12,14], .inr (some (true,2,117))),
    (![6,10,12,15], .inr (some (true,6,118))),
    (![6,10,12,16], .inl (1,0)),
    (![6,10,12,17], .inl (0,1)),
    (![6,10,12,18], .inl (0,1)),
    (![6,10,13,14], .inr (some (true,2,119))),
    (![6,10,13,15], .inr (some (true,2,120))),
    (![6,10,13,16], .inl (1,0)),
    (![6,10,13,17], .inl (0,1)),
    (![6,10,13,18], .inl (0,1)),
    (![6,10,14,15], .inl (3,0)),
    (![6,10,14,16], .inl (3,0)),
    (![6,10,14,17], .inr (some (false,1,23))),
    (![6,10,14,18], .inr (some (false,1,111))),
    (![6,10,15,16], .inl (3,0)),
    (![6,10,15,17], .inl (1,0)),
    (![6,10,15,18], .inr (some (false,1,112))),
    (![6,10,16,17], .inl (1,0)),
    (![6,10,16,18], .inl (0,1)),
    (![6,10,17,18], .inl (1,0)),
    (![6,11,12,13], .inl (2,0)),
    (![6,11,12,14], .inr (some (true,1,117))),
    (![6,11,12,15], .inr (some (true,3,118))),
    (![6,11,12,16], .inl (1,0)),
    (![6,11,12,17], .inl (0,1)),
    (![6,11,12,18], .inl (0,1)),
    (![6,11,13,14], .inr (some (true,1,119))),
    (![6,11,13,15], .inr (some (true,1,120))),
    (![6,11,13,16], .inl (1,0)),
    (![6,11,13,17], .inl (0,1)),
    (![6,11,13,18], .inl (0,1)),
    (![6,11,14,15], .inl (3,0)),
    (![6,11,14,16], .inl (3,0)),
    (![6,11,14,17], .inr (some (false,1,113))),
    (![6,11,14,18], .inr (some (false,1,114))),
    (![6,11,15,16], .inl (3,0)),
    (![6,11,15,17], .inr (some (false,1,115))),
    (![6,11,15,18], .inr (some (false,1,116))),
    (![6,11,16,17], .inl (1,0)),
    (![6,11,16,18], .inl (2,1)),
    (![6,11,17,18], .inl (1,0)),
    (![6,12,13,14], .inr none),
    (![6,12,13,15], .inr none),
    (![6,12,13,16], .inl (1,0)),
    (![6,12,13,17], .inl (0,1)),
    (![6,12,13,18], .inl (0,1)),
    (![6,12,14,15], .inr none),
    (![6,12,14,16], .inr (some (true,2,117))),
    (![6,12,14,17], .inr (some (false,1,117))),
    (![6,12,14,18], .inr (some (false,1,117))),
    (![6,12,15,16], .inr (some (true,6,118))),
    (![6,12,15,17], .inr (some (false,3,118))),
    (![6,12,15,18], .inr (some (false,3,118))),
    (![6,12,16,17], .inl (1,0)),
    (![6,12,16,18], .inl (2,0)),
    (![6,12,17,18], .inl (1,3)),
    (![6,13,14,15], .inr none),
    (![6,13,14,16], .inr (some (true,2,119))),
    (![6,13,14,17], .inr (some (false,1,119))),
    (![6,13,14,18], .inr (some (false,1,119))),
    (![6,13,15,16], .inr (some (true,2,120))),
    (![6,13,15,17], .inr (some (false,1,120))),
    (![6,13,15,18], .inr (some (false,1,120))),
    (![6,13,16,17], .inr (some (false,1,0))),
    (![6,13,16,18], .inl (2,0)),
    (![6,13,17,18], .inl (0,3)),
    (![6,14,15,16], .inl (2,0)),
    (![6,14,15,17], .inl (0,2)),
    (![6,14,15,18], .inl (0,2)),
    (![6,14,16,17], .inl (0,2)),
    (![6,14,16,18], .inr (some (true,1,15))),
    (![6,14,17,18], .inl (0,2)),
    (![6,15,16,17], .inl (0,2)),
    (![6,15,16,18], .inr (some (true,1,16))),
    (![6,15,17,18], .inl (0,2)),
    (![6,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid06 : ∀ k : Fin 220, CaseValid (block06 k).1 (block06 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align06 : (List.finRange 220).map (fun k => (block06 k).1) = fourTuples 6 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block07 : Fin 165 → Entry :=
  ![(![7,8,9,10], .inl (0,1)),
    (![7,8,9,11], .inl (0,1)),
    (![7,8,9,12], .inl (0,1)),
    (![7,8,9,13], .inl (0,1)),
    (![7,8,9,14], .inl (1,0)),
    (![7,8,9,15], .inl (1,0)),
    (![7,8,9,16], .inl (1,0)),
    (![7,8,9,17], .inr none),
    (![7,8,9,18], .inl (0,1)),
    (![7,8,10,11], .inl (0,1)),
    (![7,8,10,12], .inl (0,1)),
    (![7,8,10,13], .inl (2,1)),
    (![7,8,10,14], .inl (1,0)),
    (![7,8,10,15], .inl (1,0)),
    (![7,8,10,16], .inl (1,0)),
    (![7,8,10,17], .inl (0,1)),
    (![7,8,10,18], .inl (0,1)),
    (![7,8,11,12], .inl (0,1)),
    (![7,8,11,13], .inl (2,0)),
    (![7,8,11,14], .inl (1,0)),
    (![7,8,11,15], .inl (1,0)),
    (![7,8,11,16], .inl (1,0)),
    (![7,8,11,17], .inl (0,1)),
    (![7,8,11,18], .inl (0,1)),
    (![7,8,12,13], .inl (1,0)),
    (![7,8,12,14], .inl (1,0)),
    (![7,8,12,15], .inl (1,0)),
    (![7,8,12,16], .inl (1,0)),
    (![7,8,12,17], .inl (0,1)),
    (![7,8,12,18], .inl (0,1)),
    (![7,8,13,14], .inl (1,0)),
    (![7,8,13,15], .inl (1,0)),
    (![7,8,13,16], .inl (1,0)),
    (![7,8,13,17], .inl (0,1)),
    (![7,8,13,18], .inl (0,1)),
    (![7,8,14,15], .inl (1,0)),
    (![7,8,14,16], .inl (3,1)),
    (![7,8,14,17], .inl (1,0)),
    (![7,8,14,18], .inl (0,1)),
    (![7,8,15,16], .inl (0,1)),
    (![7,8,15,17], .inl (1,0)),
    (![7,8,15,18], .inr (some (false,3,18))),
    (![7,8,16,17], .inl (1,0)),
    (![7,8,16,18], .inl (0,1)),
    (![7,8,17,18], .inl (1,0)),
    (![7,9,10,11], .inl (2,1)),
    (![7,9,10,12], .inl (2,1)),
    (![7,9,10,13], .inl (2,0)),
    (![7,9,10,14], .inl (1,0)),
    (![7,9,10,15], .inl (1,0)),
    (![7,9,10,16], .inl (1,0)),
    (![7,9,10,17], .inl (0,1)),
    (![7,9,10,18], .inl (0,1)),
    (![7,9,11,12], .inl (2,1)),
    (![7,9,11,13], .inl (2,0)),
    (![7,9,11,14], .inl (1,0)),
    (![7,9,11,15], .inl (1,0)),
    (![7,9,11,16], .inl (1,0)),
    (![7,9,11,17], .inl (0,1)),
    (![7,9,11,18], .inl (0,1)),
    (![7,9,12,13], .inl (1,0)),
    (![7,9,12,14], .inl (1,0)),
    (![7,9,12,15], .inl (1,0)),
    (![7,9,12,16], .inl (1,0)),
    (![7,9,12,17], .inl (0,1)),
    (![7,9,12,18], .inl (0,1)),
    (![7,9,13,14], .inl (1,0)),
    (![7,9,13,15], .inl (1,0)),
    (![7,9,13,16], .inl (1,0)),
    (![7,9,13,17], .inl (0,1)),
    (![7,9,13,18], .inl (0,1)),
    (![7,9,14,15], .inl (1,0)),
    (![7,9,14,16], .inl (3,0)),
    (![7,9,14,17], .inl (1,0)),
    (![7,9,14,18], .inl (0,1)),
    (![7,9,15,16], .inl (3,1)),
    (![7,9,15,17], .inl (1,0)),
    (![7,9,15,18], .inr (some (false,6,18))),
    (![7,9,16,17], .inl (1,0)),
    (![7,9,16,18], .inl (0,1)),
    (![7,9,17,18], .inl (1,0)),
    (![7,10,11,12], .inl (2,1)),
    (![7,10,11,13], .inl (2,0)),
    (![7,10,11,14], .inl (1,0)),
    (![7,10,11,15], .inl (1,0)),
    (![7,10,11,16], .inl (1,0)),
    (![7,10,11,17], .inl (0,1)),
    (![7,10,11,18], .inl (0,1)),
    (![7,10,12,13], .inl (1,0)),
    (![7,10,12,14], .inl (1,0)),
    (![7,10,12,15], .inl (1,0)),
    (![7,10,12,16], .inl (1,0)),
    (![7,10,12,17], .inl (0,1)),
    (![7,10,12,18], .inl (0,1)),
    (![7,10,13,14], .inl (1,0)),
    (![7,10,13,15], .inl (1,0)),
    (![7,10,13,16], .inl (1,0)),
    (![7,10,13,17], .inl (0,1)),
    (![7,10,13,18], .inl (0,1)),
    (![7,10,14,15], .inl (1,0)),
    (![7,10,14,16], .inl (3,0)),
    (![7,10,14,17], .inr (some (false,1,23))),
    (![7,10,14,18], .inl (0,1)),
    (![7,10,15,16], .inl (3,0)),
    (![7,10,15,17], .inl (1,0)),
    (![7,10,15,18], .inr (some (false,5,18))),
    (![7,10,16,17], .inl (1,0)),
    (![7,10,16,18], .inl (0,1)),
    (![7,10,17,18], .inl (1,0)),
    (![7,11,12,13], .inl (1,0)),
    (![7,11,12,14], .inl (1,0)),
    (![7,11,12,15], .inl (1,0)),
    (![7,11,12,16], .inl (1,0)),
    (![7,11,12,17], .inl (0,1)),
    (![7,11,12,18], .inl (0,1)),
    (![7,11,13,14], .inl (1,0)),
    (![7,11,13,15], .inl (1,0)),
    (![7,11,13,16], .inl (1,0)),
    (![7,11,13,17], .inl (0,1)),
    (![7,11,13,18], .inl (0,1)),
    (![7,11,14,15], .inl (1,0)),
    (![7,11,14,16], .inl (3,0)),
    (![7,11,14,17], .inr (some (false,1,121))),
    (![7,11,14,18], .inl (0,1)),
    (![7,11,15,16], .inl (3,0)),
    (![7,11,15,17], .inr (some (false,1,122))),
    (![7,11,15,18], .inr (some (false,4,18))),
    (![7,11,16,17], .inl (1,0)),
    (![7,11,16,18], .inl (2,1)),
    (![7,11,17,18], .inl (1,0)),
    (![7,12,13,14], .inl (1,2)),
    (![7,12,13,15], .inl (1,2)),
    (![7,12,13,16], .inl (1,0)),
    (![7,12,13,17], .inl (0,1)),
    (![7,12,13,18], .inl (0,1)),
    (![7,12,14,15], .inl (1,2)),
    (![7,12,14,16], .inl (3,0)),
    (![7,12,14,17], .inr (some (false,1,123))),
    (![7,12,14,18], .inl (0,1)),
    (![7,12,15,16], .inl (3,0)),
    (![7,12,15,17], .inr (some (false,3,124))),
    (![7,12,15,18], .inr (some (false,3,18))),
    (![7,12,16,17], .inl (1,0)),
    (![7,12,16,18], .inl (2,0)),
    (![7,12,17,18], .inl (1,3)),
    (![7,13,14,15], .inl (1,2)),
    (![7,13,14,16], .inl (3,0)),
    (![7,13,14,17], .inr (some (false,1,125))),
    (![7,13,14,18], .inl (0,1)),
    (![7,13,15,16], .inl (3,0)),
    (![7,13,15,17], .inr (some (false,1,126))),
    (![7,13,15,18], .inr (some (false,2,18))),
    (![7,13,16,17], .inr (some (false,1,0))),
    (![7,13,16,18], .inl (2,0)),
    (![7,13,17,18], .inl (0,3)),
    (![7,14,15,16], .inl (2,0)),
    (![7,14,15,17], .inl (0,2)),
    (![7,14,15,18], .inr (some (false,1,18))),
    (![7,14,16,17], .inl (0,2)),
    (![7,14,16,18], .inl (2,0)),
    (![7,14,17,18], .inr (some (false,1,17))),
    (![7,15,16,17], .inl (0,2)),
    (![7,15,16,18], .inr (some (true,4,18))),
    (![7,15,17,18], .inr (some (false,3,18))),
    (![7,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid07 : ∀ k : Fin 165, CaseValid (block07 k).1 (block07 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align07 : (List.finRange 165).map (fun k => (block07 k).1) = fourTuples 7 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block08 : Fin 120 → Entry :=
  ![(![8,9,10,11], .inl (2,1)),
    (![8,9,10,12], .inl (2,1)),
    (![8,9,10,13], .inl (2,0)),
    (![8,9,10,14], .inl (1,0)),
    (![8,9,10,15], .inl (1,0)),
    (![8,9,10,16], .inl (1,0)),
    (![8,9,10,17], .inl (0,1)),
    (![8,9,10,18], .inl (0,1)),
    (![8,9,11,12], .inl (2,1)),
    (![8,9,11,13], .inl (1,0)),
    (![8,9,11,14], .inl (1,0)),
    (![8,9,11,15], .inl (1,0)),
    (![8,9,11,16], .inl (1,0)),
    (![8,9,11,17], .inl (0,1)),
    (![8,9,11,18], .inl (0,1)),
    (![8,9,12,13], .inl (1,0)),
    (![8,9,12,14], .inl (1,0)),
    (![8,9,12,15], .inl (1,0)),
    (![8,9,12,16], .inl (1,0)),
    (![8,9,12,17], .inl (0,1)),
    (![8,9,12,18], .inl (0,1)),
    (![8,9,13,14], .inl (1,0)),
    (![8,9,13,15], .inl (1,0)),
    (![8,9,13,16], .inl (1,0)),
    (![8,9,13,17], .inl (0,1)),
    (![8,9,13,18], .inl (0,1)),
    (![8,9,14,15], .inl (1,0)),
    (![8,9,14,16], .inl (3,0)),
    (![8,9,14,17], .inl (1,0)),
    (![8,9,14,18], .inl (0,1)),
    (![8,9,15,16], .inl (3,1)),
    (![8,9,15,17], .inl (1,0)),
    (![8,9,15,18], .inl (0,1)),
    (![8,9,16,17], .inl (1,0)),
    (![8,9,16,18], .inl (0,1)),
    (![8,9,17,18], .inl (1,0)),
    (![8,10,11,12], .inl (2,1)),
    (![8,10,11,13], .inl (1,0)),
    (![8,10,11,14], .inl (1,0)),
    (![8,10,11,15], .inl (1,0)),
    (![8,10,11,16], .inl (1,0)),
    (![8,10,11,17], .inl (0,1)),
    (![8,10,11,18], .inl (0,1)),
    (![8,10,12,13], .inl (1,0)),
    (![8,10,12,14], .inl (1,0)),
    (![8,10,12,15], .inl (1,0)),
    (![8,10,12,16], .inl (1,0)),
    (![8,10,12,17], .inl (0,1)),
    (![8,10,12,18], .inl (0,1)),
    (![8,10,13,14], .inl (1,0)),
    (![8,10,13,15], .inl (1,0)),
    (![8,10,13,16], .inl (1,0)),
    (![8,10,13,17], .inl (0,1)),
    (![8,10,13,18], .inl (0,1)),
    (![8,10,14,15], .inl (1,0)),
    (![8,10,14,16], .inl (3,0)),
    (![8,10,14,17], .inr (some (false,1,23))),
    (![8,10,14,18], .inl (0,1)),
    (![8,10,15,16], .inl (3,0)),
    (![8,10,15,17], .inl (1,0)),
    (![8,10,15,18], .inl (0,1)),
    (![8,10,16,17], .inl (1,0)),
    (![8,10,16,18], .inl (0,1)),
    (![8,10,17,18], .inl (1,0)),
    (![8,11,12,13], .inl (1,0)),
    (![8,11,12,14], .inl (1,0)),
    (![8,11,12,15], .inl (1,0)),
    (![8,11,12,16], .inl (1,0)),
    (![8,11,12,17], .inl (0,1)),
    (![8,11,12,18], .inl (0,1)),
    (![8,11,13,14], .inl (1,0)),
    (![8,11,13,15], .inl (1,0)),
    (![8,11,13,16], .inl (1,0)),
    (![8,11,13,17], .inl (0,1)),
    (![8,11,13,18], .inl (0,1)),
    (![8,11,14,15], .inl (1,0)),
    (![8,11,14,16], .inl (3,0)),
    (![8,11,14,17], .inr (some (false,1,127))),
    (![8,11,14,18], .inl (0,1)),
    (![8,11,15,16], .inl (3,0)),
    (![8,11,15,17], .inr (some (false,1,128))),
    (![8,11,15,18], .inl (0,1)),
    (![8,11,16,17], .inl (1,0)),
    (![8,11,16,18], .inl (2,1)),
    (![8,11,17,18], .inl (1,0)),
    (![8,12,13,14], .inl (1,2)),
    (![8,12,13,15], .inl (1,2)),
    (![8,12,13,16], .inl (1,0)),
    (![8,12,13,17], .inl (0,1)),
    (![8,12,13,18], .inl (0,1)),
    (![8,12,14,15], .inl (1,2)),
    (![8,12,14,16], .inl (3,0)),
    (![8,12,14,17], .inr (some (false,1,129))),
    (![8,12,14,18], .inl (0,1)),
    (![8,12,15,16], .inl (3,0)),
    (![8,12,15,17], .inr (some (false,3,130))),
    (![8,12,15,18], .inl (0,1)),
    (![8,12,16,17], .inl (1,0)),
    (![8,12,16,18], .inl (2,0)),
    (![8,12,17,18], .inl (1,3)),
    (![8,13,14,15], .inl (1,2)),
    (![8,13,14,16], .inl (3,0)),
    (![8,13,14,17], .inr (some (false,1,131))),
    (![8,13,14,18], .inl (0,1)),
    (![8,13,15,16], .inl (3,0)),
    (![8,13,15,17], .inr (some (false,1,132))),
    (![8,13,15,18], .inl (0,1)),
    (![8,13,16,17], .inr (some (false,1,0))),
    (![8,13,16,18], .inl (2,0)),
    (![8,13,17,18], .inl (0,3)),
    (![8,14,15,16], .inl (3,0)),
    (![8,14,15,17], .inl (0,2)),
    (![8,14,15,18], .inl (0,1)),
    (![8,14,16,17], .inl (0,2)),
    (![8,14,16,18], .inl (2,0)),
    (![8,14,17,18], .inr (some (false,1,19))),
    (![8,15,16,17], .inl (0,2)),
    (![8,15,16,18], .inl (2,0)),
    (![8,15,17,18], .inr (some (false,3,20))),
    (![8,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid08 : ∀ k : Fin 120, CaseValid (block08 k).1 (block08 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align08 : (List.finRange 120).map (fun k => (block08 k).1) = fourTuples 8 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block09 : Fin 84 → Entry :=
  ![(![9,10,11,12], .inr none),
    (![9,10,11,13], .inl (1,0)),
    (![9,10,11,14], .inl (1,0)),
    (![9,10,11,15], .inl (1,0)),
    (![9,10,11,16], .inl (1,0)),
    (![9,10,11,17], .inl (0,1)),
    (![9,10,11,18], .inl (0,1)),
    (![9,10,12,13], .inl (1,0)),
    (![9,10,12,14], .inl (1,0)),
    (![9,10,12,15], .inl (1,0)),
    (![9,10,12,16], .inl (1,0)),
    (![9,10,12,17], .inl (0,1)),
    (![9,10,12,18], .inl (0,1)),
    (![9,10,13,14], .inl (1,0)),
    (![9,10,13,15], .inl (1,0)),
    (![9,10,13,16], .inl (1,0)),
    (![9,10,13,17], .inl (0,1)),
    (![9,10,13,18], .inl (0,1)),
    (![9,10,14,15], .inl (1,0)),
    (![9,10,14,16], .inl (1,0)),
    (![9,10,14,17], .inr (some (false,1,23))),
    (![9,10,14,18], .inl (0,1)),
    (![9,10,15,16], .inl (3,0)),
    (![9,10,15,17], .inl (1,0)),
    (![9,10,15,18], .inl (0,1)),
    (![9,10,16,17], .inl (1,0)),
    (![9,10,16,18], .inl (0,1)),
    (![9,10,17,18], .inl (1,0)),
    (![9,11,12,13], .inl (1,0)),
    (![9,11,12,14], .inl (1,0)),
    (![9,11,12,15], .inl (1,0)),
    (![9,11,12,16], .inl (1,0)),
    (![9,11,12,17], .inl (0,1)),
    (![9,11,12,18], .inl (0,1)),
    (![9,11,13,14], .inl (1,0)),
    (![9,11,13,15], .inl (1,0)),
    (![9,11,13,16], .inl (1,0)),
    (![9,11,13,17], .inl (0,1)),
    (![9,11,13,18], .inl (0,1)),
    (![9,11,14,15], .inl (1,0)),
    (![9,11,14,16], .inl (1,0)),
    (![9,11,14,17], .inr (some (false,1,133))),
    (![9,11,14,18], .inl (0,1)),
    (![9,11,15,16], .inl (3,0)),
    (![9,11,15,17], .inr (some (false,1,134))),
    (![9,11,15,18], .inl (0,1)),
    (![9,11,16,17], .inl (1,0)),
    (![9,11,16,18], .inl (2,1)),
    (![9,11,17,18], .inl (1,0)),
    (![9,12,13,14], .inl (1,2)),
    (![9,12,13,15], .inl (1,2)),
    (![9,12,13,16], .inl (1,0)),
    (![9,12,13,17], .inl (0,1)),
    (![9,12,13,18], .inl (0,1)),
    (![9,12,14,15], .inl (1,2)),
    (![9,12,14,16], .inl (1,0)),
    (![9,12,14,17], .inr (some (false,1,135))),
    (![9,12,14,18], .inl (0,1)),
    (![9,12,15,16], .inl (3,0)),
    (![9,12,15,17], .inr (some (false,3,136))),
    (![9,12,15,18], .inl (0,1)),
    (![9,12,16,17], .inl (1,0)),
    (![9,12,16,18], .inl (2,0)),
    (![9,12,17,18], .inl (1,3)),
    (![9,13,14,15], .inl (1,2)),
    (![9,13,14,16], .inl (1,0)),
    (![9,13,14,17], .inr (some (false,1,137))),
    (![9,13,14,18], .inl (0,1)),
    (![9,13,15,16], .inl (3,0)),
    (![9,13,15,17], .inr (some (false,1,138))),
    (![9,13,15,18], .inl (0,1)),
    (![9,13,16,17], .inr (some (false,1,0))),
    (![9,13,16,18], .inl (2,0)),
    (![9,13,17,18], .inl (0,3)),
    (![9,14,15,16], .inl (3,0)),
    (![9,14,15,17], .inl (0,2)),
    (![9,14,15,18], .inl (0,1)),
    (![9,14,16,17], .inl (0,2)),
    (![9,14,16,18], .inl (2,0)),
    (![9,14,17,18], .inr (some (false,1,21))),
    (![9,15,16,17], .inl (0,2)),
    (![9,15,16,18], .inl (2,0)),
    (![9,15,17,18], .inr (some (false,3,22))),
    (![9,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid09 : ∀ k : Fin 84, CaseValid (block09 k).1 (block09 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align09 : (List.finRange 84).map (fun k => (block09 k).1) = fourTuples 9 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block10 : Fin 56 → Entry :=
  ![(![10,11,12,13], .inl (1,0)),
    (![10,11,12,14], .inl (1,0)),
    (![10,11,12,15], .inl (1,0)),
    (![10,11,12,16], .inl (1,0)),
    (![10,11,12,17], .inl (0,1)),
    (![10,11,12,18], .inl (0,1)),
    (![10,11,13,14], .inl (1,0)),
    (![10,11,13,15], .inl (1,0)),
    (![10,11,13,16], .inl (1,0)),
    (![10,11,13,17], .inl (0,1)),
    (![10,11,13,18], .inl (0,1)),
    (![10,11,14,15], .inl (1,0)),
    (![10,11,14,16], .inl (1,0)),
    (![10,11,14,17], .inr (some (false,1,23))),
    (![10,11,14,18], .inl (0,1)),
    (![10,11,15,16], .inl (1,0)),
    (![10,11,15,17], .inr (some (false,1,139))),
    (![10,11,15,18], .inl (0,1)),
    (![10,11,16,17], .inl (1,0)),
    (![10,11,16,18], .inl (2,1)),
    (![10,11,17,18], .inl (1,0)),
    (![10,12,13,14], .inl (1,2)),
    (![10,12,13,15], .inl (1,2)),
    (![10,12,13,16], .inl (1,0)),
    (![10,12,13,17], .inl (0,1)),
    (![10,12,13,18], .inl (0,1)),
    (![10,12,14,15], .inl (1,2)),
    (![10,12,14,16], .inl (1,0)),
    (![10,12,14,17], .inr (some (false,2,23))),
    (![10,12,14,18], .inl (0,1)),
    (![10,12,15,16], .inl (1,0)),
    (![10,12,15,17], .inr (some (false,1,140))),
    (![10,12,15,18], .inl (0,1)),
    (![10,12,16,17], .inl (1,0)),
    (![10,12,16,18], .inl (2,0)),
    (![10,12,17,18], .inl (1,3)),
    (![10,13,14,15], .inl (1,2)),
    (![10,13,14,16], .inl (1,0)),
    (![10,13,14,17], .inr (some (false,1,23))),
    (![10,13,14,18], .inl (0,1)),
    (![10,13,15,16], .inl (1,0)),
    (![10,13,15,17], .inr (some (false,1,141))),
    (![10,13,15,18], .inl (0,1)),
    (![10,13,16,17], .inr (some (false,1,0))),
    (![10,13,16,18], .inl (2,0)),
    (![10,13,17,18], .inl (0,3)),
    (![10,14,15,16], .inl (1,0)),
    (![10,14,15,17], .inr (some (false,1,23))),
    (![10,14,15,18], .inl (0,1)),
    (![10,14,16,17], .inr (some (false,1,23))),
    (![10,14,16,18], .inl (2,0)),
    (![10,14,17,18], .inr (some (false,2,23))),
    (![10,15,16,17], .inl (0,2)),
    (![10,15,16,18], .inl (2,0)),
    (![10,15,17,18], .inr (some (false,1,24))),
    (![10,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid10 : ∀ k : Fin 56, CaseValid (block10 k).1 (block10 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align10 : (List.finRange 56).map (fun k => (block10 k).1) = fourTuples 10 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block11 : Fin 35 → Entry :=
  ![(![11,12,13,14], .inl (1,2)),
    (![11,12,13,15], .inl (1,2)),
    (![11,12,13,16], .inl (1,0)),
    (![11,12,13,17], .inl (0,1)),
    (![11,12,13,18], .inl (0,1)),
    (![11,12,14,15], .inl (1,2)),
    (![11,12,14,16], .inl (1,0)),
    (![11,12,14,17], .inl (0,1)),
    (![11,12,14,18], .inl (0,1)),
    (![11,12,15,16], .inl (1,0)),
    (![11,12,15,17], .inl (0,1)),
    (![11,12,15,18], .inl (0,1)),
    (![11,12,16,17], .inl (1,0)),
    (![11,12,16,18], .inl (2,0)),
    (![11,12,17,18], .inl (1,3)),
    (![11,13,14,15], .inl (1,2)),
    (![11,13,14,16], .inl (1,0)),
    (![11,13,14,17], .inl (0,1)),
    (![11,13,14,18], .inl (0,1)),
    (![11,13,15,16], .inl (1,0)),
    (![11,13,15,17], .inl (0,1)),
    (![11,13,15,18], .inl (0,1)),
    (![11,13,16,17], .inr (some (false,1,0))),
    (![11,13,16,18], .inl (2,0)),
    (![11,13,17,18], .inl (0,3)),
    (![11,14,15,16], .inl (1,0)),
    (![11,14,15,17], .inl (0,1)),
    (![11,14,15,18], .inl (0,1)),
    (![11,14,16,17], .inr (some (false,1,25))),
    (![11,14,16,18], .inl (2,0)),
    (![11,14,17,18], .inl (0,3)),
    (![11,15,16,17], .inr (some (false,1,26))),
    (![11,15,16,18], .inl (2,0)),
    (![11,15,17,18], .inl (0,3)),
    (![11,16,17,18], .inl (1,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid11 : ∀ k : Fin 35, CaseValid (block11 k).1 (block11 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align11 : (List.finRange 35).map (fun k => (block11 k).1) = fourTuples 11 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block12 : Fin 20 → Entry :=
  ![(![12,13,14,15], .inr none),
    (![12,13,14,16], .inl (1,0)),
    (![12,13,14,17], .inl (0,1)),
    (![12,13,14,18], .inl (0,1)),
    (![12,13,15,16], .inl (1,0)),
    (![12,13,15,17], .inl (0,1)),
    (![12,13,15,18], .inl (0,1)),
    (![12,13,16,17], .inr (some (false,1,0))),
    (![12,13,16,18], .inl (1,0)),
    (![12,13,17,18], .inl (0,3)),
    (![12,14,15,16], .inl (1,0)),
    (![12,14,15,17], .inl (0,1)),
    (![12,14,15,18], .inl (0,1)),
    (![12,14,16,17], .inr (some (false,1,27))),
    (![12,14,16,18], .inl (1,0)),
    (![12,14,17,18], .inl (0,3)),
    (![12,15,16,17], .inr (some (false,1,28))),
    (![12,15,16,18], .inl (1,0)),
    (![12,15,17,18], .inl (0,3)),
    (![12,16,17,18], .inl (3,0))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid12 : ∀ k : Fin 20, CaseValid (block12 k).1 (block12 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align12 : (List.finRange 20).map (fun k => (block12 k).1) = fourTuples 12 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block13 : Fin 10 → Entry :=
  ![(![13,14,15,16], .inl (1,0)),
    (![13,14,15,17], .inl (0,1)),
    (![13,14,15,18], .inl (0,1)),
    (![13,14,16,17], .inr (some (false,1,0))),
    (![13,14,16,18], .inl (1,0)),
    (![13,14,17,18], .inl (0,1)),
    (![13,15,16,17], .inr (some (false,2,0))),
    (![13,15,16,18], .inl (1,0)),
    (![13,15,17,18], .inl (0,1)),
    (![13,16,17,18], .inr (some (true,1,0)))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid13 : ∀ k : Fin 10, CaseValid (block13 k).1 (block13 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align13 : (List.finRange 10).map (fun k => (block13 k).1) = fourTuples 13 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block14 : Fin 4 → Entry :=
  ![(![14,15,16,17], .inl (0,1)),
    (![14,15,16,18], .inl (1,0)),
    (![14,15,17,18], .inl (0,1)),
    (![14,16,17,18], .inr (some (true,1,1)))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid14 : ∀ k : Fin 4, CaseValid (block14 k).1 (block14 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align14 : (List.finRange 4).map (fun k => (block14 k).1) = fourTuples 14 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
private def block15 : Fin 1 → Entry :=
  ![(![15,16,17,18], .inr (some (true,1,2)))]
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem valid15 : ∀ k : Fin 1, CaseValid (block15 k).1 (block15 k).2 := by
  classical
  decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem align15 : (List.finRange 1).map (fun k => (block15 k).1) = fourTuples 15 := by
  classical
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem checked_tuple : ∀ (a : Fin 16) (e : Fin 4 → Fin 19),
    e ∈ fourTuples ⟨a.val, by omega⟩ → ∃ w, CaseValid e w := by
  classical
  intro a
  fin_cases a
  · intro e he
    change e ∈ fourTuples 0 at he
    rw [← align00] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block00 k).2, ?_⟩
    rw [← he]
    exact valid00 k
  · intro e he
    change e ∈ fourTuples 1 at he
    rw [← align01] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block01 k).2, ?_⟩
    rw [← he]
    exact valid01 k
  · intro e he
    change e ∈ fourTuples 2 at he
    rw [← align02] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block02 k).2, ?_⟩
    rw [← he]
    exact valid02 k
  · intro e he
    change e ∈ fourTuples 3 at he
    rw [← align03] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block03 k).2, ?_⟩
    rw [← he]
    exact valid03 k
  · intro e he
    change e ∈ fourTuples 4 at he
    rw [← align04] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block04 k).2, ?_⟩
    rw [← he]
    exact valid04 k
  · intro e he
    change e ∈ fourTuples 5 at he
    rw [← align05] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block05 k).2, ?_⟩
    rw [← he]
    exact valid05 k
  · intro e he
    change e ∈ fourTuples 6 at he
    rw [← align06] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block06 k).2, ?_⟩
    rw [← he]
    exact valid06 k
  · intro e he
    change e ∈ fourTuples 7 at he
    rw [← align07] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block07 k).2, ?_⟩
    rw [← he]
    exact valid07 k
  · intro e he
    change e ∈ fourTuples 8 at he
    rw [← align08] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block08 k).2, ?_⟩
    rw [← he]
    exact valid08 k
  · intro e he
    change e ∈ fourTuples 9 at he
    rw [← align09] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block09 k).2, ?_⟩
    rw [← he]
    exact valid09 k
  · intro e he
    change e ∈ fourTuples 10 at he
    rw [← align10] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block10 k).2, ?_⟩
    rw [← he]
    exact valid10 k
  · intro e he
    change e ∈ fourTuples 11 at he
    rw [← align11] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block11 k).2, ?_⟩
    rw [← he]
    exact valid11 k
  · intro e he
    change e ∈ fourTuples 12 at he
    rw [← align12] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block12 k).2, ?_⟩
    rw [← he]
    exact valid12 k
  · intro e he
    change e ∈ fourTuples 13 at he
    rw [← align13] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block13 k).2, ?_⟩
    rw [← he]
    exact valid13 k
  · intro e he
    change e ∈ fourTuples 14 at he
    rw [← align14] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block14 k).2, ?_⟩
    rw [← he]
    exact valid14 k
  · intro e he
    change e ∈ fourTuples 15 at he
    rw [← align15] at he
    obtain ⟨k, _hk, he⟩ := List.mem_map.mp he
    refine ⟨(block15 k).2, ?_⟩
    rw [← he]
    exact valid15 k

/- Equality align00..align15 aligns every
 supplied witness with the tuple on which its arithmetic proposition is checked. -/

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem increasing_tuple_mem (e : Fin 4 → Fin 19) (he : StrictMono e) :
    e ∈ fourTuples (e 0) := by
  classical
  have hev : ![e 0,e 1,e 2,e 3] = e := by
    funext i
    fin_cases i <;> rfl
  simp only [fourTuples, List.mem_flatMap, List.mem_filter, List.mem_finRange,
    true_and, List.mem_map, decide_eq_true_eq]
  exact ⟨e 1, he (by decide +kernel), e 2, he (by decide +kernel), e 3, he (by decide +kernel), hev⟩

-- This is the only support coverage interface: actual powersetCard membership.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem local_coverage (S : Finset (Fin 19))
    (hS : S ∈ (Finset.univ : Finset (Fin 19)).powersetCard 4) :
    ∃ w, CaseValid (S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2) w := by
  classical
  let e : Fin 4 ↪o Fin 19 := S.orderEmbOfFin (Finset.mem_powersetCard.mp hS).2
  have h01 : (e 0).val < (e 1).val := e.strictMono (by decide +kernel)
  have h12 : (e 1).val < (e 2).val := e.strictMono (by decide +kernel)
  have h23 : (e 2).val < (e 3).val := e.strictMono (by decide +kernel)
  have h3 : (e 3).val < 19 := (e 3).isLt
  have h0 : (e 0).val < 16 := by omega
  exact checked_tuple ⟨(e 0).val, h0⟩ e (by
    simpa using increasing_tuple_mem e e.strictMono)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem extend4_slot (e : Fin 4 → Fin 19) (he : Function.Injective e)
    (c : Fin 4 → ℤ) (i : Fin 4) : extend4 e c (e i) = c i := by
  classical
  dsimp [extend4]
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    have hne : e k ≠ e i := fun h => hki (he h)
    simp [Pi.single_apply, hne, Ne.symm hne]
  · simp

-- Only one supplied id is used in the ray branch, never a search over 187 rays.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem classify_checked (e : Fin 4 → Fin 19) (he : Function.Injective e)
    (w : Witness) (hv : CaseValid e w) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1)
    (hn : ∀ j, 0 ≤ (ε • realCof e) j) (hne : ε • realCof e ≠ 0) :
    ∃ t : Fin 187, ∃ d : ℝ, 0 < d ∧
      ε • realCof e = d • (fun j => (zZ t j : ℝ)) := by
  classical
  have hslot (i : Fin 4) : realCof e (e i) = (cof4 e i : ℝ) := by
    dsimp [realCof]
    rw [extend4_slot e he]
  rcases w with ⟨p,n⟩ | (_ | ⟨negative,d,t⟩)
  · change 0 < cof4 e p ∧ cof4 e n < 0 at hv
    have hp : (0 : ℝ) < (cof4 e p : ℝ) := by exact_mod_cast hv.1
    have hm : (cof4 e n : ℝ) < 0 := by exact_mod_cast hv.2
    rcases hε with rfl | rfl
    · have h := hn (e n)
      change 0 ≤ (1 : ℝ) * realCof e (e n) at h
      rw [hslot] at h
      linarith
    · have h := hn (e p)
      change 0 ≤ (-1 : ℝ) * realCof e (e p) at h
      rw [hslot] at h
      linarith
  · change ∀ i, cof4 e i = 0 at hv
    exfalso
    apply hne
    funext j
    simp [realCof, extend4, hv]
  · change 0 < d ∧ ∀ j : Fin 19,
      (if negative then (-1 : ℤ) else 1) * extend4 e (cof4 e) j =
        (d : ℤ) * zZ t j at hv
    have hd : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hv.1
    let s : ℝ := ((if negative then (-1 : ℤ) else 1) : ℤ)
    have hcast (j : Fin 19) : s * realCof e j = (d : ℝ) * (zZ t j : ℝ) := by
      dsimp [s, realCof]
      exact_mod_cast hv.2 j
    let j : Fin 19 := Fin.castAdd 3 (positiveSlot t)
    have hz : (0 : ℝ) < (zZ t j : ℝ) := by
      have h := gap_positive t
      have hzZ : 0 < zZ t j := by simpa [zZ, j] using h
      exact_mod_cast hzZ
    have hs : 0 < s * realCof e j := by
      rw [hcast]
      exact mul_pos hd hz
    have hn' : 0 ≤ ε * realCof e j := hn j
    have hforce : ε = s := by
      cases negative <;> rcases hε with rfl | rfl
      · norm_num [s]
      · norm_num [s] at hs
        linarith
      · norm_num [s] at hs
        linarith
      · norm_num [s]
    refine ⟨t, (d : ℝ), hd, ?_⟩
    funext k
    change ε * realCof e k = (d : ℝ) * (zZ t k : ℝ)
    rw [hforce]
    exact hcast k

-- The classification uses ordered supports with all three original rows.

private abbrev Support4 := {S : Finset (Fin 19) // S.card = 4}
set_option maxRecDepth 8192 in
private def orderedCof : Support4 → (Fin 19 → ℝ) := fun S =>
  liftCof bR (Function.Embedding.refl (Fin 3))
    (S.val.orderEmbOfFin S.property).toEmbedding

-- Same row/column embeddings as the expected liftCof definition. The only
-- determinant rewrite is the actual pinned Matrix.det_fin_three formula.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem cofactor_cast (e : Fin 4 → Fin 19) (i : Fin 4) :
    cofactor (bR.submatrix id e) i = (cof4 e i : ℝ) := by
  classical
  fin_cases i <;>
    norm_num [cofactor, Matrix.det_fin_three, Matrix.submatrix,
      cof4, det3, bR, Fin.succAbove] <;>
    push_cast <;> ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem fullCof_cast (S : Support4) :
    orderedCof S = realCof (S.val.orderEmbOfFin S.property) := by
  classical
  let e : Fin 4 ↪o Fin 19 := S.val.orderEmbOfFin S.property
  funext j
  simp only [orderedCof, liftCof, realCof, extend4, Finset.sum_apply, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hdec : (fun a b : Fin 19 => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq (Fin 19)) := Subsingleton.elim _ _
  rw [hdec]
  change (Pi.single (e i) (cofactor (bR.submatrix id (fun k => e k)) i) : Fin 19 → ℝ) j =
    (((Pi.single (e i) (cof4 e i) : Fin 19 → ℤ) j : ℤ) : ℝ)
  by_cases hj : j = e i
  · subst j
    rw [Pi.single_eq_same, Pi.single_eq_same]
    exact cofactor_cast e i
  · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, Int.cast_zero]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem oriented_full_cofactor_in_catalog
    (S : Support4) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hn : ∀ j, 0 ≤ (ε • orderedCof S) j) (hne : ε • orderedCof S ≠ 0) :
    ∃ t : Fin 187, ∃ d : ℝ, 0 < d ∧
      ε • orderedCof S = d • (fun j => (zZ t j : ℝ)) := by
  classical
  have hS : S.val ∈ (Finset.univ : Finset (Fin 19)).powersetCard 4 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩
  obtain ⟨w, hw⟩ := local_coverage S.val hS
  rw [fullCof_cast] at hn hne ⊢
  exact classify_checked (S.val.orderEmbOfFin S.property)
    (S.val.orderEmbOfFin S.property).injective w hw ε hε hn hne

-- Exact original Fin16 gap equality is consumed at projection, not just cited.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem catalog_lift (t : Fin 187) :
    liftGap (fun j => (gZ t j : ℝ)) = fun j => (zZ t j : ℝ) := by
  classical
  funext j
  refine Fin.addCases (m := 16) (n := 3) (motive := fun q =>
    liftGap (fun k => (gZ t k : ℝ)) q = (zZ t q : ℝ)) ?_ ?_ j
  · intro k
    simp [liftGap, zZ]
  · intro r
    simp only [liftGap, zZ, Fin.append_right]
    rw [catalog_slack t]
    simp [aR, Matrix.mulVec, dotProduct]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem bR_mul (z : Fin 19 → ℝ) (r : Fin 3) :
    (bR *ᵥ z) r = (aR *ᵥ project z) r - z (Fin.natAdd 16 r) := by
  classical
  change (∑ j : Fin 19, bR r j * z j) = _
  rw [Fin.sum_univ_add (a := 16) (b := 3)]
  simp [bR, bZ, aR, project, Matrix.mulVec, dotProduct, ite_mul, sub_eq_add_neg]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem bR_full_span : Submodule.span ℝ (Set.range bR.col) = ⊤ := by
  classical
  rw [← Matrix.range_mulVecLin]
  apply LinearMap.range_eq_top.mpr
  intro y
  refine ⟨Fin.append (fun _ : Fin 16 => (0 : ℝ)) (fun r => -y r), ?_⟩
  change bR *ᵥ Fin.append (fun _ : Fin 16 => (0 : ℝ)) (fun r => -y r) = y
  funext r
  rw [bR_mul]
  simp [project, Matrix.mulVec, dotProduct]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem liftGap_kernel (g : Fin 16 → ℝ) :
    InKernel bR (liftGap g) ↔
      (∀ j, 0 ≤ g j) ∧ (∀ r, 0 ≤ (aR *ᵥ g) r) := by
  classical
  constructor
  · intro hz
    exact ⟨fun j => by simpa [liftGap] using hz.1 (Fin.castAdd 3 j),
      fun r => by simpa [liftGap] using hz.1 (Fin.natAdd 16 r)⟩
  · rintro ⟨hg,hAg⟩
    refine ⟨?_, ?_⟩
    · intro j
      refine Fin.addCases (m := 16) (n := 3) (motive := fun q => 0 ≤ liftGap g q) ?_ ?_ j
      · intro k
        simpa [liftGap] using hg k
      · intro r
        simpa [liftGap] using hAg r
    · intro r
      change (bR *ᵥ liftGap g) r = 0
      rw [bR_mul]
      simp [project, liftGap]

-- This equality is checked from the supplied Lean literals, at every original id.
-- In particular Fin 187's last id reduces to originalRay's sole default branch.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem originalGap_owner (t : Fin 187) :
    originalGap t = fun q => ((originalRay t).gap q : ℤ) := by
  classical
  fin_cases t <;> funext q <;> fin_cases q <;> rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem catalog_owner_alignment (t : Fin 187) :
    gZ t = fun q => ((originalRay t).gap q : ℤ) :=
  (catalog_alignment t).trans (originalGap_owner t)
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem project_catalog_owner (t : Fin 187) :
    project (fun q => (zZ t q : ℝ)) =
      fun q => ((originalRay t).gap q : ℝ) := by
  classical
  rw [← catalog_lift]
  funext q
  change Fin.append (fun k => (gZ t k : ℝ)) (aR *ᵥ fun k => (gZ t k : ℝ))
    (Fin.castAdd 3 q) = ((originalRay t).gap q : ℝ)
  rw [Fin.append_left]
  exact_mod_cast congrFun (catalog_owner_alignment t) q

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem aR_eq_A : aR = A := by
  classical
  ext r q
  fin_cases r <;> fin_cases q <;> norm_num [aR, aZ, A]


#print axioms valid00
#print axioms align00
#print axioms valid01
#print axioms align01
#print axioms valid02
#print axioms align02
#print axioms valid03
#print axioms align03
#print axioms valid04
#print axioms align04
#print axioms valid05
#print axioms align05
#print axioms valid06
#print axioms align06
#print axioms valid07
#print axioms align07
#print axioms valid08
#print axioms align08
#print axioms valid09
#print axioms align09
#print axioms valid10
#print axioms align10
#print axioms valid11
#print axioms align11
#print axioms valid12
#print axioms align12
#print axioms valid13
#print axioms align13
#print axioms valid14
#print axioms align14
#print axioms valid15
#print axioms align15
#print axioms catalog_slack
#print axioms catalog_lift
#print axioms checked_tuple
#print axioms oriented_full_cofactor_in_catalog

end ScalarCertificate

open ScalarCertificate

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem three_row_scalar_bound (N : ℕ) (hN : 67 ≤ N)
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hmass : ∑ i, l i = 1)
    (hL3 : (∑ i : Fin 3, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 6, l ⟨N-6+i.val, by omega⟩)
    (hL4 : (∑ i : Fin 6, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 10, l ⟨N-10+i.val, by omega⟩)
    (hC3 : l ⟨0, by omega⟩ ≤ ∑ i : Fin 3, l ⟨N-3+i.val, by omega⟩) :
    let t : ℕ := (3*N+4)/8
    ∑ i, (l i)^2 ≤ (9*(N : ℝ)+16*(t : ℝ))/(3*(N : ℝ)+2*(t : ℝ))^2 := by
  classical
  -- All finite arithmetic above is local to this unbounded-N theorem.
  -- fixedGood is constructed here; it is not a hypothesis of the result.
  have fixedGood : ∀ (j : ℕ), 6 ≤ j → j ≤ N-10 →
      ∀ x : Fin 16 → ℝ, (∀ q, 0 ≤ x q) → (∀ r, 0 ≤ (A *ᵥ x) r) →
        spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j) x) := by
    intro j hj hj' x hx hAx
    have hpositions : positions N j = positions₁₆ N j := by
      rw [positions_literal N j hN]
      rfl
    have hp : ∀ q, positions N j q ≤ N := by
      rw [hpositions]
      exact positions₁₆_le N j hN hj'
    have hrays (i : Fin 187) :
        spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j)
            (fun q => ((originalRay i).gap q : ℝ))) := by
      apply spectralGood_of_square _ _ (Real.sqrt_nonneg _)
      · rw [mass_synth (positions N j) hp, hpositions,
          ray_mass_identity (originalRay i) (originalRay_valid i).moments N j hN]
        exact (ray_mass_positive (originalRay i) (originalRay_valid i)
          (N : ℝ) (j : ℝ) (by exact_mod_cast hN) (by exact_mod_cast hj)).le
      · rw [square_synth (positions N j) hp, mass_synth (positions N j) hp,
          Real.sq_sqrt (target_nonneg N), hpositions]
        simpa only [target, bulkValue, bulkIndex] using
          original_ray_gram_bound i N j hN hj hj'

    -- Good is the actual promoted norm-to-mass property after projection and
    -- synthesis at these SAME N,j and positions, not an abstract assumed cone.
    let K : PointedCone ℝ (Fin 19 → ℝ) := {
      carrier := {z | spectralGood (Real.sqrt (target N))
        (synth (d := N) (positions N j) (project z))}
      zero_mem' := by
        change spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j) (project 0))
        simp only [map_zero]
        exact spectralGood_zero N _
      add_mem' := by
        intro u v hu hv
        change spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j) (project (u+v)))
        simp only [map_add]
        exact spectralGood_add _ _ _ hu hv
      smul_mem' := by
        intro a z hz
        change spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j) (project ((a : ℝ) • z)))
        simp only [map_smul]
        exact spectralGood_smul _ (a : ℝ) _ a.property hz }

    have hull_le : PointedCone.hull ℝ (cofactorCandidates bR) ≤ K := by
      apply Submodule.span_le.mpr
      intro w hw
      have hwdata : InKernel bR w ∧ w ≠ 0 := by
        rcases hw with ⟨k, hk, ρ, σ, η, hη, hweq, hwK, hw0⟩
        exact ⟨hwK, hw0⟩
      obtain ⟨S, ε, a, hε, ha, heq⟩ :=
        cofactor_candidate_ordered_full bR bR_full_span hw
      -- FullSupport 19 3 is definitionally Support4. The local orderedCof is
      -- definitionally the private generic orderedCof bR, including the ordering.
      have hwfull : w = a • (ε • orderedCof S) := heq
      have hvn : ∀ q, 0 ≤ (ε • orderedCof S) q := by
        intro q
        have h := hwdata.1.1 q
        rw [hwfull] at h
        change 0 ≤ a * (ε • orderedCof S) q at h
        exact nonneg_of_mul_nonneg_right h ha
      have hv0 : ε • orderedCof S ≠ 0 := by
        intro hz
        apply hwdata.2
        rw [hwfull, hz, smul_zero]
      obtain ⟨t, d, hd, hcat⟩ :=
        oriented_full_cofactor_in_catalog S ε hε hvn hv0
      have hwcat : w = (a*d) • (fun q => (zZ t q : ℝ)) := by
        rw [hwfull, hcat, smul_smul]
      change spectralGood (Real.sqrt (target N))
        (synth (d := N) (positions N j) (project w))
      rw [hwcat]
      simp only [map_smul, project_catalog_owner t]
      exact spectralGood_smul _ (a*d) _ (mul_pos ha hd).le (hrays t)

    have hkernel : InKernel bR (liftGap x) := by
      apply (liftGap_kernel x).mpr
      exact ⟨hx, by simpa only [aR_eq_A] using hAx⟩
    have hmem : liftGap x ∈ PointedCone.hull ℝ (cofactorCandidates bR) :=
      (nonnegKernel_iff_mem_hull_cofactorCandidates bR (liftGap x)).mp hkernel
    have hgood := hull_le hmem
    change spectralGood (Real.sqrt (target N))
      (synth (d := N) (positions N j) (project (liftGap x))) at hgood
    have hproject : project (liftGap x) = x := by
      funext q
      change Fin.append x (aR *ᵥ x) (Fin.castAdd 3 q) = x q
      exact Fin.append_left _ _ _
    rwa [hproject] at hgood

  have hrows : ∀ r, 0 ≤ slackMap N hN l r := by
    intro r
    fin_cases r
    · exact sub_nonneg.mpr hL3
    · exact sub_nonneg.mpr hL4
    · exact sub_nonneg.mpr hC3
  have hgood := norm_from_fixed_cones N hN (Real.sqrt (target N)) fixedGood l ho hn hrows
  have hb := spectralGood_square (Real.sqrt (target N)) l (Real.sqrt_nonneg _)
    (by rw [hmass]; norm_num) hgood
  rw [hmass, Real.sq_sqrt (target_nonneg N)] at hb
  simpa only [one_pow, mul_one, target] using hb

#print axioms three_row_scalar_bound

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound

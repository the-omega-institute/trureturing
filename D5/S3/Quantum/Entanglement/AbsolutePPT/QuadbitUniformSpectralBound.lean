/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Ordered full-row cofactor padding and full-gap spectral compression. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSpectralBound
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-
The following scalar target remains unproved and is not declared here.

theorem three_row_scalar_bound (N : ℕ) (hN : 67 ≤ N)
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hmass : ∑ i, l i = 1)
    (hL3 : (∑ i : Fin 3, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 6, l ⟨N - 6 + i.val, by omega⟩)
    (hL4 : (∑ i : Fin 6, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 10, l ⟨N - 10 + i.val, by omega⟩)
    (hC3 : l ⟨0, by omega⟩ ≤
      ∑ i : Fin 3, l ⟨N - 3 + i.val, by omega⟩) :
    let t : ℕ := (3 * N + 4) / 8
    ∑ i, (l i)^2 ≤
      (9 * (N : ℝ) + 16 * (t : ℝ)) /
        (3 * (N : ℝ) + 2 * (t : ℝ))^2

The private padding results below preserve the original rows and allow zero
coordinates. The scalar proof still requires the ordered integer cofactor
classification, spectral synthesis, middle-gap compression, symbolic ray
estimates, and the unbounded integer optimization.
-/

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
private def A : Matrix (Fin 3) (Fin 16) ℝ :=
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

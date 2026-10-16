/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/FullRowCofactor
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/FullRowCofactor
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Positive cofactor candidates extend to ordered full-row supports. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open NonnegativeKernelCircuit NonnegativeKernelCofactor
open D5.S3.Arith.Lattices.CofactorKernel (cofactor augment kernel_cross_identity)
noncomputable section

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
theorem cofactor_candidate_ordered_full {n m : ℕ}
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

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound

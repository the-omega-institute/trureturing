/- GID: D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/UnequalBlockEffects
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attained spectral entropy for three effects with unequal rank caps. -/

import D5.S3.Quantum.Analysis.RefinedBMVWords
import D5.S3.Quantum.Measurement.Auric.EqualBlockEffects
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Sort

/-! # Ordered supporting prices for three effects -/

namespace D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects

open Matrix Finset
open EqualBlockEffects (diagonal_entropy effect_le_one eigenvalues_mem_unit projector_apply)
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The total spectral sum for three positive semidefinite effects. -/
def spectralSum (f : ℝ → ℝ) (A : Fin 3 → Matrix n n ℂ)
    (hp : ∀ j, (A j).PosSemidef) : ℝ :=
  ∑ j, ∑ i, f ((hp j).isHermitian.eigenvalues i)

/-- Positive effects summing to identity with prescribed traces and capped ranks. -/
def Feasible (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) (A : Fin 3 → Matrix n n ℂ) : Prop :=
  (∀ j, (A j).PosSemidef) ∧ (∑ j, A j = 1) ∧
    (∀ j, (trace (A j)).re = τ j) ∧ (∀ j, (A j).rank ≤ m j)

local notation "H" => EuclideanSpace ℂ n

private theorem pad {S T : Submodule ℂ H} (hST : S ≤ T) {k : ℕ}
    (hS : Module.finrank ℂ S ≤ k) (hT : k ≤ Module.finrank ℂ T) :
    ∃ U : Submodule ℂ H, S ≤ U ∧ U ≤ T ∧ Module.finrank ℂ U = k := by
  obtain ⟨r, hr⟩ : ∃ r, k = Module.finrank ℂ S + r :=
    ⟨k - Module.finrank ℂ S, by omega⟩
  clear hS
  induction r generalizing S with
  | zero => exact ⟨S, le_rfl, hST, by omega⟩
  | succ r ih =>
    have hn : ¬ T ≤ S := fun h => by have := Submodule.finrank_mono h; omega
    obtain ⟨v, hvT, hvS⟩ := Set.not_subset.mp hn
    let W := S ⊔ Submodule.span ℂ {v}
    have hW : Module.finrank ℂ W = Module.finrank ℂ S + 1 :=
      Submodule.finrank_sup_span_singleton hvS
    obtain ⟨U, hWU, hUT, hU⟩ := ih
      (sup_le hST (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvT)))
      (by omega : k = Module.finrank ℂ W + r)
    exact ⟨U, le_sup_left.trans hWU, hUT, hU⟩

private theorem zero_coordinates {A : Matrix n n ℂ} (h : A.IsHermitian) {l : ℕ}
    (hl : l ≤ Fintype.card n - A.rank) :
    ∃ Z : Finset n, Z.card = l ∧ ∀ i ∈ Z, h.eigenvalues i = 0 := by
  classical
  let Z := univ.filter (fun i => h.eigenvalues i = 0)
  have hZ : Z.card = Fintype.card n - A.rank := by
    rw [h.rank_eq_card_non_zero_eigs, Fintype.card_subtype_compl, Fintype.card_subtype]
    exact (Nat.sub_sub_self (card_le_univ Z)).symm
  obtain ⟨W, hW, hc⟩ := exists_subset_card_eq (s := Z) (hZ.symm ▸ hl)
  exact ⟨W, hc, fun i hi => (mem_filter.mp (hW hi)).2⟩

private def kernelSpan {A : Matrix n n ℂ} (h : A.IsHermitian) (Z : Finset n) :
    Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun i : Z => h.eigenvectorBasis i)

private theorem finrank_kernelSpan {A : Matrix n n ℂ} (h : A.IsHermitian) (Z : Finset n) :
    Module.finrank ℂ (kernelSpan h Z) = Z.card := by
  have hi : LinearIndependent ℂ (fun i : Z => h.eigenvectorBasis i) :=
    h.eigenvectorBasis.toBasis.linearIndependent.comp (fun i : Z => i.val) Subtype.val_injective
  unfold kernelSpan
  rw [finrank_span_eq_card hi, Fintype.card_coe]

private theorem paddedFlag (K : Fin 3 → Submodule ℂ H) (l : Fin 3 → ℕ)
    (hK : ∀ j, Module.finrank ℂ (K j) = l j) (hd : ∑ j, l j ≤ Fintype.card n) :
    ∃ T : Fin 3 → Submodule ℂ H, Monotone T ∧ (∀ j, K j ≤ T j) ∧
      Module.finrank ℂ (T 0) = l 0 ∧ Module.finrank ℂ (T 1) = l 0 + l 1 ∧
      Module.finrank ℂ (T 2) = l 0 + l 1 + l 2 := by
  let S := K 0 ⊔ K 1
  have hS : Module.finrank ℂ S ≤ l 0 + l 1 := by
    simpa [hK] using Submodule.finrank_add_le_finrank_add_finrank (K 0) (K 1)
  have hSK : Module.finrank ℂ (S ⊔ K 2 : Submodule ℂ H) ≤ l 0 + l 1 + l 2 :=
    (Submodule.finrank_add_le_finrank_add_finrank S (K 2)).trans (by rw [hK]; omega)
  obtain ⟨T₂, hST₂, _, ht₂⟩ := pad (le_top : S ⊔ K 2 ≤ ⊤) hSK (by
    simpa [Fin.sum_univ_three, finrank_euclideanSpace] using hd)
  obtain ⟨T₁, hST₁, h12, ht₁⟩ := pad (le_sup_left.trans hST₂) hS (by rw [ht₂]; omega)
  refine ⟨![K 0, T₁, T₂], ?_, ?_, hK 0, ht₁, ht₂⟩
  · have h01 : K 0 ≤ T₁ := le_sup_left.trans hST₁
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact le_rfl
      | exact h01
      | exact h12
      | exact h01.trans h12
      | exact False.elim (by simpa [Fin.le_def] using hij)
  · intro j
    fin_cases j
    · exact le_rfl
    · exact le_sup_right.trans hST₁
    · exact le_sup_right.trans hST₂

private def proj (S : Submodule ℂ H) : Matrix n n ℂ := (HermitianMat.projector S).mat

private theorem proj_trace (S : Submodule ℂ H) :
    (trace (proj S)).re = Module.finrank ℂ S := by
  change RCLike.re (HermitianMat.projector S).mat.trace = _
  rw [← HermitianMat.trace_eq_re_trace, HermitianMat.trace_projector]

private theorem proj_psd (S : Submodule ℂ H) : (proj S).PosSemidef :=
  (HermitianMat.mat_nonneg (HermitianMat.projector_nonneg S)).posSemidef

private theorem proj_compl (S : Submodule ℂ H) : 1 - proj S = proj Sᗮ := by
  have h := congrArg HermitianMat.mat (HermitianMat.projector_add_orthogonal S)
  simp only [HermitianMat.mat_add, HermitianMat.mat_one] at h
  exact sub_eq_of_eq_add' h.symm

private theorem proj_diff_psd {S T : Submodule ℂ H} (hst : S ≤ T) :
    (proj T - proj S).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  have h := Matrix.isPositive_toEuclideanLin_iff.mpr (proj_psd (n := n) T)
  have h' := Matrix.isPositive_toEuclideanLin_iff.mpr (proj_psd (n := n) S)
  refine ⟨by simpa using h.1.sub h'.1, fun x => ?_⟩
  simp only [map_sub, LinearMap.sub_apply, proj, projector_apply]
  rw [inner_sub_left, map_sub, sub_nonneg,
    T.re_inner_starProjection_eq_normSq, S.re_inner_starProjection_eq_normSq]
  have hn := S.norm_orthogonalProjectionOnto_apply_le (T.starProjection x)
  rw [S.orthogonalProjectionOnto_starProjection_of_le hst] at hn
  exact pow_le_pow_left₀ (norm_nonneg _) (by
    change ‖S.orthogonalProjectionOnto x‖ ≤ ‖T.starProjection x‖
    exact hn) 2

private def overlap {A : Matrix n n ℂ} (h : A.IsHermitian) (P : Matrix n n ℂ)
    (i : n) : ℝ :=
  ((Unitary.conjStarAlgAut ℂ _ (star h.eigenvectorUnitary) P) i i).re

private theorem overlap_nonneg {A P : Matrix n n ℂ} (h : A.IsHermitian)
    (hP : P.PosSemidef) (i : n) : 0 ≤ overlap h P i :=
  (Complex.nonneg_iff.mp
    ((map_nonneg (Unitary.conjStarAlgAut ℂ _ (star h.eigenvectorUnitary))
      hP.nonneg).posSemidef.diag_nonneg (i := i))).1

private theorem overlap_trace {A : Matrix n n ℂ} (h : A.IsHermitian) (P : Matrix n n ℂ) :
    ∑ i, overlap h P i = (trace P).re := by
  rw [← RefinedBMV.trace_conjugation (star h.eigenvectorUnitary) P]
  simp [trace, Complex.re_sum, overlap]

private theorem overlap_mul_trace {A : Matrix n n ℂ} (h : A.IsHermitian) (P : Matrix n n ℂ) :
    ∑ i, h.eigenvalues i * overlap h P i = (trace (P * A)).re := by
  rw [← RefinedBMV.trace_conjugation (star h.eigenvectorUnitary) (P * A), map_mul,
    h.conjStarAlgAut_star_eigenvectorUnitary]
  simp [trace, mul_diagonal, Complex.mul_re, overlap, mul_comm]

private theorem overlap_proj_one {A : Matrix n n ℂ} (h : A.IsHermitian) (S : Submodule ℂ H)
    {i : n} (hi : h.eigenvectorBasis i ∈ S) : overlap h (proj S) i = 1 := by
  have hP : (proj S).mulVec (h.eigenvectorBasis i) = h.eigenvectorBasis i := by
    have h := congrArg WithLp.ofLp (projector_apply S (h.eigenvectorBasis i))
    rw [Submodule.starProjection_eq_self_iff.mpr hi] at h
    exact h
  unfold overlap
  rw [Unitary.conjStarAlgAut_star_apply]
  have hv := congrFun (h.star_eigenvectorUnitary_mulVec i) i
  have he : ((star (h.eigenvectorUnitary : Matrix n n ℂ) * proj S *
      (h.eigenvectorUnitary : Matrix n n ℂ)) *ᵥ Pi.single i 1) i = 1 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, h.eigenvectorUnitary_mulVec, hP, hv]
    simp
  rw [mulVec_single_one, col_apply] at he
  rw [he]
  simp

private theorem overlap_sub {A : Matrix n n ℂ} (h : A.IsHermitian) (P Q : Matrix n n ℂ)
    (i : n) : overlap h (P - Q) i = overlap h P i - overlap h Q i := by
  unfold overlap
  rw [map_sub, Matrix.sub_apply, Complex.sub_re]

private theorem overlap_unit_sum {A : Matrix n n ℂ} (h : A.IsHermitian)
    (L : Fin 4 → Matrix n n ℂ) (hL : ∑ c, L c = 1) (i : n) :
    ∑ c, overlap h (L c) i = 1 := by
  have he := congrArg (fun P => overlap h P i) hL
  simpa [overlap, map_sum, Matrix.sum_apply, Complex.re_sum] using he

/-- Number of coordinates of each of the three missing types and the common type. -/
def multiplicity (l : Fin 3 → ℕ) (b : ℕ) : Fin 4 → ℕ :=
  ![l 0, l 1, l 2, b]

/-- Set each row to zero on its excluded column type. -/
def allocation (t : Fin 3 → Fin 4 → ℝ) (j : Fin 3) (c : Fin 4) : ℝ :=
  if c = j.castSucc then 0 else t j c

private theorem weighted_le_of_prefix (g w : Fin 4 → ℝ) (j : Fin 3)
    (hg : Antitone g) (hw : ∀ c, 0 ≤ w c) (hs : ∑ c, w c = 1)
    (hpre : ∑ c, (if c ≤ j.castSucc then w c else 0) = 1) :
    g j.castSucc ≤ ∑ c, g c * w c := by
  have hz (c : Fin 4) (hc : ¬ c ≤ j.castSucc) : w c = 0 := by
    have hn (c : Fin 4) : 0 ≤ w c - (if c ≤ j.castSucc then w c else 0) := by
      split <;> simp [hw]
    have hsum : ∑ c, (w c - if c ≤ j.castSucc then w c else 0) = 0 := by
      rw [sum_sub_distrib, hs, hpre, sub_self]
    have h := single_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 4))) => hn i) (mem_univ c)
    rw [hsum, ite_eq_right hc, sub_zero] at h
    exact le_antisymm h (hw c)
  calc
    g j.castSucc = ∑ c, g j.castSucc * w c := by rw [← mul_sum, hs, mul_one]
    _ ≤ ∑ c, g c * w c := by
      apply sum_le_sum
      intro c _
      by_cases hc : c ≤ j.castSucc
      · exact mul_le_mul_of_nonneg_right (hg hc) (hw c)
      · simp [hz c hc]

private theorem matrix_bound (f : ℝ → ℝ) (hf : f 0 = 0) (m : Fin 3 → ℕ)
    (l : Fin 3 → ℕ) (b : ℕ) (hl : ∀ j, l j = Fintype.card n - m j)
    (hd : ∑ c, multiplicity l b c = Fintype.card n)
    (p : Fin 3 → ℝ) (s : Fin 4 → ℝ) (g : Fin 3 → Fin 4 → ℝ)
    (hg : ∀ j, Antitone (g j))
    (hsupport : ∀ j c x, x ∈ Set.Icc (0 : ℝ) 1 → f x ≤ (p j + s c) * x + g j c)
    {τ : Fin 3 → ℝ} {A : Fin 3 → Matrix n n ℂ} (hA : Feasible m τ A) :
    spectralSum f A hA.1 ≤
      (∑ j, p j * τ j) + ∑ c, (multiplicity l b c : ℝ) * s c +
        ((∑ j, ∑ c, g j c * (multiplicity l b c : ℝ)) -
          ∑ j, g j j.castSucc * (l j : ℝ)) := by
  classical
  let h (j : Fin 3) := (hA.1 j).isHermitian
  let e (j : Fin 3) := (h j).eigenvalues
  have hz (j : Fin 3) := zero_coordinates (h j) (show l j ≤ Fintype.card n - (A j).rank by
    rw [hl]; exact Nat.sub_le_sub_left (hA.2.2.2 j) _)
  choose Z hcard hzero using hz
  have hd' : ∑ j, l j ≤ Fintype.card n := by
    simp [Fin.sum_univ_four, multiplicity, Fin.sum_univ_three] at hd ⊢
    omega
  obtain ⟨T, hT, hKT, ht0, ht1, ht2⟩ := paddedFlag
    (fun j => kernelSpan (h j) (Z j)) l (fun j => (finrank_kernelSpan _ _).trans (hcard j)) hd'
  let P (j : Fin 3) := proj (T j)
  let L : Fin 4 → Matrix n n ℂ := ![P 0, P 1 - P 0, P 2 - P 1, 1 - P 2]
  have hL : ∑ c, L c = 1 := by simp [Fin.sum_univ_four, L]
  have hLp (c : Fin 4) : (L c).PosSemidef := by
    fin_cases c
    · exact proj_psd _
    · exact proj_diff_psd (hT (by decide : (0 : Fin 3) ≤ 1))
    · exact proj_diff_psd (hT (by decide : (1 : Fin 3) ≤ 2))
    · change (1 - proj (T 2)).PosSemidef
      rw [proj_compl]
      exact proj_psd _
  have htr (c : Fin 4) : (trace (L c)).re = multiplicity l b c := by
    have hdR : ((l 0 : ℝ) + l 1 + l 2 + b) = Fintype.card n := by
      exact_mod_cast (by simpa [Fin.sum_univ_four, multiplicity] using hd :
        l 0 + l 1 + l 2 + b = Fintype.card n)
    fin_cases c <;> simp [L, P, multiplicity, trace_sub, proj_trace, ht0, ht1, ht2] <;> linarith
  let w (j : Fin 3) (c : Fin 4) (i : n) := overlap (h j) (L c) i
  have hws (j : Fin 3) (i : n) : ∑ c, w j c i = 1 := overlap_unit_sum (h j) L hL i
  have hwp (j : Fin 3) (c : Fin 4) (i : n) : 0 ≤ w j c i := overlap_nonneg _ (hLp c) i
  have hpre (j : Fin 3) (i : n) (hi : i ∈ Z j) :
      ∑ c, (if c ≤ j.castSucc then w j c i else 0) = 1 := by
    have hmem : (h j).eigenvectorBasis i ∈ T j := hKT j
      (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    have hh := overlap_proj_one (h j) (T j) hmem
    have he : ∑ c, (if c ≤ j.castSucc then w j c i else 0) = overlap (h j) (P j) i := by
      fin_cases j <;>
        simp [Fin.sum_univ_four, w, L, overlap_sub, Fin.le_def] <;> abel
    exact he.trans hh
  have hpnt (j : Fin 3) (i : n) : f (e j i) ≤
      ∑ c, w j c i * ((p j + s c) * e j i + g j c) -
        (if i ∈ Z j then g j j.castSucc else 0) := by
    by_cases hi : i ∈ Z j
    · rw [show e j i = 0 from hzero j i hi, hf, ite_eq_left hi, sub_nonneg]
      simpa [mul_comm] using weighted_le_of_prefix (g j) (fun c => w j c i) j
        (hg j) (fun c => hwp j c i) (hws j i) (hpre j i hi)
    · rw [ite_eq_right hi, sub_zero]
      have hei := eigenvalues_mem_unit (hA.1 j) (effect_le_one A hA.1 hA.2.1 j) i
      calc
        _ = ∑ c, w j c i * f (e j i) := by rw [← sum_mul, hws, one_mul]
        _ ≤ _ := sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hsupport j c _ hei) (hwp j c i)
  have hrow (j : Fin 3) :
      (∑ i, f (e j i)) ≤ p j * τ j +
        (∑ c, s c * (trace (L c * A j)).re) +
        ((∑ c, g j c * (multiplicity l b c : ℝ)) - g j j.castSucc * (l j : ℝ)) := by
    have hpen : ∑ i : n, (if i ∈ Z j then g j j.castSucc else 0) =
        g j j.castSucc * (l j : ℝ) := by
      simp [← sum_filter, hcard, nsmul_eq_mul, mul_comm]
    have hmass (c : Fin 4) : (∑ i, w j c i * e j i) = (trace (L c * A j)).re := by
      simpa [e, w, mul_comm] using overlap_mul_trace (h j) (L c)
    have hsum : ∑ c, (trace (L c * A j)).re = τ j := by
      rw [← Complex.re_sum, ← trace_sum, ← Matrix.sum_mul, hL, one_mul, hA.2.2.1]
    have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset n)) => hpnt j i)
    rw [sum_sub_distrib, hpen, Finset.sum_comm (s := (univ : Finset n))] at h
    have hsumc (c : Fin 4) : (∑ i, w j c i * ((p j + s c) * e j i + g j c)) =
        (p j + s c) * (trace (L c * A j)).re + g j c * multiplicity l b c := by
      simp_rw [show ∀ u v x y : ℝ, u * (v * x + y) = v * (u * x) + y * u by
        intros; ring]
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, hmass, overlap_trace, htr]
    simp_rw [hsumc, add_mul] at h
    simp only [sum_add_distrib, ← mul_sum (a := p j), hsum] at h
    linarith
  have hcol (c : Fin 4) : (∑ j, (trace (L c * A j)).re) = multiplicity l b c := by
    rw [← Complex.re_sum, ← trace_sum, ← Matrix.mul_sum, hA.2.1, mul_one, htr]
  have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 3))) => hrow j)
  simp only [sum_add_distrib, sum_sub_distrib] at hsum
  rw [Finset.sum_comm (f := fun j c => s c * (trace (L c * A j)).re)] at hsum
  simp_rw [← mul_sum, hcol, mul_comm (s _)] at hsum
  exact hsum

/-- The allowed scalar entries, with a missing column type for each effect
and one unrestricted type, weighted by the number of coordinates of each type. -/
def allocationValue (f : ℝ → ℝ) (l : Fin 3 → ℕ) (b : ℕ) (t : Fin 3 → Fin 4 → ℝ) : ℝ :=
  ∑ j, ∑ c, (multiplicity l b c : ℝ) * f (allocation t j c)

private theorem multiplicity_missing (l : Fin 3 → ℕ) (b : ℕ) (j : Fin 3) :
    multiplicity l b j.castSucc = l j := by
  fin_cases j <;> rfl

private theorem matrix_attains (f : ℝ → ℝ) (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (l : Fin 3 → ℕ) (b : ℕ) (hl : ∀ j, l j = Fintype.card n - m j)
    (hd : ∑ c, multiplicity l b c = Fintype.card n)
    (t : Fin 3 → Fin 4 → ℝ) (ht : ∀ j c, 0 ≤ t j c)
    (hcol : ∀ c, ∑ j, allocation t j c = 1)
    (hrow : ∀ j, (∑ c, multiplicity l b c * allocation t j c) = τ j) :
    ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
      spectralSum f A hA.1 = allocationValue f l b t := by
  classical
  let E : n ≃ (Σ c : Fin 4, Fin (multiplicity l b c)) :=
    Fintype.equivOfCardEq (by simpa [Fintype.card_sigma] using hd.symm)
  let v (j : Fin 3) (i : n) := allocation t j (E i).1
  let A (j : Fin 3) : Matrix n n ℂ := diagonal fun i => (v j i : ℂ)
  have hv (u : ℝ → ℝ) (j : Fin 3) :
      (∑ i, u (v j i)) = ∑ c, (multiplicity l b c : ℝ) * u (allocation t j c) := by
    rw [Fintype.sum_equiv E _ (fun x => u (allocation t j x.1)) fun _ => rfl]
    simp [Fintype.sum_sigma, nsmul_eq_mul]
  have hp (j : Fin 3) : (A j).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (v j i : ℂ)
    rw [Complex.nonneg_iff]
    refine ⟨?_, by simp⟩
    change 0 ≤ allocation t j (E i).1
    unfold allocation
    split <;> simp [ht]
  have hs : ∑ j, A j = 1 := by
    ext i k
    by_cases hik : i = k
    · subst k
      simp only [Matrix.sum_apply, A, diagonal_apply_eq, one_apply_eq, ← Complex.ofReal_sum, v]
      rw [hcol, Complex.ofReal_one]
    · simp [A, hik, Matrix.sum_apply]
  have htrace (j : Fin 3) : (trace (A j)).re = τ j := by
    simpa [A, trace_diagonal, Complex.re_sum] using (hv id j).trans (hrow j)
  have hr (j : Fin 3) : (A j).rank ≤ m j := by
    let count (x : ℝ) : ℝ := if x = 0 then 0 else 1
    have hc : ((A j).rank : ℝ) = ∑ i, count (v j i) := by
      change ((diagonal fun i => (v j i : ℂ)).rank : ℝ) = _
      rw [Matrix.rank_diagonal, Fintype.card_subtype, Finset.natCast_card_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : v j i = 0 <;> simp [count, hi]
    suffices hreal : ((A j).rank : ℝ) ≤ (m j : ℝ) by exact_mod_cast hreal
    rw [hc, hv]
    calc
      _ ≤ ∑ c, if c = j.castSucc then 0 else (multiplicity l b c : ℝ) := by
        apply sum_le_sum
        intro c _
        by_cases h : c = j.castSucc
        · simp [allocation, h, count]
        · simp only [ite_eq_right h]
          exact mul_le_of_le_one_right (Nat.cast_nonneg _) (by unfold count; split <;> norm_num)
      _ = (Fintype.card n : ℝ) - l j := by
        have h := sum_erase_add (univ : Finset (Fin 4)) (fun c => (multiplicity l b c : ℝ))
          (mem_univ j.castSucc)
        have hdR := congrArg (fun k : ℕ => (k : ℝ)) hd
        push_cast at hdR
        rw [hdR, multiplicity_missing] at h
        have he : (∑ c, (if c = j.castSucc then 0 else (multiplicity l b c : ℝ))) =
            ∑ c ∈ univ.erase j.castSucc, (multiplicity l b c : ℝ) := by
          rw [← filter_ne', sum_filter]
          simp_rw [ite_not]
        linarith
      _ ≤ m j := by
        rw [hl j]
        by_cases h : m j ≤ Fintype.card n
        · rw [Nat.cast_sub h]; linarith
        · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), Nat.cast_zero, sub_zero]
          exact_mod_cast le_of_not_ge h
  refine ⟨A, ⟨hp, hs, htrace, hr⟩, ?_⟩
  unfold spectralSum allocationValue
  exact sum_congr rfl fun j _ => (diagonal_entropy f (v j) _).trans (hv f j)

private theorem allocation_dual_identity (f : ℝ → ℝ) (hf : f 0 = 0)
    (l : Fin 3 → ℕ) (b : ℕ) (τ p : Fin 3 → ℝ) (s : Fin 4 → ℝ)
    (g t : Fin 3 → Fin 4 → ℝ)
    (heq : ∀ j c, f (t j c) = (p j + s c) * t j c + g j c)
    (hcol : ∀ c, ∑ j, allocation t j c = 1)
    (hrow : ∀ j, (∑ c, multiplicity l b c * allocation t j c) = τ j) :
    allocationValue f l b t =
      (∑ j, p j * τ j) + (∑ c, (multiplicity l b c : ℝ) * s c) +
        ((∑ j, ∑ c, g j c * (multiplicity l b c : ℝ)) -
          ∑ j, g j j.castSucc * (l j : ℝ)) := by
  let d (c : Fin 4) : ℝ := multiplicity l b c
  have hterm (j : Fin 3) (c : Fin 4) :
      d c * f (allocation t j c) = p j * (d c * allocation t j c) +
        (d c * s c) * allocation t j c + g j c * d c -
        (if c = j.castSucc then g j j.castSucc * l j else 0) := by
    by_cases hc : c = j.castSucc
    · subst c
      simp [allocation, hf, d, multiplicity_missing]
    · simp [allocation, hc, heq]
      ring
  have hrows (j : Fin 3) :
      (∑ c, d c * f (allocation t j c)) = p j * τ j +
        (∑ c, (d c * s c) * allocation t j c) +
        (∑ c, g j c * d c) - g j j.castSucc * l j := by
    have hmass : (∑ c, d c * allocation t j c) = τ j := hrow j
    simp only [hterm, sum_sub_distrib, sum_add_distrib, ← mul_sum (a := p j), hmass]
    simp
  unfold allocationValue
  change (∑ j, ∑ c, d c * f (allocation t j c)) = _
  simp only [hrows, sum_sub_distrib, sum_add_distrib]
  rw [sum_comm (f := fun j c => (d c * s c) * allocation t j c)]
  simp_rw [← mul_sum, hcol, mul_one]
  ring

private theorem isGreatest_of_support (f : ℝ → ℝ) (hf : f 0 = 0)
    (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) (l : Fin 3 → ℕ) (b : ℕ)
    (hl : ∀ j, l j = Fintype.card n - m j)
    (hd : ∑ c, multiplicity l b c = Fintype.card n)
    (p : Fin 3 → ℝ) (s : Fin 4 → ℝ) (g t : Fin 3 → Fin 4 → ℝ)
    (ht : ∀ j c, 0 ≤ t j c) (hg : ∀ j, Antitone (g j))
    (hsupport : ∀ j c x, x ∈ Set.Icc (0 : ℝ) 1 → f x ≤ (p j + s c) * x + g j c)
    (heq : ∀ j c, f (t j c) = (p j + s c) * t j c + g j c)
    (hcol : ∀ c, ∑ j, allocation t j c = 1)
    (hrow : ∀ j, (∑ c, multiplicity l b c * allocation t j c) = τ j) :
    IsGreatest {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
      spectralSum f A hA.1 = v} (allocationValue f l b t) := by
  refine ⟨matrix_attains f m τ l b hl hd t ht hcol hrow, ?_⟩
  rintro v ⟨A, hA, rfl⟩
  rw [allocation_dual_identity f hf l b τ p s g t heq hcol hrow]
  exact matrix_bound f hf m l b hl hd p s g hg hsupport hA

private theorem entropy_support {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    Real.negMulLog x ≤ (-Real.log t - 1) * x + t := by
  have h := mul_le_mul_of_nonneg_left
    (Real.negMulLog_le_one_sub_self (div_nonneg hx ht.le)) ht.le
  have hxt : t * (x / t) = x := by field_simp
  have hs := Real.negMulLog_mul t (x / t)
  rw [hxt] at hs
  have ht' : (x / t) * Real.negMulLog t = -Real.log t * x := by
    unfold Real.negMulLog
    field_simp
  rw [ht'] at hs
  rw [show t * (1 - x / t) = t - x by field_simp] at h
  linarith

/-- Denominators for normalized weights, ordered by the three missing types
and then the unrestricted type. -/
def columnDenominator (w : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![1 - w 0, 1 - w 1, 1 - w 2, 1]

/-- Scalar entries before imposing the zero belonging to each missing type. -/
def weightEntries (w : Fin 3 → ℝ) (j : Fin 3) (c : Fin 4) : ℝ :=
  w j / columnDenominator w c

/-- Row masses from the proportional allocation on all allowed positions. -/
def weightMass (l : Fin 3 → ℕ) (b : ℕ) (w : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  ∑ c, (multiplicity l b c : ℝ) * allocation (weightEntries w) j c

private theorem weight_columns (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j)
    (hwt : ∑ j, w j = 1) (c : Fin 4) :
    ∑ j, allocation (weightEntries w) j c = 1 := by
  rw [Fin.sum_univ_three] at hwt
  have hp (j : Fin 3) : 0 < 1 - w j := by
    have h0 := hw 0
    have h1 := hw 1
    have h2 := hw 2
    fin_cases j
    · change 0 < 1 - w 0; linarith
    · change 0 < 1 - w 1; linarith
    · change 0 < 1 - w 2; linarith
  fin_cases c <;> simp [Fin.sum_univ_three, allocation, weightEntries, columnDenominator,
    Fin.ext_iff, Fin.val_castSucc] <;>
    first
    | exact hwt
    | field_simp [(hp 0).ne', (hp 1).ne', (hp 2).ne'] <;> linarith

/-- The direct entropy has an attained maximum when positive normalized
weights, in decreasing order, give the prescribed trace masses. -/
theorem isGreatest_direct (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (hcap : ∑ j, (Fintype.card n - m j) ≤ Fintype.card n)
    (hw : ∀ j, 0 < w j) (hwt : ∑ j, w j = 1) (hord : Antitone w)
    (hrow : ∀ j, weightMass (fun j => Fintype.card n - m j)
      (Fintype.card n - ∑ k, (Fintype.card n - m k)) w j = τ j) :
    IsGreatest {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
      spectralSum Real.negMulLog A hA.1 = v}
      (allocationValue Real.negMulLog (fun j => Fintype.card n - m j)
        (Fintype.card n - ∑ j, (Fintype.card n - m j)) (weightEntries w)) := by
  let l (j : Fin 3) := Fintype.card n - m j
  let b := Fintype.card n - ∑ j, l j
  let d := columnDenominator w
  let t := weightEntries w
  have hd : ∑ c, multiplicity l b c = Fintype.card n := by
    simpa [Fin.sum_univ_four, multiplicity, ← Fin.sum_univ_three l, b] using
      Nat.add_sub_of_le hcap
  have hw1 (j : Fin 3) : w j < 1 := by
    have h0 := hw 0
    have h1 := hw 1
    have h2 := hw 2
    rw [Fin.sum_univ_three] at hwt
    fin_cases j
    · change w 0 < 1; linarith
    · change w 1 < 1; linarith
    · change w 2 < 1; linarith
  have hd0 (c : Fin 4) : 0 < d c := by
    fin_cases c
    · exact sub_pos.mpr (hw1 0)
    · exact sub_pos.mpr (hw1 1)
    · exact sub_pos.mpr (hw1 2)
    · exact zero_lt_one
  have hdm : Monotone d := by
    have h01 := sub_le_sub_left (hord (by decide : (0 : Fin 3) ≤ 1)) (1 : ℝ)
    have h12 := sub_le_sub_left (hord (by decide : (1 : Fin 3) ≤ 2)) (1 : ℝ)
    have h23 := sub_le_self (1 : ℝ) (hw 2).le
    intro a c h
    fin_cases a <;> fin_cases c <;>
      first
      | exact le_rfl
      | exact h01
      | exact h12
      | exact h23
      | exact h01.trans h12
      | exact h12.trans h23
      | exact h01.trans (h12.trans h23)
      | exact False.elim (by simpa [Fin.le_def] using h)
  have ht (j : Fin 3) (c : Fin 4) : 0 < t j c := div_pos (hw j) (hd0 c)
  let p (j : Fin 3) := -Real.log (w j) - 1
  let s (c : Fin 4) := Real.log (d c)
  have hslope (j : Fin 3) (c : Fin 4) : -Real.log (t j c) - 1 = p j + s c := by
    change -Real.log (w j / d c) - 1 = _
    rw [Real.log_div (hw j).ne' (hd0 c).ne']
    dsimp [p, s]
    ring
  exact isGreatest_of_support Real.negMulLog Real.negMulLog_zero m τ l b (fun _ => rfl) hd
    p s t t (fun j c => (ht j c).le)
    (fun j _ c hac => div_le_div_of_nonneg_left (hw j).le (hd0 _) (hdm hac))
    (fun j c x hx => hslope j c ▸ entropy_support (ht j c) hx.1)
    (fun j c => by rw [← hslope]; unfold Real.negMulLog; ring)
    (weight_columns w hw hwt) hrow

private theorem complement_support {y x : ℝ} (hy : 0 < y) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    let t := max 0 (1 - y)
    Real.negMulLog (1 - x) ≤ (Real.log y + 1) * x +
      (Real.negMulLog (1 - t) - (Real.log y + 1) * t) := by
  dsimp only
  by_cases h : y ≤ 1
  · rw [max_eq_right (sub_nonneg.mpr h)]
    have hsup := entropy_support hy (sub_nonneg.mpr hx.2)
    rw [show 1 - (1 - y) = y by ring, show Real.negMulLog y = -y * Real.log y from rfl]
    linarith
  · rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge h))]
    simp only [sub_zero, Real.negMulLog_one, mul_zero, add_zero]
    have hh := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr hx.2)
    have hl := Real.log_nonneg (le_of_not_ge h)
    nlinarith [mul_nonneg hl hx.1]

/-- Scalar entries for the complementary entropy, using multiplicative
parameters for one minus each entry. -/
def complementEntries (w : Fin 3 → ℝ) (k : Fin 4 → ℝ) (j : Fin 3) (c : Fin 4) : ℝ :=
  max 0 (1 - w j * k c)

/-- The complementary entropy has an attained maximum whenever positive
parameters with increasing column scales give the prescribed allocation. -/
theorem isGreatest_complement (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (k : Fin 4 → ℝ) (hcap : ∑ j, (Fintype.card n - m j) ≤ Fintype.card n)
    (hw : ∀ j, 0 < w j) (hk : ∀ c, 0 < k c) (hord : Monotone k)
    (hcol : ∀ c, ∑ j, allocation (complementEntries w k) j c = 1)
    (hrow : ∀ j, (∑ c, (multiplicity (fun j => Fintype.card n - m j)
      (Fintype.card n - ∑ i, (Fintype.card n - m i)) c : ℝ) *
        allocation (complementEntries w k) j c) = τ j) :
    IsGreatest {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
      spectralSum (fun x => Real.negMulLog (1 - x)) A hA.1 = v}
      (allocationValue (fun x => Real.negMulLog (1 - x)) (fun j => Fintype.card n - m j)
        (Fintype.card n - ∑ j, (Fintype.card n - m j)) (complementEntries w k)) := by
  let f (x : ℝ) := Real.negMulLog (1 - x)
  let l (j : Fin 3) := Fintype.card n - m j
  let b := Fintype.card n - ∑ j, l j
  let t := complementEntries w k
  let p (j : Fin 3) := Real.log (w j) + 1
  let s (c : Fin 4) := Real.log (k c)
  let g (j : Fin 3) (c : Fin 4) := f (t j c) - (p j + s c) * t j c
  have hd : ∑ c, multiplicity l b c = Fintype.card n := by
    simpa [Fin.sum_univ_four, multiplicity, ← Fin.sum_univ_three l, b] using
      Nat.add_sub_of_le hcap
  have ht (j : Fin 3) (c : Fin 4) : t j c ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (sub_le_self _ (mul_pos (hw j) (hk c)).le)⟩
  have hs (j : Fin 3) (c : Fin 4) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      f x ≤ (p j + s c) * x + g j c := by
    have hp : Real.log (w j * k c) + 1 = p j + s c := by
      rw [Real.log_mul (hw j).ne' (hk c).ne']
      dsimp [s, p]
      ring
    simpa only [hp, f, g, t, complementEntries] using complement_support (mul_pos (hw j) (hk c)) hx
  have hg (j : Fin 3) : Antitone (g j) := by
    intro a c hac
    have hm := Real.strictMonoOn_log.monotoneOn (show k a ∈ Set.Ioi (0 : ℝ) from hk a)
      (show k c ∈ Set.Ioi (0 : ℝ) from hk c) (hord hac)
    have hh := hs j a (t j c) (ht j c)
    have hdiff := mul_nonneg (sub_nonneg.mpr hm) (ht j c).1
    change 0 ≤ (s c - s a) * t j c at hdiff
    dsimp only [g] at hh ⊢
    linarith
  exact isGreatest_of_support f (by simp [f]) m τ l b (fun _ => rfl) hd p s g t
    (fun j c => (ht j c).1) hg hs (fun j c => by dsimp [g]; ring) hcol hrow

/-- The exact unnormalized maximum for capacities 3, 4, 4 in dimension five,
with trace masses 15/11, 20/11, 20/11. -/
theorem isGreatest_three_four_four :
    let a := (Real.sqrt 565 - 5) / 18
    IsGreatest {v : ℝ | ∃ A : Fin 3 → Matrix (Fin 5) (Fin 5) ℂ,
      ∃ hA : Feasible ![3, 4, 4] ![15 / 11, 20 / 11, 20 / 11] A,
      spectralSum Real.negMulLog A hA.1 = v}
      (4 * Real.negMulLog (1 / 2) +
        2 * (Real.negMulLog (a / (a + 1)) + Real.negMulLog (1 / (a + 1))) +
        Real.negMulLog (a / (a + 2)) + 2 * Real.negMulLog (1 / (a + 2))) := by
  dsimp only
  let a : ℝ := (Real.sqrt 565 - 5) / 18
  change IsGreatest _ (4 * Real.negMulLog (1 / 2) +
    2 * (Real.negMulLog (a / (a + 1)) + Real.negMulLog (1 / (a + 1))) +
    Real.negMulLog (a / (a + 2)) + 2 * Real.negMulLog (1 / (a + 2)))
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 565 by norm_num)
  have hn := Real.sqrt_nonneg (565 : ℝ)
  have ha : 1 ≤ a := by dsimp [a]; nlinarith
  have hq : 9 * a ^ 2 + 5 * a - 15 = 0 := by dsimp [a]; nlinarith
  have h1 : 0 < a + 1 := by linarith
  have h2 : 0 < a + 2 := by linarith
  let w : Fin 3 → ℝ := ![a / (a + 2), 1 / (a + 2), 1 / (a + 2)]
  have hw (j : Fin 3) : 0 < w j := by
    fin_cases j
    · exact div_pos (by linarith) h2
    · exact div_pos zero_lt_one h2
    · exact div_pos zero_lt_one h2
  have hwt : ∑ j, w j = 1 := by
    rw [Fin.sum_univ_three]
    change a / (a + 2) + 1 / (a + 2) + 1 / (a + 2) = 1
    field_simp <;> ring
  have hord : Antitone w := by
    have h01 : w 1 ≤ w 0 := div_le_div_of_nonneg_right ha h2.le
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact le_rfl
      | exact h01
      | exact False.elim (by simp [Fin.le_def] at hij)
  have hd0 : 1 - a / (a + 2) = 2 / (a + 2) := by field_simp <;> ring
  have hd1 : 1 - 1 / (a + 2) = (a + 1) / (a + 2) := by field_simp <;> ring
  have hhalf : (1 / (a + 2)) / (2 / (a + 2)) = 1 / 2 := by field_simp
  have hratio : ∀ z : ℝ, (z / (a + 2)) / ((a + 1) / (a + 2)) = z / (a + 1) := by
    intro z
    field_simp
  have hb (j : Fin 3) : Fintype.card (Fin 5) - (![3, 4, 4] : Fin 3 → ℕ) j =
      (![2, 1, 1] : Fin 3 → ℕ) j := by fin_cases j <;> rfl
  have hc : ∑ j : Fin 3, (Fintype.card (Fin 5) - (![3, 4, 4] : Fin 3 → ℕ) j) = 4 := by
    simp [hb, Fin.sum_univ_three]
  let x : Fin 3 → Fin 4 → ℝ :=
    ![![0, a / (a + 1), a / (a + 1), a / (a + 2)],
      ![1 / 2, 0, 1 / (a + 1), 1 / (a + 2)],
      ![1 / 2, 1 / (a + 1), 0, 1 / (a + 2)]]
  have hx : allocation (weightEntries w) = x := by
    funext j c
    fin_cases j <;> fin_cases c
    · rfl
    · change (a / (a + 2)) / (1 - 1 / (a + 2)) = _
      rw [hd1, hratio]
      rfl
    · change (a / (a + 2)) / (1 - 1 / (a + 2)) = _
      rw [hd1, hratio]
      rfl
    · exact div_one _
    · change (1 / (a + 2)) / (1 - a / (a + 2)) = _
      rw [hd0, hhalf]
      rfl
    · rfl
    · change (1 / (a + 2)) / (1 - 1 / (a + 2)) = _
      rw [hd1, hratio]
      rfl
    · exact div_one _
    · change (1 / (a + 2)) / (1 - a / (a + 2)) = _
      rw [hd0, hhalf]
      rfl
    · change (1 / (a + 2)) / (1 - 1 / (a + 2)) = _
      rw [hd1, hratio]
      rfl
    · rfl
    · exact div_one _
  have hm (j : Fin 3) : weightMass ![2, 1, 1] 1 w j =
      (![15 / 11, 20 / 11, 20 / 11] : Fin 3 → ℝ) j := by
    rw [weightMass, hx, Fin.sum_univ_four]
    fin_cases j
    · change (↑(2 : ℕ) : ℝ) * 0 + ↑(1 : ℕ) * (a / (a + 1)) +
        ↑(1 : ℕ) * (a / (a + 1)) + ↑(1 : ℕ) * (a / (a + 2)) = 15 / 11
      push_cast
      field_simp
      nlinarith
    · change (↑(2 : ℕ) : ℝ) * (1 / 2) + ↑(1 : ℕ) * 0 +
        ↑(1 : ℕ) * (1 / (a + 1)) + ↑(1 : ℕ) * (1 / (a + 2)) = 20 / 11
      push_cast
      field_simp
      nlinarith
    · change (↑(2 : ℕ) : ℝ) * (1 / 2) + ↑(1 : ℕ) * (1 / (a + 1)) +
        ↑(1 : ℕ) * 0 + ↑(1 : ℕ) * (1 / (a + 2)) = 20 / 11
      push_cast
      field_simp
      nlinarith
  have hl : (fun j : Fin 3 => Fintype.card (Fin 5) - (![3, 4, 4] : Fin 3 → ℕ) j) =
      ![2, 1, 1] := funext hb
  have hb' : Fintype.card (Fin 5) -
      (∑ j : Fin 3, (Fintype.card (Fin 5) - (![3, 4, 4] : Fin 3 → ℕ) j)) = 1 := by
    rw [hc]; decide
  have hh := isGreatest_direct (n := Fin 5) ![3, 4, 4] ![15 / 11, 20 / 11, 20 / 11] w
    (by rw [hc]; decide) hw hwt hord (by rw [hb', hl]; exact hm)
  have hv : allocationValue Real.negMulLog ![2, 1, 1] 1 (weightEntries w) =
      4 * Real.negMulLog (1 / 2) +
        2 * (Real.negMulLog (a / (a + 1)) + Real.negMulLog (1 / (a + 1))) +
        Real.negMulLog (a / (a + 2)) + 2 * Real.negMulLog (1 / (a + 2)) := by
    simp only [allocationValue, hx, Fin.sum_univ_three, Fin.sum_univ_four]
    change
      ((↑(2 : ℕ) : ℝ) * Real.negMulLog 0 + ↑(1 : ℕ) * Real.negMulLog (a / (a + 1)) +
          ↑(1 : ℕ) * Real.negMulLog (a / (a + 1)) + ↑(1 : ℕ) * Real.negMulLog (a / (a + 2))) +
        (↑(2 : ℕ) * Real.negMulLog (1 / 2) + ↑(1 : ℕ) * Real.negMulLog 0 +
          ↑(1 : ℕ) * Real.negMulLog (1 / (a + 1)) + ↑(1 : ℕ) * Real.negMulLog (1 / (a + 2))) +
        (↑(2 : ℕ) * Real.negMulLog (1 / 2) + ↑(1 : ℕ) * Real.negMulLog (1 / (a + 1)) +
          ↑(1 : ℕ) * Real.negMulLog 0 + ↑(1 : ℕ) * Real.negMulLog (1 / (a + 2))) = _
    push_cast
    rw [Real.negMulLog_zero]
    ring
  rw [hb', hl, hv] at hh
  exact hh

private def allowedRows (c : Fin 4) : Finset (Fin 3) :=
  univ.filter (fun j => c ≠ j.castSucc)

private theorem mem_allowedRows (c : Fin 4) (j : Fin 3) :
    j ∈ allowedRows c ↔ c ≠ j.castSucc := by
  simp [allowedRows]

private theorem last_mem_allowedRows (j : Fin 3) : j ∈ allowedRows (Fin.last 3) :=
  (mem_allowedRows _ _).2 (Fin.castSucc_ne_last j).symm

private theorem allowedRows_nonempty (c : Fin 4) : (allowedRows c).Nonempty := by
  fin_cases c <;> decide

private theorem multiplicity_castSucc (l : Fin 3 → ℕ) (b : ℕ) (j : Fin 3) :
    multiplicity l b j.castSucc = l j := by
  fin_cases j <;> rfl

private theorem multiplicity_last (l : Fin 3 → ℕ) (b : ℕ) :
    multiplicity l b (Fin.last 3) = b := rfl

private def priceObjective (l : Fin 3 → ℕ) (b : ℕ) (τ : Fin 3 → ℝ)
    (G : Fin 4 → (Fin 3 → ℝ) → ℝ) (u : Fin 3 → ℝ) : ℝ :=
  (∑ c, (multiplicity l b c : ℝ) * G c u) - ∑ j, τ j * u j

private theorem priceObjective_shift (l : Fin 3 → ℕ) (b : ℕ) (d : ℝ) (τ : Fin 3 → ℝ)
    (hd : (b : ℝ) + ∑ j, (l j : ℝ) = d) (hτ : ∑ j, τ j = d)
    (G : Fin 4 → (Fin 3 → ℝ) → ℝ)
    (hG : ∀ c u a, G c (fun j => u j + a) = G c u + a)
    (u : Fin 3 → ℝ) (a : ℝ) :
    priceObjective l b τ G (fun j => u j + a) = priceObjective l b τ G u := by
  unfold priceObjective
  simp only [hG, mul_add, sum_add_distrib, ← sum_mul, hτ]
  have hc : (∑ c, (multiplicity l b c : ℝ)) = d := by
    rw [Fin.sum_univ_castSucc]
    simp only [multiplicity_castSucc, multiplicity_last, add_comm _ (b : ℝ), hd]
  rw [hc]
  ring

/-- A column potential that dominates each allowed price gives a uniform
lower bound in terms of the largest difference of row prices. -/
private theorem price_coercivity (l : Fin 3 → ℕ) (b : ℕ) (d : ℝ) (τ : Fin 3 → ℝ)
    (hd : (b : ℝ) + ∑ j, (l j : ℝ) = d) (hτ : ∑ j, τ j = d)
    (hpos : ∀ j, 0 < τ j) (hupper : ∀ j, τ j < d - l j)
    (G : Fin 4 → (Fin 3 → ℝ) → ℝ)
    (hG : ∀ c u j, j ∈ allowedRows c → u j ≤ G c u) :
    ∃ δ > 0, ∀ u i k, δ * (u i - u k) ≤ priceObjective l b τ G u := by
  classical
  let margin (j : Fin 3) := min (τ j) (d - l j - τ j)
  obtain ⟨r, _, hr⟩ := univ.exists_min_image margin Finset.univ_nonempty
  let δ := margin r
  have hδ : 0 < δ := lt_min (hpos r) (sub_pos.mpr (hupper r))
  have hδτ (j : Fin 3) : δ ≤ τ j :=
    (hr j (mem_univ j)).trans (min_le_left _ _)
  have hδcap (j : Fin 3) : δ ≤ d - l j - τ j :=
    (hr j (mem_univ j)).trans (min_le_right _ _)
  refine ⟨δ, hδ, fun u i k => ?_⟩
  obtain ⟨j, _, hj⟩ := univ.exists_max_image u Finset.univ_nonempty
  let rest := (univ : Finset (Fin 3)).erase j
  have hrest : rest.Nonempty := by
    fin_cases j <;> decide
  obtain ⟨s, hs, hsecond⟩ := rest.exists_max_image u hrest
  have hsne : s ≠ j := (mem_erase.mp hs).1
  have hsj : u s ≤ u j := hj s (mem_univ s)
  have hfull : u j ≤ G (Fin.last 3) u := hG _ _ _ (last_mem_allowedRows j)
  have hmissing : ∑ a, (l a : ℝ) * (if a = j then u s else u j) ≤
      ∑ a, (l a : ℝ) * G a.castSucc u := by
    apply sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    by_cases ha : a = j
    · subst a
      exact (ite_eq_left rfl).trans_le (hG _ _ _ ((mem_allowedRows _ _).2
        (fun h => hsne (Fin.castSucc_injective _ h.symm))))
    · exact (ite_eq_right ha).trans_le (hG _ _ _ ((mem_allowedRows _ _).2
        (fun h => ha (Fin.castSucc_injective _ h))))
  have hsplit (f : Fin 3 → ℝ) : (∑ a ∈ rest, f a) + f j = ∑ a, f a :=
    sum_erase_add _ _ (mem_univ j)
  have hsum_l : (b : ℝ) + ∑ a ∈ rest, (l a : ℝ) = d - l j := by
    linarith [hsplit (fun a => (l a : ℝ))]
  have hsum_τ : ∑ a ∈ rest, τ a = d - τ j := by
    linarith [hsplit τ]
  rw [← hsplit (fun a => (l a : ℝ) * (if a = j then u s else u j))] at hmissing
  have hmissing' : (∑ a ∈ rest, (l a : ℝ)) * u j + l j * u s ≤
      ∑ a, (l a : ℝ) * G a.castSucc u := by
    rw [Finset.sum_mul]
    have hrw : (∑ a ∈ rest, (l a : ℝ) * (if a = j then u s else u j)) =
        ∑ a ∈ rest, (l a : ℝ) * u j := by
      apply sum_congr rfl
      intro a ha
      rw [ite_eq_right (mem_erase.mp ha).1]
    rw [hrw] at hmissing
    simpa using hmissing
  have hdecomp :
      (d - l j - τ j) * (u j - u s) + ∑ a ∈ rest, τ a * (u s - u a) ≤
        priceObjective l b τ G u := by
    unfold priceObjective
    rw [Fin.sum_univ_castSucc, ← hsplit (fun a => τ a * u a)]
    simp only [multiplicity_castSucc, multiplicity_last, mul_sub, sum_sub_distrib,
      ← Finset.sum_mul, hsum_τ]
    have hfull' := mul_le_mul_of_nonneg_left hfull (Nat.cast_nonneg b)
    have hl := congrArg (fun x : ℝ => x * u j) hsum_l
    linarith only [hmissing', hfull', hl]
  have hgap := mul_le_mul_of_nonneg_right (hδcap j) (sub_nonneg.mpr hsj)
  have hterms (a : Fin 3) (ha : a ∈ rest) : 0 ≤ τ a * (u s - u a) :=
    mul_nonneg (hpos a).le (sub_nonneg.mpr (hsecond a ha))
  have htop : δ * (u j - u k) ≤ priceObjective l b τ G u := by
    by_cases hk : k = j
    · subst k
      simp only [sub_self, mul_zero]
      exact (add_nonneg (mul_nonneg (sub_pos.mpr (hupper j)).le (sub_nonneg.mpr hsj))
        (sum_nonneg hterms)).trans hdecomp
    · have hk' : k ∈ rest := mem_erase.mpr ⟨hk, mem_univ k⟩
      have hkterm := mul_le_mul_of_nonneg_right (hδτ k) (sub_nonneg.mpr (hsecond k hk'))
      have hsum := single_le_sum hterms hk'
      linarith only [hgap, hkterm, hsum, hdecomp]
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_right (hj i (mem_univ i)) _) hδ.le).trans htop

private theorem exists_minimum_prices (F : (Fin 3 → ℝ) → ℝ) (hF : Continuous F)
    (hshift : ∀ u a, F (fun j => u j + a) = F u)
    {δ : ℝ} (hδ : 0 < δ) (hbound : ∀ u i k, δ * (u i - u k) ≤ F u) :
    ∃ u, ∀ v, F u ≤ F v := by
  let S : Set (Fin 3 → ℝ) := {u | u 0 = 0 ∧ F u ≤ F 0}
  let R := F 0 / δ
  have hclosed : IsClosed S :=
    (isClosed_eq (continuous_apply 0) continuous_const).inter
      (isClosed_le hF continuous_const)
  have hcompact : IsCompact S := by
    apply (isCompact_Icc (a := fun _ : Fin 3 => -R) (b := fun _ => R)).of_isClosed_subset hclosed
    intro u hu
    change u 0 = 0 ∧ F u ≤ F 0 at hu
    constructor
    · intro i
      have h := (hbound u 0 i).trans hu.2
      rw [hu.1, zero_sub] at h
      have h' : -u i ≤ R := (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using h)
      linarith
    · intro i
      have h := (hbound u i 0).trans hu.2
      rw [hu.1, sub_zero] at h
      exact (le_div_iff₀ hδ).2 (by simpa [mul_comm] using h)
  have hzero : (0 : Fin 3 → ℝ) ∈ S := ⟨rfl, le_rfl⟩
  obtain ⟨u, _, hu⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩ hF.continuousOn
  refine ⟨u, fun v => ?_⟩
  by_cases hv : F v ≤ F 0
  · let v' : Fin 3 → ℝ := fun j => v j + -v 0
    have hs : F v' = F v := hshift v _
    rw [← hs]
    exact hu (show v' ∈ S from ⟨by simp [v'], hs.trans_le hv⟩)
  · exact (hu hzero).trans (le_of_not_ge hv)

private def expSum (c : Fin 4) (u : Fin 3 → ℝ) : ℝ :=
  ∑ j ∈ allowedRows c, Real.exp (u j)

private theorem expSum_pos (c : Fin 4) (u : Fin 3 → ℝ) : 0 < expSum c u :=
  sum_pos (fun j _ => Real.exp_pos (u j)) (allowedRows_nonempty c)

private theorem le_log_expSum (c : Fin 4) (u : Fin 3 → ℝ) (j : Fin 3)
    (hj : j ∈ allowedRows c) : u j ≤ Real.log (expSum c u) := by
  rw [← Real.log_exp (u j)]
  exact Real.log_le_log (Real.exp_pos _) (single_le_sum (fun i _ => (Real.exp_pos (u i)).le) hj)

private theorem expSum_last (u : Fin 3 → ℝ) :
    expSum (Fin.last 3) u = ∑ j, Real.exp (u j) := by
  unfold expSum allowedRows
  rw [filter_eq_self.mpr]
  exact fun j _ => (mem_allowedRows _ _).1 (last_mem_allowedRows j)

private theorem expSum_castSucc (u : Fin 3 → ℝ) (j : Fin 3) :
    expSum j.castSucc u = expSum (Fin.last 3) u - Real.exp (u j) := by
  rw [expSum_last, eq_sub_iff_add_eq]
  unfold expSum allowedRows
  have h : univ.filter (fun a : Fin 3 => j.castSucc ≠ a.castSucc) = univ.erase j := by
    ext a
    simp [Fin.ext_iff, ne_comm]
  rw [h]
  exact sum_erase_add _ _ (mem_univ j)

private theorem columnDenominator_castSucc (w : Fin 3 → ℝ) (j : Fin 3) :
    columnDenominator w j.castSucc = 1 - w j := by
  fin_cases j <;> rfl

private theorem derivative_log_expSum (u : Fin 3 → ℝ) (j : Fin 3) (c : Fin 4)
    (w : Fin 3 → ℝ) (hw : ∀ i, w i = Real.exp (u i) / expSum (Fin.last 3) u) :
    HasDerivAt (fun t : ℝ => Real.log (expSum c (fun i => u i + if i = j then t else 0)))
      (allocation (weightEntries w) j c) 0 := by
  classical
  have hd (i : Fin 3) : HasDerivAt
      (fun t : ℝ => Real.exp (u i + if i = j then t else 0))
      (if i = j then Real.exp (u i) else 0) 0 := by
    by_cases hij : i = j
    · simpa [hij] using (((hasDerivAt_id (0 : ℝ)).const_add (u i)).exp)
    · simpa [hij] using (hasDerivAt_const (0 : ℝ) (Real.exp (u i)))
  have hz (i : Fin 3) : u i + (if i = j then (0 : ℝ) else 0) = u i := by simp
  have h := (HasDerivAt.fun_sum (u := allowedRows c) (fun i _ => hd i)).log
    (by simpa only [hz, expSum] using (expSum_pos c u).ne')
  simp only [hz, Finset.sum_ite_eq', mem_allowedRows] at h
  change HasDerivAt (fun t : ℝ =>
    Real.log (∑ i ∈ allowedRows c, Real.exp (u i + if i = j then t else 0))) _ 0
  have hden : expSum c u = columnDenominator w c * expSum (Fin.last 3) u := by
    refine Fin.lastCases ?_ (fun a => ?_) c
    · change _ = 1 * _
      rw [one_mul]
    · rw [expSum_castSucc]
      rw [columnDenominator_castSucc, hw, sub_mul, one_mul,
        div_mul_cancel₀ _ (expSum_pos _ _).ne']
  have heq : ((if c ≠ j.castSucc then Real.exp (u j) else 0) / expSum c u) =
      allocation (weightEntries w) j c := by
    by_cases hc : c = j.castSucc
    · simp [allocation, hc]
    · simp [allocation, weightEntries, hc, hw, hden, div_div, mul_comm]
  rw [← heq]
  exact h

/-- Every strictly admissible trace triple admits positive normalized direct
entropy weights. The row equations use the original labels. -/
theorem exists_direct_certificate (d : ℕ) (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (_hd : 0 < d) (hcap : ∑ j, (d - m j) ≤ d)
    (hpos : ∀ j, 0 < τ j) (hupper : ∀ j, τ j < (d : ℝ) - (d - m j : ℕ))
    (htotal : ∑ j, τ j = d) :
    ∃ w : Fin 3 → ℝ, (∀ j, 0 < w j) ∧ (∑ j, w j = 1) ∧
      ∀ j, weightMass (fun j => d - m j) (d - ∑ i, (d - m i)) w j = τ j := by
  let l (j : Fin 3) := d - m j
  let b := d - ∑ i, l i
  let G (c : Fin 4) (u : Fin 3 → ℝ) := Real.log (expSum c u)
  let F := priceObjective l b τ G
  have hcount : (b : ℝ) + ∑ j, (l j : ℝ) = d := by
    exact_mod_cast Nat.sub_add_cancel hcap
  obtain ⟨δ, hδ, hbound⟩ := price_coercivity l b d τ hcount htotal hpos hupper G le_log_expSum
  have hF : Continuous F := by
    have hG (c : Fin 4) : Continuous (G c) := by
      apply Continuous.log
      · exact continuous_finsetSum _ (fun j _ => Real.continuous_exp.comp (continuous_apply j))
      · exact fun u => (expSum_pos c u).ne'
    exact (continuous_finsetSum _ (fun c _ => continuous_const.mul (hG c))).sub
      (continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j)))
  have hshift (u : Fin 3 → ℝ) (a : ℝ) (c : Fin 4) :
      G c (fun j => u j + a) = G c u + a := by
    change Real.log (∑ j ∈ allowedRows c, Real.exp (u j + a)) = Real.log (expSum c u) + a
    simp only [Real.exp_add, ← Finset.sum_mul]
    change Real.log (expSum c u * Real.exp a) = _
    rw [Real.log_mul (expSum_pos c u).ne' (Real.exp_pos a).ne', Real.log_exp]
  obtain ⟨u, hu⟩ := exists_minimum_prices F hF
    (priceObjective_shift l b d τ hcount htotal G (fun c u a => hshift u a c)) hδ hbound
  let w (j : Fin 3) := Real.exp (u j) / expSum (Fin.last 3) u
  refine ⟨w, fun j => div_pos (Real.exp_pos _) (expSum_pos _ _), ?_, fun j => ?_⟩
  · change (∑ j, Real.exp (u j) / expSum (Fin.last 3) u) = 1
    rw [← Finset.sum_div, ← expSum_last, div_self (expSum_pos _ _).ne']
  · let line (t : ℝ) (i : Fin 3) := u i + if i = j then t else 0
    have hlin (i : Fin 3) : HasDerivAt (fun t => τ i * line t i)
        (if i = j then τ i else 0) 0 := by
      by_cases hij : i = j
      · simpa [line, hij] using (((hasDerivAt_id (0 : ℝ)).const_add (u i)).const_mul (τ i))
      · simpa [line, hij] using (hasDerivAt_const (0 : ℝ) (τ i * u i))
    have hD := (HasDerivAt.fun_sum (u := univ) (fun c _ =>
      (derivative_log_expSum u j c w (fun _ => rfl)).const_mul (multiplicity l b c : ℝ))).sub
        (HasDerivAt.fun_sum (u := univ) (fun i _ => hlin i))
    simp only [Finset.sum_ite_eq', mem_univ, ite_true] at hD
    have hMin : IsMinOn (fun t => F (line t)) Set.univ 0 := by
      intro t _
      have h0 : line 0 = u := by funext i; simp [line]
      change F (line 0) ≤ F (line t)
      rw [h0]
      exact hu (line t)
    have hzero := hMin.isLocalMin (by simp)
    exact sub_eq_zero.mp (hD.deriv.symm.trans hzero.deriv_eq_zero)

private theorem weightMass_relabel (e : Equiv.Perm (Fin 3)) (l : Fin 3 → ℕ) (b : ℕ)
    (w : Fin 3 → ℝ) (j : Fin 3) :
    weightMass (l ∘ e) b (w ∘ e) j = weightMass l b w (e j) := by
  have hlast (v : Fin 3 → ℝ) (i : Fin 3) :
      allocation (weightEntries v) i (Fin.last 3) = v i := by
    have h := (mem_allowedRows _ _).1 (last_mem_allowedRows i)
    change (if Fin.last 3 = i.castSucc then 0 else v i / 1) = v i
    rw [ite_eq_right h, div_one]
  have hmiss (v : Fin 3 → ℝ) (i k : Fin 3) :
      allocation (weightEntries v) i k.castSucc = if k = i then 0 else v i / (1 - v k) := by
    simp [allocation, weightEntries, columnDenominator_castSucc, Fin.ext_iff]
  unfold weightMass
  conv_lhs => rw [Fin.sum_univ_castSucc]
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [multiplicity_castSucc, multiplicity_last, hlast, hmiss, Function.comp_apply]
  congr 1
  simpa only [e.apply_eq_iff_eq] using Equiv.sum_comp e
    (fun k => (l k : ℝ) * (if k = e j then 0 else w (e j) / (1 - w k)))

private theorem feasible_relabel (e : Equiv.Perm (Fin 3)) (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (A : Fin 3 → Matrix n n ℂ) (hA : Feasible m τ A) :
    Feasible (m ∘ e) (τ ∘ e) (A ∘ e) :=
  ⟨fun j => hA.1 (e j), (Equiv.sum_comp e A).trans hA.2.1, fun j => hA.2.2.1 (e j),
    fun j => hA.2.2.2 (e j)⟩

private theorem spectralValues_relabel (e : Equiv.Perm (Fin 3)) (f : ℝ → ℝ)
    (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) :
    {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible (m ∘ e) (τ ∘ e) A,
      spectralSum f A hA.1 = v} =
    {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
      spectralSum f A hA.1 = v} := by
  ext v
  constructor <;> rintro ⟨A, hA, rfl⟩
  · have h := feasible_relabel e.symm _ _ A hA
    have h' : Feasible m τ (A ∘ e.symm) := by simpa [Function.comp_def] using h
    exact ⟨_, h', Equiv.sum_comp e.symm
      (fun j => ∑ i, f ((hA.1 j).isHermitian.eigenvalues i))⟩
  · refine ⟨_, feasible_relabel e m τ A hA, ?_⟩
    exact Equiv.sum_comp e (fun j => ∑ i, f ((hA.1 j).isHermitian.eigenvalues i))

/-- The direct entropy maximum for strictly admissible traces is attained by
the proportional allocation after sorting the weights and relabeling the rows. -/
theorem exists_isGreatest_direct (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (hd : 0 < Fintype.card n) (hcap : ∑ j, (Fintype.card n - m j) ≤ Fintype.card n)
    (hpos : ∀ j, 0 < τ j) (hupper : ∀ j, τ j < (Fintype.card n : ℝ) - (Fintype.card n - m j : ℕ))
    (htotal : ∑ j, τ j = Fintype.card n) :
    ∃ (e : Equiv.Perm (Fin 3)) (w : Fin 3 → ℝ), Antitone w ∧
      IsGreatest {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
        spectralSum Real.negMulLog A hA.1 = v}
        (allocationValue Real.negMulLog (fun j => Fintype.card n - m (e j))
          (Fintype.card n - ∑ j, (Fintype.card n - m j)) (weightEntries w)) := by
  let l (j : Fin 3) := Fintype.card n - m j
  obtain ⟨w, hw, hwt, hr⟩ :=
    exists_direct_certificate (Fintype.card n) m τ hd hcap hpos hupper htotal
  let e := Tuple.sort (fun j => -w j)
  have he : Antitone (w ∘ e) := fun _ _ hij =>
    neg_le_neg_iff.mp (Tuple.monotone_sort (fun j => -w j) hij)
  have hc : (∑ j, l (e j)) = ∑ j, l j := Equiv.sum_comp e l
  have hcap' : (∑ j, l (e j)) ≤ Fintype.card n := hc.trans_le hcap
  have hr' (j : Fin 3) : weightMass (l ∘ e)
      (Fintype.card n - ∑ i, l (e i)) (w ∘ e) j = τ (e j) := by
    rw [hc, weightMass_relabel]
    exact hr (e j)
  have hm := isGreatest_direct (n := n) (m ∘ e) (τ ∘ e) (w ∘ e) hcap'
    (fun j => hw (e j)) ((Equiv.sum_comp e w).trans hwt) he hr'
  change IsGreatest _ (allocationValue Real.negMulLog (l ∘ e)
    (Fintype.card n - ∑ j, l (e j)) (weightEntries (w ∘ e))) at hm
  rw [spectralValues_relabel, hc] at hm
  exact ⟨e, w ∘ e, he, hm⟩

private def pairWeight (w : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  ∑ i ∈ (univ : Finset (Fin 3)).erase j, w i

private theorem pairWeight_eq (w : Fin 3 → ℝ) (j : Fin 3) :
    pairWeight w j = (∑ i, w i) - w j :=
  eq_sub_iff_add_eq.2 (sum_erase_add _ _ (mem_univ j))

private theorem pairWeight_pos (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (j : Fin 3) :
    0 < pairWeight w j := by
  apply sum_pos (fun i _ => hw i)
  fin_cases j <;> decide

private def complementScales (w : Fin 3 → ℝ) (c : Fin 4) : ℝ :=
  Fin.lastCases
    (max (2 / ∑ i, w i) (univ.sup' univ_nonempty (fun i => (pairWeight w i)⁻¹)))
    (fun i => (pairWeight w i)⁻¹) c

private theorem complementScales_pos (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (c : Fin 4) :
    0 < complementScales w c := by
  refine Fin.lastCases ?_ (fun i => ?_) c
  · exact (div_pos two_pos (sum_pos (fun i _ => hw i) univ_nonempty)).trans_le (le_max_left _ _)
  · simpa only [complementScales, Fin.lastCases_castSucc] using inv_pos.mpr (pairWeight_pos w hw i)

private theorem clipped_pair {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    max 0 (1 - a * (a + b)⁻¹) + max 0 (1 - b * (a + b)⁻¹) = 1 := by
  have hab := add_pos ha hb
  have h (x : ℝ) (hx : x ≤ a + b) : 0 ≤ 1 - x * (a + b)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact sub_nonneg.mpr ((div_le_one hab).2 hx)
  rw [max_eq_right (h a (by linarith)), max_eq_right (h b (by linarith))]
  field_simp
  ring

private theorem clipped_triple {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hac : a ≤ c) (hbc : b ≤ c) :
    let k := max (2 / (a + b + c)) (a + b)⁻¹
    max 0 (1 - a * k) + max 0 (1 - b * k) + max 0 (1 - c * k) = 1 := by
  dsimp only
  have hab := add_pos ha hb
  have hsum := add_pos hab hc
  by_cases ht : c ≤ a + b
  · have hk : (a + b)⁻¹ ≤ 2 / (a + b + c) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hab hsum]
      linarith
    have h (x : ℝ) (hx : x ≤ c) : 0 ≤ 1 - x * (2 / (a + b + c)) := by
      rw [← mul_div_assoc]
      exact sub_nonneg.mpr ((div_le_one hsum).2 (by linarith))
    rw [max_eq_left hk, max_eq_right (h a hac), max_eq_right (h b hbc), max_eq_right (h c le_rfl)]
    field_simp
    ring
  · have ht' := le_of_not_ge ht
    have hk : 2 / (a + b + c) ≤ (a + b)⁻¹ := by
      rw [inv_eq_one_div, div_le_div_iff₀ hsum hab]
      linarith
    have h : 1 - c * (a + b)⁻¹ ≤ 0 := by
      rw [← div_eq_mul_inv]
      exact sub_nonpos.mpr ((one_le_div hab).2 ht')
    rw [max_eq_right hk, max_eq_left h, add_zero]
    exact clipped_pair ha hb

private theorem complement_columns (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) (c : Fin 4) :
    ∑ j, allocation (complementEntries w (complementScales w)) j c = 1 := by
  refine Fin.lastCases ?_ (fun i => ?_) c
  · let e := Tuple.sort w
    have he (j : Fin 3) : w (e j) ≤ w (e 2) :=
      Tuple.monotone_sort w (by omega : j ≤ 2)
    have he' (j : Fin 3) : w j ≤ w (e 2) := by simpa using he (e.symm j)
    have hsum : (∑ j, w j) = w (e 0) + w (e 1) + w (e 2) := by
      rw [← Equiv.sum_comp e w, Fin.sum_univ_three]
    have hpair :
        univ.sup' univ_nonempty (fun i => (pairWeight w i)⁻¹) = (pairWeight w (e 2))⁻¹ := by
      refine le_antisymm (sup'_le _ _ fun j _ => ?_)
        (le_sup' (fun i => (pairWeight w i)⁻¹) (mem_univ (e 2)))
      apply inv_anti₀ (pairWeight_pos w hw (e 2))
      rw [pairWeight_eq, pairWeight_eq]
      exact sub_le_sub_left (he' j) _
    have hpair' : pairWeight w (e 2) = w (e 0) + w (e 1) := by
      rw [pairWeight_eq, hsum]
      ring
    have hLast (j : Fin 3) : Fin.last 3 ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
    simp only [allocation, ite_eq_right (hLast _), complementEntries, complementScales,
      Fin.lastCases_last, hsum, hpair, hpair']
    rw [← Equiv.sum_comp e, Fin.sum_univ_three]
    exact clipped_triple (hw _) (hw _) (hw _) (he 0) (he 1)
  · have h0 : pairWeight w 0 = w 1 + w 2 := by
      unfold pairWeight
      rw [show (univ : Finset (Fin 3)).erase 0 = {1, 2} by decide]
      simp
    have h1 : pairWeight w 1 = w 0 + w 2 := by
      unfold pairWeight
      rw [show (univ : Finset (Fin 3)).erase 1 = {0, 2} by decide]
      simp
    have h2 : pairWeight w 2 = w 0 + w 1 := by
      unfold pairWeight
      rw [show (univ : Finset (Fin 3)).erase 2 = {0, 1} by decide]
      simp
    unfold allocation complementEntries
    simp only [complementScales, Fin.lastCases_castSucc]
    fin_cases i <;> simp [Fin.sum_univ_three, Fin.ext_iff, h0, h1, h2]
    · exact clipped_pair (hw 1) (hw 2)
    · exact clipped_pair (hw 0) (hw 2)
    · exact clipped_pair (hw 0) (hw 1)

private def complementWeights (u : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  Real.exp (-u j - 1)

private def complementPoint (u : Fin 3 → ℝ) (j : Fin 3) (c : Fin 4) : ℝ :=
  allocation (complementEntries (complementWeights u) (complementScales (complementWeights u))) j c

private theorem complementPoint_zero (u : Fin 3 → ℝ) (j : Fin 3) (c : Fin 4)
    (h : c = j.castSucc) : complementPoint u j c = 0 := by
  simp [complementPoint, allocation, h]

private theorem complementPoint_unit (u : Fin 3 → ℝ) (j : Fin 3) (c : Fin 4) :
    complementPoint u j c ∈ Set.Icc (0 : ℝ) 1 := by
  unfold complementPoint allocation
  split
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_max_left _ _, max_le zero_le_one (sub_le_self _
      (mul_pos (Real.exp_pos _) (complementScales_pos _ (fun _ => Real.exp_pos _) _)).le)⟩

private theorem continuous_complementPoint (j : Fin 3) (c : Fin 4) :
    Continuous fun u => complementPoint u j c := by
  have hw (i : Fin 3) : Continuous fun u => complementWeights u i :=
    Real.continuous_exp.comp ((continuous_apply i).neg.sub continuous_const)
  have hp (i : Fin 3) : Continuous fun u => (pairWeight (complementWeights u) i)⁻¹ :=
    (continuous_finsetSum _ fun j _ => hw j).inv₀
      (fun u => (pairWeight_pos _ (fun _ => Real.exp_pos _) i).ne')
  have hk (c : Fin 4) : Continuous fun u => complementScales (complementWeights u) c := by
    refine Fin.lastCases ?_ (fun i => ?_) c
    · exact (continuous_const.div (continuous_finsetSum _ fun j _ => hw j)
        (fun u => (sum_pos (fun i _ => Real.exp_pos (-u i - 1)) univ_nonempty).ne')).max
        (Continuous.finset_sup'_apply univ_nonempty fun i _ => hp i)
    · simpa only [complementScales, Fin.lastCases_castSucc] using hp i
  by_cases h : c = j.castSucc
  · simpa [complementPoint, allocation, h] using
      (continuous_const : Continuous fun _ : Fin 3 → ℝ => (0 : ℝ))
  · simp only [complementPoint, allocation, ite_eq_right h, complementEntries]
    exact continuous_const.max (continuous_const.sub ((hw j).mul (hk c)))

private def complementScore (u x : Fin 3 → ℝ) : ℝ :=
  ∑ j, (Real.negMulLog (1 - x j) + u j * x j)

private def complementPotential (c : Fin 4) (u : Fin 3 → ℝ) : ℝ :=
  complementScore u (fun j => complementPoint u j c)

private theorem complementPotential_ge_score (c : Fin 4) (u x : Fin 3 → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (hsum : ∑ j, x j = 1)
    (hzero : ∀ j, c = j.castSucc → x j = 0) :
    complementScore u x ≤ complementPotential c u := by
  let k := complementScales (complementWeights u) c
  let y (j : Fin 3) := complementPoint u j c
  have hs (j : Fin 3) :
      Real.negMulLog (1 - x j) + u j * x j ≤
        Real.negMulLog (1 - y j) + u j * y j + Real.log k * (x j - y j) := by
    by_cases h : c = j.castSucc
    · rw [hzero j h, show y j = 0 from complementPoint_zero u j c h]
      simp
    · have hk : 0 < k := complementScales_pos _ (fun _ => Real.exp_pos _) _
      have hlog : Real.log (complementWeights u j * k) + 1 = -u j + Real.log k := by
        unfold complementWeights
        rw [Real.log_mul (Real.exp_pos _).ne' hk.ne', Real.log_exp]
        ring
      have hsup := complement_support (mul_pos (Real.exp_pos (-u j - 1)) hk) (hx j)
      dsimp only at hsup
      change Real.negMulLog (1 - x j) ≤
        (Real.log (complementWeights u j * k) + 1) * x j +
          (Real.negMulLog (1 - max 0 (1 - complementWeights u j * k)) -
            (Real.log (complementWeights u j * k) + 1) *
              max 0 (1 - complementWeights u j * k)) at hsup
      have hy : y j = max 0 (1 - complementWeights u j * k) := by
        simp only [y, complementPoint, allocation, ite_eq_right h, complementEntries, k]
      rw [hlog, ← hy] at hsup
      linarith only [hsup]
  have hy : ∑ j, y j = 1 := complement_columns _ (fun _ => Real.exp_pos _) c
  have h := sum_le_sum (s := (univ : Finset (Fin 3))) (fun j _ => hs j)
  simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib, hsum, hy, sub_self, mul_zero,
    add_zero] at h
  simpa only [complementScore, complementPotential, sum_add_distrib, y] using h

private theorem le_complementPotential (c : Fin 4) (u : Fin 3 → ℝ) (j : Fin 3)
    (hj : j ∈ allowedRows c) : u j ≤ complementPotential c u := by
  let vertex (i : Fin 3) : ℝ := if i = j then 1 else 0
  have hv (i : Fin 3) : vertex i ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : i = j <;> simp [vertex, h]
  have hs : ∑ i, vertex i = 1 := by simp [vertex]
  have hz (i : Fin 3) (h : c = i.castSucc) : vertex i = 0 := by
    have hi : i ≠ j := fun hij => (mem_allowedRows _ _).1 hj (hij ▸ h)
    simp [vertex, hi]
  refine le_trans ?_ (complementPotential_ge_score c u vertex hv hs hz)
  have hvertex (i : Fin 3) : Real.negMulLog (1 - vertex i) + u i * vertex i =
      (if i = j then u i else 0) := by
    by_cases h : i = j <;> simp [vertex, h]
  simp [complementScore, hvertex]

private theorem complementScore_shift (u x : Fin 3 → ℝ) (a : ℝ) (hx : ∑ j, x j = 1) :
    complementScore (fun j => u j + a) x = complementScore u x + a := by
  unfold complementScore
  simp only [add_mul, ← add_assoc, sum_add_distrib, ← mul_sum, hx, mul_one]

private theorem complementPotential_shift (c : Fin 4) (u : Fin 3 → ℝ) (a : ℝ) :
    complementPotential c (fun j => u j + a) = complementPotential c u + a := by
  let v : Fin 3 → ℝ := fun j => u j + a
  have h (p : Fin 3 → ℝ) : ∑ j, complementPoint p j c = 1 :=
    complement_columns _ (fun _ => Real.exp_pos _) c
  have h₁ := complementPotential_ge_score c u (fun j => complementPoint v j c)
    (fun j => complementPoint_unit v j c) (h v) (fun j => complementPoint_zero v j c)
  have h₂ := complementPotential_ge_score c v (fun j => complementPoint u j c)
    (fun j => complementPoint_unit u j c) (h u) (fun j => complementPoint_zero u j c)
  refine le_antisymm ?_ ?_
  · change complementScore (fun j => u j + a) _ ≤ _
    rw [complementScore_shift _ _ _ (h v)]
    exact add_le_add h₁ le_rfl
  · change complementScore (fun j => u j + a) (fun j => complementPoint u j c) ≤ _ at h₂
    rw [complementScore_shift _ _ _ (h u)] at h₂
    exact h₂

open Filter Topology in
/-- Every strictly admissible trace triple admits a complementary entropy
certificate with the original row labels and positive row and column parameters. -/
theorem exists_complement_certificate (d : ℕ) (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (_hd : 0 < d) (hcap : ∑ j, (d - m j) ≤ d)
    (hpos : ∀ j, 0 < τ j) (hupper : ∀ j, τ j < (d : ℝ) - (d - m j : ℕ))
    (htotal : ∑ j, τ j = d) :
    ∃ (w : Fin 3 → ℝ) (k : Fin 4 → ℝ), (∀ j, 0 < w j) ∧ (∀ c, 0 < k c) ∧
      (∀ c, ∑ j, allocation (complementEntries w k) j c = 1) ∧
      ∀ j, (∑ c, (multiplicity (fun j => d - m j) (d - ∑ i, (d - m i)) c : ℝ) *
        allocation (complementEntries w k) j c) = τ j := by
  let l (j : Fin 3) := d - m j
  let b := d - ∑ i, l i
  let F := priceObjective l b τ complementPotential
  have hcount : (b : ℝ) + ∑ j, (l j : ℝ) = d := by
    exact_mod_cast Nat.sub_add_cancel hcap
  obtain ⟨δ, hδ, hbound⟩ := price_coercivity l b d τ hcount htotal hpos hupper _
    le_complementPotential
  have hG (c : Fin 4) : Continuous (complementPotential c) := by
    unfold complementPotential complementScore
    apply continuous_finsetSum
    intro j _
    apply Continuous.add
    · exact Real.continuous_negMulLog.comp
        (continuous_const.sub (continuous_complementPoint j c))
    · exact (continuous_apply j).mul (continuous_complementPoint j c)
  have hF : Continuous F :=
    (continuous_finsetSum _ (fun c _ => continuous_const.mul (hG c))).sub
      (continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j)))
  obtain ⟨u, hu⟩ := exists_minimum_prices F hF
    (priceObjective_shift l b d τ hcount htotal _ complementPotential_shift) hδ hbound
  refine ⟨complementWeights u, complementScales (complementWeights u), fun _ => Real.exp_pos _,
    complementScales_pos _ (fun _ => Real.exp_pos _),
    complement_columns _ (fun _ => Real.exp_pos _), fun j => ?_⟩
  let line (t : ℝ) (i : Fin 3) := u i + if i = j then t else 0
  let mass (p : Fin 3 → ℝ) : ℝ :=
    ∑ c, (multiplicity l b c : ℝ) * complementPoint p j c
  change mass u = τ j
  have hcompare (t : ℝ) (c : Fin 4) :
      complementPotential c (line t) ≤
        complementPotential c u + t * complementPoint (line t) j c := by
    let x (i : Fin 3) := complementPoint (line t) i c
    have h := complementPotential_ge_score c u x (fun i => complementPoint_unit _ i c)
      (complement_columns _ (fun _ => Real.exp_pos _) _) (fun i => complementPoint_zero _ i c)
    have hscore : complementScore (line t) x = complementScore u x + t * x j := by
      simp only [complementScore, line, add_mul, ← add_assoc, sum_add_distrib, ite_mul,
        zero_mul, sum_ite_eq', mem_univ, ite_true]
    exact hscore.trans_le (add_le_add h le_rfl)
  have hineq (t : ℝ) : 0 ≤ t * (mass (line t) - τ j) := by
    have h := sum_le_sum (s := (univ : Finset (Fin 4))) fun c _ =>
      mul_le_mul_of_nonneg_left (hcompare t c) (Nat.cast_nonneg (multiplicity l b c))
    simp only [mul_add, sum_add_distrib, mul_left_comm _ t, ← mul_sum] at h
    have hmin := hu (line t)
    have hτ : (∑ i, τ i * line t i) = (∑ i, τ i * u i) + τ j * t := by
      simp only [line, mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    unfold F priceObjective at hmin
    rw [hτ] at hmin
    change (∑ c, (multiplicity l b c : ℝ) * complementPotential c (line t)) ≤
      (∑ c, (multiplicity l b c : ℝ) * complementPotential c u) + t * mass (line t) at h
    linarith only [hmin, h]
  have hcts : Continuous (fun t => mass (line t)) := by
    have hline : Continuous line := continuous_pi fun i => by
      by_cases hi : i = j
      · simp only [line, hi, ite_true]
        exact continuous_const.add continuous_id
      · simpa [line, hi] using (continuous_const : Continuous fun _ : ℝ => u i)
    exact (continuous_finsetSum _ (fun c _ =>
      continuous_const.mul (continuous_complementPoint j c))).comp hline
  have h0 : line 0 = u := by funext i; simp [line]
  have hlim : Tendsto (fun t => mass (line t)) (𝓝 0) (𝓝 (mass u)) := by
    simpa only [h0] using hcts.continuousAt (x := (0 : ℝ)).tendsto
  refine le_antisymm ?_ ?_
  · apply le_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := Set.Iio 0)))
    filter_upwards [self_mem_nhdsWithin (s := Set.Iio (0 : ℝ))] with t ht
    have ht' : t < 0 := ht
    have h := hineq t
    by_contra! hn
    exact (mul_neg_of_neg_of_pos ht' (sub_pos.mpr hn)).not_ge h
  · apply ge_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with t ht
    have ht' : 0 < t := ht
    have h := hineq t
    by_contra! hn
    exact (mul_neg_of_pos_of_neg ht' (sub_neg.mpr hn)).not_ge h

#print axioms exists_complement_certificate

#print axioms exists_isGreatest_direct

#print axioms exists_direct_certificate

#print axioms isGreatest_direct
#print axioms isGreatest_complement
#print axioms isGreatest_three_four_four

end
end D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects

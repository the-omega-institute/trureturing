/- GID: D5/S3/Quantum/Measurement/Auric/UnequalBlockEffects
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/UnequalBlockEffects
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attained spectral entropy for three effects with unequal rank caps. -/

import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Proj
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Ordered supporting prices for three effects -/

namespace D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects

open Matrix Finset
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

private theorem proj_apply (S : Submodule ℂ H) (x : H) :
    toEuclideanLin (proj S) x = S.starProjection x := by
  change toEuclideanLin
      (LinearMap.toMatrix (PiLp.basisFun 2 ℂ n) (PiLp.basisFun 2 ℂ n)
        (S.subtypeL.comp S.orthogonalProjectionOnto)) x = _
  rw [show toEuclideanLin = toLpLin (2 : ENNReal) (2 : ENNReal) from rfl,
    toLpLin_eq_toLin, Matrix.toLin_toMatrix] <;> rfl

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
  simp only [map_sub, LinearMap.sub_apply, proj_apply]
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

private theorem trace_conj (U : Matrix.unitaryGroup n ℂ) (B : Matrix n n ℂ) :
    trace (Unitary.conjStarAlgAut ℂ _ U B) = trace B := by
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

private theorem overlap_trace {A : Matrix n n ℂ} (h : A.IsHermitian) (P : Matrix n n ℂ) :
    ∑ i, overlap h P i = (trace P).re := by
  rw [← trace_conj (star h.eigenvectorUnitary) P]
  simp [trace, Complex.re_sum, overlap]

private theorem overlap_mul_trace {A : Matrix n n ℂ} (h : A.IsHermitian) (P : Matrix n n ℂ) :
    ∑ i, h.eigenvalues i * overlap h P i = (trace (P * A)).re := by
  rw [← trace_conj (star h.eigenvectorUnitary) (P * A), map_mul,
    h.conjStarAlgAut_star_eigenvectorUnitary]
  simp [trace, mul_diagonal, Complex.mul_re, overlap, mul_comm]

private theorem overlap_proj_one {A : Matrix n n ℂ} (h : A.IsHermitian) (S : Submodule ℂ H)
    {i : n} (hi : h.eigenvectorBasis i ∈ S) : overlap h (proj S) i = 1 := by
  have hP : (proj S).mulVec (h.eigenvectorBasis i) = h.eigenvectorBasis i := by
    have h := congrArg WithLp.ofLp (proj_apply S (h.eigenvectorBasis i))
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

private theorem overlap_one {A : Matrix n n ℂ} (h : A.IsHermitian) (i : n) :
    overlap h 1 i = 1 := by simp [overlap]

private theorem overlap_unit_sum {A : Matrix n n ℂ} (h : A.IsHermitian)
    (L : Fin 4 → Matrix n n ℂ) (hL : ∑ c, L c = 1) (i : n) :
    ∑ c, overlap h (L c) i = 1 := by
  have he := congrArg (fun P => overlap h P i) hL
  simpa [overlap, map_sum, Matrix.sum_apply, Complex.re_sum] using he

private theorem effect_spectrum_unit {A : Fin 3 → Matrix n n ℂ}
    (hp : ∀ j, (A j).PosSemidef) (hs : ∑ j, A j = 1) (j : Fin 3) (i : n) :
    (hp j).isHermitian.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  have hle : A j ≤ 1 := by
    apply Matrix.le_iff.mpr
    rw [← hs, ← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_sub_cancel_right]
    exact Matrix.posSemidef_sum _ fun k _ => hp k
  exact ⟨(hp j).eigenvalues_nonneg i,
    (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff (hp j).isHermitian 1).mpr
      (by simpa using hle) i⟩

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
      calc
        _ = ∑ c, w j c i * f (e j i) := by rw [← sum_mul, hws, one_mul]
        _ ≤ _ := sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hsupport j c _ (effect_spectrum_unit hA.1 hA.2.1 j i))
            (hwp j c i)
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

private theorem diagonal_spectrum (f : ℝ → ℝ) (v : n → ℝ)
    (h : (diagonal fun i => (v i : ℂ)).IsHermitian) :
    (∑ i, f (h.eigenvalues i)) = ∑ i, f (v i) := by
  have hdiag : (diagonal (fun i => (v i : ℂ))).charpoly.roots =
      Finset.univ.val.map (fun i => (v i : ℂ)) := by
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have he := h.roots_charpoly_eq_eigenvalues
  rw [hdiag] at he
  simpa [Multiset.map_map, Function.comp_def] using
    (congrArg (fun t : Multiset ℂ => (t.map (f ∘ Complex.re)).sum) he).symm

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
  exact sum_congr rfl fun j _ => (diagonal_spectrum f (v j) _).trans (hv f j)

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

private theorem denom_missing (w : Fin 3 → ℝ) (j : Fin 3) :
    columnDenominator w j.castSucc = 1 - w j := by fin_cases j <;> rfl

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

#print axioms isGreatest_direct
#print axioms isGreatest_complement
#print axioms isGreatest_three_four_four

end
end D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects

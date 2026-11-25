/- GID: D5/S3/Quantum/Foundation/QutritSingletonIncidence
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/QutritSingletonIncidence
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: A shared original pure ray determines the homogeneous intersection of actual qutrits. -/

import D5.S3.Quantum.Foundation.QutritSchurPlane

/-! Singleton incidence for actual qutrits under original whole-pair-ball geometry.

The four-slot escape audit is tracked in issue #34179.
-/

noncomputable section
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace BigOperators

namespace D5.S3.Quantum.Foundation.QutritSingletonIncidence

open CircuitBalancedConfirmation WholePairBallConfirmation HitSectionGeneration SectionROGFrame

private abbrev Mat := HermitianMat (Fin 3) ℂ

private def P (i : Fin 3) : Mat := HermitianMat.diagonal ℂ (Pi.single i 1)

private theorem pivot_nonneg (i : Fin 3) : 0 ≤ P i := by
  rw [HermitianMat.zero_le_iff, P, HermitianMat.diagonal_mat, Matrix.posSemidef_diagonal_iff]
  intro j
  by_cases h : j = i <;> simp [h]

private theorem pivot_trace (i : Fin 3) : (P i).trace = 1 := by
  rw [HermitianMat.trace_eq_one_iff, P, HermitianMat.diagonal_mat, Matrix.trace_diagonal]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private theorem pivot_injective : Function.Injective P := by
  intro i j h
  by_contra hij
  have he := congrArg (fun X : Mat => X.mat i i) h
  change (P i).mat i i = (P j).mat i i at he
  rw [P, P, HermitianMat.diagonal_mat, HermitianMat.diagonal_mat] at he
  simp [Pi.single_apply, hij] at he

/-- A support-traceless three-by-three Hermitian matrix admits a singular
representative after addition of a real multiple of the zero-support pivot. -/
private theorem singular_representative (X : Mat) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (h : a * (X.mat 1 1).re + b * (X.mat 2 2).re = 0) :
    ∃ t : ℝ, (X + t • P 0).mat.det = 0 := by
  let x := (X.mat 1 1).re
  let y := (X.mat 2 2).re
  let z := X.mat 1 2
  let c := x * y - Complex.normSq z
  have hxy : a * x + b * y = 0 := h
  have h21 : X.mat 2 1 = star z := by
    exact (congrFun (congrFun X.H 2) 1).symm
  have hc : X.mat 1 1 * X.mat 2 2 - X.mat 1 2 * X.mat 2 1 = (c : ℂ) := by
    rw [h21, ← X.H.coe_re_apply_self 1, ← X.H.coe_re_apply_self 2]
    change (x : ℂ) * (y : ℂ) - z * star z = (c : ℂ)
    change (x : ℂ) * (y : ℂ) - z * (starRingEnd ℂ) z = (c : ℂ)
    rw [Complex.mul_conj]
    simp [c]
  have hdetReal : ((X.mat.det.re : ℝ) : ℂ) = X.mat.det := by
    rw [X.H.det_eq_prod_eigenvalues, Fin.prod_univ_three]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hshift (t : ℝ) : (X + t • P 0).mat.det = X.mat.det + (t : ℂ) * (c : ℂ) := by
    rw [← hc, Matrix.det_fin_three, Matrix.det_fin_three]
    simp only [HermitianMat.mat_add, HermitianMat.mat_smul, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, P, HermitianMat.diagonal_mat, Matrix.diagonal_apply]
    norm_num [Pi.single_apply]
    ring
  by_cases hz : c = 0
  · have hprod : x * y ≤ 0 := by
      by_cases hx : 0 ≤ x
      · have hy : y ≤ 0 := by
          by_contra! hpos
          have := mul_pos hb hpos
          have := mul_nonneg ha.le hx
          linarith
        exact mul_nonpos_of_nonneg_of_nonpos hx hy
      · have hx' : x ≤ 0 := le_of_not_ge hx
        have hy : 0 ≤ y := by
          by_contra! hneg
          have := mul_neg_of_pos_of_neg hb hneg
          have := mul_neg_of_pos_of_neg ha (lt_of_not_ge hx)
          linarith
        exact mul_nonpos_of_nonpos_of_nonneg hx' hy
    have hz' : Complex.normSq z = 0 := by
      dsimp [c] at hz
      have := Complex.normSq_nonneg z
      linarith
    have hxy' : x * y = 0 := by dsimp [c] at hz; linarith
    have hx : x = 0 := by
      rcases mul_eq_zero.mp hxy' with he | he
      · exact he
      · rw [he, mul_zero, add_zero] at hxy
        exact (mul_eq_zero.mp hxy).resolve_left ha.ne'
    have hy : y = 0 := by
      rw [hx, mul_zero, zero_add] at hxy
      exact (mul_eq_zero.mp hxy).resolve_left hb.ne'
    have h11 : X.mat 1 1 = 0 := by
      rw [← X.H.coe_re_apply_self 1]
      change (x : ℂ) = 0
      simp [hx]
    have h22 : X.mat 2 2 = 0 := by
      rw [← X.H.coe_re_apply_self 2]
      change (y : ℂ) = 0
      simp [hy]
    have h12 : X.mat 1 2 = 0 := Complex.normSq_eq_zero.mp hz'
    have h21' : X.mat 2 1 = 0 := by
      rw [h21]
      change star (X.mat 1 2) = 0
      rw [h12, star_zero]
    refine ⟨0, ?_⟩
    rw [zero_smul, add_zero, Matrix.det_fin_three, h11, h22, h12, h21']
    ring
  · refine ⟨-X.mat.det.re / c, ?_⟩
    rw [hshift, ← hdetReal]
    push_cast
    field_simp [show (c : ℂ) ≠ 0 by exact_mod_cast hz]
    simp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u g : V →ₗ[ℝ] ℝ}

private abbrev spanFace (F : C.Face) := Submodule.span ℝ (F : Set V)

omit [FiniteDimensional ℝ V] in
/-- Two pure atoms in the second qutrit cannot produce an additional vector
in the first span at zero exposing support. -/
private theorem two_atom_incidence
    (H J : C.Face) (p : pure C u)
    (hg : ∀ x ∈ C, 0 ≤ g x)
    (hg0 : ∀ x ∈ C, g x = 0 ↔ x ∈ H)
    (hmeet : ∀ x : V, x ∈ H ∧ x ∈ J ↔ ∃ a : ℝ, 0 ≤ a ∧ x = a • (p : V))
    (hS : spanFace H ≤ LinearMap.ker g)
    (hlu : Set.InjOn (spanFace H).mkQ
      {r : V | ∃ (q : pure C u) (a : ℝ), 0 < a ∧ r = a • (q : V) ∧ g r = 1})
    (q r : pure C u) (hq : (q : V) ∈ J) (hr : (r : V) ∈ J)
    (a b : ℝ) (h : a • (q : V) + b • (r : V) ∈ spanFace H) :
    a • (q : V) + b • (r : V) ∈ Submodule.span ℝ {(p : V)} := by
  let L := Submodule.span ℝ {(p : V)}
  have hpure (s : pure C u) (hs : (s : V) ∈ J) (hz : g s = 0) : (s : V) ∈ L := by
    obtain ⟨t, _, ht⟩ := (hmeet s).mp ⟨(hg0 s (pure_mem s).1).mp hz, hs⟩
    exact Submodule.mem_span_singleton.mpr ⟨t, ht.symm⟩
  have hbala : a * g q + b * g r = 0 := by
    have hz := LinearMap.mem_ker.mp (hS h)
    simpa only [map_add, map_smul, smul_eq_mul] using hz
  by_cases hqz : g q = 0
  · have hqL := hpure q hq hqz
    have hb' : b * g r = 0 := by simpa [hqz] using hbala
    have hrL : b • (r : V) ∈ L := by
      rcases mul_eq_zero.mp hb' with he | he
      · simp [he]
      · exact L.smul_mem b (hpure r hr he)
    exact L.add_mem (L.smul_mem a hqL) hrL
  by_cases hrz : g r = 0
  · have ha' : a * g q = 0 := by simpa [hrz] using hbala
    have ha0 := (mul_eq_zero.mp ha').resolve_right hqz
    simpa [ha0] using L.smul_mem b (hpure r hr hrz)
  by_cases ha : a = 0
  · have hb' : b * g r = 0 := by simpa [ha] using hbala
    have hb0 := (mul_eq_zero.mp hb').resolve_right hrz
    simp [ha, hb0]
  let t := a * g q
  let Q := (g q)⁻¹ • (q : V)
  let R := (g r)⁻¹ • (r : V)
  have ht : t ≠ 0 := mul_ne_zero ha hqz
  have htQ : t • Q = a • (q : V) := by
    dsimp [t, Q]
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hqz, mul_one]
  have htR : t • R = -b • (r : V) := by
    dsimp [R]
    rw [smul_smul]
    congr 1
    dsimp [t]
    rw [← div_eq_mul_inv]
    apply (div_eq_iff hrz).mpr
    linarith
  have hdiff : t • (Q - R) ∈ spanFace H := by
    rw [smul_sub, htQ, htR, neg_smul, sub_neg_eq_add]
    exact h
  have hdiff' : Q - R ∈ spanFace H := (spanFace H).smul_mem_iff ht |>.mp hdiff
  have hQ : g Q = 1 := by simp [Q, hqz]
  have hR : g R = 1 := by simp [R, hrz]
  have hEq : Q = R := hlu
    ⟨q, _, inv_pos.mpr (lt_of_le_of_ne (hg q (pure_mem q).1) (Ne.symm hqz)), rfl, hQ⟩
    ⟨r, _, inv_pos.mpr (lt_of_le_of_ne (hg r (pure_mem r).1) (Ne.symm hrz)), rfl, hR⟩
    (Submodule.Quotient.eq _ |>.mpr hdiff')
  have hzero : a • (q : V) + b • (r : V) = 0 := by
    have he := congrArg (fun v : V => t • v) hEq
    rw [htQ, htR, neg_smul] at he
    rw [he]
    abel
  rw [hzero]
  exact L.zero_mem


omit [FiniteDimensional ℝ V] in
/-- The exposing support on J has exactly one zero eigenvalue. Its
trace-one zero pivot is the shared original pure ray. -/
private theorem adapted_coordinates
    (H J : C.Face) (p : pure C u)
    (hg : ∀ x ∈ C, 0 ≤ g x)
    (hg0 : ∀ x ∈ C, g x = 0 ↔ x ∈ H)
    (hmeet : ∀ x : V, x ∈ H ∧ x ∈ J ↔ ∃ a : ℝ, 0 ≤ a ∧ x = a • (p : V))
    (e : spanFace J ≃ₗ[ℝ] Mat)
    (hcone : ∀ z : spanFace J, (z : V) ∈ J ↔ 0 ≤ e z)
    (htrace : ∀ z : spanFace J, (e z).trace = u z) :
    ∃ (I : Mat →ₗ[ℝ] V) (a b : ℝ),
      Function.Injective I ∧ LinearMap.range I = spanFace J ∧
      (∀ X, I X ∈ J ↔ 0 ≤ X) ∧ (∀ X, u (I X) = X.trace) ∧
      I (P 0) = (p : V) ∧ 0 < a ∧ 0 < b ∧
      (∀ X, g (I X) = a * (X.mat 1 1).re + b * (X.mat 2 2).re) := by
  classical
  let I₀ : Mat →ₗ[ℝ] V := (spanFace J).subtype.comp e.symm.toLinearMap
  have hI₀ (X) : I₀ X ∈ J ↔ 0 ≤ X := by simpa [I₀] using hcone (e.symm X)
  obtain ⟨G, hG, hrep⟩ := HermitianExclusionKernel.positive_representative (g.comp I₀)
    (fun X hX => hg _ (J.isFaceOf.le ((hI₀ X).mpr hX)))
  let U := G.H.eigenvectorUnitary
  let E := QutritSchurPlane.unitaryEquiv U
  let I₁ := I₀.comp E.toLinearMap
  let d := G.H.eigenvalues
  have hd (i) : 0 ≤ d i :=
    (G.H.posSemidef_iff_eigenvalues_nonneg.mp (HermitianMat.zero_le_iff.mp hG)) i
  have hI : Function.Injective I₁ :=
    Subtype.val_injective.comp (e.symm.injective.comp E.injective)
  have hR : LinearMap.range I₁ = spanFace J := by
    ext x
    constructor
    · rintro ⟨X, rfl⟩
      exact (e.symm (E X)).property
    · intro hx
      exact ⟨E.symm (e ⟨x, hx⟩), by simp [I₁, I₀]⟩
  have hEc (X : Mat) : E X = X.conj U.val := rfl
  have hIC (X) : I₁ X ∈ J ↔ 0 ≤ X := by
    change I₀ (E X) ∈ J ↔ 0 ≤ X
    rw [hI₀, hEc, ← (HermitianMat.conj U.val).map_zero, HermitianMat.le_conj_unitary]
    simp only [map_zero]
  have hIT (X) : u (I₁ X) = X.trace := by
    change u (e.symm (E X) : spanFace J) = X.trace
    rw [← htrace, e.apply_symm_apply, hEc, HermitianMat.trace_conj_unitary]
  have hread (X : Mat) : g (I₁ X) = ∑ i, d i * (X.mat i i).re := by
    change (g.comp I₀) (E X) = _
    rw [hrep, hEc, G.eq_conj_diagonal, HermitianMat.inner_conj_unitary,
      QutritSchurPlane.diagonal_read]
  have hpJ : (p : V) ∈ H ∧ (p : V) ∈ J :=
    (hmeet p).mpr ⟨1, by norm_num, by simp⟩
  have hpg := (hg0 p (pure_mem p).1).mpr hpJ.1
  have hpR : (p : V) ∈ LinearMap.range I₁ := by
    rw [hR]
    exact Submodule.subset_span hpJ.2
  obtain ⟨X, hX⟩ := hpR
  have hXpsd := HermitianMat.zero_le_iff.mp ((hIC X).mp (hX.symm ▸ hpJ.2))
  have hXdiag (i) : 0 ≤ (X.mat i i).re :=
    (Complex.nonneg_iff.mp (hXpsd.diag_nonneg (i := i))).1
  have hsum : ∑ i, d i * (X.mat i i).re = 0 := by rw [← hread, hX, hpg]
  obtain ⟨i, hi⟩ : ∃ i, d i = 0 := by
    by_contra! hn
    have hz (j) : (X.mat j j).re = 0 := by
      have hl : d j * (X.mat j j).re ≤ ∑ i, d i * (X.mat i i).re :=
        Finset.single_le_sum (fun i _ => mul_nonneg (hd i) (hXdiag i)) (Finset.mem_univ j)
      rw [hsum] at hl
      exact (mul_eq_zero.mp (le_antisymm hl (mul_nonneg (hd j) (hXdiag j)))).resolve_left (hn j)
    have ht : X.trace = 0 := by
      rw [HermitianMat.trace_eq_re_trace]
      change (∑ j, X.mat j j).re = 0
      rw [Complex.re_sum]
      exact Finset.sum_eq_zero (fun j _ => hz j)
    have hpunit := hIT X
    rw [hX, (pure_mem p).2, ht] at hpunit
    norm_num at hpunit
  have hP (j) (hj : d j = 0) : I₁ (P j) = (p : V) := by
    have hPJ : I₁ (P j) ∈ J := (hIC _).mpr (pivot_nonneg j)
    have hpzero : g (I₁ (P j)) = 0 := by
      rw [hread]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k = j
      · subst k
        simp [hj]
      · rw [P, HermitianMat.diagonal_mat]
        simp [Pi.single_apply, hk]
    obtain ⟨t, _, ht⟩ := (hmeet _).mp ⟨(hg0 _ (J.isFaceOf.le hPJ)).mp hpzero, hPJ⟩
    have hunit := hIT (P j)
    rw [ht, map_smul, (pure_mem p).2, smul_eq_mul, mul_one, pivot_trace] at hunit
    simpa [hunit] using ht
  have huniq (j) (hj : d j = 0) : j = i :=
    pivot_injective (hI ((hP j hj).trans (hP i hi).symm))
  let σ : Fin 3 ≃ Fin 3 := Equiv.swap i 0
  have hσ : σ i = 0 := by simp [σ]
  let R := QutritSchurPlane.reindexEquiv σ.symm
  let I := I₁.comp R.toLinearMap
  have hRc (Y : Mat) : R Y = Y.reindex σ.symm := rfl
  have hRrange : LinearMap.range I = spanFace J := by
    rw [← hR]
    ext x
    constructor
    · rintro ⟨Y, rfl⟩
      exact ⟨R Y, rfl⟩
    · rintro ⟨Y, rfl⟩
      exact ⟨R.symm Y, by simp [I]⟩
  have hRcone (Y) : I Y ∈ J ↔ 0 ≤ Y := by
    change I₁ (R Y) ∈ J ↔ 0 ≤ Y
    rw [hIC, hRc, HermitianMat.zero_le_iff, HermitianMat.zero_le_iff, HermitianMat.mat_reindex]
    exact Matrix.posSemidef_submatrix_equiv σ
  have hRtrace (Y) : u (I Y) = Y.trace := by
    change u (I₁ (R Y)) = Y.trace
    rw [hIT, hRc, HermitianMat.trace_reindex]
  have hP0 : R (P 0) = P i := by
    apply HermitianMat.ext
    rw [hRc, HermitianMat.mat_reindex, P, HermitianMat.diagonal_mat, P, HermitianMat.diagonal_mat]
    apply Matrix.ext
    intro j k
    by_cases hjk : j = k
    · subst k
      have he : σ j = 0 ↔ j = i := by rw [← hσ]; exact σ.injective.eq_iff
      simp [Matrix.submatrix, Pi.single_apply, he]
    · have hne : σ j ≠ σ k := fun hh => hjk (σ.injective hh)
      simp [Matrix.submatrix, hjk, hne]
  have hread' (Y : Mat) : g (I Y) = ∑ j, d (σ.symm j) * (Y.mat j j).re := by
    change g (I₁ (R Y)) = _
    rw [hread, hRc, HermitianMat.mat_reindex]
    apply Fintype.sum_equiv σ
    intro j
    simp [Matrix.submatrix]
  have hd0 : d (σ.symm 0) = 0 := by rw [← hσ, σ.symm_apply_apply]; exact hi
  have hdpos (j : Fin 3) (hj : j ≠ 0) : 0 < d (σ.symm j) := by
    refine lt_of_le_of_ne (hd _) ?_
    intro hzero
    apply hj
    rw [← σ.apply_symm_apply j, huniq _ hzero.symm, hσ]
  refine ⟨I, d (σ.symm 1), d (σ.symm 2), hI.comp R.injective, hRrange,
    hRcone, hRtrace, ?_, hdpos 1 (by decide), hdpos 2 (by decide), ?_⟩
  · change I₁ (R (P 0)) = _
    rw [hP0, hP i hi]
  · intro Y
    rw [hread', Fin.sum_univ_three, hd0]
    ring

/-- Under original whole-pair-ball geometry, two actual qutrits sharing a
single original pure ray have precisely its real line as their homogeneous
intersection. The first qutrit has a nonnegative exposing support. -/
theorem original_qutrit_singleton_incidence
    (H J : C.Face) (p : pure C u)
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : ∀ x ∈ C, 0 ≤ g x)
    (hg0 : ∀ x ∈ C, g x = 0 ↔ x ∈ H)
    (hballs : wholePairBalls C u)
    (hmeet : ∀ x : V, x ∈ H ∧ x ∈ J ↔ ∃ a : ℝ, 0 ≤ a ∧ x = a • (p : V))
    (eH : Submodule.span ℝ (H : Set V) ≃ₗ[ℝ] HermitianMat (Fin 3) ℂ)
    (hconeH : ∀ z : Submodule.span ℝ (H : Set V), (z : V) ∈ H ↔ 0 ≤ eH z)
    (htraceH : ∀ z : Submodule.span ℝ (H : Set V), (eH z).trace = u z)
    (eJ : Submodule.span ℝ (J : Set V) ≃ₗ[ℝ] HermitianMat (Fin 3) ℂ)
    (hconeJ : ∀ z : Submodule.span ℝ (J : Set V), (z : V) ∈ J ↔ 0 ≤ eJ z)
    (htraceJ : ∀ z : Submodule.span ℝ (J : Set V), (eJ z).trace = u z) :
    Submodule.span ℝ (H : Set V) ⊓ Submodule.span ℝ (J : Set V) =
      Submodule.span ℝ {(p : V)} := by
  classical
  let S := spanFace H
  let T := spanFace J
  let L := Submodule.span ℝ {(p : V)}
  have hgH (x) (hx : x ∈ H) : g x = 0 := (hg0 x (H.isFaceOf.le hx)).mpr hx
  have hS : S ≤ LinearMap.ker g := Submodule.span_le.mpr hgH
  have hp : (p : V) ∈ H ∧ (p : V) ∈ J :=
    (hmeet p).mpr ⟨1, by norm_num, by simp⟩
  have hLS : L ≤ S := (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span hp.1)
  have hLT : L ≤ T := (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span hp.2)
  have hpS : (p : V) ∈ S := Submodule.subset_span hp.1
  have hpL : (p : V) ∈ L := Submodule.mem_span_singleton_self _
  have hlu := QutritPureLift.unique_original_pure_lift H hu hg hgH hballs eH hconeH htraceH
  obtain ⟨I, a, b, hI, hR, hIC, hIT, hP, ha, hb, hread⟩ :=
    adapted_coordinates H J p hg hg0 hmeet eJ hconeJ htraceJ
  have hsingular (Y : Mat) (hY : I Y ∈ S) (hdet : Y.mat.det = 0) : I Y ∈ L := by
    have hprod : ∏ i, (Y.H.eigenvalues i : ℂ) = 0 := Y.H.det_eq_prod_eigenvalues.symm.trans hdet
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
    have hi' : Y.H.eigenvalues i = 0 := by exact_mod_cast hi
    let v (j : Fin 3) : EuclideanSpace ℂ (Fin 3) := Y.H.eigenvectorBasis j
    let w (j : Fin 3) : pure C u := ⟨I (rankOne (v j)),
      QutritSchurPlane.unit_rankOne_original J I hI
        (fun x hx => by rw [hR]; exact Submodule.subset_span hx)
        hIC hIT (v j) (Y.H.eigenvectorBasis.orthonormal.norm_eq_one j)⟩
    have hw (j : Fin 3) : (w j : V) ∈ J := (hIC _).mpr (rankOne_nonneg _)
    have hs : I Y = ∑ j, Y.H.eigenvalues j • (w j : V) := by
      have hYsum : Y = ∑ j, Y.H.eigenvalues j • rankOne (v j) := by
        apply HermitianMat.ext
        change Y.mat = (∑ j, Y.H.eigenvalues j • rankOne (v j)).mat
        rw [HermitianMat.mat_finset_sum]
        simp only [HermitianMat.mat_smul]
        exact D5.S3.Quantum.Matrix.CartesianVariance.hermitian_spectral_sum Y.mat Y.H
      simpa [w, map_sum, map_smul] using congrArg I hYsum
    rw [Fin.sum_univ_three] at hs
    fin_cases i
    · change Y.H.eigenvalues 0 = 0 at hi'
      simp only [hi', zero_smul, zero_add] at hs
      rw [hs] at hY ⊢
      exact two_atom_incidence H J p hg hg0 hmeet hS hlu (w 1) (w 2) (hw 1) (hw 2) _ _ hY
    · change Y.H.eigenvalues 1 = 0 at hi'
      simp only [hi', zero_smul, add_zero] at hs
      rw [hs] at hY ⊢
      exact two_atom_incidence H J p hg hg0 hmeet hS hlu (w 0) (w 2) (hw 0) (hw 2) _ _ hY
    · change Y.H.eigenvalues 2 = 0 at hi'
      simp only [hi', zero_smul, add_zero] at hs
      rw [hs] at hY ⊢
      exact two_atom_incidence H J p hg hg0 hmeet hS hlu (w 0) (w 1) (hw 0) (hw 1) _ _ hY
  refine le_antisymm ?_ (le_inf hLS hLT)
  rintro x ⟨hxS, hxT⟩
  have hxR : x ∈ LinearMap.range I := by rw [hR]; exact hxT
  obtain ⟨X, rfl⟩ := hxR
  have hz : a * (X.mat 1 1).re + b * (X.mat 2 2).re = 0 := by
    rw [← hread]
    exact hS hxS
  obtain ⟨t, ht⟩ := singular_representative X a b ha hb hz
  have hY : I (X + t • P 0) ∈ S := by
    rw [map_add, map_smul, hP]
    exact S.add_mem hxS (S.smul_mem t hpS)
  have hYL := hsingular _ hY ht
  rw [map_add, map_smul, hP] at hYL
  have he : I X = (I X + t • (p : V)) - t • (p : V) := by abel
  rw [he]
  exact L.sub_mem hYL (L.smul_mem t hpL)

end D5.S3.Quantum.Foundation.QutritSingletonIncidence

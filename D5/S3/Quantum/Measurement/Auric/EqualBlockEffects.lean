/- GID: D5/S3/Quantum/Measurement/Auric/EqualBlockEffects
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/EqualBlockEffects
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp attained spectral entropy bounds for three equally capped effects. -/

import D5.S3.Quantum.PureState.PhaseRecordSpectralMemory
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Proj
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Order.Interval.Finset.Fin

/-! # Sharp spectral entropy for three effects with equal rank caps -/

namespace D5.S3.Quantum.Measurement.Auric.EqualBlockEffects

open Matrix Finset
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open PhaseRecordSpectralMemory

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

private def spectralOrder : Fin (Fintype.card n) ≃ n :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

private def band (p q : ℕ) (hq : q ≤ Fintype.card n) : Finset n :=
  ((Finset.Ico p q).attachFin fun _ hi => (Finset.mem_Ico.mp hi).2.trans_le hq).map
    (spectralOrder (n := n)).toEmbedding

omit [DecidableEq n] in
private theorem mem_band {p q : ℕ} {hq : q ≤ Fintype.card n} {i : n} :
    i ∈ band p q hq ↔ p ≤ (spectralOrder.symm i).val ∧ (spectralOrder.symm i).val < q := by
  rw [band, Finset.mem_map_equiv]
  simp [Finset.mem_Ico]

omit [DecidableEq n] in
private theorem card_band (p q : ℕ) (hq : q ≤ Fintype.card n) :
    (band (n := n) p q hq).card = q - p := by
  simp [band, Nat.card_Ico]

theorem eigenvalues_mem_unit {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (hA1 : A ≤ 1) (i : n) : hA.isHermitian.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨hA.eigenvalues_nonneg i,
    (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hA.isHermitian 1).mpr
      (by simpa using hA1) i⟩

private theorem eigenvalues_zero_off {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {m : ℕ} (hm : m ≤ Fintype.card n) (hr : A.rank ≤ m)
    {i : n} (hi : i ∉ band 0 m hm) : hA.isHermitian.eigenvalues i = 0 := by
  classical
  let e := hA.isHermitian.eigenvalues
  have hi' : m ≤ (spectralOrder.symm i).val := by
    simpa [mem_band, not_lt] using hi
  by_contra hn
  have hpos : 0 < e i := lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hn)
  let emb : Fin (m + 1) ↪ n :=
    (Fin.castLEEmb (by omega)).trans (spectralOrder (n := n)).toEmbedding
  let f (j : Fin (m + 1)) : {k // e k ≠ 0} :=
    ⟨emb j, ne_of_gt (hpos.trans_le (hA.isHermitian.eigenvalues₀_antitone (by
      change (spectralOrder.symm (emb j)).val ≤ (spectralOrder.symm i).val
      simpa [emb] using (show j.val ≤ (spectralOrder.symm i).val by omega))))⟩
  have h := Fintype.card_le_of_injective f (fun j k h => emb.injective (congrArg Subtype.val h))
  rw [Fintype.card_fin, ← hA.isHermitian.rank_eq_card_non_zero_eigs] at h
  omega

omit [Fintype n] in
theorem effect_le_one (A : Fin 3 → Matrix n n ℂ)
    (hp : ∀ j, (A j).PosSemidef) (hs : ∑ j, A j = 1) (j : Fin 3) : A j ≤ 1 := by
  apply Matrix.le_iff.mpr
  rw [← hs, ← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_sub_cancel_right]
  exact Matrix.posSemidef_sum _ fun k _ => hp k

private theorem sum_eigenvalues_re_trace {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∑ i, hA.eigenvalues i = (trace A).re := by
  rw [hA.trace_eq_sum_eigenvalues, Complex.re_sum]
  rfl

private theorem trace_conjugate (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    trace (Unitary.conjStarAlgAut ℂ _ U A) = trace A := by
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

theorem projector_apply (S : Submodule ℂ (EuclideanSpace ℂ n))
    (x : EuclideanSpace ℂ n) :
    toEuclideanLin (HermitianMat.projector S).mat x = S.starProjection x := by
  change toEuclideanLin
      (LinearMap.toMatrix (PiLp.basisFun 2 ℂ n) (PiLp.basisFun 2 ℂ n)
        (S.subtypeL.comp S.orthogonalProjectionOnto)) x = _
  rw [show toEuclideanLin = toLpLin (2 : ENNReal) (2 : ENNReal) from rfl,
    toLpLin_eq_toLin, Matrix.toLin_toMatrix] <;> rfl

private theorem tail_mass_le (A : Fin 3 → Matrix n n ℂ)
    (hp : ∀ j, (A j).PosSemidef) (hs : ∑ j, A j = 1)
    {m b : ℕ} (hm : m ≤ Fintype.card n) (hb : b ≤ m)
    (hd : b + 3 * (Fintype.card n - m) ≤ Fintype.card n) :
    (∑ j, ∑ i ∈ band (m - b) m hm, (hp j).isHermitian.eigenvalues i) ≤ b := by
  classical
  let J := band (n := n) 0 m hm
  let K := band (n := n) (m - b) m hm
  let U (j : Fin 3) : Matrix.unitaryGroup n ℂ := (hp j).isHermitian.eigenvectorUnitary
  let T (j : Fin 3) := Unitary.conjStarAlgAut ℂ _ (star (U j))
  let e (j : Fin 3) := (hp j).isHermitian.eigenvalues
  let F : EuclideanSpace ℂ n →ₗ[ℂ] (Fin 3 × {i : n // i ∉ J} → ℂ) :=
    LinearMap.pi fun ji => (LinearMap.proj ji.2.val).comp
      ((WithLp.linearEquiv 2 ℂ (n → ℂ)).toLinearMap.comp
        (toEuclideanLin (star (U ji.1 : Matrix n n ℂ))))
  have hcodomain : Module.finrank ℂ (Fin 3 × {i : n // i ∉ J} → ℂ) =
      3 * (Fintype.card n - m) := by
    rw [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin]
    congr 1
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    simp [J, card_band]
  have hdim : b ≤ Module.finrank ℂ F.ker := by
    have hr := F.finrank_range_add_finrank_ker
    have hle := Submodule.finrank_le F.range
    rw [hcodomain] at hle
    rw [finrank_euclideanSpace] at hr
    omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hdim
  let v' : Fin b → EuclideanSpace ℂ n := fun i => (v i).val
  have hv' : LinearIndependent ℂ v' := hv.map' F.ker.subtype (by simp)
  let S := Submodule.span ℂ (Set.range v')
  have hSF : S ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (v i).prop
  have hSb : Module.finrank ℂ S = b := by
    simpa [S] using (finrank_span_eq_card hv')
  let P := (HermitianMat.projector S).mat
  have hP0 : 0 ≤ P := HermitianMat.mat_nonneg (HermitianMat.projector_nonneg S)
  have hP1 : P ≤ 1 := by
    apply Matrix.le_iff.mpr
    have h := congrArg HermitianMat.mat (HermitianMat.projector_add_orthogonal S)
    simp only [HermitianMat.mat_add, HermitianMat.mat_one] at h
    rw [← h, add_sub_cancel_left]
    exact (HermitianMat.mat_nonneg (HermitianMat.projector_nonneg Sᗮ)).posSemidef
  have hPtr : (trace P).re = b := by
    change RCLike.re (HermitianMat.projector S).mat.trace = _
    rw [← HermitianMat.trace_eq_re_trace, HermitianMat.trace_projector, hSb]
  have hKcard : K.card = b := by simp [K, card_band, Nat.sub_sub_self hb]
  have tail (j : Fin 3) : (∑ i ∈ K, e j i) ≤ (trace (P * A j)).re := by
    let G := T j P
    let w (i : n) := (G i i).re
    have hG0 : 0 ≤ G := map_nonneg (T j) hP0
    have hG1 : G ≤ 1 := by simpa [G] using (OrderHomClass.mono (T j) hP1)
    have hw0 (i : n) : 0 ≤ w i :=
      (Complex.nonneg_iff.mp (hG0.posSemidef.diag_nonneg (i := i))).1
    have hw1 (i : n) : w i ≤ 1 := by
      have h := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hG1).diag_nonneg (i := i))).1
      simpa [w, Matrix.sub_apply, sub_nonneg] using h
    have hw (i : n) (hi : i ∉ J) : w i = 0 := by
      have row (x : EuclideanSpace ℂ n) :
          (toEuclideanLin (star (U j : Matrix n n ℂ))
            (toEuclideanLin P x)).ofLp i = 0 := by
        have hx := hSF (show toEuclideanLin P x ∈ S by
          rw [projector_apply]
          exact S.starProjection_apply_mem x)
        exact congrFun (LinearMap.mem_ker.mp hx) (j, ⟨i, hi⟩)
      have hrow (k : n) : (star (U j : Matrix n n ℂ) * P) i k = 0 := by
        have hm := congrArg
          (fun L : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n =>
            (L (EuclideanSpace.single k 1)).ofLp i)
          (toLpLin_mul_same (2 : ENNReal) (star (U j : Matrix n n ℂ)) P)
        have hr := hm.trans (row (EuclideanSpace.single k 1))
        simpa only [toLpLin_apply, WithLp.ofLp_toLp, PiLp.ofLp_single,
          mulVec_single_one, col_apply] using hr
      have hz : G i i = 0 := by
        change (Unitary.conjStarAlgAut ℂ _ (star (U j)) P) i i = 0
        rw [Unitary.conjStarAlgAut_star_apply, Matrix.mul_apply]
        simp [hrow]
      simp [w, hz]
    have hwt : ∑ i, w i = b := by
      change (∑ i, (G i i).re) = _
      rw [← Complex.re_sum, ← show trace G = ∑ i, G i i from rfl,
        show trace G = trace P from trace_conjugate (star (U j)) P, hPtr]
    have htr : (trace (P * A j)).re = ∑ i, e j i * w i := by
      have hD := (hp j).isHermitian.conjStarAlgAut_star_eigenvectorUnitary
      change T j (A j) = _ at hD
      rw [← trace_conjugate (star (U j)) (P * A j)]
      change (trace (T j (P * A j))).re = _
      rw [map_mul, hD]
      simp [G, w, e, trace, mul_diagonal, Complex.mul_re, mul_comm]
    let a (i : n) : ℝ := if i ∈ J then 1 - e j i else 0
    have ha (i : n) : 0 ≤ a i := by
      by_cases hi : i ∈ J
      · simpa [a, hi, sub_nonneg, e] using
          (eigenvalues_mem_unit (hp j) (effect_le_one A hp hs j) i).2
      · simp [a, hi]
    have htop (i : n) (hi : i ∈ K) (k : n) (hk : k ∉ K) : a k ≤ a i := by
      have hi' := mem_band.mp hi
      have hiJ : i ∈ J := mem_band.mpr ⟨Nat.zero_le _, hi'.2⟩
      by_cases hkJ : k ∈ J
      · have hk' := (mem_band.mp hkJ).2
        have hord : (spectralOrder.symm k).val ≤ (spectralOrder.symm i).val := by
          by_contra! h
          exact hk (mem_band.mpr ⟨hi'.1.trans h.le, hk'⟩)
        simp only [a, ite_eq_left hiJ, ite_eq_left hkJ]
        exact sub_le_sub_left ((hp j).isHermitian.eigenvalues₀_antitone hord) 1
      · simpa [a, hkJ] using ha i
    have hbound := weighted_sum_le_top a w b K
      (by rw [hKcard, min_eq_left (hb.trans hm)]) htop ha hw0 hw1 hwt.le
    have hwform : ∑ i, a i * w i = (b : ℝ) - ∑ i, e j i * w i := by
      rw [← hwt, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ J
      · simp [a, hi, sub_mul]
      · simp [hw i hi]
    have haform : ∑ i ∈ K, a i = (b : ℝ) - ∑ i ∈ K, e j i := by
      have hconst : (∑ _ ∈ K, (1 : ℝ)) = b := by simp [hKcard]
      rw [← hconst, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i hi => by
        have hiJ : i ∈ J := mem_band.mpr ⟨Nat.zero_le _, (mem_band.mp hi).2⟩
        simp [a, hiJ]
    rw [hwform, haform, ← htr] at hbound
    linarith
  calc
    _ ≤ ∑ j, (trace (P * A j)).re := Finset.sum_le_sum fun j _ => tail j
    _ = b := by rw [← Complex.re_sum, ← trace_sum, ← Matrix.mul_sum, hs, mul_one, hPtr]

/-- The eigenvalue objective for the input projection or its complement. -/
def entropyIntegrand (complement : Bool) (x : ℝ) : ℝ :=
  if complement then Real.negMulLog (1 - x) else Real.negMulLog x

/-- Total unnormalized spectral entropy for three effects. -/
def effectEntropy (complement : Bool) (A : Fin 3 → Matrix n n ℂ)
    (hp : ∀ j, (A j).PosSemidef) : ℝ :=
  ∑ j, ∑ i, entropyIntegrand complement ((hp j).isHermitian.eigenvalues i)

/-- Positive effects of equal trace, with a common upper bound on rank. -/
def Feasible (m : ℕ) (A : Fin 3 → Matrix n n ℂ) : Prop :=
  (∀ j, (A j).PosSemidef) ∧ (∑ j, A j = 1) ∧
    (∀ j, (trace (A j)).re = (Fintype.card n : ℝ) / 3) ∧ (∀ j, (A j).rank ≤ m)

/-- Unnormalized optimum, with zero excess rank in the Jensen range. -/
def entropyBound (complement : Bool) (m d : ℕ) : ℝ :=
  let ell := d - m
  let b := d - 3 * ell
  3 * ((2 * ell : ℕ) : ℝ) * entropyIntegrand complement (1 / 2) +
    3 * (b : ℝ) * entropyIntegrand complement (1 / 3)

private theorem integrand_zero (c : Bool) : entropyIntegrand c 0 = 0 := by
  cases c <;> simp [entropyIntegrand]

private theorem integrand_concave (c : Bool) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (entropyIntegrand c) := by
  cases c
  · exact Real.concaveOn_negMulLog.subset (fun _ hx => hx.1) (convex_Icc _ _)
  · refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := Real.concaveOn_negMulLog.2 (show 1 - x ∈ Set.Ici (0 : ℝ) from sub_nonneg.mpr hx.2)
      (show 1 - y ∈ Set.Ici (0 : ℝ) from sub_nonneg.mpr hy.2) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    simpa [entropyIntegrand, show a * (1 - x) + b * (1 - y) = 1 - (a * x + b * y) by
      nlinarith only [hab]] using h

private theorem integrand_differentiable (c : Bool) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (entropyIntegrand c) x := by
  cases c
  · exact Real.differentiableAt_negMulLog (ne_of_gt hx.1)
  · change DifferentiableAt ℝ (fun y => Real.negMulLog (1 - y)) x
    exact (Real.differentiableAt_negMulLog (ne_of_gt (sub_pos.mpr hx.2))).comp x
      (differentiableAt_const _ |>.sub differentiableAt_id)

private theorem integrand_support (c : Bool) {t x : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    entropyIntegrand c x ≤ entropyIntegrand c t + deriv (entropyIntegrand c) t * (x - t) := by
  have hfc := integrand_concave c
  have hd := integrand_differentiable c ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  rcases lt_trichotomy x t with h | rfl | h
  · have hs := hfc.deriv_le_slope hx ht' h hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs
    linarith
  · simp
  · have hs := hfc.slope_le_deriv ht' hx h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
    linarith

private theorem effect_entropy_le (c : Bool) {m : ℕ} (A : Fin 3 → Matrix n n ℂ)
    (hA : Feasible m A) (hd : 3 * (Fintype.card n - m) ≤ Fintype.card n) :
    effectEntropy c A hA.1 ≤ entropyBound c m (Fintype.card n) := by
  classical
  let d := Fintype.card n
  let ell := d - m
  let b := d - 3 * ell
  let k := min m d
  have hdk : k ≤ d := min_le_right _ _
  have hkb : b ≤ k := by dsimp [b, k, ell]; omega
  have hd' : b + 3 * (d - k) = d := by dsimp [b, k, ell]; omega
  have hk : k - b = 2 * ell := by dsimp [k, b, ell]; omega
  have hdb : d = 3 * ell + b := by dsimp [ell, b]; omega
  let J := band (n := n) 0 k hdk
  let K := band (n := n) (k - b) k hdk
  let e (j : Fin 3) := (hA.1 j).isHermitian.eigenvalues
  let f := entropyIntegrand c
  let u : ℝ := 1 / 2
  let v : ℝ := 1 / 3
  let p := deriv f u
  let q := deriv f v
  have hv : v ∈ Set.Ioo (0 : ℝ) 1 := by norm_num [v]
  have hu : u ∈ Set.Ioo (0 : ℝ) 1 := by norm_num [u]
  have hvu : v < u := by norm_num [v, u]
  have hq : p ≤ q := by
    have hv' : v ∈ Set.Icc (0 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    exact ((integrand_concave c).deriv_le_slope hv' hu' hvu
      (integrand_differentiable c hu)).trans
      ((integrand_concave c).slope_le_deriv hv' hu' hvu (integrand_differentiable c hv))
  have hKJ : K ⊆ J := fun _ hi => mem_band.mpr ⟨Nat.zero_le _, (mem_band.mp hi).2⟩
  have hJ : J.card = k := by simp [J, card_band]
  have hK : K.card = b := by simp [K, card_band, Nat.sub_sub_self hkb]
  have hH : (J \ K).card = 2 * ell := by rw [Finset.card_sdiff_of_subset hKJ, hJ, hK, hk]
  have hrank (j : Fin 3) : (A j).rank ≤ k :=
    le_min (hA.2.2.2 j) (Matrix.rank_le_card_width _)
  have he0 (j : Fin 3) (i : n) (hi : i ∉ J) : e j i = 0 :=
    eigenvalues_zero_off (hA.1 j) hdk (hrank j) hi
  have htail : (∑ j, ∑ i ∈ K, e j i) ≤ b :=
    tail_mass_le A hA.1 hA.2.1 hdk hkb hd'.le
  have hs (j : Fin 3) : (∑ i ∈ J, e j i) = (d : ℝ) / 3 := by
    rw [Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => he0 j i hi),
      sum_eigenvalues_re_trace, hA.2.2.1]
  have hsplit (g : n → ℝ) :
      (∑ i ∈ J \ K, g i) + (∑ i ∈ K, g i) = ∑ i ∈ J, g i :=
    Finset.sum_sdiff hKJ
  have hreal : (d : ℝ) = 3 * (ell : ℝ) + b := by exact_mod_cast hdb
  have hlocal (j : Fin 3) :
      (∑ i, f (e j i)) ≤ ((2 * ell : ℕ) : ℝ) * f u + (b : ℝ) * f v +
        (q - p) * ((∑ i ∈ K, e j i) - (b : ℝ) / 3) := by
    have hzero (i : n) (_ : i ∈ (Finset.univ : Finset n)) (hi : i ∉ J) :
        f (e j i) = 0 := by
      rw [he0 j i hi]
      exact integrand_zero c
    rw [← Finset.sum_subset (Finset.subset_univ J) hzero, ← hsplit (fun i => f (e j i))]
    have hm (i : n) := eigenvalues_mem_unit (hA.1 j) (effect_le_one A hA.1 hA.2.1 j) i
    have hhead := Finset.sum_le_sum (s := J \ K) fun i _ => integrand_support c hu (hm i)
    have hlast := Finset.sum_le_sum (s := K) fun i _ => integrand_support c hv (hm i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, hH, hK, Nat.cast_mul, Nat.cast_ofNat] at hhead hlast
    have hmass : (∑ i ∈ J \ K, e j i) =
        (d : ℝ) / 3 - ∑ i ∈ K, e j i := by
      linarith only [(hsplit (e j)).trans (hs j)]
    rw [hmass] at hhead
    have hscaled := congrArg (fun z : ℝ => p * z) hreal
    dsimp only [p, q, u, v, f] at hhead hlast hscaled ⊢
    push_cast
    nlinarith only [hhead, hlast, hscaled]
  let δ (j : Fin 3) := (∑ i ∈ K, e j i) - (b : ℝ) / 3
  have hδ : ∑ j, δ j ≤ 0 := by
    dsimp [δ]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]
    linarith only [htail]
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hlocal j)
  change (∑ j, ∑ i, f (e j i)) ≤
    3 * ((2 * ell : ℕ) : ℝ) * f u + 3 * (b : ℝ) * f v
  apply h.trans
  change (∑ j, (((2 * ell : ℕ) : ℝ) * f u + (b : ℝ) * f v + (q - p) * δ j)) ≤ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
  nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq) hδ]

private def diagonalWitness {ell b : ℕ} (x : (Fin 3 × Fin ell) ⊕ Fin b)
    (j : Fin 3) : ℝ :=
  match x with
  | .inl y => if y.1 = j then 0 else 1 / 2
  | .inr _ => 1 / 3

private theorem sum_witness {ell b : ℕ} (x : (Fin 3 × Fin ell) ⊕ Fin b) :
    ∑ j, diagonalWitness x j = 1 := by
  cases x with
  | inl y =>
    obtain ⟨a, z⟩ := y
    fin_cases a <;> norm_num [Fin.sum_univ_three, diagonalWitness]
  | inr y => norm_num [Fin.sum_univ_three, diagonalWitness]

private theorem sum_witness_function {ell b : ℕ} (f : ℝ → ℝ) (hf : f 0 = 0) (j : Fin 3) :
    (∑ x : (Fin 3 × Fin ell) ⊕ Fin b, f (diagonalWitness x j)) =
      ((2 * ell : ℕ) : ℝ) * f (1 / 2) + (b : ℝ) * f (1 / 3) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  fin_cases j <;>
    simp [Fin.sum_univ_three, diagonalWitness, hf, nsmul_eq_mul, Nat.cast_mul] <;> ring

theorem diagonal_entropy (f : ℝ → ℝ) (v : n → ℝ)
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

private theorem effect_entropy_attains (c : Bool) {m : ℕ}
    (hd : 3 * (Fintype.card n - m) ≤ Fintype.card n) :
    ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m A,
      effectEntropy c A hA.1 = entropyBound c m (Fintype.card n) := by
  classical
  let d := Fintype.card n
  let ell := d - m
  let b := d - 3 * ell
  have hdb : d = 3 * ell + b := by dsimp [ell, b]; omega
  let E : n ≃ (Fin 3 × Fin ell) ⊕ Fin b := Fintype.equivOfCardEq (by simpa using hdb)
  let v (j : Fin 3) (i : n) := diagonalWitness (E i) j
  let A (j : Fin 3) : Matrix n n ℂ := diagonal fun i => (v j i : ℂ)
  have hp (j : Fin 3) : (A j).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (v j i : ℂ)
    rw [Complex.nonneg_iff]
    refine ⟨?_, by simp⟩
    change 0 ≤ diagonalWitness (E i) j
    cases E i with
    | inl y =>
      simp only [diagonalWitness]
      split <;> norm_num
    | inr y => norm_num [diagonalWitness]
  have hs : ∑ j, A j = 1 := by
    ext i k
    by_cases hik : i = k
    · subst k
      simp only [Matrix.sum_apply, A, diagonal_apply_eq, one_apply_eq, ← Complex.ofReal_sum, v]
      rw [sum_witness, Complex.ofReal_one]
    · simp [A, hik, Matrix.sum_apply]
  have hv (f : ℝ → ℝ) (hf : f 0 = 0) (j : Fin 3) :
      (∑ i, f (v j i)) = ((2 * ell : ℕ) : ℝ) * f (1 / 2) + (b : ℝ) * f (1 / 3) :=
    (Fintype.sum_equiv E _ _ fun _ => rfl).trans (sum_witness_function f hf j)
  have ht (j : Fin 3) : (trace (A j)).re = (d : ℝ) / 3 := by
    have hv' := hv (fun x => x) rfl j
    change (∑ i, v j i) = _ at hv'
    rw [show (trace (A j)).re = ∑ i, v j i by simp [A, trace_diagonal, Complex.re_sum],
      hv']
    have hreal : (d : ℝ) = 3 * (ell : ℝ) + b := by exact_mod_cast hdb
    push_cast
    linarith
  have hr (j : Fin 3) : (A j).rank ≤ m := by
    let count (x : ℝ) : ℝ := if x = 0 then 0 else 1
    have hh := hv count (by simp [count]) j
    have hcard : ((A j).rank : ℝ) = ∑ i, count (v j i) := by
      change ((diagonal fun i => (v j i : ℂ)).rank : ℝ) = _
      rw [Matrix.rank_diagonal, Fintype.card_subtype, Finset.natCast_card_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : v j i = 0 <;> simp [count, hi]
    rw [← hcard] at hh
    norm_num [count] at hh
    have hr' : (A j).rank = 2 * ell + b := by
      exact_mod_cast hh
    rw [hr']
    dsimp [ell, b] at *
    omega
  refine ⟨A, ⟨hp, hs, ht, hr⟩, ?_⟩
  unfold effectEntropy
  simp only [A, diagonal_entropy, hv _ (integrand_zero c), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  change _ = 3 * ((2 * ell : ℕ) : ℝ) * entropyIntegrand c (1 / 2) +
    3 * (b : ℝ) * entropyIntegrand c (1 / 3)
  ring

/-- For three positive effects adding to identity, of trace one third of the
ambient dimension and rank at most `m`, the spectral entropy reaches its sharp
value whenever `3 * (d - m) ≤ d`. Both entropy objectives share the same diagonal
construction. The formula includes zero dimension and zero common support. -/
theorem isGreatest_effectEntropy (c : Bool) (m : ℕ)
    (hd : 3 * (Fintype.card n - m) ≤ Fintype.card n) :
    IsGreatest {s : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m A,
      effectEntropy c A hA.1 = s} (entropyBound c m (Fintype.card n)) := by
  refine ⟨effect_entropy_attains c hd, ?_⟩
  rintro s ⟨A, hA, rfl⟩
  exact effect_entropy_le c A hA hd

#print axioms isGreatest_effectEntropy

end
end D5.S3.Quantum.Measurement.Auric.EqualBlockEffects

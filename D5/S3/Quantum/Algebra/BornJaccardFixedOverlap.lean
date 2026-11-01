/- GID: D5/S3/Quantum/Algebra/BornJaccardFixedOverlap
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/BornJaccardFixedOverlap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual compression and simultaneous fixed-overlap interval attainment. -/

import D5.S3.Quantum.Algebra.BornJaccardTracialClassification
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.FinCases

noncomputable section
open scoped InnerProductSpace ComplexOrder
open LinearMap
namespace D5.S3.Quantum.Algebra.BornJaccardFixedOverlap
open BornJaccardTracialClassification

variable {n : ℕ}

/-- Compression onto the actual subspace; no invariance is required. -/
def compression (rho : Module.End ℂ (H n)) (T : Submodule ℂ (H n)) :
    Module.End ℂ T :=
  T.orthogonalProjectionOnto.toLinearMap ∘ₗ rho ∘ₗ T.subtype

private theorem compression_inner (rho : Module.End ℂ (H n))
    (T : Submodule ℂ (H n)) (x y : T) :
    inner ℂ x (compression rho T y) = inner ℂ (x : H n) (rho y) := by
  exact T.inner_orthogonalProjectionOnto_eq_of_mem_left x (rho y)

private theorem compression_symmetric (rho : Module.End ℂ (H n))
    (hs : rho.IsSymmetric) (T : Submodule ℂ (H n)) :
    (compression rho T).IsSymmetric := by
  intro x y
  rw [← inner_conj_symm, compression_inner, ← hs, inner_conj_symm,
    compression_inner]

/-- The two eigenvalues of the actual density compression, in decreasing order. -/
def intervalEigenvalues (rho : Matrix (Fin n) (Fin n) ℂ) (hp : rho.PosDef)
    (T : Submodule ℂ (H n)) (hT : Module.finrank ℂ T = 2) : Fin 2 → ℝ :=
  (compression_symmetric rho.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hp.isHermitian) T).eigenvalues hT

private theorem compression_trace (rho : Module.End ℂ (H n))
    (T : Submodule ℂ (H n)) :
    (LinearMap.trace ℂ T (compression rho T)).re = weight rho T := by
  unfold weight compression projection
  change (LinearMap.trace ℂ T
    (T.orthogonalProjectionOnto.toLinearMap ∘ₗ (rho ∘ₗ T.subtype))).re =
    (LinearMap.trace ℂ (H n)
      ((rho ∘ₗ T.subtype) ∘ₗ T.orthogonalProjectionOnto.toLinearMap)).re
  rw [LinearMap.trace_comp_comm']

private theorem projection_orthogonal_sup (R U : Submodule ℂ (H n))
    (hU : U ≤ R.orthogonal) :
    projection (R ⊔ U) = projection R + projection U := by
  ext x
  change (R ⊔ U).starProjection x = R.starProjection x + U.starProjection x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.add_mem_sup (R.starProjection_apply_mem x)
      (U.starProjection_apply_mem x)
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have hUR : inner ℂ (U.starProjection x) a = 0 :=
      R.inner_left_of_mem_orthogonal ha (hU (U.starProjection_apply_mem x))
    have hRU : inner ℂ (R.starProjection x) b = 0 :=
      R.inner_right_of_mem_orthogonal (R.starProjection_apply_mem x) (hU hb)
    have hR := R.starProjection_inner_eq_zero x a ha
    have hV := U.starProjection_inner_eq_zero x b hb
    simp only [inner_sub_left, inner_add_left] at hR hV
    simp only [inner_sub_left, inner_add_left, inner_add_right]
    rw [hUR, hRU]
    linear_combination hR + hV

private theorem weight_orthogonal_sup (rho : Module.End ℂ (H n))
    (R U : Submodule ℂ (H n)) (hU : U ≤ R.orthogonal) :
    weight rho (R ⊔ U) = weight rho R + weight rho U := by
  simp only [weight, projection_orthogonal_sup R U hU, mul_add, map_add, Complex.add_re]

private theorem interval_inf (R T L N : Submodule ℂ (H n))
    (hT : T ≤ R.orthogonal) (hL : L ≤ T) (hN : N ≤ T) (hLN : L ⊓ N = ⊥) :
    (R ⊔ L) ⊓ (R ⊔ N) = R := by
  apply le_antisymm _ (le_inf le_sup_left le_sup_left)
  intro x hx
  obtain ⟨a, ha, u, hu, hxu⟩ := Submodule.mem_sup.mp hx.1
  obtain ⟨b, hb, v, hv, hxv⟩ := Submodule.mem_sup.mp hx.2
  have huv : u - v ∈ R := by
    have heq : u - v = b - a := by
      calc
        u - v = (a + u) - (a + v) := by module
        _ = (b + v) - (a + v) := by rw [hxu, hxv]
        _ = b - a := by module
    rw [heq]
    exact R.sub_mem hb ha
  have huvT : u - v ∈ R.orthogonal := hT (T.sub_mem (hL hu) (hN hv))
  have huv0 : u - v = 0 := by
    have h := (show u - v ∈ R ⊓ R.orthogonal from ⟨huv, huvT⟩)
    simpa only [R.inf_orthogonal_eq_bot, Submodule.mem_bot] using h
  have huv' : u = v := sub_eq_zero.mp huv0
  have hu0 : u = 0 := by
    have h : u ∈ L ⊓ N := ⟨hu, huv'.symm ▸ hv⟩
    simpa only [hLN, Submodule.mem_bot] using h
  simpa [← hxu, hu0] using ha

private theorem weight_unit_line (rho : Module.End ℂ (H n)) (w : H n)
    (hw : inner ℂ w w = 1) : weight rho (ℂ ∙ w) = (inner ℂ w (rho w)).re := by
  have hn : ‖w‖ ^ 2 = (1 : ℝ) := by
    have h := congrArg Complex.re hw
    simpa only [inner_self_eq_norm_sq_to_K, Complex.ofReal_re, Complex.one_re] using h
  have hP : projection (ℂ ∙ w) = (InnerProductSpace.rankOne ℂ w w).toLinearMap := by
    ext v
    simp [projection, Submodule.starProjection_singleton, hn,
      InnerProductSpace.rankOne_apply]
  rw [weight, hP, trace_mul_rank]

private theorem interval_defect (rho : Module.End ℂ (H n))
    (c : ℝ) (R T L N : Submodule ℂ (H n))
    (hT : T ≤ R.orthogonal) (hL : L ≤ T) (hN : N ≤ T)
    (hLN : L ⊓ N = ⊥) (hjoin : L ⊔ N = T)
    (hden : 0 < c + weight rho R + weight rho T) :
    distance rho c (R ⊔ L) (R ⊔ N) -
        distance rho c (R ⊔ L) (R ⊔ T) -
        distance rho c (R ⊔ T) (R ⊔ N) =
      (weight rho L + weight rho N - weight rho T) /
        (c + weight rho R + weight rho T) := by
  have hLT : R ⊔ L ≤ R ⊔ T := sup_le_sup_left hL R
  have hNT : R ⊔ N ≤ R ⊔ T := sup_le_sup_left hN R
  have hj : (R ⊔ L) ⊔ (R ⊔ N) = R ⊔ T := by
    rw [← hjoin]
    ac_rfl
  have hi := interval_inf R T L N hT hL hN hLN
  have hwt := weight_orthogonal_sup rho R T hT
  have hwl := weight_orthogonal_sup rho R L (hL.trans hT)
  have hwn := weight_orthogonal_sup rho R N (hN.trans hT)
  have hd : c + weight rho (R ⊔ T) ≠ 0 := by rw [hwt]; linarith
  simp only [distance, hj, hi, sup_eq_right.mpr hLT, inf_eq_left.mpr hLT,
    sup_eq_left.mpr hNT, inf_eq_right.mpr hNT, if_neg hd, hwt, hwl, hwn]
  field_simp
  <;> ring

private theorem pair_construction (rho : Module.End ℂ (H n)) (e f : H n)
    (hee : inner ℂ e e = 1) (hff : inner ℂ f f = 1)
    (hef : inner ℂ e f = 0) (M m r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hqee : inner ℂ e (rho e) = (M : ℂ))
    (hqff : inner ℂ f (rho f) = (m : ℂ))
    (hqef : inner ℂ e (rho f) = 0) (hqfe : inner ℂ f (rho e) = 0) :
    ∃ u v : H n,
      u ∈ (ℂ ∙ e) ⊔ (ℂ ∙ f) ∧ v ∈ (ℂ ∙ e) ⊔ (ℂ ∙ f) ∧
      inner ℂ u u = 1 ∧ inner ℂ v v = 1 ∧ inner ℂ u v = (r : ℂ) ∧
      (ℂ ∙ u) ⊓ (ℂ ∙ v) = ⊥ ∧
      (ℂ ∙ u) ⊔ (ℂ ∙ v) = (ℂ ∙ e) ⊔ (ℂ ∙ f) ∧
      weight rho (ℂ ∙ u) = (M + m + r * (M - m)) / 2 ∧
      weight rho (ℂ ∙ v) = (M + m + r * (M - m)) / 2 := by
  let a : ℝ := Real.sqrt ((1 + r) / 2)
  let b : ℝ := Real.sqrt ((1 - r) / 2)
  have ha : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb : 0 < b := Real.sqrt_pos.2 (by linarith)
  have haa : a ^ 2 = (1 + r) / 2 := Real.sq_sqrt (by linarith)
  have hbb : b ^ 2 = (1 - r) / 2 := Real.sq_sqrt (by linarith)
  have hab : a ^ 2 + b ^ 2 = 1 := by linarith
  have hab' : a ^ 2 - b ^ 2 = r := by linarith
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  have hfe : inner ℂ f e = 0 := by rw [← inner_conj_symm, hef, map_zero]
  let u : H n := (a : ℂ) • e + (b : ℂ) • f
  let v : H n := (a : ℂ) • e - (b : ℂ) • f
  let E : Submodule ℂ (H n) := (ℂ ∙ e) ⊔ (ℂ ∙ f)
  have huE : u ∈ E := E.add_mem
    (Submodule.mem_sup_left ((ℂ ∙ e).smul_mem _ (Submodule.mem_span_singleton_self e)))
    (Submodule.mem_sup_right ((ℂ ∙ f).smul_mem _ (Submodule.mem_span_singleton_self f)))
  have hvE : v ∈ E := E.sub_mem
    (Submodule.mem_sup_left ((ℂ ∙ e).smul_mem _ (Submodule.mem_span_singleton_self e)))
    (Submodule.mem_sup_right ((ℂ ∙ f).smul_mem _ (Submodule.mem_span_singleton_self f)))
  have huu : inner ℂ u u = 1 := by
    simp only [u, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, hee, hff, hef, hfe, mul_one, mul_zero, add_zero, zero_add]
    exact_mod_cast (show a * a + b * b = 1 by nlinarith [hab])
  have hvv : inner ℂ v v = 1 := by
    simp only [v, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, hee, hff, hef, hfe, mul_one, mul_zero, sub_zero, zero_sub]
    exact_mod_cast (show a * a - -(b * b) = 1 by nlinarith [hab])
  have huv : inner ℂ u v = (r : ℂ) := by
    simp only [u, v, inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, hee, hff, hef, hfe, mul_one, mul_zero, sub_zero, zero_sub]
    exact_mod_cast (show a * a + -(b * b) = r by nlinarith [hab'])
  have hjoin : (ℂ ∙ u) ⊔ (ℂ ∙ v) = E := by
    apply le_antisymm
      (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 huE)
        ((Submodule.span_singleton_le_iff_mem _ _).2 hvE))
    apply sup_le
    · apply (Submodule.span_singleton_le_iff_mem _ _).2
      have hh := ((ℂ ∙ u) ⊔ (ℂ ∙ v)).smul_mem ((2 * (a : ℂ))⁻¹)
        (Submodule.add_mem_sup (Submodule.mem_span_singleton_self u)
          (Submodule.mem_span_singleton_self v))
      have heq : (2 * (a : ℂ))⁻¹ • (u + v) = e := by
        calc
          _ = ((2 * (a : ℂ))⁻¹ * (2 * (a : ℂ))) • e := by dsimp [u, v]; module
          _ = e := by rw [inv_mul_cancel₀ (mul_ne_zero (by norm_num) hac), one_smul]
      rwa [heq] at hh
    · apply (Submodule.span_singleton_le_iff_mem _ _).2
      have hh := ((ℂ ∙ u) ⊔ (ℂ ∙ v)).smul_mem ((2 * (b : ℂ))⁻¹)
        (((ℂ ∙ u) ⊔ (ℂ ∙ v)).sub_mem
          (Submodule.mem_sup_left (Submodule.mem_span_singleton_self u))
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
      have heq : (2 * (b : ℂ))⁻¹ • (u - v) = f := by
        calc
          _ = ((2 * (b : ℂ))⁻¹ * (2 * (b : ℂ))) • f := by dsimp [u, v]; module
          _ = f := by rw [inv_mul_cancel₀ (mul_ne_zero (by norm_num) hbc), one_smul]
      rwa [heq] at hh
  have hinf : (ℂ ∙ u) ⊓ (ℂ ∙ v) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp hx.1
    obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp hx.2
    have heq := hα.trans hβ.symm
    have h₁ := congrArg (fun w => inner ℂ e w) heq
    have h₂ := congrArg (fun w => inner ℂ f w) heq
    simp only [u, v, inner_add_right, inner_sub_right, inner_smul_right,
      hee, hff, hef, hfe, mul_one, mul_zero, add_zero, zero_add, sub_zero,
      zero_sub, mul_neg] at h₁ h₂
    have hαβ : α = β := (mul_right_cancel₀ hac) h₁
    have hα0 : α = 0 := by
      have hh : α * (2 * (b : ℂ)) = 0 := by rw [← hαβ] at h₂; linear_combination h₂
      exact (mul_eq_zero.mp hh).resolve_right (mul_ne_zero (by norm_num) hbc)
    simpa only [Submodule.mem_bot, ← hα, hα0, zero_smul]
  have hwu : weight rho (ℂ ∙ u) = (M + m + r * (M - m)) / 2 := by
    rw [weight_unit_line rho u huu]
    have hq : inner ℂ u (rho u) = ((a ^ 2 * M + b ^ 2 * m : ℝ) : ℂ) := by
      simp only [u, map_add, map_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, Complex.conj_ofReal,
        hqee, hqff, hqef, hqfe, mul_zero, add_zero, zero_add]
      push_cast
      ring
    rw [hq, Complex.ofReal_re, haa, hbb]
    ring
  have hwv : weight rho (ℂ ∙ v) = (M + m + r * (M - m)) / 2 := by
    rw [weight_unit_line rho v hvv]
    have hq : inner ℂ v (rho v) = ((a ^ 2 * M + b ^ 2 * m : ℝ) : ℂ) := by
      simp only [v, map_sub, map_smul, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, Complex.conj_ofReal,
        hqee, hqff, hqef, hqfe, mul_zero, sub_zero, zero_sub, mul_neg]
      push_cast
      ring
    rw [hq, Complex.ofReal_re, haa, hbb]
    ring
  exact ⟨u, v, huE, hvE, huu, hvv, huv, hinf, hjoin, hwu, hwv⟩

/-- For every allowed overlap, actual lines attain the proposed sharp value in
the original interval distance. The universal upper bound is a separate assertion. -/
theorem fixed_overlap_attainment (hn : 2 ≤ n)
    (rho : Matrix (Fin n) (Fin n) ℂ) (hp : rho.PosDef) (ht : Matrix.trace rho = 1)
    (c : ℝ) (hc : 0 ≤ c) (R T : Submodule ℂ (H n))
    (hTR : T ≤ R.orthogonal) (hT : Module.finrank ℂ T = 2)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    let lam := intervalEigenvalues rho hp T hT
    0 < lam 1 ∧ lam 1 ≤ lam 0 ∧
      weight rho.toEuclideanLin T = lam 0 + lam 1 ∧
      0 < c + weight rho.toEuclideanLin R + (lam 0 + lam 1) ∧
      ∃ u v : T, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ‖inner ℂ u v‖ = r ∧
        let L := (ℂ ∙ u).map T.subtype
        let N := (ℂ ∙ v).map T.subtype
        Module.finrank ℂ L = 1 ∧ Module.finrank ℂ N = 1 ∧
        L ⊓ N = ⊥ ∧ L ⊔ N = T ∧
        distance rho.toEuclideanLin c (R ⊔ L) (R ⊔ N) -
            distance rho.toEuclideanLin c (R ⊔ L) (R ⊔ T) -
            distance rho.toEuclideanLin c (R ⊔ T) (R ⊔ N) =
          r * (lam 0 - lam 1) /
            (c + weight rho.toEuclideanLin R + (lam 0 + lam 1)) := by
  let A := rho.toEuclideanLin
  let K := compression A T
  let hs : K.IsSymmetric := compression_symmetric A
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hp.isHermitian) T
  let lam := hs.eigenvalues hT
  let B := hs.eigenvectorBasis hT
  let e : H n := B 0
  let f : H n := B 1
  have hee : inner ℂ e e = 1 := B.inner_eq_one 0
  have hff : inner ℂ f f = 1 := B.inner_eq_one 1
  have hef : inner ℂ e f = 0 := B.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)
  have hq (i j : Fin 2) :
      inner ℂ (B i : H n) (A (B j)) =
        (lam j : ℂ) * inner ℂ (B i) (B j) := by
    rw [← compression_inner A T (B i) (B j)]
    change inner ℂ (B i) (K (B j)) = _
    rw [hs.apply_eigenvectorBasis hT j, inner_smul_right]
  have hpos (i : Fin 2) : 0 < lam i := by
    have h := native_matrix_faithfulness rho hp (B i)
      (show (B i : H n) ≠ 0 by
        intro hz
        exact B.toBasis.ne_zero i (Subtype.ext hz))
    rw [hq i i, B.inner_eq_one, mul_one, Complex.ofReal_re] at h
    exact h
  have horder : lam 1 ≤ lam 0 := hs.eigenvalues_antitone hT (by decide)
  have hweight : weight A T = lam 0 + lam 1 := by
    rw [← compression_trace A T]
    simpa only [Fin.sum_univ_two] using hs.re_trace_eq_sum_eigenvalues hT
  have hnon : 0 ≤ weight A R := by
    apply weight_nonneg
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (native_matrix_faithfulness rho hp x hx).le
  have hden : 0 < c + weight A R + (lam 0 + lam 1) := by
    linarith [hpos 0, hpos 1]
  have hspan : (ℂ ∙ e) ⊔ (ℂ ∙ f) = T := by
    apply le_antisymm
      (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (B 0).property)
        ((Submodule.span_singleton_le_iff_mem _ _).2 (B 1).property))
    intro x hx
    have heq := congrArg (fun y : T => (y : H n)) (B.sum_repr ⟨x, hx⟩)
    simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul] at heq
    rw [← heq]
    exact Submodule.add_mem_sup
      ((ℂ ∙ e).smul_mem _ (Submodule.mem_span_singleton_self e))
      ((ℂ ∙ f).smul_mem _ (Submodule.mem_span_singleton_self f))
  obtain ⟨u, v, huT, hvT, huu, hvv, huv, hinf, hjoin, hwu, hwv⟩ :=
    pair_construction A e f hee hff hef (lam 0) (lam 1) r hr hr1
      (by simpa only [B.inner_eq_one, mul_one] using hq 0 0)
      (by simpa only [B.inner_eq_one, mul_one] using hq 1 1)
      (by simpa only [B.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1), mul_zero]
        using hq 0 1)
      (by simpa only [B.inner_eq_zero (by decide : (1 : Fin 2) ≠ 0), mul_zero]
        using hq 1 0)
  rw [hspan] at huT hvT hjoin
  have hun : ‖u‖ = 1 := by
    have h := congrArg Complex.re huu
    rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_re, Complex.one_re] at h
    nlinarith [norm_nonneg u]
  have hvn : ‖v‖ = 1 := by
    have h := congrArg Complex.re hvv
    rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_re, Complex.one_re] at h
    nlinarith [norm_nonneg v]
  have hu0 : u ≠ 0 := by intro h; simpa [h] using hun
  have hv0 : v ≠ 0 := by intro h; simpa [h] using hvn
  have hL : ℂ ∙ u ≤ T := (Submodule.span_singleton_le_iff_mem _ _).2 huT
  have hN : ℂ ∙ v ≤ T := (Submodule.span_singleton_le_iff_mem _ _).2 hvT
  have hdef := interval_defect A c R T (ℂ ∙ u) (ℂ ∙ v)
    hTR hL hN hinf hjoin (by simpa only [hweight] using hden)
  have hvalue : distance A c (R ⊔ (ℂ ∙ u)) (R ⊔ (ℂ ∙ v)) -
      distance A c (R ⊔ (ℂ ∙ u)) (R ⊔ T) -
      distance A c (R ⊔ T) (R ⊔ (ℂ ∙ v)) =
      r * (lam 0 - lam 1) / (c + weight A R + (lam 0 + lam 1)) := by
    rw [hdef, hwu, hwv, hweight]
    congr 1
    ring
  refine ⟨hpos 1, horder, hweight, hden, ⟨u, huT⟩, ⟨v, hvT⟩, hun, hvn, ?_, ?_⟩
  · change ‖inner ℂ u v‖ = r
    rw [huv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  · simp only [Submodule.map_span, Set.image_singleton, Submodule.subtype_apply]
    exact ⟨finrank_span_singleton hu0, finrank_span_singleton hv0, hinf, hjoin, hvalue⟩

#print axioms fixed_overlap_attainment

end D5.S3.Quantum.Algebra.BornJaccardFixedOverlap

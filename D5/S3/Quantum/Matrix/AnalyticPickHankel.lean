/- GID: D5/S3/Quantum/Matrix/AnalyticPickHankel
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/AnalyticPickHankel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/AnalyticPickKernel, mathlib/module/Mathlib.Analysis.Analytic.Order]
   utility: none
   digest: Real boundary Loewner blocks and normalized analytic Hankel positivity. -/

/-
admission_basis: escape-witness
Real derivative slopes and analytic Taylor factorizations turn global analytic
Pick positivity into a normalized third-order boundary Hankel inequality.
The argument is classical; the principal matrix power supplier is separate.
-/

import D5.S3.Quantum.Matrix.AnalyticPickKernel
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv

/-! Boundary confluence of an actual holomorphic matrix-valued Pick function. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise
open D5.S3.Quantum.Matrix.AnalyticPickKernel
namespace D5.S3.Quantum.Matrix.AnalyticPickHankel

section Boundary

variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma deriv_isHermitian_of_real
    {T : ℂ → Matrix d d ℂ} {Q : Matrix d d ℂ} {x : ℝ}
    (hT : HasDerivAt T Q (x : ℂ))
    (hReal : ∀ᶠ t : ℝ in 𝓝 x, (T (t : ℂ)).IsHermitian) :
    Q.IsHermitian := by
  have hRay : HasDerivAt (fun t : ℝ => T (t : ℂ)) Q x := by
    simpa using! hT.scomp x Complex.ofRealCLM.hasDerivAt
  have hs := hRay.tendsto_slope
  have hHerm : ∀ᶠ t : ℝ in 𝓝[≠] x,
      (slope (fun t : ℝ => T (t : ℂ)) x t).IsHermitian := by
    filter_upwards [hReal.filter_mono nhdsWithin_le_nhds] with t ht
    rw [slope_def_module]
    exact (ht.sub hReal.self_of_nhds).smul (by simp [IsSelfAdjoint])
  have hClosed : IsClosed {M : Matrix d d ℂ | M.IsHermitian} :=
    isClosed_eq (by fun_prop) continuous_id
  exact hClosed.mem_of_tendsto hs hHerm

private def diagonalPick (T : ℂ → Matrix d d ℂ) (x ε : ℝ) : Matrix d d ℂ :=
  let z := (x : ℂ) + I * (ε : ℂ)
  (z - star z)⁻¹ • (T z - (T z)ᴴ)

private lemma diagonal_pick_limit
    {T : ℂ → Matrix d d ℂ} {Q : Matrix d d ℂ} {x : ℝ}
    (hT : HasDerivAt T Q (x : ℂ))
    (hValue : (T (x : ℂ)).IsHermitian) (hQ : Q.IsHermitian) :
    Tendsto (diagonalPick T x) (𝓝[>] (0 : ℝ)) (𝓝 Q) := by
  have hi : HasDerivAt (fun ε : ℝ => (x : ℂ) + I * (ε : ℂ)) I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt.const_mul I).const_add (x : ℂ)
  have hr : HasDerivAt (fun ε : ℝ => T ((x : ℂ) + I * (ε : ℂ))) (I • Q) 0 := by
    simpa [Function.comp_def] using! hT.scomp_of_eq 0 hi (by simp)
  let r : ℝ → Matrix d d ℂ := fun ε => ε⁻¹ •
    (T ((x : ℂ) + I * (ε : ℂ)) - T (x : ℂ))
  have hs : Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 (I • Q)) := by
    simpa [r] using hr.tendsto_slope_zero_right
  have hlim := (hs.sub hs.star).const_smul (-I / 2)
  have hTarget : (-I / 2) • (I • Q - star (I • Q)) = Q := by
    ext a b
    simp [star_smul, Matrix.star_eq_conjTranspose, hQ.eq,
      Matrix.smul_apply, smul_eq_mul, Complex.star_def]
    linear_combination - Q a b * Complex.I_sq
  rw [hTarget] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hε)
  have hden : ((x : ℂ) + I * (ε : ℂ)) - star ((x : ℂ) + I * (ε : ℂ)) =
      2 * I * (ε : ℂ) := by
    simp [Complex.star_def]
    <;> ring
  simp only [diagonalPick, hden]
  ext a b
  simp only [r, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, hValue.eq, Matrix.conjTranspose_apply,
    star_sub, star_add, star_mul, star_trivial, Complex.star_def, Complex.conj_ofReal, Complex.star_def, Complex.conj_I]
  simp only [Complex.real_smul, Complex.ofReal_inv, _root_.mul_inv_rev, Complex.inv_I]
  field_simp [he]
  <;> ring

private lemma off_diagonal_pick_limit
    {T : ℂ → Matrix d d ℂ} {x y : ℝ} (hxy : x ≠ y)
    (hx : ContinuousAt T (x : ℂ)) (hy : ContinuousAt T (y : ℂ)) :
    Tendsto (fun ε : ℝ =>
      (((x : ℂ) + I * (ε : ℂ)) - star ((y : ℂ) + I * (ε : ℂ)))⁻¹ •
        (T ((x : ℂ) + I * (ε : ℂ)) - (T ((y : ℂ) + I * (ε : ℂ)))ᴴ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((x : ℂ) - (y : ℂ))⁻¹ • (T (x : ℂ) - (T (y : ℂ))ᴴ))) := by
  have hxl : Tendsto (fun ε : ℝ => (x : ℂ) + I * (ε : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have h : ContinuousAt (fun ε : ℝ => (x : ℂ) + I * (ε : ℂ)) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hyl : Tendsto (fun ε : ℝ => (y : ℂ) + I * (ε : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (y : ℂ)) := by
    have h : ContinuousAt (fun ε : ℝ => (y : ℂ) + I * (ε : ℂ)) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hd : (x : ℂ) - star (y : ℂ) ≠ 0 := by
    simpa using Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hxy)
  simpa only [star_trivial, Complex.star_def, Complex.conj_ofReal, Matrix.star_eq_conjTranspose, Function.comp_def] using!
    ((hxl.sub hyl.star).inv₀ hd).smul
      ((hx.tendsto.comp hxl).sub (hy.tendsto.comp hyl).star)

/-- The real boundary two-point Loewner block follows from the global Pick
property and local analytic, Hermitian real-axis extensions at the two points. -/
theorem real_two_point_loewner_posSemidef
    {T : ℂ → Matrix d d ℂ}
    (hT : DifferentiableOn ℂ T {z | 0 < z.im})
    (hPos : ∀ z : ℂ, 0 < z.im → (AnalyticPickKernel.imaginaryPart (T z)).PosSemidef)
    {x y : ℝ} (hxy : x ≠ y)
    (hx : DifferentiableAt ℂ T (x : ℂ)) (hy : DifferentiableAt ℂ T (y : ℂ))
    (hRx : ∀ᶠ t : ℝ in 𝓝 x, (T (t : ℂ)).IsHermitian)
    (hRy : ∀ᶠ t : ℝ in 𝓝 y, (T (t : ℂ)).IsHermitian) :
    (fromBlocks (deriv T (x : ℂ))
      (((x : ℂ) - (y : ℂ))⁻¹ • (T (x : ℂ) - T (y : ℂ)))
      (((x : ℂ) - (y : ℂ))⁻¹ • (T (x : ℂ) - T (y : ℂ)))
      (deriv T (y : ℂ))).PosSemidef := by
  let points : ℝ → Fin 2 → ℂ := fun ε =>
    ![(x : ℂ) + I * (ε : ℂ), (y : ℂ) + I * (ε : ℂ)]
  let e : d ⊕ d → Fin 2 × d := Sum.elim (fun a => (0, a)) (fun a => (1, a))
  have hPSD : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ((pickGram (points ε) T).submatrix e e).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply (upper_half_plane_pick_posSemidef hT hPos (points ε) ?_).submatrix e
    intro i
    fin_cases i <;> simpa [points] using hε
  have hdx := diagonal_pick_limit hx.hasDerivAt hRx.self_of_nhds
    (deriv_isHermitian_of_real hx.hasDerivAt hRx)
  have hdy := diagonal_pick_limit hy.hasDerivAt hRy.self_of_nhds
    (deriv_isHermitian_of_real hy.hasDerivAt hRy)
  have hxyL := off_diagonal_pick_limit hxy hx.continuousAt hy.continuousAt
  have hyxL := off_diagonal_pick_limit hxy.symm hy.continuousAt hx.continuousAt
  have hSwap : ((y : ℂ) - (x : ℂ))⁻¹ • (T (y : ℂ) - T (x : ℂ)) =
      ((x : ℂ) - (y : ℂ))⁻¹ • (T (x : ℂ) - T (y : ℂ)) := by
    rw [← neg_sub (x : ℂ) (y : ℂ), inv_neg]
    module
  rw [hRx.self_of_nhds.eq, hSwap] at hyxL
  rw [hRy.self_of_nhds.eq] at hxyL
  have hLim : Tendsto (fun ε => (pickGram (points ε) T).submatrix e e)
      (𝓝[>] (0 : ℝ))
      (𝓝 (fromBlocks (deriv T (x : ℂ))
        (((x : ℂ) - (y : ℂ))⁻¹ • (T (x : ℂ) - T (y : ℂ)))
        (((x : ℂ) - (y : ℂ))⁻¹ • (T (x : ℂ) - T (y : ℂ)))
        (deriv T (y : ℂ)))) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    rcases a with a | a <;> rcases b with b | b
    · simpa [points, e, pickGram, diagonalPick, Matrix.submatrix, fromBlocks,
        Matrix.smul_apply, smul_eq_mul] using (hdx.apply_nhds a).apply_nhds b
    · simpa [points, e, pickGram, Matrix.submatrix, fromBlocks,
        Matrix.smul_apply, smul_eq_mul, hRy.self_of_nhds.eq] using
          (hxyL.apply_nhds a).apply_nhds b
    · simpa [points, e, pickGram, Matrix.submatrix, fromBlocks,
        Matrix.smul_apply, smul_eq_mul, hRx.self_of_nhds.eq, hSwap] using
          (hyxL.apply_nhds a).apply_nhds b
    · simpa [points, e, pickGram, diagonalPick, Matrix.submatrix, fromBlocks,
        Matrix.smul_apply, smul_eq_mul] using (hdy.apply_nhds a).apply_nhds b
  exact Matrix.posSemidef_is_closed.mem_of_tendsto hLim hPSD

end Boundary

section Hankel

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Actual Taylor coefficients, with factorial normalization. -/
def normalizedCoefficient (T : ℂ → Matrix d d ℂ) (k : ℕ) : Matrix d d ℂ :=
  (k.factorial : ℂ)⁻¹ • iteratedDeriv k T 0

private lemma loewner_shear_posSemidef {A B C : Matrix d d ℂ}
    (hL : (fromBlocks A B B C).PosSemidef) (h : ℝ) :
    (fromBlocks A ((h : ℂ)⁻¹ • (B - A)) ((h : ℂ)⁻¹ • (B - A))
      (((h : ℂ)⁻¹ ^ 2) • (A - (2 : ℂ) • B + C))).PosSemidef := by
  let k : ℂ := (h : ℂ)⁻¹
  let S : Matrix (d ⊕ d) (d ⊕ d) ℂ :=
    fromBlocks 1 ((-k) • 1) 0 (k • 1)
  have hk : star k = k := by simp [k]
  have heq : Sᴴ * fromBlocks A B B C * S =
      fromBlocks A (k • (B - A)) (k • (B - A))
        ((k ^ 2) • (A - (2 : ℂ) • B + C)) := by
    simp only [S, fromBlocks_conjTranspose, Matrix.conjTranspose_one,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_smul, star_neg, hk,
      fromBlocks_multiply, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, smul_smul]
    apply fromBlocks_inj.mpr
    refine ⟨rfl, ?_, ?_, ?_⟩ <;> ext a b <;>
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;> ring
  have hp := hL.conjTranspose_mul_mul_same S
  rw [heq] at hp
  exact hp

/-- The normalized third-order Hankel block of any holomorphic matrix-valued
Pick function is positive semidefinite at a real analytic, Hermitian boundary
point. Only local regularity at zero is required on the real boundary. -/
theorem normalized_hankel_posSemidef
    {T : ℂ → Matrix d d ℂ}
    (hT : DifferentiableOn ℂ T {z | 0 < z.im})
    (hPos : ∀ z : ℂ, 0 < z.im → (AnalyticPickKernel.imaginaryPart (T z)).PosSemidef)
    (hA : AnalyticAt ℂ T 0)
    (hReal : ∀ᶠ t : ℝ in 𝓝 0, (T (t : ℂ)).IsHermitian) :
    (fromBlocks (normalizedCoefficient T 1) (normalizedCoefficient T 2)
      (normalizedCoefficient T 2) (normalizedCoefficient T 3)).PosSemidef := by
  let c1 := normalizedCoefficient T 1
  let c2 := normalizedCoefficient T 2
  let c3 := normalizedCoefficient T 3
  obtain ⟨F, hF, hTF⟩ := hA.exists_eventuallyEq_sum_add_pow_mul 4
  obtain ⟨H, hH, hDH⟩ := hA.deriv.exists_eventuallyEq_sum_add_pow_mul 3
  have hc1 : c1 = deriv T 0 := by simp [c1, normalizedCoefficient, iteratedDeriv_one]
  have hTaylor : ∀ᶠ z : ℂ in 𝓝 0,
      T z = T 0 + z • c1 + z ^ 2 • c2 + z ^ 3 • c3 + z ^ 4 • F z := by
    filter_upwards [hTF] with z hz
    rw [hz]
    simp [c1, c2, c3, normalizedCoefficient, Finset.sum_range_succ,
      div_eq_mul_inv, smul_smul, iteratedDeriv_zero, iteratedDeriv_one]
  have hTaylorD : ∀ᶠ z : ℂ in 𝓝 0,
      deriv T z = c1 + (2 * z) • c2 + (3 * z ^ 2) • c3 + z ^ 3 • H z := by
    filter_upwards [hDH] with z hz
    rw [hz]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add, pow_zero, pow_one, Nat.factorial_zero, Nat.cast_one, div_one,
      one_smul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_ofNat,
      ← iteratedDeriv_succ']
    simp [c1, c2, c3, normalizedCoefficient, smul_smul, div_eq_mul_inv]
    <;> module
  have hCast : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hPSD : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (fromBlocks c1 (c2 + (h : ℂ) • c3 + (h : ℂ) ^ 2 • F (h : ℂ))
        (c2 + (h : ℂ) • c3 + (h : ℂ) ^ 2 • F (h : ℂ))
        (c3 + (h : ℂ) • (H (h : ℂ) - (2 : ℂ) • F (h : ℂ)))).PosSemidef := by
    filter_upwards [(hCast.eventually hA.eventually_analyticAt).filter_mono nhdsWithin_le_nhds,
      hReal.eventually_nhds.filter_mono nhdsWithin_le_nhds,
      (hCast.eventually hTaylor).filter_mono nhdsWithin_le_nhds,
      (hCast.eventually hTaylorD).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with h hAh hRh hTh hDh hh
    have hn : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hh)
    let B : Matrix d d ℂ := (h : ℂ)⁻¹ • (T (h : ℂ) - T 0)
    have hL := real_two_point_loewner_posSemidef hT hPos (ne_of_lt hh)
      (by simpa using hA.differentiableAt) hAh.differentiableAt hReal hRh
    have hL' : (fromBlocks c1 B B (deriv T (h : ℂ))).PosSemidef := by
      simpa only [Complex.ofReal_zero, zero_sub, inv_neg, neg_smul,
        ← smul_neg, neg_sub, ← hc1, B] using hL
    have hS := loewner_shear_posSemidef hL' h
    have hOff : (h : ℂ)⁻¹ • (B - c1) =
        c2 + (h : ℂ) • c3 + (h : ℂ) ^ 2 • F (h : ℂ) := by
      dsimp only [B]
      rw [hTh]
      ext a b
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      field_simp [hn]
      <;> ring
    have hBottom : ((h : ℂ)⁻¹ ^ 2) •
        (c1 - (2 : ℂ) • B + deriv T (h : ℂ)) =
        c3 + (h : ℂ) • (H (h : ℂ) - (2 : ℂ) • F (h : ℂ)) := by
      dsimp only [B]
      rw [hTh, hDh]
      ext a b
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      field_simp [hn]
      <;> ring
    rwa [hOff, hBottom] at hS
  have hCo : ContinuousAt (fun t : ℝ => (t : ℂ)) 0 :=
    Complex.continuous_ofReal.continuousAt
  have hFc : ContinuousAt (fun h : ℝ => F (h : ℂ)) 0 :=
    hF.continuousAt.comp (f := fun t : ℝ => (t : ℂ)) hCo
  have hHc : ContinuousAt (fun h : ℝ => H (h : ℂ)) 0 :=
    hH.continuousAt.comp (f := fun t : ℝ => (t : ℂ)) hCo
  have hFe (a b : d) : ContinuousAt (fun h : ℝ => F (h : ℂ) a b) 0 :=
    continuousAt_pi.mp (continuousAt_pi.mp hFc a) b
  have hHe (a b : d) : ContinuousAt (fun h : ℝ => H (h : ℂ) a b) 0 :=
    continuousAt_pi.mp (continuousAt_pi.mp hHc a) b
  have hOffCont (a b : d) : ContinuousAt
      (fun h : ℝ => c2 a b + (h : ℂ) * c3 a b + (h : ℂ) ^ 2 * F (h : ℂ) a b) 0 :=
    (continuousAt_const.add (hCo.mul continuousAt_const)).add
      ((hCo.pow 2).mul (hFe a b))
  have hBottomCont (a b : d) : ContinuousAt
      (fun h : ℝ => c3 a b + (h : ℂ) * (H (h : ℂ) a b - 2 * F (h : ℂ) a b)) 0 :=
    continuousAt_const.add
      (hCo.mul ((hHe a b).sub (continuousAt_const.mul (hFe a b))))
  have hCont : ContinuousAt (fun h : ℝ =>
      fromBlocks c1 (c2 + (h : ℂ) • c3 + (h : ℂ) ^ 2 • F (h : ℂ))
        (c2 + (h : ℂ) • c3 + (h : ℂ) ^ 2 • F (h : ℂ))
        (c3 + (h : ℂ) • (H (h : ℂ) - (2 : ℂ) • F (h : ℂ)))) 0 := by
    apply continuousAt_pi.mpr
    intro a
    apply continuousAt_pi.mpr
    intro b
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;>
      first | exact continuousAt_const | exact hOffCont a b | exact hBottomCont a b
  have hLim := hCont.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hp := Matrix.posSemidef_is_closed.mem_of_tendsto hLim hPSD
  simpa [c1, c2, c3] using hp

end Hankel

end D5.S3.Quantum.Matrix.AnalyticPickHankel

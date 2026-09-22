/- GID: D5/S3/Geometry/Distances/FanCircleCapacity
   generality: G
   mirror-B: D5/B/S3/Geometry/Distances/FanCircleCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.SumMeasure, mathlib/module/Mathlib.MeasureTheory.Measure.ProbabilityMeasure, mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.Circle, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Fan's moving three-point circle capacity over all measures on the actual point set. -/

/- proof_shape: result: content
   escape_witness: the unified optimizer path is proved nondecreasing through the
     zero transition of its positive-part quadratic denominator
   admission_basis: open-problem-resolution (issue #9471)
   Direct frozen dependencies: none (pinned Mathlib only). -/

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false

namespace D5.S3.Geometry.Distances.FanCircleCapacity

open MeasureTheory

/-- The three unit-circle points in Fan's Conjecture 5.9, at polar angles
`psi`, `phi`, and `-phi`. -/
def points (phi psi : ℝ) : Set ℂ :=
  {Complex.exp ((psi : ℂ) * Complex.I),
    Complex.exp ((phi : ℂ) * Complex.I),
    Complex.exp ((-phi : ℂ) * Complex.I)}

/-- Fan's positive-order energy of a probability measure on the actual point subtype. -/
noncomputable def energy
    (r : ℝ) (K : Set ℂ) (mu : ProbabilityMeasure K) : ℝ :=
  ∫ x : K, ∫ y : K, dist (x : ℂ) (y : ℂ) ^ r
    ∂(mu : Measure K) ∂(mu : Measure K)

/-- The negative-exponent Riesz capacity in Fan's convention:
the `1 / r` power of the supremal positive-order energy. -/
noncomputable def capacity (r : ℝ) (K : Set ℂ) : ℝ :=
  (sSup (Set.range (energy r K))) ^ r⁻¹

set_option maxHeartbeats 1000000 in
-- The inlined finite-measure and analytic proof requires a larger elaboration budget.
/-- Fan's Conjecture 5.9 for the exact moving three-point circle set and all
probability measures on that set. -/
theorem result (r phi psi : ℝ) (hr : 2 ≤ r)
    (hphi₀ : Real.pi / 2 < phi) (hphi₁ : phi ≤ 2 * Real.pi / 3)
    (hpsi₀ : 0 ≤ psi) (hpsi₁ : psi ≤ 2 * Real.pi - 3 * phi) :
    capacity r (points phi psi) ≤
      capacity r (points phi (2 * Real.pi - 3 * phi)) := by
  have ambient_correspondence (r : ℝ) (K : Set ℂ) (hK : MeasurableSet K) :
      (∀ mu : ProbabilityMeasure K, ∃ nu : ProbabilityMeasure ℂ,
        (nu : Measure ℂ) Kᶜ = 0 ∧
        (nu : Measure ℂ) = (mu : Measure K).map ((↑) : K → ℂ) ∧
        (∫ x : ℂ, ∫ y : ℂ, dist x y ^ r ∂(nu : Measure ℂ) ∂(nu : Measure ℂ)) =
          energy r K mu) ∧
      (∀ nu : ProbabilityMeasure ℂ, (nu : Measure ℂ) Kᶜ = 0 →
        ∃ mu : ProbabilityMeasure K,
          (mu : Measure K).map ((↑) : K → ℂ) = (nu : Measure ℂ) ∧
          energy r K mu =
            ∫ x : ℂ, ∫ y : ℂ, dist x y ^ r ∂(nu : Measure ℂ) ∂(nu : Measure ℂ)) := by
    have hemb : MeasurableEmbedding ((↑) : K → ℂ) :=
      MeasurableEmbedding.subtype_coe hK
    have hforward (mu : ProbabilityMeasure K) : ∃ nu : ProbabilityMeasure ℂ,
        (nu : Measure ℂ) Kᶜ = 0 ∧
        (nu : Measure ℂ) = (mu : Measure K).map ((↑) : K → ℂ) ∧
        (∫ x : ℂ, ∫ y : ℂ, dist x y ^ r ∂(nu : Measure ℂ) ∂(nu : Measure ℂ)) =
          energy r K mu := by
      let nu : ProbabilityMeasure ℂ := mu.map hemb.measurable.aemeasurable
      refine ⟨nu, ?_, rfl, ?_⟩
      · rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply hemb.measurable hK.compl]
        simp
      · unfold energy
        change (∫ x : ℂ, ∫ y : ℂ, dist x y ^ r
          ∂Measure.map ((↑) : K → ℂ) (mu : Measure K)
          ∂Measure.map ((↑) : K → ℂ) (mu : Measure K)) = _
        rw [hemb.integral_map]
        simp_rw [hemb.integral_map]
    refine ⟨hforward, ?_⟩
    intro nu hnu
    have hKone : (nu : Measure ℂ) K = 1 :=
      (prob_compl_eq_zero_iff hK).mp hnu
    let muMeasure : Measure K := Measure.comap ((↑) : K → ℂ) (nu : Measure ℂ)
    have hmuProbability : IsProbabilityMeasure muMeasure := by
      constructor
      dsimp [muMeasure]
      rw [comap_subtype_coe_apply hK]
      simpa using hKone
    let mu : ProbabilityMeasure K := ⟨muMeasure, hmuProbability⟩
    have hmap : (mu : Measure K).map ((↑) : K → ℂ) = (nu : Measure ℂ) := by
      change (Measure.comap ((↑) : K → ℂ) (nu : Measure ℂ)).map
        ((↑) : K → ℂ) = (nu : Measure ℂ)
      rw [map_comap_subtype_coe hK, Measure.restrict_eq_self_of_ae_mem]
      exact (mem_ae_iff_prob_eq_one hK).mpr hKone
    refine ⟨mu, hmap, ?_⟩
    obtain ⟨nu', _, hnu', henergy⟩ := hforward mu
    rw [hnu', hmap] at henergy
    exact henergy.symm

  have finite_double_integral
      {X : Type} [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype X]
      (mu : ProbabilityMeasure X) (f : X → X → ℝ) :
      (∫ x, ∫ y, f x y ∂(mu : Measure X) ∂(mu : Measure X)) =
        ∑ x, ∑ y, (mu : Measure X).real {x} * (mu : Measure X).real {y} * f x y := by
    rw [integral_fintype Integrable.of_finite]
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring

  have chord_distance (s t : ℝ) :
      dist (Complex.exp ((s : ℂ) * Complex.I))
          (Complex.exp ((t : ℂ) * Complex.I)) =
        2 * |Real.sin ((s - t) / 2)| := by
    rw [dist_eq_norm, Complex.exp_mul_I, Complex.exp_mul_I, Complex.norm_def,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.cos_ofReal_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.sin_ofReal_re, Complex.I_im, mul_one, add_zero,
      Complex.sub_im, Complex.add_im, Complex.cos_ofReal_im,
      Complex.mul_im, Complex.ofReal_im, zero_mul, Complex.sin_ofReal_im,
      zero_add]
    norm_num
    rw [show (Real.cos s - Real.cos t) * (Real.cos s - Real.cos t) +
          (Real.sin s - Real.sin t) * (Real.sin s - Real.sin t) =
        (2 * |Real.sin ((s - t) / 2)|) ^ 2 by
      simp only [mul_pow, sq_abs]
      calc
        (Real.cos s - Real.cos t) * (Real.cos s - Real.cos t) +
            (Real.sin s - Real.sin t) * (Real.sin s - Real.sin t) =
            2 - 2 * Real.cos (s - t) := by
              rw [Real.cos_sub]
              nlinarith [Real.sin_sq_add_cos_sq s, Real.sin_sq_add_cos_sq t]
        _ = 2 ^ 2 * Real.sin ((s - t) / 2) ^ 2 := by
              rw [show s - t = 2 * ((s - t) / 2) by ring,
                Real.cos_two_mul_eq_one_sub]
              ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity

  have three_point_geometry
      (phi psi : ℝ) (hphi₀ : Real.pi / 2 < phi)
      (hphi₁ : phi ≤ 2 * Real.pi / 3) (hpsi₀ : 0 ≤ psi)
      (hpsi₁ : psi ≤ 2 * Real.pi - 3 * phi) :
      let a := 2 * Real.sin ((phi - psi) / 2)
      let b := 2 * Real.sin ((phi + psi) / 2)
      let c := 2 * Real.sin phi
      ∃ e : Fin 3 ≃ points phi psi,
        dist ((e 0 : points phi psi) : ℂ) (e 1 : ℂ) = c ∧
        dist ((e 1 : points phi psi) : ℂ) (e 2 : ℂ) = a ∧
        dist ((e 2 : points phi psi) : ℂ) (e 0 : ℂ) = b ∧
        0 < a ∧ a ≤ b ∧ b ≤ c := by
    dsimp only
    have hpi : 0 < Real.pi := Real.pi_pos
    have hphi_pos : 0 < phi := by linarith
    have hphi_pi : phi < Real.pi := by nlinarith
    let x := (phi - psi) / 2
    let y := (phi + psi) / 2
    have hx_pos : 0 < x := by dsimp [x]; linarith
    have hy_pos : 0 < y := by dsimp [y]; linarith
    have hxy : x ≤ y := by dsimp [x, y]; linarith
    have hy_cap : y ≤ Real.pi - phi := by dsimp [y]; linarith
    have hcap_half : Real.pi - phi ≤ Real.pi / 2 := by linarith
    have hx_half : x ≤ Real.pi / 2 := hxy.trans (hy_cap.trans hcap_half)
    have hy_half : y ≤ Real.pi / 2 := hy_cap.trans hcap_half
    have hneg_half_x : -(Real.pi / 2) ≤ x := by linarith
    have hneg_half_y : -(Real.pi / 2) ≤ y := by linarith
    have hsx_pos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hx_pos (hx_half.trans_lt (by linarith))
    have hsy_pos : 0 < Real.sin y :=
      Real.sin_pos_of_pos_of_lt_pi hy_pos (hy_half.trans_lt (by linarith))
    have hsphi_pos : 0 < Real.sin phi := Real.sin_pos_of_pos_of_lt_pi hphi_pos hphi_pi
    have hsxy : Real.sin x ≤ Real.sin y :=
      Real.sin_le_sin_of_le_of_le_pi_div_two hneg_half_x hy_half hxy
    have hy_nonneg : 0 ≤ y := hy_pos.le
    have hcap_nonneg : 0 ≤ Real.pi - phi := by linarith
    have hsyphi : Real.sin y ≤ Real.sin phi := by
      calc
        Real.sin y ≤ Real.sin (Real.pi - phi) :=
          Real.sin_le_sin_of_le_of_le_pi_div_two hneg_half_y hcap_half hy_cap
        _ = Real.sin phi := by rw [Real.sin_pi_sub]
    let zneg : ℂ := Complex.exp ((-phi : ℝ) * Complex.I)
    let zpos : ℂ := Complex.exp ((phi : ℂ) * Complex.I)
    let zmov : ℂ := Complex.exp ((psi : ℂ) * Complex.I)
    have hdist₀₁ : dist zneg zpos = 2 * Real.sin phi := by
      rw [show zneg = Complex.exp (((-phi : ℝ) : ℂ) * Complex.I) by rfl,
        show zpos = Complex.exp ((phi : ℂ) * Complex.I) by rfl, chord_distance]
      rw [show ((-phi : ℝ) - phi) / 2 = -phi by ring, Real.sin_neg, abs_neg,
        abs_of_pos hsphi_pos]
    have hdist₁₂ : dist zpos zmov = 2 * Real.sin x := by
      rw [show zpos = Complex.exp ((phi : ℂ) * Complex.I) by rfl,
        show zmov = Complex.exp ((psi : ℂ) * Complex.I) by rfl, chord_distance]
      rw [show (phi - psi) / 2 = x by rfl, abs_of_pos hsx_pos]
    have hdist₂₀ : dist zmov zneg = 2 * Real.sin y := by
      rw [show zmov = Complex.exp ((psi : ℂ) * Complex.I) by rfl,
        show zneg = Complex.exp (((-phi : ℝ) : ℂ) * Complex.I) by rfl, chord_distance]
      rw [show (psi - -phi) / 2 = y by dsimp [y]; ring, abs_of_pos hsy_pos]
    have hzneg_pos : zneg ≠ zpos := dist_pos.mp (hdist₀₁.symm ▸ mul_pos (by norm_num) hsphi_pos)
    have hzpos_mov : zpos ≠ zmov := dist_pos.mp (hdist₁₂.symm ▸ mul_pos (by norm_num) hsx_pos)
    have hzmov_neg : zmov ≠ zneg := dist_pos.mp (hdist₂₀.symm ▸ mul_pos (by norm_num) hsy_pos)
    let q : Fin 3 → points phi psi := ![
      ⟨zneg, by simp [zneg, points]⟩,
      ⟨zpos, by simp [zpos, points]⟩,
      ⟨zmov, by simp [zmov, points]⟩]
    have hq_inj : Function.Injective q := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [q]
    have hq_surj : Function.Surjective q := by
      intro z
      rcases z.property with hz | hz | hz
      · refine ⟨2, Subtype.ext ?_⟩
        simpa [q, zmov] using hz.symm
      · refine ⟨1, Subtype.ext ?_⟩
        simpa [q, zpos] using hz.symm
      · refine ⟨0, Subtype.ext ?_⟩
        simpa [q, zneg] using hz.symm
    let e : Fin 3 ≃ points phi psi := Equiv.ofBijective q ⟨hq_inj, hq_surj⟩
    refine ⟨e, ?_, ?_, ?_, by positivity, ?_, ?_⟩
    · exact hdist₀₁
    · exact hdist₁₂
    · exact hdist₂₀
    · nlinarith
    · nlinarith

  have three_point_maximum
      (A B C : ℝ) (hA : 0 < A) (hAB : A ≤ B) (hBC : B ≤ C) :
      let S := max (A + B - C) 0
      let D := 4 * A * B - S ^ 2
      let U := (C / 2) * (4 * A * B) / D
      ∃ u₀ v₀ w₀ : ℝ,
        0 ≤ u₀ ∧ 0 ≤ v₀ ∧ 0 ≤ w₀ ∧ u₀ + v₀ + w₀ = 1 ∧
        2 * C * u₀ * v₀ + 2 * A * v₀ * w₀ + 2 * B * w₀ * u₀ = U ∧
        ∀ u v w : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → u + v + w = 1 →
          2 * C * u * v + 2 * A * v * w + 2 * B * w * u ≤ U := by
    have hB : 0 < B := hA.trans_le hAB
    have hC : 0 < C := hB.trans_le hBC
    by_cases hS : A + B - C ≤ 0
    · simp only [max_eq_right hS]
      have hABpos : 0 < A * B := mul_pos hA hB
      have hU : (C / 2) * (4 * A * B) / (4 * A * B - 0 ^ 2) = C / 2 := by
        field_simp
        ring
      refine ⟨1 / 2, 1 / 2, 0, by positivity, by positivity, le_rfl, by ring, ?_, ?_⟩
      · rw [hU]
        ring
      · intro u v w hu hv hw hsum
        rw [hU]
        have huv := le_total u v
        rcases huv with huv | hvu
        · have hlin : A * v + B * u ≤ C * v := by
            calc
              A * v + B * u ≤ A * v + B * v := by nlinarith
              _ = (A + B) * v := by ring
              _ ≤ C * v := by nlinarith
          have hlinw := mul_le_mul_of_nonneg_right hlin hw
          have hvone : v ≤ 1 := by nlinarith
          have hsq : 0 ≤ (2 * v - 1) ^ 2 := sq_nonneg _
          calc
            2 * C * u * v + 2 * A * v * w + 2 * B * w * u ≤
                2 * C * v * (u + w) := by nlinarith
            _ = 2 * C * v * (1 - v) := by congr 1 <;> linarith
            _ ≤ C / 2 := by nlinarith
        · have hlin : A * v + B * u ≤ C * u := by
            calc
              A * v + B * u ≤ A * u + B * u := by nlinarith
              _ = (A + B) * u := by ring
              _ ≤ C * u := by nlinarith
          have hlinw := mul_le_mul_of_nonneg_right hlin hw
          have huone : u ≤ 1 := by nlinarith
          have hsq : 0 ≤ (2 * u - 1) ^ 2 := sq_nonneg _
          calc
            2 * C * u * v + 2 * A * v * w + 2 * B * w * u ≤
                2 * C * u * (v + w) := by nlinarith
            _ = 2 * C * u * (1 - u) := by congr 1 <;> linarith
            _ ≤ C / 2 := by nlinarith
    · have hSpos : 0 < A + B - C := lt_of_not_ge hS
      have hSleA : A + B - C ≤ A := by linarith
      have hSleB : A + B - C ≤ B := by linarith
      have hD : 0 < 4 * A * B - (A + B - C) ^ 2 := by
        have hmul₁ : (A + B - C) ^ 2 ≤ (A + B - C) * B := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left hSleB hSpos.le
        have hmul₂ : (A + B - C) * B ≤ A * B := by
          exact mul_le_mul_of_nonneg_right hSleA hB.le
        nlinarith [mul_pos hA hB]
      simp only [max_eq_left hSpos.le]
      let D := 4 * A * B - (A + B - C) ^ 2
      let u₀ := A * (B + C - A) / D
      let v₀ := B * (C + A - B) / D
      let w₀ := C * (A + B - C) / D
      have hD' : 0 < D := hD
      have hDne : D ≠ 0 := ne_of_gt hD'
      have hCA : A ≤ C := hAB.trans hBC
      have hBCA : 0 < B + C - A := by linarith
      have hCAB : 0 < C + A - B := by linarith
      have hu₀ : 0 ≤ u₀ := by
        dsimp [u₀]
        exact div_nonneg (mul_nonneg hA.le hBCA.le) hD'.le
      have hv₀ : 0 ≤ v₀ := by
        dsimp [v₀]
        exact div_nonneg (mul_nonneg hB.le hCAB.le) hD'.le
      have hw₀ : 0 ≤ w₀ := by
        dsimp [w₀]
        positivity
      have hsum₀ : u₀ + v₀ + w₀ = 1 := by
        dsimp [u₀, v₀, w₀]
        field_simp [hDne]
        ring
      refine ⟨u₀, v₀, w₀, hu₀, hv₀, hw₀, hsum₀, ?_, ?_⟩
      · dsimp [u₀, v₀, w₀]
        change _ = (C / 2) * (4 * A * B) / D
        field_simp [hDne]
        ring
      · intro u v w hu hv hw hsum
        have hid :
            (C / 2) * (4 * A * B) / D -
                (2 * C * u * v + 2 * A * v * w + 2 * B * w * u) =
              ((2 * B * (u - u₀) + (A + B - C) * (v - v₀)) ^ 2 +
                D * (v - v₀) ^ 2) / (2 * B) := by
          have hw_eq : w = 1 - u - v := by linarith
          rw [hw_eq]
          dsimp [u₀, v₀]
          field_simp [hDne, ne_of_gt hB]
          ring
        rw [show 4 * A * B - (A + B - C) ^ 2 = D by rfl]
        rw [← sub_nonneg, hid]
        positivity

  have three_point_energy_sup
      {X : Type} [MeasurableSpace X] [MeasurableSingletonClass X]
      (e : Fin 3 ≃ X) (f : X → X → ℝ) (A B C : ℝ)
      (hf_symm : ∀ x y, f x y = f y x) (hf_diag : ∀ x, f x x = 0)
      (hf₀₁ : f (e 0) (e 1) = C) (hf₁₂ : f (e 1) (e 2) = A)
      (hf₂₀ : f (e 2) (e 0) = B)
      (hA : 0 < A) (hAB : A ≤ B) (hBC : B ≤ C) :
      let S := max (A + B - C) 0
      let D := 4 * A * B - S ^ 2
      sSup (Set.range fun mu : ProbabilityMeasure X ↦
        ∫ x, ∫ y, f x y ∂(mu : Measure X) ∂(mu : Measure X)) =
        (C / 2) * (4 * A * B) / D := by
    classical
    letI : Fintype X := Fintype.ofEquiv (Fin 3) e
    dsimp only
    obtain ⟨u₀, v₀, w₀, hu₀, hv₀, hw₀, hsum₀, hvalue₀, hbound⟩ :=
      three_point_maximum A B C hA hAB hBC
    let m : Fin 3 → ℝ := ![u₀, v₀, w₀]
    let c : X → ℝ := fun x ↦ m (e.symm x)
    have hc_nonneg : ∀ x, 0 ≤ c x := by
      intro x
      generalize hi : e.symm x = i
      fin_cases i <;> simp [c, m, hi, hu₀, hv₀, hw₀]
    have hc_sum : ∑ x, c x = 1 := by
      rw [← e.sum_comp]
      simpa [c, m, Fin.sum_univ_three] using hsum₀
    have hc_hasSum : HasSum c 1 := by simpa [hc_sum] using hasSum_fintype c
    let nu : Measure X := Measure.sum fun x ↦ ENNReal.ofReal (c x) • Measure.dirac x
    have hnu : IsProbabilityMeasure nu := by
      dsimp [nu]
      exact HasSum.isProbabilityMeasure_sum_dirac hc_nonneg hc_hasSum
    let mu₀ : ProbabilityMeasure X := ⟨nu, hnu⟩
    have hmass (x : X) : (mu₀ : Measure X).real {x} = c x := by
      rw [measureReal_def]
      change (nu {x}).toReal = c x
      dsimp [nu]
      rw [Measure.sum_smul_dirac_singleton, ENNReal.toReal_ofReal (hc_nonneg x)]
    have hexpand (mu : ProbabilityMeasure X) :
        (∫ x, ∫ y, f x y ∂(mu : Measure X) ∂(mu : Measure X)) =
          2 * C * (mu : Measure X).real {e 0} * (mu : Measure X).real {e 1} +
          2 * A * (mu : Measure X).real {e 1} * (mu : Measure X).real {e 2} +
          2 * B * (mu : Measure X).real {e 2} * (mu : Measure X).real {e 0} := by
      rw [finite_double_integral, ← e.sum_comp]
      simp_rw [← e.sum_comp]
      simp only [Fin.sum_univ_three, hf_diag, hf₀₁, hf₁₂, hf₂₀,
        hf_symm (e 1) (e 0), hf_symm (e 2) (e 1), hf_symm (e 0) (e 2)]
      ring
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨mu₀, ?_⟩
      change (∫ x, ∫ y, f x y ∂(mu₀ : Measure X) ∂(mu₀ : Measure X)) = _
      rw [hexpand]
      simp_rw [hmass]
      simpa [c, m] using hvalue₀
    · rintro z ⟨mu, rfl⟩
      change (∫ x, ∫ y, f x y ∂(mu : Measure X) ∂(mu : Measure X)) ≤ _
      rw [hexpand]
      apply hbound
      · exact measureReal_nonneg
      · exact measureReal_nonneg
      · exact measureReal_nonneg
      · have hsum : ∑ x, (mu : Measure X).real {x} = 1 := by
          simpa using MeasureTheory.sum_measureReal_singleton
            (μ := (mu : Measure X)) (Finset.univ : Finset X)
        rw [← e.sum_comp, Fin.sum_univ_three] at hsum
        exact hsum

  have capacity_formula
      (r phi psi : ℝ) (hr : 2 ≤ r) (hphi₀ : Real.pi / 2 < phi)
      (hphi₁ : phi ≤ 2 * Real.pi / 3) (hpsi₀ : 0 ≤ psi)
      (hpsi₁ : psi ≤ 2 * Real.pi - 3 * phi) :
      let a := 2 * Real.sin ((phi - psi) / 2)
      let b := 2 * Real.sin ((phi + psi) / 2)
      let c := 2 * Real.sin phi
      let A := a ^ r
      let B := b ^ r
      let C := c ^ r
      let S := max (A + B - C) 0
      let D := 4 * A * B - S ^ 2
      capacity r (points phi psi) = ((C / 2) * (4 * A * B) / D) ^ r⁻¹ := by
    dsimp only
    obtain ⟨e, hdist₀₁, hdist₁₂, hdist₂₀, ha, hab, hbc⟩ :=
      three_point_geometry phi psi hphi₀ hphi₁ hpsi₀ hpsi₁
    let a := 2 * Real.sin ((phi - psi) / 2)
    let b := 2 * Real.sin ((phi + psi) / 2)
    let c := 2 * Real.sin phi
    have hb : 0 < b := ha.trans_le hab
    have hc : 0 < c := hb.trans_le hbc
    have hr_nonneg : 0 ≤ r := by linarith
    have hA : 0 < a ^ r := Real.rpow_pos_of_pos ha r
    have hAB : a ^ r ≤ b ^ r := Real.rpow_le_rpow ha.le hab hr_nonneg
    have hBC : b ^ r ≤ c ^ r := Real.rpow_le_rpow hb.le hbc hr_nonneg
    have hsup := three_point_energy_sup e
      (fun x y : points phi psi ↦ dist (x : ℂ) (y : ℂ) ^ r)
      (a ^ r) (b ^ r) (c ^ r)
      (fun x y ↦ by rw [dist_comm])
      (fun x ↦ by simp [Real.zero_rpow (by linarith : r ≠ 0)])
      (by simpa [c] using congrArg (fun t : ℝ ↦ t ^ r) hdist₀₁)
      (by simpa [a] using congrArg (fun t : ℝ ↦ t ^ r) hdist₁₂)
      (by simpa [b] using congrArg (fun t : ℝ ↦ t ^ r) hdist₂₀)
      hA hAB hBC
    unfold capacity
    congr 1

  have power_displacement
      (p u v : ℝ) (hp : 1 ≤ p) (hu₀ : 0 ≤ u) (huv : u ≤ v) (hv₁ : v ≤ 1)
      (hsum : 1 ≤ u ^ p + v ^ p) : v - u ≤ v ^ p - u ^ p := by
    have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
    have hv₀ : 0 ≤ v := hu₀.trans huv
    have hu₁ : u ≤ 1 := huv.trans hv₁
    by_cases hp_one : p = 1
    · subst p
      simp
    have hp_gt : 1 < p := lt_of_le_of_ne hp (Ne.symm hp_one)
    let alpha := p⁻¹
    have halpha_pos : 0 < alpha := by dsimp [alpha]; positivity
    have halpha_lt : alpha < 1 := by
      dsimp [alpha]
      exact inv_lt_one_of_one_lt₀ hp_gt
    have halpha_nonneg : 0 ≤ alpha := halpha_pos.le
    have halpha_ne : alpha ≠ 0 := ne_of_gt halpha_pos
    let s := u ^ p
    let t := v ^ p
    let delta := t - s
    have hs₀ : 0 ≤ s := Real.rpow_nonneg hu₀ p
    have ht₀ : 0 ≤ t := Real.rpow_nonneg hv₀ p
    have hst : s ≤ t := Real.rpow_le_rpow hu₀ huv hp_pos.le
    have ht₁ : t ≤ 1 := by
      simpa [t] using Real.rpow_le_rpow hv₀ hv₁ hp_pos.le
    have hdelta₀ : 0 ≤ delta := sub_nonneg.mpr hst
    have hdelta₁ : delta ≤ 1 := by dsimp [delta]; linarith
    have hs_alpha : s ^ alpha = u := by
      dsimp [s, alpha]
      exact Real.rpow_rpow_inv hu₀ hp_pos.ne'
    have ht_alpha : t ^ alpha = v := by
      dsimp [t, alpha]
      exact Real.rpow_rpow_inv hv₀ hp_pos.ne'
    by_cases hdelta_zero : delta = 0
    · have hst_eq : s = t := by linarith
      rw [← hs_alpha, ← ht_alpha, hst_eq]
      simp [hdelta_zero]
    by_cases hdelta_one : delta = 1
    · have hs_zero : s = 0 := by dsimp [delta] at hdelta_one; linarith
      have ht_one : t = 1 := by dsimp [delta] at hdelta_one; linarith
      have hu_zero : u = 0 := by
        rw [← hs_alpha, hs_zero]
        exact Real.zero_rpow halpha_ne
      have hv_one : v = 1 := by rw [← ht_alpha, ht_one, Real.one_rpow]
      rw [hu_zero, hv_one, Real.one_rpow, Real.zero_rpow hp_pos.ne']
    have hdelta_pos : 0 < delta := lt_of_le_of_ne hdelta₀ (Ne.symm hdelta_zero)
    have hdelta_lt : delta < 1 := lt_of_le_of_ne hdelta₁ hdelta_one
    let z := (1 - delta) / 2
    have hz_pos : 0 < z := by dsimp [z]; linarith
    have hz_half : z < 1 / 2 := by dsimp [z]; linarith
    have hzs : z ≤ s := by
      dsimp [z, delta, s, t] at *
      linarith
    let h : ℝ → ℝ := fun w ↦ w ^ alpha - (1 - w) ^ alpha + 1 - 2 * w
    have hh_cont : Continuous h := by
      dsimp [h]
      fun_prop
    let h' : ℝ → ℝ := fun w ↦
      alpha * w ^ (alpha - 1) + alpha * (1 - w) ^ (alpha - 1) - 2
    let h'' : ℝ → ℝ := fun w ↦
      alpha * (alpha - 1) * (w ^ (alpha - 2) - (1 - w) ^ (alpha - 2))
    have hh' (w : ℝ) (hw : w ∈ interior (Set.Icc (0 : ℝ) (1 / 2))) :
        HasDerivWithinAt h (h' w) (interior (Set.Icc (0 : ℝ) (1 / 2))) w := by
      have hw' : w ∈ Set.Ioo (0 : ℝ) (1 / 2) := by simpa using hw
      have hw_ne : w ≠ 0 := ne_of_gt hw'.1
      have hw_lt_one : w < 1 := hw'.2.trans (by norm_num)
      have h1w_ne : 1 - w ≠ 0 := by linarith
      apply HasDerivAt.hasDerivWithinAt
      dsimp [h, h']
      convert (((Real.hasDerivAt_rpow_const (x := w) (p := alpha) (Or.inl hw_ne)).sub
        ((Real.hasDerivAt_rpow_const (x := 1 - w) (p := alpha) (Or.inl h1w_ne)).comp w
          ((hasDerivAt_const w 1).sub (hasDerivAt_id w)))).add_const 1).sub
            ((hasDerivAt_const w 2).mul (hasDerivAt_id w)) using 1
      all_goals first | rfl | (funext q; ring) | ring
    have hh'' (w : ℝ) (hw : w ∈ interior (Set.Icc (0 : ℝ) (1 / 2))) :
        HasDerivWithinAt h' (h'' w) (interior (Set.Icc (0 : ℝ) (1 / 2))) w := by
      have hw' : w ∈ Set.Ioo (0 : ℝ) (1 / 2) := by simpa using hw
      have hw_ne : w ≠ 0 := ne_of_gt hw'.1
      have hw_lt_one : w < 1 := hw'.2.trans (by norm_num)
      have h1w_ne : 1 - w ≠ 0 := by linarith
      apply HasDerivAt.hasDerivWithinAt
      dsimp [h', h'']
      convert ((((hasDerivAt_const w alpha).mul
        (Real.hasDerivAt_rpow_const (x := w) (p := alpha - 1) (Or.inl hw_ne))).add
        ((hasDerivAt_const w alpha).mul
          ((Real.hasDerivAt_rpow_const (x := 1 - w) (p := alpha - 1) (Or.inl h1w_ne)).comp w
            ((hasDerivAt_const w 1).sub (hasDerivAt_id w))))).sub_const 2) using 1
      all_goals first | rfl | (funext q; ring) | ring
    have hh''_nonpos (w : ℝ) (hw : w ∈ interior (Set.Icc (0 : ℝ) (1 / 2))) :
        h'' w ≤ 0 := by
      have hw' : w ∈ Set.Ioo (0 : ℝ) (1 / 2) := by simpa using hw
      have hw_le : w ≤ 1 - w := by nlinarith [hw'.2]
      have hpow : (1 - w) ^ (alpha - 2) ≤ w ^ (alpha - 2) := by
        exact Real.rpow_le_rpow_of_nonpos hw'.1 hw_le (by linarith)
      dsimp [h'']
      have hcoef : alpha * (alpha - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos halpha_nonneg (by linarith)
      exact mul_nonpos_of_nonpos_of_nonneg hcoef (sub_nonneg.mpr hpow)
    have hh_concave : ConcaveOn ℝ (Set.Icc (0 : ℝ) (1 / 2)) h :=
      concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _) hh_cont.continuousOn
        hh' hh'' hh''_nonpos
    have hh_nonneg : 0 ≤ h z := by
      have hmin := hh_concave.min_le_of_mem_Icc
        (show (0 : ℝ) ∈ Set.Icc 0 (1 / 2) by norm_num)
        (show (1 / 2 : ℝ) ∈ Set.Icc 0 (1 / 2) by norm_num)
        (show z ∈ Set.Icc 0 (1 / 2) by exact ⟨hz_pos.le, hz_half.le⟩)
      have hh_zero : h 0 = 0 := by simp [h, halpha_ne]
      have hh_half : h (1 / 2) = 0 := by dsimp [h]; ring
      rw [hh_zero, hh_half, min_self] at hmin
      exact hmin
    have hcentral : (1 - z) ^ alpha - z ^ alpha ≤ delta := by
      dsimp [h] at hh_nonneg
      have hzdelta : 1 - 2 * z = delta := by dsimp [z]; ring
      linarith
    let F : ℝ → ℝ := fun w ↦ (w + delta) ^ alpha - w ^ alpha
    let F' : ℝ → ℝ := fun w ↦
      alpha * ((w + delta) ^ (alpha - 1) - w ^ (alpha - 1))
    have hF_cont : ContinuousOn F (Set.Ici z) := by
      apply Continuous.continuousOn
      dsimp [F]
      fun_prop
    have hF' (w : ℝ) (hw : w ∈ interior (Set.Ici z)) :
        HasDerivWithinAt F (F' w) (interior (Set.Ici z)) w := by
      have hw' : z < w := by simpa using hw
      have hw_pos : 0 < w := hz_pos.trans hw'
      have hwd_pos : 0 < w + delta := by positivity
      apply HasDerivAt.hasDerivWithinAt
      dsimp [F, F']
      convert ((Real.hasDerivAt_rpow_const (x := w + delta) (p := alpha)
        (Or.inl hwd_pos.ne')).comp w ((hasDerivAt_id w).add_const delta)).sub
          (Real.hasDerivAt_rpow_const (x := w) (p := alpha) (Or.inl hw_pos.ne')) using 1
      all_goals first | rfl | (funext q; ring) | ring
    have hF'_nonpos (w : ℝ) (hw : w ∈ interior (Set.Ici z)) : F' w ≤ 0 := by
      have hw' : z < w := by simpa using hw
      have hw_pos : 0 < w := hz_pos.trans hw'
      have hporder : (w + delta) ^ (alpha - 1) ≤ w ^ (alpha - 1) :=
        Real.rpow_le_rpow_of_nonpos hw_pos (by linarith) (by linarith)
      dsimp [F']
      exact mul_nonpos_of_nonneg_of_nonpos halpha_nonneg (sub_nonpos.mpr hporder)
    have hF_anti : AntitoneOn F (Set.Ici z) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici z) hF_cont hF' hF'_nonpos
    have hFs : F s ≤ F z := hF_anti
      (by simpa only [Set.mem_Ici] using (le_rfl : z ≤ z))
      (by simpa only [Set.mem_Ici] using hzs) hzs
    have ht_eq : t = s + delta := by dsimp [delta]; ring
    have hz_eq : z + delta = 1 - z := by dsimp [z]; ring
    calc
      v - u = t ^ alpha - s ^ alpha := by rw [ht_alpha, hs_alpha]
      _ = (s + delta) ^ alpha - s ^ alpha := by rw [ht_eq]
      _ = F s := rfl
      _ ≤ F z := hFs
      _ = (1 - z) ^ alpha - z ^ alpha := by dsimp [F]; rw [hz_eq]
      _ ≤ delta := hcentral
      _ = t - s := rfl
      _ = v ^ p - u ^ p := rfl

  have hasDerivAt_max_zero_sq (x : ℝ) :
      HasDerivAt (fun y : ℝ ↦ max y 0 ^ 2) (2 * max x 0) x := by
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have heq : (fun y : ℝ ↦ max y 0 ^ 2) =ᶠ[nhds x] fun _ ↦ 0 := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        have hy' : y < 0 := hy
        simp [max_eq_right hy'.le]
      simpa [max_eq_right hx.le] using
        (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
    · subst x
      apply hasDerivAt_iff_tendsto_slope_zero.mpr
      have hc : ContinuousAt (fun y : ℝ ↦ max y 0) 0 :=
        continuousAt_id.max continuousAt_const
      have ht : Filter.Tendsto (fun y : ℝ ↦ max y 0) (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
        by
          simpa using hc.mono_left
            (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) {0}ᶜ ≤ nhds 0)
      have heq : (fun y : ℝ ↦ max y 0) =ᶠ[nhdsWithin 0 {0}ᶜ]
          fun y ↦ y⁻¹ • (max (0 + y) 0 ^ 2 - max 0 0 ^ 2) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : y ≠ 0 := by simpa using hy
        by_cases hy : 0 ≤ y
        · simp only [zero_add, max_eq_left hy, max_self, pow_two, zero_mul,
            sub_zero, smul_eq_mul]
          field_simp
        · have hy' : y < 0 := lt_of_not_ge hy
          simp [max_eq_right hy'.le, hy0]
      simpa using ht.congr' heq
    · have heq : (fun y : ℝ ↦ max y 0 ^ 2) =ᶠ[nhds x] fun y ↦ y * y := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        have hy' : 0 < y := hy
        simp [max_eq_left hy'.le, pow_two]
      have hmul : HasDerivAt (fun y : ℝ ↦ y * y) (2 * x) x :=
        ((hasDerivAt_id x).mul (hasDerivAt_id x)).congr_deriv (by simp [id]; ring)
      simpa [max_eq_left hx.le] using hmul.congr_of_eventuallyEq heq

  have power_ratio_displacement
      (r a b c : ℝ) (hr : 2 ≤ r) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
      (hactive : c ^ r < a ^ r + b ^ r) :
      c ^ r * (b ^ 2 - a ^ 2) ≤ (b ^ r - a ^ r) * c ^ 2 := by
    have hb : 0 < b := ha.trans_le hab
    have hc : 0 < c := hb.trans_le hbc
    have hp : 1 ≤ r / 2 := by linarith
    let u := a ^ 2 / c ^ 2
    let v := b ^ 2 / c ^ 2
    have hu₀ : 0 ≤ u := by dsimp [u]; positivity
    have huv : u ≤ v := by
      dsimp [u, v]
      gcongr
    have hv₁ : v ≤ 1 := by
      dsimp [v]
      rw [div_le_one (sq_pos_of_pos hc)]
      gcongr
    have hpow_a : u ^ (r / 2) = a ^ r / c ^ r := by
      dsimp [u]
      rw [Real.div_rpow (sq_nonneg a) (sq_nonneg c)]
      congr 1
      · rw [← Real.rpow_two a, ← Real.rpow_mul ha.le]
        congr 1
        ring
      · rw [← Real.rpow_two c, ← Real.rpow_mul hc.le]
        congr 1
        ring
    have hpow_b : v ^ (r / 2) = b ^ r / c ^ r := by
      dsimp [v]
      rw [Real.div_rpow (sq_nonneg b) (sq_nonneg c)]
      congr 1
      · rw [← Real.rpow_two b, ← Real.rpow_mul hb.le]
        congr 1
        ring
      · rw [← Real.rpow_two c, ← Real.rpow_mul hc.le]
        congr 1
        ring
    have hsum : 1 ≤ u ^ (r / 2) + v ^ (r / 2) := by
      rw [hpow_a, hpow_b]
      rw [← add_div]
      have hactive' : 1 * c ^ r ≤ a ^ r + b ^ r := by simpa using hactive.le
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hc r)).2 hactive'
    have hdisp := power_displacement (r / 2) u v hp hu₀ huv hv₁ hsum
    rw [hpow_a, hpow_b] at hdisp
    dsimp [u, v] at hdisp
    field_simp [ne_of_gt hc, ne_of_gt (Real.rpow_pos_of_pos hc r)] at hdisp ⊢
    nlinarith

  have active_bracket_nonneg
      (r x y : ℝ) (hr : 2 ≤ r)
      (hsx : 0 < Real.sin x) (hsy : 0 < Real.sin y)
      (hsxy : 0 < Real.sin (x + y))
      (hab : 2 * Real.sin x ≤ 2 * Real.sin y)
      (hbc : 2 * Real.sin y ≤ 2 * Real.sin (x + y))
      (hactive : (2 * Real.sin (x + y)) ^ r <
        (2 * Real.sin x) ^ r + (2 * Real.sin y) ^ r) :
      0 ≤ ((2 * Real.sin y) ^ r + (2 * Real.sin (x + y)) ^ r -
          (2 * Real.sin x) ^ r) * Real.cot y -
        ((2 * Real.sin x) ^ r + (2 * Real.sin (x + y)) ^ r -
          (2 * Real.sin y) ^ r) * Real.cot x := by
    let a := 2 * Real.sin x
    let b := 2 * Real.sin y
    let c := 2 * Real.sin (x + y)
    let A := a ^ r
    let B := b ^ r
    let C := c ^ r
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    have hc : 0 < c := by dsimp [c]; positivity
    have hdisp : C * (b ^ 2 - a ^ 2) ≤ (B - A) * c ^ 2 := by
      exact power_ratio_displacement r a b c hr ha hab hbc hactive
    have hsq : Real.sin y ^ 2 - Real.sin x ^ 2 =
        Real.sin (x + y) * Real.sin (y - x) := by
      rw [Real.sin_add, Real.sin_sub]
      nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y]
    have hscaled : C * Real.sin (y - x) ≤ (B - A) * Real.sin (x + y) := by
      dsimp [a, b, c] at hdisp
      rw [show (2 * Real.sin y) ^ 2 - (2 * Real.sin x) ^ 2 =
          4 * (Real.sin y ^ 2 - Real.sin x ^ 2) by ring,
        show (2 * Real.sin (x + y)) ^ 2 = 4 * Real.sin (x + y) ^ 2 by ring,
        hsq] at hdisp
      nlinarith
    have hcot_add : (Real.cot x + Real.cot y) * (Real.sin x * Real.sin y) =
        Real.sin (x + y) := by
      rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
      field_simp [ne_of_gt hsx, ne_of_gt hsy]
      rw [Real.sin_add]
      ring
    have hcot_sub : (Real.cot x - Real.cot y) * (Real.sin x * Real.sin y) =
        Real.sin (y - x) := by
      rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
      field_simp [ne_of_gt hsx, ne_of_gt hsy]
      rw [Real.sin_sub]
      ring
    have hden : 0 < Real.sin x * Real.sin y := mul_pos hsx hsy
    have hmul : 0 ≤ ((B + C - A) * Real.cot y - (A + C - B) * Real.cot x) *
        (Real.sin x * Real.sin y) := by
      rw [show (B + C - A) * Real.cot y - (A + C - B) * Real.cot x =
        (B - A) * (Real.cot x + Real.cot y) - C * (Real.cot x - Real.cot y) by ring]
      rw [sub_mul, mul_assoc, mul_assoc, hcot_add, hcot_sub]
      linarith
    change 0 ≤ (B + C - A) * Real.cot y - (A + C - B) * Real.cot x
    rw [mul_comm] at hmul
    exact nonneg_of_mul_nonneg_right hmul hden

  have profile_hasDerivAt_nonneg
      (r phi t : ℝ) (hr : 2 ≤ r)
      (hsx : 0 < Real.sin ((phi - t) / 2))
      (hsy : 0 < Real.sin ((phi + t) / 2))
      (hsphi : 0 < Real.sin phi)
      (hab : 2 * Real.sin ((phi - t) / 2) ≤ 2 * Real.sin ((phi + t) / 2))
      (hbc : 2 * Real.sin ((phi + t) / 2) ≤ 2 * Real.sin phi) :
      let profile := fun psi : ℝ ↦
        let a := 2 * Real.sin ((phi - psi) / 2)
        let b := 2 * Real.sin ((phi + psi) / 2)
        let c := 2 * Real.sin phi
        let A := a ^ r
        let B := b ^ r
        let C := c ^ r
        let S := max (A + B - C) 0
        let D := 4 * A * B - S ^ 2
        (C / 2) * (4 * A * B) / D
      ∃ d : ℝ, HasDerivAt profile d t ∧ 0 ≤ d := by
    dsimp only
    let x := (phi - t) / 2
    let y := (phi + t) / 2
    let a := 2 * Real.sin x
    let b := 2 * Real.sin y
    let c := 2 * Real.sin phi
    let A := a ^ r
    let B := b ^ r
    let C := c ^ r
    let s := A + B - C
    let q := max s 0 ^ 2
    let D := 4 * A * B - q
    have ha : 0 < a := by dsimp [a, x]; positivity
    have hb : 0 < b := by dsimp [b, y]; positivity
    have hc : 0 < c := by dsimp [c]; positivity
    have hA : 0 < A := Real.rpow_pos_of_pos ha r
    have hB : 0 < B := Real.rpow_pos_of_pos hb r
    have hC : 0 < C := Real.rpow_pos_of_pos hc r
    have hr₀ : 0 ≤ r := by linarith
    have hAB : A ≤ B := Real.rpow_le_rpow ha.le hab hr₀
    have hBC : B ≤ C := Real.rpow_le_rpow hb.le hbc hr₀
    have hCA : A ≤ C := hAB.trans hBC
    have hsA : s ≤ A := by dsimp [s]; linarith
    have hsB : s ≤ B := by dsimp [s]; linarith
    have hmaxA : max s 0 ≤ A := max_le hsA hA.le
    have hmaxB : max s 0 ≤ B := max_le hsB hB.le
    have hqAB : q ≤ A * B := by
      dsimp [q]
      rw [pow_two]
      exact mul_le_mul hmaxA hmaxB (le_max_right _ _) hA.le
    have hD : 0 < D := by
      dsimp [D]
      nlinarith [mul_pos hA hB]
    let af : ℝ → ℝ := fun psi ↦ 2 * Real.sin ((phi - psi) / 2)
    let bf : ℝ → ℝ := fun psi ↦ 2 * Real.sin ((phi + psi) / 2)
    let Af : ℝ → ℝ := fun psi ↦ af psi ^ r
    let Bf : ℝ → ℝ := fun psi ↦ bf psi ^ r
    let sf : ℝ → ℝ := fun psi ↦ Af psi + Bf psi - C
    let qf : ℝ → ℝ := fun psi ↦ max (sf psi) 0 ^ 2
    let Df : ℝ → ℝ := fun psi ↦ 4 * Af psi * Bf psi - qf psi
    let profile : ℝ → ℝ := fun psi ↦ (C / 2) * (4 * Af psi * Bf psi) / Df psi
    have hxder : HasDerivAt (fun psi : ℝ ↦ (phi - psi) / 2) (-1 / 2) t := by
      simpa only [Pi.sub_apply, id_eq, zero_sub] using!
        ((hasDerivAt_const t phi).sub (hasDerivAt_id t)).div_const 2
    have hyder : HasDerivAt (fun psi : ℝ ↦ (phi + psi) / 2) (1 / 2) t := by
      simpa only [Pi.add_apply, id_eq, zero_add] using!
        ((hasDerivAt_const t phi).add (hasDerivAt_id t)).div_const 2
    have haf : HasDerivAt af (-Real.cos x) t := by
      have h := (hasDerivAt_const t 2).mul
        ((Real.hasDerivAt_sin ((phi - t) / 2)).comp t hxder)
      change HasDerivAt af (-Real.cos x) t
      convert! h using 1 <;> dsimp [af, x] <;> ring
    have hbf : HasDerivAt bf (Real.cos y) t := by
      have h := (hasDerivAt_const t 2).mul
        ((Real.hasDerivAt_sin ((phi + t) / 2)).comp t hyder)
      change HasDerivAt bf (Real.cos y) t
      convert! h using 1 <;> dsimp [bf, y] <;> ring
    have hAf : HasDerivAt Af (-(r / 2) * A * Real.cot x) t := by
      have hraw : HasDerivAt Af ((-Real.cos x) * r * a ^ (r - 1)) t := by
        simpa [Af, show af t = a by rfl] using haf.rpow_const (p := r) (Or.inl ha.ne')
      apply hraw.congr_deriv
      rw [Real.rpow_sub_one ha.ne', Real.cot_eq_cos_div_sin]
      dsimp [a, A]
      field_simp [ne_of_gt hsx] <;> ring
    have hBf : HasDerivAt Bf ((r / 2) * B * Real.cot y) t := by
      have hraw : HasDerivAt Bf (Real.cos y * r * b ^ (r - 1)) t := by
        simpa [Bf, show bf t = b by rfl] using hbf.rpow_const (p := r) (Or.inl hb.ne')
      apply hraw.congr_deriv
      rw [Real.rpow_sub_one hb.ne', Real.cot_eq_cos_div_sin]
      dsimp [b, B]
      field_simp [ne_of_gt hsy] <;> ring
    let Aprime := -(r / 2) * A * Real.cot x
    let Bprime := (r / 2) * B * Real.cot y
    let sprime := Aprime + Bprime
    have hsf : HasDerivAt sf sprime t := by
      dsimp [sf, sprime, Aprime, Bprime]
      exact (hAf.add hBf).sub_const C
    have hqf : HasDerivAt qf (2 * max s 0 * sprime) t := by
      have hcomp := (hasDerivAt_max_zero_sq s).comp t hsf
      change HasDerivAt (fun psi ↦ max (sf psi) 0 ^ 2) _ t
      simpa only [Function.comp_apply] using! hcomp
    let n := 4 * A * B
    let nprime := 4 * (Aprime * B + A * Bprime)
    let dprime := nprime - 2 * max s 0 * sprime
    have hnf : HasDerivAt (fun psi ↦ 4 * Af psi * Bf psi) nprime t := by
      have h := ((hasDerivAt_const t 4).mul hAf).mul hBf
      apply h.congr_deriv
      dsimp [nprime, Aprime, Bprime]
      ring
    have hDf : HasDerivAt Df dprime t := by
      dsimp [Df, dprime]
      exact hnf.sub hqf
    have hprofile : HasDerivAt profile
        ((C / 2) * (nprime * D - n * dprime) / D ^ 2) t := by
      have hnum := (hasDerivAt_const t (C / 2)).mul hnf
      have hdiv := hnum.div hDf hD.ne'
      change HasDerivAt profile _ t
      apply hdiv.congr_deriv
      dsimp [profile, Df, n, D, q, s, A, B, Af, Bf, af, bf, a, b, x, y]
      field_simp [hD.ne']
      ring
    refine ⟨(C / 2) * (nprime * D - n * dprime) / D ^ 2, ?_, ?_⟩
    · simpa [profile, Af, Bf, af, bf, C, c, x, y] using hprofile
    · by_cases hspos : 0 < s
      · have hbracket : 0 ≤ (B + C - A) * Real.cot y -
            (A + C - B) * Real.cot x := by
          have hxy : x + y = phi := by dsimp [x, y]; ring
          have hactive' : (2 * Real.sin (x + y)) ^ r <
              (2 * Real.sin x) ^ r + (2 * Real.sin y) ^ r := by
            rw [hxy]
            simpa [A, B, C, a, b, c, s] using hspos
          have h := active_bracket_nonneg r x y hr hsx hsy
            (by simpa [hxy] using hsphi)
            (by simpa [x, y] using hab)
            (by simpa [hxy, y] using hbc)
            hactive'
          simpa [A, B, C, a, b, c, hxy] using h
        have hformula : nprime * D - n * dprime =
            2 * r * A * B * s *
              ((B + C - A) * Real.cot y - (A + C - B) * Real.cot x) := by
          dsimp [nprime, dprime, n, D, q, sprime, Aprime, Bprime]
          rw [max_eq_left hspos.le]
          dsimp [s]
          ring
        rw [hformula]
        positivity
      · have hsnonpos : s ≤ 0 := le_of_not_gt hspos
        have hzero : nprime * D - n * dprime = 0 := by
          dsimp [dprime, D, q]
          rw [max_eq_right hsnonpos]
          ring
        rw [hzero]
        simp

  let L := 2 * Real.pi - 3 * phi
  let profile := fun t : ℝ ↦
    let a := 2 * Real.sin ((phi - t) / 2)
    let b := 2 * Real.sin ((phi + t) / 2)
    let c := 2 * Real.sin phi
    let A := a ^ r
    let B := b ^ r
    let C := c ^ r
    let S := max (A + B - C) 0
    let D := 4 * A * B - S ^ 2
    (C / 2) * (4 * A * B) / D
  have hL₀ : 0 ≤ L := by dsimp [L]; linarith
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc 0 L) :
      ∃ d : ℝ, HasDerivAt profile d t ∧ 0 ≤ d := by
    have ht₀ : 0 ≤ t := ht.1
    have htL : t ≤ 2 * Real.pi - 3 * phi := by simpa [L] using ht.2
    obtain ⟨e, h₀₁, h₁₂, h₂₀, ha, hab, hbc⟩ :=
      three_point_geometry phi t hphi₀ hphi₁ ht₀ htL
    have hb : 0 < 2 * Real.sin ((phi + t) / 2) := ha.trans_le hab
    have hc : 0 < 2 * Real.sin phi := hb.trans_le hbc
    have hsx : 0 < Real.sin ((phi - t) / 2) := by linarith
    have hsy : 0 < Real.sin ((phi + t) / 2) := by linarith
    have hsphi : 0 < Real.sin phi := by linarith
    simpa [profile] using
      profile_hasDerivAt_nonneg r phi t hr hsx hsy hsphi hab hbc
  have hcont : ContinuousOn profile (Set.Icc 0 L) := by
    intro t ht
    obtain ⟨d, hd, _⟩ := hpoint t ht
    exact hd.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ profile (interior (Set.Icc 0 L)) := by
    intro t ht
    obtain ⟨d, hd, _⟩ := hpoint t (interior_subset ht)
    exact hd.differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ interior (Set.Icc 0 L), 0 ≤ deriv profile t := by
    intro t ht
    obtain ⟨d, hd, hd₀⟩ := hpoint t (interior_subset ht)
    rw [hd.deriv]
    exact hd₀
  have hmono : MonotoneOn profile (Set.Icc 0 L) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 L) hcont hdiff hderiv
  have hprofile : profile psi ≤ profile L :=
    hmono ⟨hpsi₀, by simpa [L] using hpsi₁⟩ ⟨hL₀, le_rfl⟩
      (by simpa [L] using hpsi₁)
  have hpsiFormula := capacity_formula r phi psi hr hphi₀ hphi₁ hpsi₀ hpsi₁
  have hLFormula := capacity_formula r phi L hr hphi₀ hphi₁ hL₀ (by simp [L])
  rw [hpsiFormula, hLFormula]
  have hbase₀ : 0 ≤ profile psi := by
    obtain ⟨e, h₀₁, h₁₂, h₂₀, ha, hab, hbc⟩ :=
      three_point_geometry phi psi hphi₀ hphi₁ hpsi₀ hpsi₁
    let a := 2 * Real.sin ((phi - psi) / 2)
    let b := 2 * Real.sin ((phi + psi) / 2)
    let c := 2 * Real.sin phi
    let A := a ^ r
    let B := b ^ r
    let C := c ^ r
    let s := max (A + B - C) 0
    let D := 4 * A * B - s ^ 2
    have hb : 0 < b := ha.trans_le hab
    have hc : 0 < c := hb.trans_le hbc
    have hA : 0 < A := Real.rpow_pos_of_pos ha r
    have hB : 0 < B := Real.rpow_pos_of_pos hb r
    have hC : 0 < C := Real.rpow_pos_of_pos hc r
    have hAB : A ≤ B := Real.rpow_le_rpow ha.le hab (by linarith)
    have hBC : B ≤ C := Real.rpow_le_rpow hb.le hbc (by linarith)
    have hsA : s ≤ A := by dsimp [s]; exact max_le (by linarith) hA.le
    have hsB : s ≤ B := by dsimp [s]; exact max_le (by linarith) hB.le
    have hsAB : s ^ 2 ≤ A * B := by
      rw [pow_two]
      exact mul_le_mul hsA hsB (le_max_right _ _) hA.le
    have hD : 0 < D := by dsimp [D]; nlinarith [mul_pos hA hB]
    dsimp [profile, a, b, c, A, B, C, s, D]
    positivity
  apply Real.rpow_le_rpow hbase₀
  · simpa [profile, L] using hprofile
  · positivity

end D5.S3.Geometry.Distances.FanCircleCapacity

/- GID: D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticJointLimit
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CountableGaussianQuadraticJointLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Countable Gaussian quadratic sums converge jointly with old Gaussian coordinates. -/

import D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit
import D5.S3.Fourier.Asymptotics.GaussianQuadraticMixedDefect

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticJointLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The actual countable quadratic sums converge jointly with any fixed finite Gaussian
vector to the product law, even when the old vector is correlated with every row. -/
theorem result (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) (X : Ω → EuclideanSpace ℝ (Fin d)) (hX : AEMeasurable X P)
    (G : ℕ → ℕ → Ω → ℝ) (a : ℕ → ℕ → ℝ) (v : ℝ≥0)
    (hG : ∀ n j, HasLaw (G n j) (gaussianReal 0 1) P)
    (hind : ∀ n, iIndepFun (G n) P)
    (hjoint : ∀ n N, HasGaussianLaw
      (fun ω => (X ω, fun j : Fin N => G n j ω)) P)
    (ha : ∀ n, Summable (fun j => (a n j)^2))
    (hM : Tendsto (fun n => ⨆ j, |a n j|) atTop (𝓝 0))
    (hS : Tendsto (fun n => ∑' j, (a n j)^2) atTop (𝓝 ((v : ℝ)/2))) :
    letI := Measure.isProbabilityMeasure_map hX
    ∃ (hmem : ∀ n j, MemLp (fun ω => a n j*((G n j ω)^2-1)) 2 P)
      (Q : ℕ → Lp ℝ 2 P),
      (∀ n, HasSum (fun j => (hmem n j).toLp
        (fun ω => a n j*((G n j ω)^2-1))) (Q n)) ∧
      TendstoInDistribution (fun n ω => (X ω, Q n ω)) atTop
        (id : EuclideanSpace ℝ (Fin d) × ℝ → EuclideanSpace ℝ (Fin d) × ℝ)
        (fun _ => P) ((P.map X).prod (gaussianReal 0 v)) := by
  classical
  obtain ⟨hmem, Q, hQ, hlim⟩ :=
    CountableGaussianQuadraticLimit.result Ω P G a v hG hind ha hM hS
  have := Measure.isProbabilityMeasure_map hX
  refine ⟨hmem, Q, hQ, ?_⟩
  let M (n : ℕ) : ℝ := ⨆ j, |a n j|
  have hle (n j : ℕ) : |a n j| ≤ M n := by
    have hzero : Tendsto (fun j => |a n j|) atTop (𝓝 0) := by
      have h := Real.continuous_sqrt.continuousAt.tendsto.comp (ha n).tendsto_atTop_zero
      simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using h
    exact le_ciSup hzero.bddAbove_range j
  have hnonneg (n : ℕ) : 0 ≤ M n := (abs_nonneg (a n 0)).trans (hle n 0)
  have hdefect (Y : Ω → ℝ)
      (hY : ∀ n N, HasGaussianLaw (fun ω => (Y ω, fun j : Fin N => G n j ω)) P)
      (t : ℝ) (n : ℕ) :
      ‖charFun (P.map (fun ω => Y ω+t*Q n ω)) 1 -
        charFun (P.map Y) 1 * charFun (P.map (Q n)) t‖ ≤
        (|t| * M n*Var[Y; P]) * Real.exp (|t| * M n*Var[Y; P]) := by
    have hYL := (hY n 0).fst
    let U : Lp ℝ 2 P := hYL.memLp_two.toLp Y
    let Z (N : ℕ) : Lp ℝ 2 P := ∑ j ∈ Finset.range N,
      (hmem n j).toLp (fun ω => a n j*((G n j ω)^2-1))
    have hZ : Tendsto Z atTop (𝓝 (Q n)) := (hQ n).tendsto_sum_nat
    have hshift : Tendsto (fun N => U+t • Z N) atTop (𝓝 (U+t • Q n)) :=
      tendsto_const_nhds.add (hZ.const_smul t)
    have hdist := (tendstoInMeasure_of_tendsto_Lp hshift).tendstoInDistribution
      (fun N => (Lp.aestronglyMeasurable _).aemeasurable)
    have hzdist := (tendstoInMeasure_of_tendsto_Lp hZ).tendstoInDistribution
      (fun N => (Lp.aestronglyMeasurable _).aemeasurable)
    have hrepr (N : ℕ) : ⇑(Z N) =ᵐ[P]
        (fun ω => ∑ j : Fin N, a n j*((G n j ω)^2-1)) := by
      refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
      filter_upwards [ae_all_iff.mpr (fun j => (hmem n j).coeFn_toLp)] with ω hω
      exact (Finset.sum_congr (s₁ := Finset.range N) rfl (fun j _ => hω j)).trans
        (Fin.sum_univ_eq_sum_range (fun j => a n j*((G n j ω)^2-1)) N).symm
    have hshiftrepr (V : Lp ℝ 2 P) : ⇑(U+t • V) =ᵐ[P] (fun ω => Y ω+t*V ω) := by
      filter_upwards [Lp.coeFn_add U (t • V), Lp.coeFn_smul t V,
        hYL.memLp_two.coeFn_toLp] with ω h1 h2 h3
      simp only [h1, h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, U, h3]
    have hc1 := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hdist.tendsto) 1
    have hc2 := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hzdist.tendsto) t
    have hc := (hc1.sub (hc2.const_mul (charFun (P.map Y) 1))).norm
    change Tendsto (fun N => ‖charFun (P.map (U+t • Z N)) 1 -
      charFun (P.map Y) 1 * charFun (P.map (Z N)) t‖) atTop
      (𝓝 ‖charFun (P.map (U+t • Q n)) 1 -
      charFun (P.map Y) 1 * charFun (P.map (Q n)) t‖) at hc
    rw [Measure.map_congr (hshiftrepr (Q n))] at hc
    apply le_of_tendsto hc
    apply Filter.Eventually.of_forall
    intro N
    have hfin := GaussianQuadraticMixedDefect.result P (fun j : Fin N => G n j)
      (fun j => hG n j) ((hind n).precomp Fin.val_injective) Y (hY n N) (fun j => t*a n j) (|t| * M n)
      (mul_nonneg (abs_nonneg _) (hnonneg n)) (fun j => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hle n j) (abs_nonneg _))
    rw [Measure.map_congr (hshiftrepr (Z N))]
    rw [Measure.map_congr (hrepr N)]
    have heq : (fun ω => Y ω+t*Z N ω) =ᵐ[P]
        (fun ω => Y ω+∑ j : Fin N, (t*a n j)*((G n j ω)^2-1)) := by
      filter_upwards [hrepr N] with ω hω
      rw [hω, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [Measure.map_congr heq]
    have heq2 : (fun ω => ∑ j : Fin N, (t*a n j)*((G n j ω)^2-1)) =
        fun ω => t*∑ j : Fin N, a n j*((G n j ω)^2-1) := by
      ext ω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [heq2, charFun_map_mul_comp (by fun_prop), mul_one] at hfin
    exact hfin
  let E := EuclideanSpace ℝ (Fin d)
  let ν := (P.map X).prod (gaussianReal 0 v)
  have hlift : TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (X ω, Q n ω)) atTop
      (WithLp.toLp 2 : E × ℝ → WithLp 2 (E × ℝ)) (fun _ => P) ν := by
    refine ⟨(fun n => by fun_prop), (by fun_prop), ?_⟩
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro u
    let x : E := (WithLp.ofLp u).1
    let t : ℝ := (WithLp.ofLp u).2
    let Y (ω : Ω) : ℝ := ⟪x, X ω⟫
    have hY (n N : ℕ) : HasGaussianLaw
        (fun ω => (Y ω, fun j : Fin N => G n j ω)) P := by
      exact (hjoint n N).map_fun
        (((innerSL ℝ x).comp (ContinuousLinearMap.fst ℝ E (Fin N → ℝ))).prod
          (ContinuousLinearMap.snd ℝ E (Fin N → ℝ)))
    have hbound := fun n => hdefect Y hY t n
    have hsmall : Tendsto (fun n => |t| * M n*Var[Y; P]) atTop (𝓝 0) := by
      simpa using (hM.const_mul |t|).mul_const Var[Y; P]
    have herr : Tendsto (fun n => charFun (P.map (fun ω => Y ω+t*Q n ω)) 1 -
        charFun (P.map Y) 1 * charFun (P.map (Q n)) t) atTop (𝓝 0) := by
      apply squeeze_zero_norm hbound
      simpa using hsmall.mul (Real.continuous_exp.continuousAt.tendsto.comp hsmall)
    have hc := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim.tendsto) t
    change Tendsto (fun n => charFun (P.map (Q n)) t) atTop
      (𝓝 (charFun ((gaussianReal 0 v).map id) t)) at hc
    have hh := herr.add (hc.const_mul (charFun (P.map Y) 1))
    have hmap (n : ℕ) : charFun (P.map (fun ω => WithLp.toLp 2 (X ω, Q n ω))) u =
        charFun (P.map (fun ω => Y ω+t*Q n ω)) 1 := by
      rw [charFun_apply, charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
        integral_map (by fun_prop) (by fun_prop)]
      congr 1
      ext ω
      simp [Y, x, t, WithLp.prod_inner_apply, real_inner_comm, real_inner_self_eq_norm_sq]
    have hmapX : charFun (P.map X) x = charFun (P.map Y) 1 := by
      rw [charFun_apply, charFun_apply_real, integral_map hX (by fun_prop),
        integral_map (by dsimp [Y]; fun_prop) (by fun_prop)]
      congr 1
      ext ω
      simp [Y, real_inner_comm]
    change Tendsto (fun n => charFun (P.map (fun ω => WithLp.toLp 2 (X ω, Q n ω))) u)
      atTop (𝓝 (charFun (ν.map (WithLp.toLp 2)) u))
    simp only [hmap, ν, charFun_prod, ← hmapX, sub_add_cancel, zero_add,
      Measure.map_id, x, t] at hh ⊢
    exact hh
  have hout := hlift.continuous_comp
    (g := (WithLp.ofLp : WithLp 2 (E × ℝ) → E × ℝ)) (by fun_prop)
  exact hout

end D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticJointLimit

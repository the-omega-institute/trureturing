/- GID: D5/S3/Quantum/Analysis/Hermite/PhysicalProductTotality
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/Hermite/PhysicalProductTotality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual physical product Hermite tests are total for all positive parameters. -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0; see docs/reports/hermite-suppliers/tauceti-LICENSE.txt.
Adapted from TauCetiProject/TauCeti at f749c1bb6b118c898f8d152e8ff9ad3d2b339dfd,
Analysis/InnerProductSpace/L2/Pi.lean and MeasureTheory/Integral/PiSystem.lean.
The coordinate density and product-measure proof are used locally, without retaining
thin tensor/basis declarations. No originality is claimed for the donor construction.
-/
import D5.S3.Quantum.Analysis.Hermite.GaussianPolynomialTotality
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.PiSystem

open MeasureTheory MeasureTheory.Measure Polynomial Complex Filter WithLp
open scoped Topology ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Quantum.Analysis.Hermite.PhysicalProductTotality

/-- The physical product function, with the probabilists' Hermite convention. -/
noncomputable def physicalHermite (d : ℕ) (hbar : ℝ) (mass frequency : Fin d → ℝ)
    (alpha : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ∏ j, ((aeval (Real.sqrt 2 * x j / Real.sqrt (hbar / (mass j * frequency j)))
      (Polynomial.hermite (alpha j)) *
      Real.exp (-((x j / Real.sqrt (hbar / (mass j * frequency j))) ^ 2) / 2) /
      (Real.sqrt (Real.sqrt (hbar / (mass j * frequency j))) *
        Real.sqrt ((alpha j).factorial * Real.sqrt Real.pi)) : ℝ) : ℂ)

/-- Actual positive-parameter physical Hermite tests detect every volume L2 vector,
including the empty-coordinate Dirac space. -/
theorem physical_product_totality (d : ℕ) (hbar : ℝ) (mass frequency : Fin d → ℝ)
    (hhbar : 0 < hbar) (hmass : ∀ j, 0 < mass j) (hfrequency : ∀ j, 0 < frequency j) :
    (∀ alpha, MemLp (physicalHermite d hbar mass frequency alpha) 2 volume) ∧
    ∀ g : EuclideanSpace ℝ (Fin d) → ℂ, MemLp g 2 volume →
      (∀ alpha, ∫ x, physicalHermite d hbar mass frequency alpha x * g x = 0) →
        g =ᵐ[volume] 0 := by
  classical
  let ell : Fin d → ℝ := fun j => Real.sqrt (hbar / (mass j * frequency j))
  have hell (j) : 0 < ell j := Real.sqrt_pos.2 (div_pos hhbar (mul_pos (hmass j) (hfrequency j)))
  let width : Fin d → ℝ := fun j => mass j * frequency j / hbar
  have hwidth (j) : 0 < width j := div_pos (mul_pos (hmass j) (hfrequency j)) hhbar
  let tests : Fin d → ℕ → ℝ → ℂ := fun j n x =>
    ((aeval (Real.sqrt 2 * x / ell j) (Polynomial.hermite n) *
      Real.exp (-(x / ell j) ^ 2 / 2) /
      (Real.sqrt (ell j) * Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)) : ℝ) : ℂ)
  have polynomial_memLp (b : ℝ) (hb : 0 < b) (q : Polynomial ℝ) :
      MemLp (fun x : ℝ => q.eval x * Real.exp (-(b * x ^ 2) / 2)) 2 volume := by
    have monomial (n : ℕ) :
        MemLp (fun x : ℝ => x ^ n * Real.exp (-(b * x ^ 2) / 2)) 2 volume := by
      refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
      have hi := integrable_rpow_mul_exp_neg_mul_sq hb
        (s := ((2 * n : ℕ) : ℝ)) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))
      simp only [Real.rpow_natCast] at hi
      refine hi.congr (ae_of_all _ fun x => ?_)
      dsimp only
      rw [mul_pow, ← Real.exp_nat_mul]
      have he : (2 : ℝ) * (-(b * x ^ 2) / 2) = -b * x ^ 2 := by ring
      norm_num only [Nat.cast_ofNat] at *
      rw [he, ← pow_mul, Nat.mul_comm n 2]
    have hs := memLp_finsetSum q.support (fun n hn => (monomial n).const_mul (q.coeff n))
    convert hs using 1
    funext x
    simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul, mul_assoc]
  let polys (j : Fin d) : Polynomial.Sequence ℝ :=
    { elems' := fun n => ((Polynomial.hermite n).map (Int.castRingHom ℝ)).comp
        (Polynomial.C (Real.sqrt 2 / ell j) * Polynomial.X)
      degree_eq' := fun n => by
        rw [Polynomial.degree_comp]
        · rw [Polynomial.degree_map_eq_of_injective (Int.castRingHom ℝ).injective_int,
            Polynomial.degree_hermite, Polynomial.degree_C_mul_X (div_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num)) (hell j).ne')]
          simp
        · rw [Polynomial.degree_C_mul_X (div_ne_zero (Real.sqrt_ne_zero'.2 (by norm_num)) (hell j).ne')]
          norm_num }
  have polyeq (j : Fin d) (n : ℕ) (x : ℝ) :
      (polys j n).eval x = aeval (Real.sqrt 2 * x / ell j) (Polynomial.hermite n) := by
    change (((Polynomial.hermite n).map (Int.castRingHom ℝ)).comp
      (Polynomial.C (Real.sqrt 2 / ell j) * Polynomial.X)).eval x = _
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_map]
    simp only [Polynomial.aeval_def]
    congr 1
    ring
  have gausseq (j : Fin d) (x : ℝ) :
      Real.exp (-(width j * x ^ 2) / 2) = Real.exp (-(x / ell j) ^ 2 / 2) := by
    congr 1
    have hellsq : (ell j) ^ 2 = hbar / (mass j * frequency j) :=
      Real.sq_sqrt (le_of_lt (div_pos hhbar (mul_pos (hmass j) (hfrequency j))))
    rw [div_pow, hellsq]
    dsimp only [width]
    field_simp
  have test_memLp (j : Fin d) (n : ℕ) : MemLp (tests j n) 2 volume := by
    have hp := (polynomial_memLp (width j) (hwidth j) (polys j n)).const_mul
      (Real.sqrt (ell j) * Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹
    apply hp.ofReal.ae_eq
    apply ae_of_all
    intro x
    dsimp only
    rw [polyeq, gausseq]
    change (((Real.sqrt (ell j) * Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))⁻¹ *
      (aeval (Real.sqrt 2 * x / ell j) (Polynomial.hermite n) *
      Real.exp (-(x / ell j) ^ 2 / 2)) : ℝ) : ℂ) = _
    dsimp only [tests]
    simp only [div_eq_inv_mul]
  let vectors (j : Fin d) (n : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
    (test_memLp j n).toLp (tests j n)
  have hdense (j : Fin d) : Dense (Submodule.span ℂ (Set.range (vectors j)) :
      Set (Lp ℂ 2 (volume : Measure ℝ))) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff]
    refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
    rw [Submodule.mem_orthogonal] at hf
    have htest (n : ℕ) : ∫ x : ℝ, tests j n x * f x = 0 := by
      have h := hf (vectors j n) (Submodule.subset_span ⟨n, rfl⟩)
      rw [L2.inner_def] at h
      convert h using 1
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (test_memLp j n)] with x hx
      rw [hx]
      simp only [RCLike.inner_apply', tests, Complex.conj_ofReal]
    have hpair (q : Polynomial ℝ) : Integrable (fun x : ℝ =>
        ((q.eval x : ℝ) : ℂ) * (Real.exp (-(width j * x ^ 2) / 2) : ℂ) * f x) volume := by
      convert (polynomial_memLp (width j) (hwidth j) q).ofReal.integrable_mul (Lp.memLp f) using 1
      funext x
      exact (congrArg (fun z : ℂ => z * f x) (Complex.ofReal_mul (q.eval x) _)).symm
    let A : Polynomial ℝ →ₗ[ℝ] ℂ :=
      { toFun := fun q => ∫ x : ℝ, ((q.eval x : ℝ) : ℂ) *
          (Real.exp (-(width j * x ^ 2) / 2) : ℂ) * f x
        map_add' := fun q r => by
          simp only [Polynomial.eval_add, Complex.ofReal_add, add_mul]
          exact integral_add (hpair q) (hpair r)
        map_smul' := fun c q => by
          simp only [Polynomial.eval_smul, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply]
          simp only [mul_assoc, integral_const_mul, Complex.real_smul] }
    have hAzero : A = 0 := by
      refine LinearMap.ext_on_range
        ((polys j).span fun n => isUnit_iff_ne_zero.2
          (Polynomial.leadingCoeff_ne_zero.mpr ((polys j).ne_zero n))) fun n => ?_
      change (∫ x : ℝ, (((polys j n).eval x : ℝ) : ℂ) *
        (Real.exp (-(width j * x ^ 2) / 2) : ℂ) * f x) = 0
      have hc : 0 < Real.sqrt (ell j) *
          Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) := mul_pos (Real.sqrt_pos.2 (hell j))
        (Real.sqrt_pos.2 (mul_pos (by exact_mod_cast Nat.factorial_pos n) (Real.sqrt_pos.2 Real.pi_pos)))
      have he : (fun x : ℝ => (((polys j n).eval x : ℝ) : ℂ) *
          (Real.exp (-(width j * x ^ 2) / 2) : ℂ) * f x) =
          fun x : ℝ => ((Real.sqrt (ell j) *
            Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) : ℝ) : ℂ) *
            (tests j n x * f x) := by
        funext x
        rw [polyeq, gausseq]
        dsimp only [tests]
        have hd1 : (Real.sqrt (ell j) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (hell j)).ne'
        have hd2 : (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2
            (mul_pos (by exact_mod_cast Nat.factorial_pos n) (Real.sqrt_pos.2 Real.pi_pos))).ne'
        simp only [Complex.ofReal_div, Complex.ofReal_mul]
        field_simp
      rw [he, integral_const_mul, htest, mul_zero]
    have hae := (GaussianPolynomialTotality.gaussian_polynomial_totality
      (width j) (hwidth j) f (Lp.memLp f) (fun q => by
        exact congrArg (fun B : Polynomial ℝ →ₗ[ℝ] ℂ => B q) hAzero)).2
    rw [Lp.ext_iff]
    exact hae.trans (Lp.coeFn_zero ℂ 2 volume).symm

  have setIntegral_eq_zero_of_isPiSystem {ρ : Measure (Fin d → ℝ)}
      {S : Set (Set (Fin d → ℝ))} (hgen : (inferInstance : MeasurableSpace (Fin d → ℝ)) =
        MeasurableSpace.generateFrom S) (hpi : IsPiSystem S) {f : (Fin d → ℝ) → ℂ}
      (hf : Integrable f ρ) (huniv : ∫ x, f x ∂ρ = 0)
      (hS : ∀ s ∈ S, ∫ x in s, f x ∂ρ = 0) :
      ∀ u, MeasurableSet u → ∫ x in u, f x ∂ρ = 0 := by
    refine MeasurableSpace.induction_on_inter (C := fun u _ => ∫ x in u, f x ∂ρ = 0)
      hgen hpi ?_ hS ?_ ?_
    · simp
    · intro u hu ih
      rw [setIntegral_compl hu hf, huniv, ih, sub_zero]
    · intro u hd hm ih
      rw [integral_iUnion hm hd hf.integrableOn]
      simp [ih]
  have memLp_pi_prod {f : Fin d → ℝ → ℂ} (hf : ∀ i, MemLp (f i) 2 (volume : Measure ℝ)) :
      MemLp (fun x : Fin d → ℝ => ∏ i, f i (x i)) 2 ((volume : Measure (Fin d → ℝ))) := by
    have hmeas : AEStronglyMeasurable (fun x : Fin d → ℝ => ∏ i, f i (x i)) ((volume : Measure (Fin d → ℝ))) :=
      Finset.aestronglyMeasurable_fun_prod (f := fun i (x : Fin d → ℝ) => f i (x i)) _ fun i _ =>
        (hf i).aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_eval (fun _ : Fin d => (volume : Measure ℝ)) i)
    rw [memLp_two_iff_integrable_sq_norm hmeas]
    rcases isEmpty_or_nonempty (Fin d) with hι | hι
    · -- With no coordinates the integrand is constant and the product measure is a Dirac mass.
      have : IsProbabilityMeasure ((volume : Measure (Fin d → ℝ))) := by rw [volume_pi_eq_dirac 0]; infer_instance
      simp
    -- Only the submultiplicative bound `‖∏ aᵢ‖ ≤ ∏ ‖aᵢ‖` is needed, so the norm need not be
    -- multiplicative; `Finset.norm_prod_le'` gives it for a nonempty index without `‖1‖ = 1`.
    refine (Integrable.fintype_prod_dep fun i =>
      (memLp_two_iff_integrable_sq_norm (hf i).aestronglyMeasurable).1 (hf i)).mono'
      (hmeas.norm.pow 2) (.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
    gcongr
    exact Finset.norm_prod_le' _ Finset.univ_nonempty _
  let L2piMul (F : Fin d → Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 ((volume : Measure (Fin d → ℝ))) :=
    (memLp_pi_prod (fun i => Lp.memLp (F i))).toLp _
  have coeFn_L2piMul (F : Fin d → Lp ℂ 2 (volume : Measure ℝ)) :
      ⇑(L2piMul F) =ᵐ[(volume : Measure (Fin d → ℝ))] fun x : Fin d → ℝ => ∏ i, F i (x i) :=
    MemLp.coeFn_toLp _
  have coeFn_L2piMul_update (j : Fin d) (F : Fin d → Lp ℂ 2 (volume : Measure ℝ)) (v : Lp ℂ 2 (volume : Measure ℝ)) :
      ⇑(L2piMul (Function.update F j v)) =ᵐ[(volume : Measure (Fin d → ℝ))]
        fun x : Fin d → ℝ => v (x j) * ∏ i ∈ Finset.univ.erase j, F i (x i) := by
    filter_upwards [coeFn_L2piMul (Function.update F j v)] with x hx
    rw [hx, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
    simp +contextual [Finset.prod_congr rfl, Function.update_of_ne]
  have L2piMul_update_add (j : Fin d) (F : Fin d → Lp ℂ 2 (volume : Measure ℝ)) (v w : Lp ℂ 2 (volume : Measure ℝ)) :
      L2piMul (Function.update F j (v + w))
        = L2piMul (Function.update F j v) + L2piMul (Function.update F j w) := by
    rw [Lp.ext_iff]
    filter_upwards [coeFn_L2piMul_update j F (v + w), coeFn_L2piMul_update j F v,
      coeFn_L2piMul_update j F w,
      Lp.coeFn_add (L2piMul (Function.update F j v)) (L2piMul (Function.update F j w)),
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin d => (volume : Measure ℝ)) j).tendsto_ae.eventually (Lp.coeFn_add v w)]
      with x h h1 h2 hadd hv
    rw [h, hadd, Pi.add_apply, h1, h2, hv, Pi.add_apply, add_mul]
  have L2piMul_update_smul (j : Fin d) (F : Fin d → Lp ℂ 2 (volume : Measure ℝ)) (c : ℂ) (v : Lp ℂ 2 (volume : Measure ℝ)) :
      L2piMul (Function.update F j (c • v)) = c • L2piMul (Function.update F j v) := by
    rw [Lp.ext_iff]
    filter_upwards [coeFn_L2piMul_update j F (c • v), coeFn_L2piMul_update j F v,
      Lp.coeFn_smul c (L2piMul (Function.update F j v)),
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin d => (volume : Measure ℝ)) j).tendsto_ae.eventually (Lp.coeFn_smul c v)]
      with x h h1 hsmul hv
    rw [h, hsmul, Pi.smul_apply, h1, hv, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  have inner_L2piMul (F G : Fin d → Lp ℂ 2 (volume : Measure ℝ)) :
      inner ℂ (L2piMul F) (L2piMul G) = ∏ i, inner ℂ (F i) (G i) := by
    rw [L2.inner_def]
    calc
      ∫ x, inner ℂ (L2piMul F x) (L2piMul G x) ∂((volume : Measure (Fin d → ℝ)))
          = ∫ x : Fin d → ℝ, ∏ i, inner ℂ (F i (x i)) (G i (x i)) ∂((volume : Measure (Fin d → ℝ))) := by
            refine integral_congr_ae ?_
            filter_upwards [coeFn_L2piMul F, coeFn_L2piMul G] with x hF hG
            rw [hF, hG]
            simp only [RCLike.inner_apply', map_prod, Finset.prod_mul_distrib]
      _ = ∏ i, ∫ x, inner ℂ (F i x) (G i x) ∂(volume : Measure ℝ) :=
            integral_fintype_prod_eq_prod (fun i x => inner ℂ (F i x) (G i x))
      _ = ∏ i, inner ℂ (F i) (G i) :=
            Finset.prod_congr rfl fun i _ => (L2.inner_def _ _).symm
  have norm_L2piMul (F : Fin d → Lp ℂ 2 (volume : Measure ℝ)) : ‖L2piMul F‖ = ∏ i, ‖F i‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), ← Finset.prod_pow]
    have hh := inner_L2piMul F F
    simp only [inner_self_eq_norm_sq_to_K] at hh
    have hc : ((‖L2piMul F‖ ^ 2 : ℝ) : ℂ) = ((∏ i, ‖F i‖ ^ 2 : ℝ) : ℂ) := by
      convert hh using 1 <;> norm_cast
    exact Complex.ofReal_injective hc
  have norm_L2piMul_update (j : Fin d) (F : Fin d → Lp ℂ 2 (volume : Measure ℝ)) (v : Lp ℂ 2 (volume : Measure ℝ)) :
      ‖L2piMul (Function.update F j v)‖ = (∏ i ∈ Finset.univ.erase j, ‖F i‖) * ‖v‖ := by
    rw [norm_L2piMul, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self, mul_comm]
    simp +contextual [Finset.prod_congr rfl, Function.update_of_ne]
  let L2piMulSlot (j : Fin d) (F : Fin d → Lp ℂ 2 (volume : Measure ℝ)) :
      Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 ((volume : Measure (Fin d → ℝ))) :=
    LinearMap.mkContinuous
      { toFun := fun v => L2piMul (Function.update F j v)
        map_add' := L2piMul_update_add j F
        map_smul' := fun c v => L2piMul_update_smul j F c v }
      (∏ i ∈ Finset.univ.erase j, ‖F i‖) fun v => le_of_eq (norm_L2piMul_update j F v)
  have L2piMulSlot_apply (j : Fin d) (F : Fin d → Lp ℂ 2 (volume : Measure ℝ)) (v : Lp ℂ 2 (volume : Measure ℝ)) :
      L2piMulSlot j F v = L2piMul (Function.update F j v) :=
    LinearMap.mkContinuous_apply _ _ _ _
  have setIntegral_pi_eq_zero_of_forall_inner {h : Lp ℂ 2 ((volume : Measure (Fin d → ℝ)))}
      (hz : ∀ F : Fin d → Lp ℂ 2 (volume : Measure ℝ), inner ℂ (L2piMul F) h = 0)
      (s : Fin d → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) (hfin : ∀ i, (volume : Measure ℝ) (s i) ≠ ⊤) :
      ∫ x in Set.univ.pi s, h x ∂((volume : Measure (Fin d → ℝ))) = 0 := by
    set F : Fin d → Lp ℂ 2 (volume : Measure ℝ) := fun i => indicatorConstLp 2 (hs i) (hfin i) (1 : ℂ)
    have hFc : ∀ᵐ x : Fin d → ℝ ∂((volume : Measure (Fin d → ℝ))),
        ∀ i, F i (x i) = (s i).indicator (fun _ => (1 : ℂ)) (x i) := by
      rw [ae_all_iff]
      exact fun i => (Measure.quasiMeasurePreserving_eval (fun _ : Fin d => (volume : Measure ℝ)) i).tendsto_ae.eventually
        indicatorConstLp_coeFn
    calc ∫ x in Set.univ.pi s, h x ∂((volume : Measure (Fin d → ℝ)))
        = ∫ x, (Set.univ.pi s).indicator (fun y => h y) x ∂((volume : Measure (Fin d → ℝ))) :=
          (integral_indicator (MeasurableSet.univ_pi hs)).symm
      _ = ∫ x, inner ℂ ((L2piMul F) x) (h x) ∂((volume : Measure (Fin d → ℝ))) := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_L2piMul F, hFc] with x hx hF
          classical
          simp [hx, hF, Set.indicator_apply, Fintype.prod_boole]
      _ = inner ℂ (L2piMul F) h := (L2.inner_def _ _).symm
      _ = 0 := hz F
  have setIntegral_inter_univ_pi_spanningSets_eq_zero {h : Lp ℂ 2 ((volume : Measure (Fin d → ℝ)))}
      (hz : ∀ F : Fin d → Lp ℂ 2 (volume : Measure ℝ), inner ℂ (L2piMul F) h = 0) {u : Set (Fin d → ℝ)}
      (hu : MeasurableSet u) (n : ℕ) :
      ∫ x in u ∩ (Set.univ.pi fun i => spanningSets (volume : Measure ℝ) n), h x ∂((volume : Measure (Fin d → ℝ))) = 0 := by
    classical
    have hboxfin : (volume : Measure (Fin d → ℝ)) (Set.univ.pi fun i => spanningSets (volume : Measure ℝ) n) < ⊤ := by
      rw [volume_pi_pi]
      exact ENNReal.prod_lt_top fun i _ => measure_spanningSets_lt_top (volume : Measure ℝ) n
    have huniv : ∫ x, h x ∂(((volume : Measure (Fin d → ℝ))).restrict
        (Set.univ.pi fun i => spanningSets (volume : Measure ℝ) n)) = 0 :=
      setIntegral_pi_eq_zero_of_forall_inner hz _ (fun i => measurableSet_spanningSets (volume : Measure ℝ) n)
        (fun i => (measure_spanningSets_lt_top (volume : Measure ℝ) n).ne)
    have hS : ∀ t ∈ (Set.pi Set.univ '' Set.pi Set.univ fun i => {v : Set ℝ | MeasurableSet v}),
        ∫ x in t, h x ∂(((volume : Measure (Fin d → ℝ))).restrict
          (Set.univ.pi fun i => spanningSets (volume : Measure ℝ) n)) = 0 := by
      rintro _ ⟨t, ht, rfl⟩
      rw [Measure.restrict_restrict
        (MeasurableSet.univ_pi (t := t) fun i => ht i (Set.mem_univ i)), ← Set.pi_inter_distrib]
      exact setIntegral_pi_eq_zero_of_forall_inner hz _
        (fun i => (show MeasurableSet (t i) from ht i (Set.mem_univ i)).inter
          (measurableSet_spanningSets (volume : Measure ℝ) n))
        (fun i => (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
          (measure_spanningSets_lt_top (volume : Measure ℝ) n)).ne)
    have hdyn := setIntegral_eq_zero_of_isPiSystem generateFrom_pi.symm isPiSystem_pi
      (integrableOn_Lp_of_measure_ne_top h one_le_two hboxfin.ne) huniv hS u hu
    rwa [Measure.restrict_restrict hu] at hdyn
  have setIntegral_eq_zero_of_forall_inner_pi {h : Lp ℂ 2 ((volume : Measure (Fin d → ℝ)))}
      (hz : ∀ F : Fin d → Lp ℂ 2 (volume : Measure ℝ), inner ℂ (L2piMul F) h = 0)
      (u : Set (Fin d → ℝ)) (hu : MeasurableSet u) (hfin : (volume : Measure (Fin d → ℝ)) u < ⊤) :
      ∫ x in u, h x ∂((volume : Measure (Fin d → ℝ))) = 0 := by
    have hmono : Monotone fun n => u ∩ (Set.univ.pi fun i => spanningSets (volume : Measure ℝ) n) := fun m n hmn =>
      Set.inter_subset_inter_right _ (Set.pi_mono fun i _ => monotone_spanningSets (volume : Measure ℝ) hmn)
    have hcover : ⋃ n, u ∩ (Set.univ.pi fun i => spanningSets (volume : Measure ℝ) n) = u := by
      rw [← Set.inter_iUnion,
        Set.iUnion_univ_pi_of_monotone fun i => monotone_spanningSets (volume : Measure ℝ)]
      simp [iUnion_spanningSets, Set.pi_univ]
    have htend := tendsto_setIntegral_of_monotone
      (fun n => hu.inter (MeasurableSet.univ_pi fun i => measurableSet_spanningSets (volume : Measure ℝ) n)) hmono
      (by rw [hcover]; exact integrableOn_Lp_of_measure_ne_top h one_le_two hfin.ne)
    rw [hcover] at htend
    simp only [setIntegral_inter_univ_pi_spanningSets_eq_zero hz hu] at htend
    exact tendsto_nhds_unique htend tendsto_const_nhds
  have inner_tests (f : Lp ℂ 2 (volume : Measure (Fin d → ℝ)))
      (hz : ∀ k : Fin d → ℕ, inner ℂ f (L2piMul fun i => vectors i (k i)) = 0)
      (F : Fin d → Lp ℂ 2 (volume : Measure ℝ)) : inner ℂ f (L2piMul F) = 0 := by
    suffices key : ∀ S : Finset (Fin d), ∀ F : Fin d → Lp ℂ 2 (volume : Measure ℝ),
        (∀ i ∉ S, ∃ n, F i = vectors i n) → inner ℂ f (L2piMul F) = 0 from
      key Finset.univ F (by simp)
    intro S
    induction S using Finset.induction with
    | empty =>
        intro F hF
        choose k hk using fun i => hF i (Finset.notMem_empty i)
        simpa [← funext hk] using hz k
    | @insert j S hj ih =>
        intro F hF
        let A := (innerSL ℂ f).comp (L2piMulSlot j F)
        have hA : A = 0 := by
          refine ContinuousLinearMap.ext_on (hdense j) ?_
          rintro v ⟨n, rfl⟩
          change inner ℂ f (L2piMul (Function.update F j (vectors j n))) = 0
          refine ih _ fun i hi => ?_
          rcases eq_or_ne i j with rfl | hij
          · exact ⟨n, Function.update_self ..⟩
          · simpa [hij] using hF i (by simp [hij, hi])
        have hv := congrArg (fun B : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] ℂ => B (F j)) hA
        simpa [A, L2piMulSlot_apply] using hv
  have product_memLp (k : Fin d → ℕ) :
      MemLp (fun x : Fin d → ℝ => ∏ i, tests i (k i) (x i)) 2 volume :=
    memLp_pi_prod (fun i => test_memLp i (k i))
  have physical_eq (k : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) :
      physicalHermite d hbar mass frequency k x = ∏ i, tests i (k i) (x i) := rfl
  constructor
  · intro k
    convert (product_memLp k).comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin d)) using 1
    all_goals rfl
  · intro g hg hz
    let f : Lp ℂ 2 (volume : Measure (Fin d → ℝ)) :=
      (hg.comp_measurePreserving (PiLp.volume_preserving_toLp (Fin d))).toLp
        (fun x => g (toLp 2 x))
    have hf : ⇑f =ᵐ[volume] (fun x => g (toLp 2 x)) := MemLp.coeFn_toLp _
    have hk : ∀ k : Fin d → ℕ, inner ℂ (L2piMul fun i => vectors i (k i)) f = 0 := by
      intro k
      rw [L2.inner_def]
      have hc : ∀ᵐ x : Fin d → ℝ ∂volume, ∀ i, vectors i (k i) (x i) = tests i (k i) (x i) := by
        rw [ae_all_iff]
        exact fun i => (Measure.quasiMeasurePreserving_eval
          (fun _ : Fin d => (volume : Measure ℝ)) i).tendsto_ae.eventually
            (MemLp.coeFn_toLp (test_memLp i (k i)))
      calc
        (∫ x : Fin d → ℝ, inner ℂ ((L2piMul fun i => vectors i (k i)) x) (f x)) =
            ∫ x : Fin d → ℝ, physicalHermite d hbar mass frequency k (toLp 2 x) *
              g (toLp 2 x) := by
          apply integral_congr_ae
          filter_upwards [coeFn_L2piMul (fun i => vectors i (k i)), hc, hf] with x hx hc hf
          rw [hx, hf, physical_eq]
          simp only [hc, RCLike.inner_apply', map_prod]
          have hreal (i : Fin d) : (starRingEnd ℂ) (tests i (k i) (x i)) = tests i (k i) (x i) :=
            Complex.conj_ofReal _
          simp only [hreal]
        _ = ∫ x : EuclideanSpace ℝ (Fin d), physicalHermite d hbar mass frequency k x *
            g x := by
          convert (PiLp.volume_preserving_toLp (Fin d)).integral_comp
            (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
            (fun x => physicalHermite d hbar mass frequency k x * g x) using 1
        _ = 0 := hz k
    have hall : ∀ F : Fin d → Lp ℂ 2 (volume : Measure ℝ), inner ℂ (L2piMul F) f = 0 := by
      intro F
      rw [inner_eq_zero_symm]
      exact inner_tests f (fun k => by rw [inner_eq_zero_symm]; exact hk k) F
    have hae := Lp.ae_eq_zero_of_forall_setIntegral_eq_zero f (by norm_num) (by norm_num)
      (fun s _ hs => integrableOn_Lp_of_measure_ne_top f one_le_two hs.ne)
      (fun s hs hfin => setIntegral_eq_zero_of_forall_inner_pi hall s hs hfin)
    have hcomp := hf.symm.trans hae
    have hback := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.tendsto_ae.eventually hcomp
    change ∀ᵐ x : EuclideanSpace ℝ (Fin d) ∂volume, g x = (0 : ℂ)
    convert hback using 1
    rfl
end D5.S3.Quantum.Analysis.Hermite.PhysicalProductTotality

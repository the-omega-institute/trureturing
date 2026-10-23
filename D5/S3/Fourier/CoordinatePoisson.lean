/- GID: D5/S3/Fourier/CoordinatePoisson
   generality: G
   mirror-B: D5/B/S3/Fourier/CoordinatePoisson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier coefficients of integer periodizations in coordinate volume. -/

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.ContinuousMap.Periodic
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Coordinate integer periodization

The unit cube is a fundamental domain for translation by integer vectors.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators

namespace D5.S3.Fourier.CoordinatePoisson
noncomputable section

variable {n : Type*} [Fintype n]

private abbrev castVector (a : n → ℤ) : n → ℝ := fun i => (a i : ℝ)

local instance integerTranslation : AddAction (n → ℤ) (n → ℝ) where
  vadd a x := castVector a + x
  zero_vadd x := by
    change castVector 0 + x = x
    ext i
    simp [castVector]
  add_vadd a b x := by
    change castVector (a + b) + x = castVector a + (castVector b + x)
    ext i
    simp [castVector, add_assoc]

local instance : ContinuousConstVAdd (n → ℤ) (n → ℝ) where
  continuous_const_vadd _ := continuous_const.add continuous_id

local instance : VAddInvariantMeasure (n → ℤ) (n → ℝ) volume where
  measure_preimage_vadd a s hs :=
    measure_preimage_add (μ := volume) (castVector a) s

private def cube : Set (n → ℝ) := {x | ∀ i, x i ∈ Ioc 0 1}

private lemma cube_fundamental :
    IsAddFundamentalDomain (n → ℤ) (cube : Set (n → ℝ)) volume := by
  refine IsAddFundamentalDomain.mk' ?_ (fun x => ?_)
  · exact (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)).nullMeasurableSet
  · have hi (i : n) : ∃! a : ℤ, (a : ℝ) + x i ∈ Ioc 0 1 := by
      simpa [add_comm] using
        existsUnique_add_zsmul_mem_Ioc (show (0 : ℝ) < 1 by norm_num) (x i) 0
    choose a ha hu using hi
    refine ⟨a, ha, fun b hb => funext (fun i => hu i (b i) (hb i))⟩

private lemma integral_eq_tsum_cube (f : (n → ℝ) → ℂ) (hf : Integrable f) :
    (∫ x, f x) = ∑' a : n → ℤ, ∫ x in cube, f (x + castVector a) := by
  have h := cube_fundamental.integral_eq_tsum'' f hf
  change (∫ x, f x) = ∑' a : n → ℤ, ∫ x in cube, f (castVector a + x) at h
  simpa only [add_comm] using h

private lemma periodic_tsum (f : (n → ℝ) → ℂ) (a : n → ℤ) (x : n → ℝ) :
    (∑' k : n → ℤ, f (x + castVector a + castVector k)) =
      ∑' k : n → ℤ, f (x + castVector k) := by
  convert (Equiv.addLeft a).tsum_eq (fun k : n → ℤ => f (x + castVector k)) using 1
  congr 1
  ext k
  congr 1
  ext i
  simp [castVector, add_assoc]

private lemma periodic_descends (F : C(n → ℝ, ℂ))
    (hF : ∀ (a : n → ℤ) x, F (x + castVector a) = F x) :
    ∃ G : C(UnitAddTorus n, ℂ), ∀ x : n → ℝ, G (fun i => (x i : UnitAddCircle)) = F x := by
  let q : (n → ℝ) → UnitAddTorus n := fun x i => (x i : UnitAddCircle)
  have hq : IsOpenQuotientMap q :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  have hfiber (x y : n → ℝ) (h : q x = q y) : F x = F y := by
    have hi (i : n) : ∃ a : ℤ, (a : ℝ) = x i - y i := by
      have he : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]
        exact congrFun h i
      simpa using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp he
    choose a ha using hi
    have he : y + castVector a = x := by ext i; dsimp [castVector]; linarith [ha i]
    rw [← he, hF a y]
  let G : UnitAddTorus n → ℂ := fun z => F (hq.surjective z).choose
  have he (x : n → ℝ) : G (q x) = F x := by
    exact hfiber _ _ (hq.surjective (q x)).choose_spec
  refine ⟨⟨G, hq.isQuotientMap.continuous_iff.mpr ?_⟩, he⟩
  simpa only [Function.comp_def, he] using F.continuous

private lemma quotient_add_cast (x : n → ℝ) (a : n → ℤ) :
    (fun i => ((x + castVector a) i : UnitAddCircle)) =
      (fun i => (x i : UnitAddCircle)) := by
  funext i
  have ha : ((a i : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨a i, by simp⟩
  simpa [castVector, AddCircle.coe_add, ha]

private lemma mFourier_norm_apply (k : n → ℤ) (x : UnitAddTorus n) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp [UnitAddTorus.mFourier, fourier_apply]

private lemma mFourier_cast (k : n → ℤ) (x : n → ℝ) :
    UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) =
      Complex.exp (-2 * Real.pi * Complex.I * (∑ i, (k i : ℝ) * x i : ℝ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Pi.neg_apply, Int.cast_neg, Complex.ofReal_one, div_one, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_intCast, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- Poisson summation in coordinate volume. Local normal convergence and genuine
integrability justify periodization and its Fourier coefficient integrals. -/
theorem tsum_eq_tsum_integral {f : C(n → ℝ, ℂ)} (hf : Integrable f)
    (hloc : ∀ K : TopologicalSpace.Compacts (n → ℝ),
      Summable (fun a : n → ℤ =>
        ‖(f.comp (ContinuousMap.addRight (fun i => (a i : ℝ)))).restrict K‖))
    (hfourier : Summable (fun k : n → ℤ =>
      ∫ x : n → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
        (∑ i, (k i : ℝ) * x i : ℝ)) * f x)) :
    (∑' a : n → ℤ, f (fun i => (a i : ℝ))) = ∑' k : n → ℤ,
      ∫ x : n → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
        (∑ i, (k i : ℝ) * x i : ℝ)) * f x := by
  let F : C(n → ℝ, ℂ) := ∑' a : n → ℤ, f.comp (ContinuousMap.addRight (castVector a))
  have hsum := ContinuousMap.summable_of_locally_summable_norm hloc
  have hF (x : n → ℝ) : F x = ∑' a : n → ℤ, f (x + castVector a) :=
    (ContinuousMap.tsum_apply hsum x).symm
  obtain ⟨G, hG⟩ := periodic_descends F (fun a x => by simp only [hF]; exact periodic_tsum f a x)
  let K : TopologicalSpace.Compacts (n → ℝ) :=
    ⟨Icc (0 : n → ℝ) 1, isCompact_Icc⟩
  let u : (n → ℤ) → ℝ := fun a =>
    ‖(f.comp (ContinuousMap.addRight (castVector a))).restrict K‖
  have hu : Summable u := hloc K
  have hc : MeasurableSet (cube : Set (n → ℝ)) :=
    MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  have hcb : (cube : Set (n → ℝ)) ⊆ (K : Set (n → ℝ)) := by
    intro x hx
    exact ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
  letI hfinite : IsFiniteMeasure (volume.restrict (cube : Set (n → ℝ))) :=
    isFiniteMeasure_restrict.mpr
      (measure_mono hcb |>.trans_lt K.isCompact.measure_lt_top).ne
  have hbound (a : n → ℤ) (x : n → ℝ) (hx : x ∈ cube) :
      ‖f (x + castVector a)‖ ≤ u a := by
    simpa only [u, ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight] using
      ((f.comp (ContinuousMap.addRight (castVector a))).restrict (K : Set (n → ℝ))).norm_coe_le_norm
        ⟨x, hcb hx⟩
  have hcoeff (k : n → ℤ) : UnitAddTorus.mFourierCoeff G k =
      ∫ x : n → ℝ, Complex.exp (-2 * Real.pi * Complex.I *
        (∑ i, (k i : ℝ) * x i : ℝ)) * f x := by
    let e : (n → ℝ) → ℂ := fun x =>
      UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle))
    have he : Continuous e := by dsimp [e]; fun_prop
    have hen (x : n → ℝ) : ‖e x‖ = 1 := mFourier_norm_apply _ _
    have hei : Integrable (fun x => e x * f x) := by
      apply Integrable.mono' hf.norm
        (he.mul f.continuous).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun x => by simp [norm_mul, hen])
    have heper (a : n → ℤ) (x : n → ℝ) : e (x + castVector a) = e x := by
      exact congrArg (UnitAddTorus.mFourier (-k)) (quotient_add_cast x a)
    have hswap : (∑' a : n → ℤ, ∫ x in cube, e x * f (x + castVector a)) =
        ∫ x in cube, ∑' a : n → ℤ, e x * f (x + castVector a) := by
      apply HasSum.tsum_eq
      apply hasSum_integral_of_dominated_convergence (fun a _ => u a)
      · intro a
        exact (he.mul (f.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
      · intro a
        filter_upwards [ae_restrict_mem hc] with x hx
        simpa only [norm_mul, hen, one_mul] using hbound a x hx
      · exact Filter.Eventually.of_forall (fun _ => hu)
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem hc] with x hx
        exact ((hu.of_norm_bounded (fun a => hbound a x hx)).mul_left (e x)).hasSum
    rw [UnitAddTorus.mFourierCoeff_eq_integral G k 0]
    simp only [Pi.zero_apply, zero_add, smul_eq_mul]
    change (∫ x in cube, e x * G (fun i => (x i : UnitAddCircle))) = _
    simp_rw [hG, hF, ← tsum_mul_left]
    rw [← hswap]
    calc
      _ = ∑' a : n → ℤ, ∫ x in cube, e (x + castVector a) * f (x + castVector a) := by
        simp_rw [heper]
      _ = ∫ x, e x * f x := (integral_eq_tsum_cube (fun x => e x * f x) hei).symm
      _ = _ := by simp only [e, mFourier_cast]
  have hGs : Summable (UnitAddTorus.mFourierCoeff G) := by
    exact hfourier.congr (fun k => (hcoeff k).symm)
  have hrec := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hGs (0 : UnitAddTorus n)
  have hzero : G 0 = ∑' a : n → ℤ, f (castVector a) := by
    convert (hG (0 : n → ℝ)).trans (hF 0) using 1 <;> simp
  rw [← hzero]
  exact hrec.tsum_eq.symm.trans (tsum_congr (fun k => by
    simp only [hcoeff, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Pi.zero_apply, fourier_eval_zero, Finset.prod_const_one, smul_eq_mul, mul_one]))

end
end D5.S3.Fourier.CoordinatePoisson

/- GID: D5/S3/Fourier/TorusOrbitClosure
   generality: G
   mirror-B: D5/B/S3/Fourier/TorusOrbitClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Fourier.AddCircleMulti]
   utility: none
   digest: Integer characters characterize finite torus nonnegative power orbit closures. -/

import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.UrysohnsLemma

namespace D5.S3.Fourier.TorusOrbitClosure

open Set MeasureTheory UnitAddTorus
open scoped BigOperators
noncomputable section

/-- Every finite torus power orbit has exactly the points satisfying its integer character
relations. Haar averaging on the actual compact orbit closure and density of trigonometric
polynomials give the reverse inclusion, including torsion and empty products. -/
theorem result {I : Type*} [Fintype I] (g z : I → Circle) :
    z ∈ closure (range (fun n : ℕ => g ^ n)) ↔
      ∀ k : I → ℤ, (∏ i, (g i) ^ (k i)) = 1 → (∏ i, (z i) ^ (k i)) = 1 := by
  classical
  have hAdd (g z : UnitAddTorus I) :
      z ∈ closure (range (fun n : ℕ => n • g)) ↔
        ∀ k : I → ℤ, mFourier k g = 1 → mFourier k z = 1 := by
    classical
    let χ (k : I → ℤ) : AddChar (UnitAddTorus I) ℂ := {
      toFun := mFourier k
      map_zero_eq_one' := by simp [mFourier]
      map_add_eq_mul' := by
        intro x y
        simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
          zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib] }
    have hc (k : I → ℤ) : Continuous (χ k) := (mFourier k).continuous
    constructor
    · intro hz k hk
      apply closure_minimal (s := range (fun n : ℕ => n • g))
        (t := {w | mFourier k w = 1}) ?_ (isClosed_eq (hc k) continuous_const) hz
      rintro _ ⟨n, rfl⟩
      change χ k (n • g) = 1
      rw [AddChar.map_nsmul_eq_pow, show χ k g = 1 from hk, one_pow]
    · intro hz
      let G := (AddSubgroup.zmultiples g).topologicalClosure
      have hG : (G : Set (UnitAddTorus I)) = closure (range (fun n : ℕ => n • g)) := by
        rw [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_zmultiples,
          closure_range_zsmul_eq_nsmul]
      have hGc : IsClosed (G : Set (UnitAddTorus I)) :=
        (AddSubgroup.zmultiples g).isClosed_topologicalClosure
      have hg : g ∈ G := subset_closure (AddSubgroup.mem_zmultiples g)
      let : CompactSpace G := isCompact_iff_compactSpace.mp hGc.isCompact
      let μ : Measure G := Measure.addHaarMeasure ⊤
      let : IsProbabilityMeasure μ := ⟨by
        exact Measure.addHaarMeasure_self⟩
      let av : C(G, ℂ) →L[ℂ] ℂ :=
        (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)
      have hav (f : C(G, ℂ)) : av f = ∫ x : G, f x ∂μ := by
        change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ f) = _
        rw [← L1.integral_eq', L1.integral_eq_integral]
        exact integral_congr_ae (ContinuousMap.coeFn_toLp μ f)
      let incl : C(G, UnitAddTorus I) := ⟨Subtype.val, continuous_subtype_val⟩
      let shift : C(G, UnitAddTorus I) :=
        ⟨fun x => z + (x : UnitAddTorus I), continuous_const.add continuous_subtype_val⟩
      let A : C(UnitAddTorus I, ℂ) →L[ℂ] ℂ := av.comp (ContinuousMap.compCLM ℂ ℂ incl)
      let B : C(UnitAddTorus I, ℂ) →L[ℂ] ℂ := av.comp (ContinuousMap.compCLM ℂ ℂ shift)
      have hAB : A = B := by
        apply ContinuousLinearMap.ext_on (s := range (mFourier (d := I)))
        · rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
            span_mFourier_closure_eq_top]
          rfl
        · rintro _ ⟨k, rfl⟩
          change av ((mFourier k).comp incl) = av ((mFourier k).comp shift)
          rw [hav, hav]
          change (∫ x : G, χ k x ∂μ) = ∫ x : G, χ k (z + x) ∂μ
          simp_rw [AddChar.map_add_eq_mul]
          rw [integral_const_mul]
          by_cases hk : χ k g = 1
          · rw [show χ k z = 1 from hz k hk, one_mul]
          · have hi := integral_add_left_eq_self (μ := μ)
              (fun x : G => χ k (x : UnitAddTorus I)) (⟨g, hg⟩ : G)
            change (∫ x : G, χ k (g + (x : UnitAddTorus I)) ∂μ) = _ at hi
            simp_rw [AddChar.map_add_eq_mul] at hi
            rw [integral_const_mul] at hi
            have hzero : (∫ x : G, χ k (x : UnitAddTorus I) ∂μ) = 0 := by
              by_contra hne
              exact hk ((mul_eq_right₀ hne).mp hi)
            rw [hzero, mul_zero]
      rw [← hG]
      by_contra hzG
      have hcoset : IsClosed (range shift) := isCompact_range shift.continuous |>.isClosed
      have hdis : Disjoint (G : Set (UnitAddTorus I)) (range shift) := by
        apply disjoint_left.mpr
        rintro w hw ⟨x, rfl⟩
        apply hzG
        have hsub := G.sub_mem hw x.property
        simpa [shift] using hsub
      obtain ⟨f, hf0, hf1, _⟩ := exists_continuous_zero_one_of_isClosed hGc hcoset hdis
      let F : C(UnitAddTorus I, ℂ) :=
        ⟨fun w => (f w : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
      have heq := congrArg (fun L : C(UnitAddTorus I, ℂ) →L[ℂ] ℂ => L F) hAB
      change av (F.comp incl) = av (F.comp shift) at heq
      rw [hav, hav] at heq
      have h0 : (fun x : G => F (incl x)) = fun _ => (0 : ℂ) := by
        funext x
        change (f x : ℂ) = 0
        rw [hf0 x.property]
        rfl
      have h1 : (fun x : G => F (shift x)) = fun _ => (1 : ℂ) := by
        funext x
        change (f (shift x) : ℂ) = 1
        rw [hf1 (mem_range_self x)]
        rfl
      change (∫ x : G, F (incl x) ∂μ) = ∫ x : G, F (shift x) ∂μ at heq
      rw [h0, h1] at heq
      exact zero_ne_one (by
        simpa only [integral_zero, integral_const, probReal_univ, one_smul] using heq)
  -- Coordinatewise circle homeomorphisms preserve powers, characters, and closures.
  let e : UnitAddTorus I ≃ₜ (I → Circle) :=
    Homeomorph.piCongrRight (fun _ => AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)
  have epow (a : UnitAddTorus I) (n : ℕ) : e (n • a) = e a ^ n := by
    ext i
    simp [e, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_nsmul]
  have echar (k : I → ℤ) (a : UnitAddTorus I) :
      mFourier k a = ((∏ i, (e a i) ^ (k i) : Circle) : ℂ) := by
    simp only [mFourier, ContinuousMap.coe_mk, fourier_apply,
      AddCircle.toCircle_zsmul]
    change (∏ i, Circle.coeHom ((AddCircle.toCircle (a i)) ^ k i)) =
      Circle.coeHom (∏ i, (e a i) ^ k i)
    rw [map_prod]
    congr 1
    ext i
    rw [show e a i = AddCircle.toCircle (a i) by
      simp [e, AddCircle.homeomorphCircle_apply]]
  have eclosure (a : UnitAddTorus I) :
      e '' closure (range (fun n : ℕ => n • a)) =
        closure (range (fun n : ℕ => (e a) ^ n)) := by
    rw [e.image_closure, ← range_comp]
    simp only [Function.comp_def, epow]
  have hmem : z ∈ closure (range (fun n : ℕ => g ^ n)) ↔
      e.symm z ∈ closure (range (fun n : ℕ => n • e.symm g)) := by
    rw [← e.apply_symm_apply g, ← eclosure, e.symm_apply_apply]
    constructor
    · rintro ⟨a, ha, haz⟩
      have hza : e.symm z = a := by rw [← haz, e.symm_apply_apply]
      rwa [hza]
    · intro h
      exact ⟨e.symm z, h, e.apply_symm_apply z⟩
  rw [hmem, hAdd]
  have hchar (k : I → ℤ) (w : I → Circle) :
      mFourier k (e.symm w) = 1 ↔ (∏ i, (w i) ^ (k i)) = 1 := by
    rw [echar, e.apply_symm_apply]
    exact Circle.coe_eq_one
  simp only [hchar]

#print axioms result

end

end D5.S3.Fourier.TorusOrbitClosure

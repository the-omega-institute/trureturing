/- GID: D5/S3/Quantum/Analysis/NormalMomentFamily
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NormalMomentFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact full continuous-moment families and scalar normal posterior realizations. -/

/-
admission_basis: escape-witness
escape_witness: compact_normal_posterior_family
compact_normal_posterior_family: proof_shape: content. The derived all-coordinate
norm bound, closed product construction, scalar real Riesz measure and exact
complex mass identity are live prerequisites of its compact measure range and
whole-L1 posterior realization conclusions. Every private helper is consumed
on this route. The concrete closedCarrier instance is used for the actual
inherited C-star algebra and order on M.toStarSubalgebra.
utility none: arbitrary-space analytic construction, without finite enumeration,
numerical certification or a bounded checker.
-/

import D5.S3.Quantum.Analysis.VonNeumannNormalL1
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-! # Full continuous-moment families

The ambient topology is the product, over every complex continuous function,
of the actual weak-star continuous dual. No normality or compactness is part
of the defining data. Scalar measures come from real Riesz representation.
-/

noncomputable section

open Set MeasureTheory
open scoped ComplexOrder Topology CompactlySupported

namespace D5.S3.Quantum.Analysis.NormalMomentFamily

open NormalFunctionals NormalL1Realization

abbrev Interval := Set.Icc (0 : ℝ) 1

/-- The actual posterior coordinate on the closed unit interval. -/
def posterior : C(Interval, ℂ) := ⟨fun t => (t.val : ℂ), by fun_prop⟩

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- All continuous functions, with a weak-star dual coordinate for each. -/
abbrev Ambient (A : Type*) [CStarAlgebra A] := C(Interval, ℂ) → WeakDual ℂ A

/-- Only positivity, complex linearity and the two prescribed moments are data. -/
def Compatible (ρ σ : StrongDual ℂ A) (F : Ambient A) : Prop :=
  (∀ g h a, F (g + h) a = F g a + F h a) ∧
  (∀ (z : ℂ) g a, F (z • g) a = z * F g a) ∧
  (∀ g, (∀ t, 0 ≤ g t) → ∀ a : A, 0 ≤ a → 0 ≤ F g a) ∧
  (∀ a, F 1 a = (ρ + σ) a) ∧ (∀ a, F posterior a = ρ a)

/-- The actual full continuous-moment family, with its induced evaluation topology. -/
def Family (ρ σ : StrongDual ℂ A) := {F : Ambient A // Compatible ρ σ F}

instance (ρ σ : StrongDual ℂ A) : TopologicalSpace (Family ρ σ) :=
  inferInstanceAs (TopologicalSpace {F : Ambient A // Compatible ρ σ F})

/-- Every genuine positive complex-linear map with the prescribed moments is a
point of this full family. No extra boundedness or normality is required. -/
def ofLinearMap {ρ σ : StrongDual ℂ A}
    (J : C(Interval, ℂ) →ₗ[ℂ] StrongDual ℂ A)
    (hp : ∀ g, (∀ t, 0 ≤ g t) → ∀ a : A, 0 ≤ a → 0 ≤ J g a)
    (hu : J 1 = ρ + σ) (ht : J posterior = ρ) : Family ρ σ :=
  ⟨fun g => (J g).toWeakDual,
    (by intro g h a; change J (g + h) a = _; rw [map_add]; rfl),
    (by intro z g a; change J (z • g) a = _; rw [map_smul]; rfl),
    hp, (by intro a; change J 1 a = _; rw [hu]),
    (by intro a; change J posterior a = _; rw [ht])⟩

/-- Recover the genuine complex-linear map from its full coordinate family. -/
def linearMap {ρ σ : StrongDual ℂ A} (F : Family ρ σ) :
    C(Interval, ℂ) →ₗ[ℂ] StrongDual ℂ A where
  toFun g := (F.val g).toStrongDual
  map_add' g h := by ext a; exact F.property.1 g h a
  map_smul' z g := by ext a; exact F.property.2.1 z g a

omit [StarOrderedRing A] in
private theorem positive {ρ σ : StrongDual ℂ A} (F : Family ρ σ) :
    ∀ g, (∀ t, 0 ≤ g t) → ∀ a : A, 0 ≤ a → 0 ≤ linearMap F g a :=
  F.property.2.2.1

omit [StarOrderedRing A] in
theorem unit_value {ρ σ : StrongDual ℂ A} (F : Family ρ σ) :
    linearMap F 1 = ρ + σ := by ext a; exact F.property.2.2.2.1 a

omit [StarOrderedRing A] in
theorem posterior_value {ρ σ : StrongDual ℂ A} (F : Family ρ σ) :
    linearMap F posterior = ρ := by ext a; exact F.property.2.2.2.2 a

private def realMap (u : C(Interval, ℝ)) : C(Interval, ℂ) :=
  ⟨fun t => (u t : ℂ), by fun_prop⟩

private theorem coordinate_bound {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    (g : C(Interval, ℂ)) : ‖linearMap F g‖ ≤ 2 * ‖g‖ * ((ρ + σ) 1).re := by
  let J := linearMap F
  let u : C(Interval, ℝ) := ⟨fun t => max (g t).re 0, by fun_prop⟩
  let v : C(Interval, ℝ) := ⟨fun t => max (-(g t).re) 0, by fun_prop⟩
  let s : C(Interval, ℝ) := ⟨fun t => max (g t).im 0, by fun_prop⟩
  let t : C(Interval, ℝ) := ⟨fun t => max (-(g t).im) 0, by fun_prop⟩
  have hn (w : C(Interval, ℝ)) (hw : ∀ x, 0 ≤ w x) :
      ‖J (realMap w)‖ = (J (realMap w) 1).re :=
    positive_norm_eq_mass _ (positive F _ (fun x => by
      change (0 : ℂ) ≤ (w x : ℂ); exact_mod_cast hw x))
  have he : realMap u - realMap v + Complex.I • (realMap s - realMap t) = g := by
    ext x
    apply Complex.ext <;>
      simp [realMap, u, v, s, t, max_zero_sub_max_neg_zero_eq_self,
        Complex.mul_re, Complex.mul_im]
  have habs (r : ℝ) : max r 0 + max (-r) 0 = |r| := by
    rcases le_total 0 r with hr | hr <;> simp [hr, abs_of_nonneg, abs_of_nonpos]
  have hb (w w' : C(Interval, ℝ)) (hw : ∀ x, w x + w' x ≤ ‖g‖) :
      (J (realMap w) 1).re + (J (realMap w') 1).re ≤
        ‖g‖ * ((ρ + σ) 1).re := by
    have hp : ∀ x, 0 ≤ ((‖g‖ : ℂ) • (1 : C(Interval, ℂ)) -
        (realMap w + realMap w')) x := by
      intro x
      change (0 : ℂ) ≤ (‖g‖ : ℂ) * 1 - ((w x : ℂ) + (w' x : ℂ))
      exact Complex.nonneg_iff.mpr ⟨by simpa using sub_nonneg.mpr (hw x), by simp⟩
    have h := (Complex.nonneg_iff.mp (positive F _ hp 1 zero_le_one)).1
    change 0 ≤ (J _ 1).re at h
    simpa [map_sub, map_add, map_smul, J, unit_value, Complex.mul_re, mul_add] using h
  have huv := hb u v (fun x => by
    change max (g x).re 0 + max (-(g x).re) 0 ≤ ‖g‖
    rw [habs]; exact (Complex.abs_re_le_norm _).trans (g.norm_coe_le_norm x))
  have hst := hb s t (fun x => by
    change max (g x).im 0 + max (-(g x).im) 0 ≤ ‖g‖
    rw [habs]; exact (Complex.abs_im_le_norm _).trans (g.norm_coe_le_norm x))
  calc
    ‖J g‖ = ‖J (realMap u) - J (realMap v) +
        Complex.I • (J (realMap s) - J (realMap t))‖ := by
      rw [← he, map_add, map_sub, map_smul, map_sub]
    _ ≤ ‖J (realMap u)‖ + ‖J (realMap v)‖ +
        (‖J (realMap s)‖ + ‖J (realMap t)‖) := by
      calc
        _ ≤ ‖J (realMap u) - J (realMap v)‖ +
            ‖Complex.I • (J (realMap s) - J (realMap t))‖ := norm_add_le _ _
        _ ≤ _ := by simpa only [norm_smul, Complex.norm_I, one_mul] using
            add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
    _ = (J (realMap u) 1).re + (J (realMap v) 1).re +
        ((J (realMap s) 1).re + (J (realMap t) 1).re) := by
      rw [hn u (fun _ => le_max_right _ _), hn v (fun _ => le_max_right _ _),
        hn s (fun _ => le_max_right _ _), hn t (fun _ => le_max_right _ _)]
    _ ≤ 2 * ‖g‖ * ((ρ + σ) 1).re := by linarith

omit [PartialOrder A] [StarOrderedRing A] in
private theorem continuous_eval (g : C(Interval, ℂ)) (a : A) :
    Continuous (fun F : Ambient A => F g a) :=
  (WeakDual.eval_continuous a).comp (continuous_apply g)

omit [StarOrderedRing A] in
private theorem closed_compatible (ρ σ : StrongDual ℂ A) :
    IsClosed {F : Ambient A | Compatible ρ σ F} := by
  simp only [Compatible, ofPred_and, ofPred_forall]
  refine ((isClosed_iInter fun g => isClosed_iInter fun h => isClosed_iInter fun a =>
    isClosed_eq (continuous_eval _ _) ((continuous_eval _ _).add (continuous_eval _ _))).inter
    ((isClosed_iInter fun z => isClosed_iInter fun g => isClosed_iInter fun a =>
      isClosed_eq (continuous_eval _ _) (continuous_const.mul (continuous_eval _ _))).inter
    ((isClosed_iInter fun g => isClosed_iInter fun _hg => isClosed_iInter fun a =>
      isClosed_iInter fun _ha => isClosed_le continuous_const (continuous_eval _ _)).inter
    ((isClosed_iInter fun a => isClosed_eq (continuous_eval _ _) continuous_const).inter
      (isClosed_iInter fun a => isClosed_eq (continuous_eval _ _) continuous_const)))))

private theorem compact_compatible (ρ σ : StrongDual ℂ A) :
    IsCompact {F : Ambient A | Compatible ρ σ F} := by
  have hc := isCompact_pi_infinite (fun g : C(Interval, ℂ) =>
    WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) (2 * ‖g‖ * ((ρ + σ) 1).re))
  apply hc.of_isClosed_subset (closed_compatible ρ σ)
  intro F hF g
  change dist (F g).toStrongDual 0 ≤ _
  rw [dist_zero_right]
  exact coordinate_bound (⟨F, hF⟩ : Family ρ σ) g

omit [StarOrderedRing A] in
private theorem nonempty_family (ρ σ : StrongDual ℂ A)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a) :
    Nonempty (Family ρ σ) := by
  let J : C(Interval, ℂ) →ₗ[ℂ] StrongDual ℂ A :=
    { toFun g := g ⟨1, by simp⟩ • ρ + g ⟨0, by simp⟩ • σ
      map_add' g h := by
        ext a
        change (g _ + h _) * ρ a + (g _ + h _) * σ a =
          (g _ * ρ a + g _ * σ a) + (h _ * ρ a + h _ * σ a)
        ring
      map_smul' z g := by
        ext a
        change (z * g _) * ρ a + (z * g _) * σ a = z * (g _ * ρ a + g _ * σ a)
        ring }
  refine ⟨ofLinearMap J ?_ ?_ ?_⟩
  · intro g hg a ha
    exact add_nonneg (mul_nonneg (hg _) (hρ a ha)) (mul_nonneg (hg _) (hσ a ha))
  · ext a; change (1 : ℂ) * ρ a + 1 * σ a = _; simp
  · ext a
    change (1 : ℂ) * ρ a + 0 * σ a = _
    simp

private def massFunctional {ρ σ : StrongDual ℂ A} (F : Family ρ σ) :
    C_c(Interval, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun f := (linearMap F (realMap f.toContinuousMap) 1).re
      map_add' f g := by
        have he : realMap (f + g).toContinuousMap =
            realMap f.toContinuousMap + realMap g.toContinuousMap := by ext x; simp [realMap]
        simp only [he, map_add, add_apply, Complex.add_re]
      map_smul' r f := by
        have he : realMap (r • f).toContinuousMap =
            (r : ℂ) • realMap f.toContinuousMap := by ext x; simp [realMap]
        simp only [he, map_smul, smul_apply, smul_eq_mul,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          RingHom.id_apply] }
    (by
      intro f hf
      exact (Complex.nonneg_iff.mp (positive F _ (fun x => by
        change (0 : ℂ) ≤ (f x : ℂ)
        exact_mod_cast hf x) 1 zero_le_one)).1)

/-- The scalar finite regular Riesz measure of the mass functional of the family point. -/
def scalarMeasure {ρ σ : StrongDual ℂ A} (F : Family ρ σ) : Measure Interval :=
  RealRMK.rieszMeasure (massFunctional F)

instance {ρ σ : StrongDual ℂ A} (F : Family ρ σ) : IsFiniteMeasure (scalarMeasure F) :=
  inferInstanceAs (IsFiniteMeasure (RealRMK.rieszMeasure (massFunctional F)))

instance {ρ σ : StrongDual ℂ A} (F : Family ρ σ) : (scalarMeasure F).Regular :=
  inferInstanceAs ((RealRMK.rieszMeasure (massFunctional F)).Regular)

/-- The same measure in Mathlib's genuine topology of weak convergence of finite measures. -/
def finiteMeasure {ρ σ : StrongDual ℂ A} (F : Family ρ σ) : FiniteMeasure Interval :=
  ⟨scalarMeasure F, inferInstance⟩

private theorem integral_real {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    (u : C(Interval, ℝ)) :
    ∫ x, u x ∂scalarMeasure F = (linearMap F (realMap u) 1).re := by
  exact RealRMK.integral_rieszMeasure (massFunctional F)
    (CompactlySupportedContinuousMap.continuousMapEquiv u)

private theorem mass_real_im {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    (u : C(Interval, ℝ)) : (linearMap F (realMap u) 1).im = 0 := by
  let p : C(Interval, ℝ) := ⟨fun x => max (u x) 0, by fun_prop⟩
  let n : C(Interval, ℝ) := ⟨fun x => max (-(u x)) 0, by fun_prop⟩
  have he : realMap u = realMap p - realMap n := by
    ext x
    simp [realMap, p, n, ← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]
  have hi (v : C(Interval, ℝ)) (hv : ∀ x, 0 ≤ v x) :
      (linearMap F (realMap v) 1).im = 0 := by
    exact (Complex.nonneg_iff.mp (positive F _ (fun x => by
      change (0 : ℂ) ≤ (v x : ℂ); exact_mod_cast hv x) 1 zero_le_one)).2.symm
  rw [he, map_sub, sub_apply, Complex.sub_im,
    hi p (fun _ => le_max_right _ _), hi n (fun _ => le_max_right _ _), sub_self]

theorem integral_complex {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    (g : C(Interval, ℂ)) : linearMap F g 1 = ∫ x, g x ∂scalarMeasure F := by
  let u : C(Interval, ℝ) := ⟨fun x => (g x).re, by fun_prop⟩
  let v : C(Interval, ℝ) := ⟨fun x => (g x).im, by fun_prop⟩
  have hi : Integrable g (scalarMeasure F) :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have he : g = realMap u + Complex.I • realMap v := by
    ext x
    change g x = ((g x).re : ℂ) + Complex.I * ((g x).im : ℂ)
    simpa only [mul_comm] using (Complex.re_add_im (g x)).symm
  have hr (w : C(Interval, ℝ)) :
      linearMap F (realMap w) 1 = ((∫ x, w x ∂scalarMeasure F : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa only [Complex.ofReal_re] using (integral_real F w).symm
    · simpa only [Complex.ofReal_im] using mass_real_im F w
  calc
    linearMap F g 1 = linearMap F (realMap u) 1 +
        Complex.I * linearMap F (realMap v) 1 := by
      rw [he, map_add, map_smul]; rfl
    _ = ((∫ x, (g x).re ∂scalarMeasure F : ℝ) : ℂ) +
        ((∫ x, (g x).im ∂scalarMeasure F : ℝ) : ℂ) * Complex.I := by
      rw [hr u, hr v]; exact congrArg₂ (· + ·) rfl (mul_comm _ _)
    _ = ∫ x, g x ∂scalarMeasure F := integral_re_add_im hi

private theorem continuous_finiteMeasure (ρ σ : StrongDual ℂ A) :
    Continuous (finiteMeasure (ρ := ρ) (σ := σ)) := by
  apply FiniteMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro u
  have he : (fun F : Family ρ σ => ∫ x, u x ∂(finiteMeasure F : Measure Interval)) =
      (fun F : Family ρ σ => (linearMap F (realMap u) 1).re) := by
    funext F
    exact integral_real F u
  rw [he]
  exact Complex.continuous_re.comp ((continuous_eval (realMap u) 1).comp continuous_subtype_val)

private theorem total_mass {ρ σ : StrongDual ℂ A} (F : Family ρ σ) :
    (scalarMeasure F) Set.univ = ENNReal.ofReal (((ρ + σ) 1).re) := by
  have h := integral_real F (1 : C(Interval, ℝ))
  have he : realMap (1 : C(Interval, ℝ)) = 1 := by ext x; simp [realMap]
  rw [he, unit_value] at h
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at h
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm.trans (congrArg ENNReal.ofReal h)

private abbrev concreteCStarAlgebra
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : CStarAlgebra M.toStarSubalgebra := inferInstance

attribute [instance] concreteCStarAlgebra

private abbrev concreteStarOrderedRing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) : StarOrderedRing M.toStarSubalgebra := inferInstance

attribute [instance] concreteStarOrderedRing

set_option maxHeartbeats 1200000 in
-- The concrete carrier elaborates inherited C-star and ordered instances throughout.
/-- For an arbitrary concrete von Neumann algebra, the actual full moment family
is nonempty and compact, its Riesz measures vary weakly continuously with compact
range, and every point is realized by a positive normal whole-complex-L1
contraction with both exact posterior moments. The zero pair is included. -/
theorem compact_normal_posterior_family
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (hn : IsOrderNormal (ρ + σ)) :
    IsCompact {F : Ambient M.toStarSubalgebra | Compatible ρ σ F} ∧
    Nonempty (Family ρ σ) ∧
    Continuous (finiteMeasure (ρ := ρ) (σ := σ)) ∧
    IsCompact (Set.range (finiteMeasure (ρ := ρ) (σ := σ))) ∧
    ∀ F : Family ρ σ,
      (scalarMeasure F).Regular ∧
      scalarMeasure F Set.univ = ENNReal.ofReal (((ρ + σ) 1).re) ∧
      (∀ g : C(Interval, ℂ), linearMap F g 1 = ∫ x, g x ∂scalarMeasure F) ∧
      ∃ Γ : (Interval →₁[scalarMeasure F] ℂ) →L[ℂ] StrongDual ℂ M.toStarSubalgebra,
        (∀ g : C(Interval, ℂ), Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ g) =
          linearMap F g) ∧
        (∀ h : Interval →₁[scalarMeasure F] ℂ, IsOrderNormal (Γ h)) ∧
        (∀ h : Interval →₁[scalarMeasure F] ℂ, (∀ᵐ x ∂scalarMeasure F, 0 ≤ h x) →
          ∀ a : M.toStarSubalgebra, 0 ≤ a → 0 ≤ Γ h a) ∧
        (∀ h : Interval →₁[scalarMeasure F] ℂ, Γ h 1 = ∫ x, h x ∂scalarMeasure F) ∧
        ‖Γ‖ ≤ 1 ∧
        Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ posterior) = ρ ∧
        Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ (1 - posterior)) = σ := by
  have hc := compact_compatible ρ σ
  have hcont := continuous_finiteMeasure ρ σ
  have : CompactSpace (Family ρ σ) := isCompact_iff_compactSpace.mp hc
  refine ⟨hc, nonempty_family ρ σ hρ hσ, hcont, isCompact_range hcont, ?_⟩
  intro F
  refine ⟨inferInstance, total_mass F, integral_complex F, ?_⟩
  obtain ⟨Γ, he, hnormal, hp, hm, hb⟩ :=
    exists_normal_L1_extension (scalarMeasure F) (linearMap F) (positive F)
      (by rw [unit_value]; exact hn) (integral_complex F)
  refine ⟨Γ, he, hnormal, hp, hm, hb, ?_, ?_⟩
  · rw [he, posterior_value]
  · rw [he, map_sub, unit_value, posterior_value]
    abel

#print axioms compact_normal_posterior_family

end D5.S3.Quantum.Analysis.NormalMomentFamily

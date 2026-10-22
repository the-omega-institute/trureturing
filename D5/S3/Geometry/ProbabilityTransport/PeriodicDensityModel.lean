/- GID: D5/S3/Geometry/ProbabilityTransport/PeriodicDensityModel
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/PeriodicDensityModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual smooth periodic density and characteristic transport -/
import Mathlib

/-!
# PeriodicDensityModel

Actual smooth periodic density transport on the closed time slab.
-/

set_option maxHeartbeats 2000000


noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace SmoothDensityTransport

abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)
abbrev Euclid (d : ℕ) := EuclideanSpace ℝ (Fin d)

def quotient (d : ℕ) (a : Euclid d) : Torus d := fun i => (a i : UnitAddCircle)

def representative (d : ℕ) (x : Torus d) : Euclid d :=
  WithLp.toLp 2 (fun i => (AddCircle.equivIoc 1 0 (x i)).1)

def basisVector (d : ℕ) (i : Fin d) : Euclid d :=
  WithLp.toLp 2 (Pi.single i (1 : ℝ))

/-- Explicit product of the normalized Haar probabilities, including d = 0. -/
def haar (d : ℕ) : Measure (Torus d) :=
  Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))

def densityMeasure {d : ℕ} (r : Torus d → ℝ) : Measure (Torus d) :=
  (haar d).withDensity (fun x => ENNReal.ofReal (r x))

def liftedGradient {d : ℕ} (f : Torus d → ℝ) (a : Euclid d) : Euclid d :=
  WithLp.toLp 2 (fun i =>
    (fderiv ℝ (fun b : Euclid d => f (quotient d b)) a) (basisVector d i))

def gradient {d : ℕ} (f : Torus d → ℝ) (x : Torus d) : Euclid d :=
  liftedGradient f (representative d x)

def divergence {d : ℕ} (V : Torus d → Euclid d) (x : Torus d) : ℝ :=
  ∑ i : Fin d,
    (fderiv ℝ (fun a : Euclid d => V (quotient d a) i)
      (representative d x)) (basisVector d i)

def laplacian {d : ℕ} (f : Torus d → ℝ) : Torus d → ℝ :=
  divergence (gradient f)

def partition {d : ℕ} (U : Torus d → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, Real.exp (-U x / τ) ∂(haar d)

def gibbs {d : ℕ} (U : Torus d → ℝ) (τ : ℝ) (x : Torus d) : ℝ :=
  (partition U τ)⁻¹ * Real.exp (-U x / τ)

def freeEnergy {d : ℕ} (U : Torus d → ℝ) (τ : ℝ) (r : Torus d → ℝ) : ℝ :=
  (∫ x, U x * r x ∂(haar d)) + τ * (∫ x, r x * Real.log (r x) ∂(haar d))

def densityKL {d : ℕ} (r p : Torus d → ℝ) : ℝ :=
  ∫ x, r x * Real.log (r x / p x) ∂(haar d)

def chemicalPotential {d : ℕ} (U : Torus d → ℝ) (τ : ℝ)
    (ρ : ℝ → Torus d → ℝ) (t : ℝ) (x : Torus d) : ℝ :=
  U x + τ * Real.log (ρ t x)

def velocity {d : ℕ} (U : Torus d → ℝ) (τ : ℝ)
    (ρ : ℝ → Torus d → ℝ) (t : ℝ) (x : Torus d) : Euclid d :=
  -gradient (chemicalPotential U τ ρ t) x

/-- Only the original smooth positive normalized solution data. The two smoothness
fields record joint smoothness up to the closed slab and smooth spatial slices.
No energy derivative, IBP, bounds, transport, or coupling estimate is supplied. -/
structure SmoothFP (d : ℕ) (T τ : ℝ) (U : Torus d → ℝ)
    (ρ : ℝ → Torus d → ℝ) : Prop where
  time_nonnegative : 0 ≤ T
  temperature_positive : 0 < τ
  potential_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Euclid d => U (quotient d a))
  density_smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : ℝ × Euclid d => ρ z.1 (quotient d z.2)) (Icc 0 T ×ˢ univ)
  spatial_smooth : ∀ t ∈ Icc 0 T,
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Euclid d => ρ t (quotient d a))
  density_continuous : ContinuousOn (fun z : ℝ × Torus d => ρ z.1 z.2)
    (Icc 0 T ×ˢ univ)
  positive : ∀ t ∈ Icc 0 T, ∀ x, 0 < ρ t x
  normalized : ∀ t ∈ Icc 0 T, ∫ x, ρ t x ∂(haar d) = 1
  pde : ∀ t ∈ Ioo 0 T, ∀ x,
    HasDerivAt (fun s => ρ s x)
      (divergence (fun y => ρ t y • gradient U y) x + τ * laplacian (ρ t) x) t

end SmoothDensityTransport



noncomputable section
open Set MeasureTheory Topology
open scoped ENNReal
namespace SmoothDensityTransport

local instance haar_probability (d : ℕ) : IsProbabilityMeasure (haar d) := by
  unfold haar
  infer_instance

theorem quotient_isQuotientMap (d : ℕ) : IsQuotientMap (quotient d) := by
  have hp : IsOpenQuotientMap
      (fun a : Fin d → ℝ => fun i => (a i : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
  exact hp.isQuotientMap.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isQuotientMap

theorem continuous_of_lift {d : ℕ} {E : Type*} [TopologicalSpace E]
    {f : Torus d → E} (hf : Continuous (fun a : Euclid d => f (quotient d a))) :
    Continuous f :=
  (quotient_isQuotientMap d).continuous_iff.mpr hf

theorem compact_integrable {d : ℕ} {μ : Measure (Torus d)}
    [IsFiniteMeasure μ] {f : Torus d → ℝ} (hf : Continuous f) : Integrable f μ := by
  simpa only [integrableOn_univ] using
    hf.continuousOn.integrableOn_compact (K := univ) isCompact_univ

private theorem density_slab_positive_bounds {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ) :
    ∃ m M : ℝ, 0 < m ∧
      ∀ t ∈ Icc 0 T, ∀ x, m ≤ ρ t x ∧ ρ t x ≤ M := by
  let K : Set (ℝ × Torus d) := Icc 0 T ×ˢ univ
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hne : K.Nonempty := ⟨(0, 0), ⟨⟨le_rfl, h.time_nonnegative⟩, mem_univ _⟩⟩
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne h.density_continuous
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne h.density_continuous
  refine ⟨ρ a.1 a.2, ρ b.1 b.2, h.positive a.1 ha.1 a.2, ?_⟩
  intro t ht x
  exact ⟨hmin (show (t, x) ∈ K from ⟨ht, mem_univ x⟩),
    hmax (show (t, x) ∈ K from ⟨ht, mem_univ x⟩)⟩

private theorem density_slice_continuous {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Continuous (ρ t) := by
  apply continuousOn_univ.mp
  exact h.density_continuous.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun x _ => ⟨ht, mem_univ x⟩)

private theorem density_eq_tilted_log {d : ℕ} {r : Torus d → ℝ}
    (hr : ∀ x, 0 < r x) (hn : ∫ x, r x ∂haar d = 1) :
    densityMeasure r = (haar d).tilted (fun x => Real.log (r x)) := by
  have he : (fun x => Real.exp (Real.log (r x))) = r :=
    funext (fun x => Real.exp_log (hr x))
  simp only [densityMeasure, Measure.tilted, he, hn, div_one]
  congr 1
  funext x
  rw [Real.exp_log (hr x)]

private theorem gibbs_eq_tilted {d : ℕ} (U : Torus d → ℝ) (τ : ℝ) :
    densityMeasure (gibbs U τ) = (haar d).tilted (fun x => -U x / τ) := by
  unfold densityMeasure Measure.tilted gibbs partition
  congr 1
  funext x
  congr 1
  ring

/-- Actual normalized density measures and actual finite measure KL. This is a
consequence of SmoothFP alone, independent of any flow. -/
theorem gibbs_kl_from_smoothFP {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ) :
    0 < partition U τ ∧ IsProbabilityMeasure (densityMeasure (gibbs U τ)) ∧
    ∀ t ∈ Icc 0 T,
      IsProbabilityMeasure (densityMeasure (ρ t)) ∧
      InformationTheory.klDiv (densityMeasure (ρ t)) (densityMeasure (gibbs U τ)) ≠ ⊤ ∧
      densityKL (ρ t) (gibbs U τ) =
        (InformationTheory.klDiv (densityMeasure (ρ t))
          (densityMeasure (gibbs U τ))).toReal ∧
      freeEnergy U τ (ρ t) = τ * densityKL (ρ t) (gibbs U τ) -
        τ * Real.log (partition U τ) := by
  have hUc : Continuous U := continuous_of_lift h.potential_smooth.continuous
  have hEc : Continuous (fun x => Real.exp (-U x / τ)) := Real.continuous_exp.comp (hUc.neg.div_const τ)
  have hEi : Integrable (fun x => Real.exp (-U x / τ)) (haar d) := compact_integrable hEc
  have hZ : 0 < partition U τ := integral_exp_pos hEi
  have hπ : densityMeasure (gibbs U τ) = (haar d).tilted (fun x => -U x / τ) :=
    gibbs_eq_tilted U τ
  have hπprob : IsProbabilityMeasure (densityMeasure (gibbs U τ)) := by
    rw [hπ]
    exact isProbabilityMeasure_tilted hEi
  letI := hπprob
  refine ⟨hZ, hπprob, ?_⟩
  obtain ⟨m, M, hm, hb⟩ := density_slab_positive_bounds h
  intro t ht
  have hr : ∀ x, 0 < ρ t x := fun x => hm.trans_le (hb t ht x).1
  have hrc : Continuous (ρ t) := density_slice_continuous h ht
  have hlc : Continuous (fun x => Real.log (ρ t x)) := hrc.log (fun x => (hr x).ne')
  have hn : ∫ x, ρ t x ∂haar d = 1 := h.normalized t ht
  have hμ : densityMeasure (ρ t) = (haar d).tilted (fun x => Real.log (ρ t x)) :=
    density_eq_tilted_log hr hn
  have he : (fun x => Real.exp (Real.log (ρ t x))) = ρ t :=
    funext (fun x => Real.exp_log (hr x))
  have hei : Integrable (fun x => Real.exp (Real.log (ρ t x))) (haar d) := by
    rw [he]
    exact compact_integrable hrc
  have hμprob : IsProbabilityMeasure (densityMeasure (ρ t)) := by
    rw [hμ]
    exact isProbabilityMeasure_tilted hei
  letI := hμprob
  have hac0 : densityMeasure (ρ t) ≪ haar d := by
    rw [hμ]
    exact tilted_absolutelyContinuous _ _
  have hac : densityMeasure (ρ t) ≪ densityMeasure (gibbs U τ) := by
    rw [hπ]
    exact hac0.trans (absolutelyContinuous_tilted hEi)
  have hleft : llr (densityMeasure (ρ t)) (haar d) =ᵐ[haar d]
      fun x => Real.log (ρ t x) := by
    rw [hμ]
    have hself : haar d ≪ haar d := Measure.AbsolutelyContinuous.rfl
    filter_upwards [llr_tilted_left hself
      hei hlc.measurable.aemeasurable, llr_self (haar d)] with x hx hx0
    simpa only [he, hn, Real.log_one, sub_zero, hx0, Pi.zero_apply, add_zero] using hx
  have hright : llr (densityMeasure (ρ t)) (densityMeasure (gibbs U τ)) =ᵐ[densityMeasure (ρ t)]
      fun x => U x / τ + Real.log (partition U τ) + Real.log (ρ t x) := by
    rw [hπ]
    filter_upwards [llr_tilted_right hac0 hEi, hac0.ae_le hleft] with x hx hx0
    simpa only [neg_div, neg_neg, hx0, partition] using hx
  have hKc : Continuous (fun x => U x / τ + Real.log (partition U τ) + Real.log (ρ t x)) :=
    ((hUc.div_const τ).add continuous_const).add hlc
  have hlli : Integrable (llr (densityMeasure (ρ t)) (densityMeasure (gibbs U τ)))
      (densityMeasure (ρ t)) := (compact_integrable hKc).congr hright.symm
  have hπpos : ∀ x, 0 < gibbs U τ x := fun x =>
    mul_pos (inv_pos.mpr hZ) (Real.exp_pos _)
  have hlogπ (x : Torus d) : Real.log (gibbs U τ x) =
      -U x / τ - Real.log (partition U τ) := by
    rw [gibbs, Real.log_mul (inv_ne_zero hZ.ne') (Real.exp_pos _).ne',
      Real.log_inv, Real.log_exp]
    ring
  have hratio (x : Torus d) : Real.log (ρ t x / gibbs U τ x) =
      Real.log (ρ t x) + U x / τ + Real.log (partition U τ) := by
    rw [Real.log_div (hr x).ne' (hπpos x).ne', hlogπ]
    ring
  have hllr : llr (densityMeasure (ρ t)) (densityMeasure (gibbs U τ)) =ᵐ[densityMeasure (ρ t)]
      fun x => Real.log (ρ t x / gibbs U τ x) := by
    filter_upwards [hright] with x hx
    rw [hx, hratio]
    ring
  have hpair : (∫ x, Real.log (ρ t x / gibbs U τ x) ∂densityMeasure (ρ t)) =
      densityKL (ρ t) (gibbs U τ) := by
    rw [hμ, integral_tilted]
    simp only [he, hn, div_one, smul_eq_mul, densityKL]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by dsimp; rw [Real.exp_log (hr x)])
  have hreal : (InformationTheory.klDiv (densityMeasure (ρ t))
      (densityMeasure (gibbs U τ))).toReal = densityKL (ρ t) (gibbs U τ) := by
    rw [InformationTheory.toReal_klDiv hac hlli, integral_congr_ae hllr, hpair]
    simp
  refine ⟨hμprob, InformationTheory.klDiv_ne_top hac hlli, hreal.symm, ?_⟩
  have hiA : Integrable (fun x => ρ t x * Real.log (ρ t x)) (haar d) :=
    compact_integrable (hrc.mul hlc)
  have hiB : Integrable (fun x => U x * ρ t x) (haar d) :=
    compact_integrable (hUc.mul hrc)
  have hiC : Integrable (fun x => Real.log (partition U τ) * ρ t x) (haar d) :=
    (compact_integrable hrc).const_mul _
  have hKL : densityKL (ρ t) (gibbs U τ) =
      (∫ x, ρ t x * Real.log (ρ t x) ∂haar d) +
      (∫ x, U x * ρ t x ∂haar d) / τ + Real.log (partition U τ) := by
    unfold densityKL
    calc
      _ = ∫ x, (ρ t x * Real.log (ρ t x) + (U x * ρ t x) / τ) +
          Real.log (partition U τ) * ρ t x ∂haar d := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by dsimp; rw [hratio]; ring)
      _ = _ := by
        have hAB := integral_add hiA (hiB.div_const τ)
        have hABC := integral_add (hiA.add (hiB.div_const τ)) hiC
        dsimp only [Pi.add_apply] at hAB hABC
        rw [hABC, hAB, MeasureTheory.integral_div, integral_const_mul, hn, mul_one]
  rw [hKL]
  unfold freeEnergy
  field_simp [h.temperature_positive.ne']
  <;> ring

end SmoothDensityTransport


noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SmoothDensityTransport

theorem quotient_add (d : ℕ) (a b : Euclid d) :
    quotient d (a + b) = quotient d a + quotient d b := by
  funext i
  exact AddCircle.coe_add 1 (a i) (b i)

theorem quotient_sub (d : ℕ) (a b : Euclid d) :
    quotient d (a - b) = quotient d a - quotient d b := by
  funext i
  exact AddCircle.coe_sub 1 (a i) (b i)

theorem quotient_representative (d : ℕ) (x : Torus d) :
    quotient d (representative d x) = x := by
  funext i
  change (((AddCircle.equivIoc 1 0 (x i)).1 : ℝ) : UnitAddCircle) = x i
  exact AddCircle.coe_equivIoc

/-- Differentiate the exact translation identity in any quotient fibre. No
continuous representative section is used. This helper is consumed below. -/
theorem fderiv_lift_eq_of_quotient_eq {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Torus d → E}
    {a b : Euclid d} (hab : quotient d a = quotient d b) :
    fderiv ℝ (fun z : Euclid d => f (quotient d z)) a =
      fderiv ℝ (fun z : Euclid d => f (quotient d z)) b := by
  let F : Euclid d → E := fun z => f (quotient d z)
  have hshift : (fun z => F (z + (b - a))) = F := by
    funext z
    simp only [F, quotient_add, quotient_sub, hab, sub_self, add_zero]
  have hpoint : a + (b - a) = b := by abel
  have H := congrArg (fun G : Euclid d → E => fderiv ℝ G a) hshift
  rw [fderiv_comp_add_right, hpoint] at H
  exact H.symm

theorem gradient_at_quotient {d : ℕ} {f : Torus d → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n (fun a : Euclid d => f (quotient d a))) (a : Euclid d) :
    gradient f (quotient d a) = liftedGradient f a := by
  have H := fderiv_lift_eq_of_quotient_eq (f := f)
    (a := representative d (quotient d a)) (b := a) (quotient_representative d _)
  unfold gradient liftedGradient
  rw [H]

theorem smooth_gradient_lift {d : ℕ} {f : Torus d → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Euclid d => f (quotient d a))) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Euclid d => gradient f (quotient d a)) := by
  simp_rw [gradient_at_quotient hf]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem continuous_gradient {d : ℕ} {f : Torus d → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Euclid d => f (quotient d a))) :
    Continuous (gradient f) := continuous_of_lift (smooth_gradient_lift hf).continuous

/-- C1 continuity used by the actual Haar integration-by-parts bridge. -/
theorem continuous_gradient_C1 {d : ℕ} {f : Torus d → ℝ}
    (hf : ContDiff ℝ 1 (fun a : Euclid d => f (quotient d a))) :
    Continuous (gradient f) := by
  apply continuous_of_lift
  have hG : Continuous (fun a : Euclid d => liftedGradient f a) := by
    unfold liftedGradient
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
      (continuous_pi (fun i =>
        (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const))
  simpa only [gradient_at_quotient hf] using hG

end SmoothDensityTransport

noncomputable section
open Set MeasureTheory
namespace SmoothDensityTransport
-- Exact existing Mathlib normalized product, with the original quotient pullback.
theorem exact14_haar_pullback {d : ℕ} (g : Torus d → ℝ) :
    (∫ x, g x ∂haar d) =
      ∫ z in {z : Fin d → ℝ | ∀ i, z i ∈ Ioc (0 : ℝ) 1},
        g (quotient d (WithLp.toLp 2 z)) := by
  have H := UnitAddTorus.integral_preimage (d := Fin d) g (fun _ => 0)
  change (∫ x, g x ∂haar d) =
    ∫ z in {z : Fin d → ℝ | ∀ i, z i ∈ Ioc (0 : ℝ) (0 + 1)},
      g (quotient d (WithLp.toLp 2 z)) at H
  simpa only [zero_add] using H
end SmoothDensityTransport

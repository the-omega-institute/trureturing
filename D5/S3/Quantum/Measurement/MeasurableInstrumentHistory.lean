/- GID: D5/S3/Quantum/Measurement/MeasurableInstrumentHistory
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/MeasurableInstrumentHistory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Scalar densities for positive finite-dimensional matrix history measures. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Order.Archimedean

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder ComplexConjugate ENNReal

namespace D5.S3.Quantum.Measurement.MeasurableInstrumentHistory

attribute [local instance] Matrix.normedAddCommGroup
attribute [local instance] Matrix.seminormedAddCommGroup

local instance matrixMeasurableSpace (I : Type*) : MeasurableSpace (Matrix I I ℂ) :=
  inferInstanceAs (MeasurableSpace (I → I → ℂ))

local instance matrixContinuousENorm (I : Type*) [Fintype I] :
    ContinuousENorm (Matrix I I ℂ) :=
  inferInstanceAs (ContinuousENorm (I → I → ℂ))

variable {H I : Type*} [MeasurableSpace H] [Fintype I]

/-- The coordinate measures are the entries of one finite-dimensional matrix-valued
history measure. Its scalar trace measure is specified by the displayed equality. -/
structure PositiveHistoryMeasure (H I : Type*) [MeasurableSpace H] [Fintype I] where
  coordinate : I → I → ComplexMeasure H
  traceMeasure : Measure H
  finite_trace : IsFiniteMeasure traceMeasure
  positive : ∀ s, MeasurableSet s →
    Matrix.PosSemidef (fun i j => coordinate i j s : Matrix I I ℂ)
  trace_eq : ∀ s, MeasurableSet s →
    Matrix.trace (fun i j => coordinate i j s : Matrix I I ℂ) =
      ((traceMeasure s).toReal : ℂ)

variable (M : PositiveHistoryMeasure H I)

/-- A positive matrix-valued history measure has one measurable density against
its scalar trace measure. The same density represents every matrix coordinate. -/
theorem positive_history_density (base : Matrix I I ℂ) (hbase : Matrix.PosSemidef base)
    (hbase_trace : Matrix.trace base = 1) :
    ∃ ρ : H → Matrix I I ℂ,
      Measurable ρ ∧ Integrable ρ M.traceMeasure ∧
      (∀ h, Matrix.PosSemidef (ρ h) ∧ Matrix.trace (ρ h) = 1) ∧
      (∀ s, MeasurableSet s →
        ∀ i j, (∫ h in s, ρ h i j ∂M.traceMeasure) = M.coordinate i j s) ∧
      (∀ f : H → Matrix I I ℂ, Integrable f M.traceMeasure →
        (∀ s, MeasurableSet s →
          ∀ i j, (∫ h in s, f h i j ∂M.traceMeasure) = M.coordinate i j s) →
        f =ᵐ[M.traceMeasure] ρ) := by
  classical
  let : IsFiniteMeasure M.traceMeasure := M.finite_trace
  let ρ : H → Matrix I I ℂ := fun h i j => (M.coordinate i j).rnDeriv M.traceMeasure h
  have hρ : Integrable ρ M.traceMeasure := by
    apply Integrable.of_eval
    intro i
    apply Integrable.of_eval
    intro j
    exact ComplexMeasure.integrable_rnDeriv _ _
  have hcoord : ∀ s, MeasurableSet s →
      ∀ i j, (∫ h in s, ρ h i j ∂M.traceMeasure) = M.coordinate i j s := by
    intro s hs i j
    have hac0 : M.coordinate i j ≪ᵥ M.traceMeasure.toENNRealVectorMeasure := by
      apply VectorMeasure.AbsolutelyContinuous.mk
      intro t ht hzero
      rw [Measure.toENNRealVectorMeasure_apply_measurable ht] at hzero
      have htrace : Matrix.trace (fun a b => M.coordinate a b t : Matrix I I ℂ) = 0 := by
        rw [M.trace_eq t ht, hzero]
        simp
      have hmatrix := (M.positive t ht).trace_eq_zero_iff.mp htrace
      exact congrFun (congrFun hmatrix i) j
    have hac := (ComplexMeasure.absolutelyContinuous_ennreal_iff
      (M.coordinate i j) M.traceMeasure.toENNRealVectorMeasure).mp hac0
    have hre := SignedMeasure.withDensityᵥ_rnDeriv_eq
      ((M.coordinate i j).re) M.traceMeasure hac.1
    have him := SignedMeasure.withDensityᵥ_rnDeriv_eq
      ((M.coordinate i j).im) M.traceMeasure hac.2
    have hre' := congrArg (fun v : SignedMeasure H => v s) hre
    have him' := congrArg (fun v : SignedMeasure H => v s) him
    apply Complex.ext
    · change RCLike.re (∫ h in s, ρ h i j ∂M.traceMeasure) = _
      rw [← integral_re ((hρ.eval i).eval j).integrableOn]
      change (∫ h in s, (M.coordinate i j).re.rnDeriv M.traceMeasure h
        ∂M.traceMeasure) = (M.coordinate i j s).re
      rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs] at hre'
      simpa [ComplexMeasure.re, VectorMeasure.mapRangeₗ,
        VectorMeasure.mapRange_apply, Complex.reCLM_apply] using hre'
    · change RCLike.im (∫ h in s, ρ h i j ∂M.traceMeasure) = _
      rw [← integral_im ((hρ.eval i).eval j).integrableOn]
      change (∫ h in s, (M.coordinate i j).im.rnDeriv M.traceMeasure h
        ∂M.traceMeasure) = (M.coordinate i j s).im
      rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs] at him'
      simpa [ComplexMeasure.im, VectorMeasure.mapRangeₗ,
        VectorMeasure.mapRange_apply, Complex.imCLM_apply] using him'
  have htrace_int : Integrable (fun h => Matrix.trace (ρ h)) M.traceMeasure := by
    change Integrable (fun h => ∑ i : I, ρ h i i) M.traceMeasure
    exact integrable_finsetSum Finset.univ (fun i _ => ((hρ.eval i).eval i))
  have htrace_set : ∀ s, MeasurableSet s → M.traceMeasure s < ∞ →
      (∫ h in s, Matrix.trace (ρ h) ∂M.traceMeasure) =
        ∫ _ in s, (1 : ℂ) ∂M.traceMeasure := by
    intro s hs _
    calc
      (∫ h in s, Matrix.trace (ρ h) ∂M.traceMeasure) =
          ∑ i : I, ∫ h in s, ρ h i i ∂M.traceMeasure := by
            change (∫ h in s, ∑ i : I, ρ h i i ∂M.traceMeasure) = _
            exact integral_finsetSum Finset.univ
              (fun i _ => ((hρ.eval i).eval i).integrableOn)
      _ = Matrix.trace (fun i j => M.coordinate i j s : Matrix I I ℂ) := by
            simp [Matrix.trace, Matrix.diag, hcoord s hs]
      _ = ((M.traceMeasure s).toReal : ℂ) := M.trace_eq s hs
      _ = ∫ _ in s, (1 : ℂ) ∂M.traceMeasure := by
            simp [Measure.real]
  have htrace_ae := htrace_int.ae_eq_of_forall_setIntegral_eq
    (fun h => Matrix.trace (ρ h)) (fun _ => (1 : ℂ))
    (integrable_const _) htrace_set
  have hherm_coord : ∀ i j : I, ∀ᵐ h ∂M.traceMeasure,
      star (ρ h j i) = ρ h i j := by
    intro i j
    have hstar : Integrable (fun h => star (ρ h j i)) M.traceMeasure := by
      have hconj := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
        ((hρ.eval j).eval i))
      change Integrable (fun h => conj (ρ h j i)) M.traceMeasure at hconj
      change Integrable (fun h => conj (ρ h j i)) M.traceMeasure
      exact hconj
    apply hstar.ae_eq_of_forall_setIntegral_eq
      (fun h => star (ρ h j i)) (fun h => ρ h i j) ((hρ.eval i).eval j)
    intro s hs _
    have hpos := (M.positive s hs).isHermitian.eq
    have hij := congrFun (congrFun hpos i) j
    simp only [Complex.star_def, integral_conj, hcoord s hs j i,
      hcoord s hs i j] at *
    exact hij
  have hherm_ae : ∀ᵐ h ∂M.traceMeasure, (ρ h).IsHermitian := by
    have hcoord_all : ∀ᵐ h ∂M.traceMeasure, ∀ i j : I,
        star (ρ h j i) = ρ h i j :=
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (hherm_coord i))
    filter_upwards [hcoord_all] with h hh
    change (ρ h)ᴴ = ρ h
    ext i j
    simpa only [Matrix.conjTranspose_apply] using hh i j
  let Q (q : I → ℂ) (A : Matrix I I ℂ) : ℂ := star q ⬝ᵥ (A *ᵥ q)
  have hQ_exp (q : I → ℂ) (A : Matrix I I ℂ) :
      Q q A = ∑ i : I, ∑ j : I, star (q i) * A i j * q j := by
    simp [Q, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hQ_int (q : I → ℂ) : Integrable (fun h => Q q (ρ h)) M.traceMeasure := by
    simp_rw [hQ_exp]
    apply integrable_finsetSum Finset.univ
    intro i _
    apply integrable_finsetSum Finset.univ
    intro j _
    exact (((hρ.eval i).eval j).const_mul _).mul_const _
  have hQ_set (q : I → ℂ) (s : Set H) (hs : MeasurableSet s) :
      (∫ h in s, Q q (ρ h) ∂M.traceMeasure) =
        Q q (fun i j => M.coordinate i j s) := by
    rw [hQ_exp q (fun i j => M.coordinate i j s)]
    simp_rw [hQ_exp]
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_mul_const, integral_const_mul, hcoord s hs i j]
      · intro j _
        exact ((((hρ.eval i).eval j).const_mul _).mul_const _).integrableOn
    · intro i _
      exact (integrable_finsetSum Finset.univ (fun j _ =>
        (((hρ.eval i).eval j).const_mul _).mul_const _)).integrableOn
  have hQ_re_ae (q : I → ℂ) : ∀ᵐ h ∂M.traceMeasure,
      0 ≤ (Q q (ρ h)).re := by
    have hreal : Integrable (fun h => (Q q (ρ h)).re) M.traceMeasure := by
      exact Complex.reCLM.integrable_comp (hQ_int q)
    apply ae_nonneg_of_forall_setIntegral_nonneg hreal
    intro s hs _
    change 0 ≤ ∫ h in s, RCLike.re (Q q (ρ h)) ∂M.traceMeasure
    rw [integral_re (hQ_int q).integrableOn, hQ_set q s hs]
    exact (M.positive s hs).re_dotProduct_nonneg q
  let rationalComplex : ℚ × ℚ → ℂ :=
    Complex.equivRealProdCLM.symm ∘
      Prod.map (fun r : ℚ => (r : ℝ)) (fun r : ℚ => (r : ℝ))
  let rationalVector : (I → ℚ × ℚ) → (I → ℂ) :=
    Pi.map (fun _ => rationalComplex)
  have hdenseComplex : DenseRange rationalComplex := by
    exact (Complex.equivRealProdCLM.symm.surjective.denseRange).comp
      (Rat.denseRange_cast.prodMap Rat.denseRange_cast)
      Complex.equivRealProdCLM.symm.continuous
  have hdenseVector : DenseRange rationalVector := by
    exact DenseRange.piMap (fun _ => hdenseComplex)
  have hQ_rational : ∀ᵐ h ∂M.traceMeasure,
      ∀ r : I → ℚ × ℚ, 0 ≤ (Q (rationalVector r) (ρ h)).re := by
    exact ae_all_iff.mpr (fun r => hQ_re_ae (rationalVector r))
  have hQ_closed (A : Matrix I I ℂ) :
      IsClosed {q : I → ℂ | 0 ≤ (Q q A).re} := by
    have hstar : Continuous (fun q : I → ℂ => star q) :=
      continuous_pi (fun i => continuous_star.comp (continuous_apply i))
    have hvec : Continuous (fun q : I → ℂ => A *ᵥ q) :=
      continuous_const.matrix_mulVec continuous_id
    have hquad : Continuous (fun q : I → ℂ => Q q A) := by
      simpa only [Q] using hstar.dotProduct hvec
    simpa only [Set.preimage, Set.mem_Ici, Function.comp_apply] using
      (isClosed_Ici.preimage (Complex.continuous_re.comp hquad))
  have hpsd_ae : ∀ᵐ h ∂M.traceMeasure, Matrix.PosSemidef (ρ h) := by
    filter_upwards [hherm_ae, hQ_rational] with h hh hq
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
    intro q
    have hreal : 0 ≤ (Q q (ρ h)).re :=
      hdenseVector.induction_on q (hQ_closed (ρ h)) hq
    apply Complex.nonneg_iff.mpr
    exact ⟨hreal, (hh.im_star_dotProduct_mulVec_self q).symm⟩
  have hgood_ae : ∀ᵐ h ∂M.traceMeasure,
      Matrix.PosSemidef (ρ h) ∧ Matrix.trace (ρ h) = 1 := by
    filter_upwards [hpsd_ae, htrace_ae] with h hp ht
    exact ⟨hp, ht⟩
  have hρ_meas : Measurable ρ := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    change Measurable (fun h =>
      Complex.mk ((M.coordinate i j).re.rnDeriv M.traceMeasure h)
        ((M.coordinate i j).im.rnDeriv M.traceMeasure h))
    have hpair : Measurable (fun h =>
        ((M.coordinate i j).re.rnDeriv M.traceMeasure h,
          (M.coordinate i j).im.rnDeriv M.traceMeasure h)) :=
      (SignedMeasure.measurable_rnDeriv _ _).prodMk
        (SignedMeasure.measurable_rnDeriv _ _)
    exact Complex.equivRealProdCLM.symm.continuous.measurable.comp hpair
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hgood_ae)
  let clean : H → Matrix I I ℂ := fun h => if h ∈ N then base else ρ h
  have hclean_meas : Measurable clean :=
    Measurable.ite hNmeas measurable_const hρ_meas
  have hclean_ae : clean =ᵐ[M.traceMeasure] ρ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNzero] with h hh
    simp only [clean, if_neg hh]
  have hclean_int : Integrable clean M.traceMeasure := hρ.congr hclean_ae.symm
  have hclean_good (h : H) : Matrix.PosSemidef (clean h) ∧
      Matrix.trace (clean h) = 1 := by
    by_cases hh : h ∈ N
    · simpa only [clean, if_pos hh] using And.intro hbase hbase_trace
    · have hg : Matrix.PosSemidef (ρ h) ∧ Matrix.trace (ρ h) = 1 := by
        by_contra hbad
        exact hh (hNsub hbad)
      simpa only [clean, if_neg hh] using hg
  have hclean_coord : ∀ s, MeasurableSet s →
      ∀ i j, (∫ h in s, clean h i j ∂M.traceMeasure) = M.coordinate i j s := by
    intro s hs i j
    calc
      (∫ h in s, clean h i j ∂M.traceMeasure) =
          ∫ h in s, ρ h i j ∂M.traceMeasure := by
            apply integral_congr_ae
            exact ae_restrict_of_ae (hclean_ae.mono fun h heq =>
              congrFun (congrFun heq i) j)
      _ = M.coordinate i j s := hcoord s hs i j
  refine ⟨clean, hclean_meas, hclean_int, hclean_good, hclean_coord, ?_⟩
  intro f hf hfcoord
  have hentry : ∀ i j : I, (fun h => f h i j) =ᵐ[M.traceMeasure]
      (fun h => clean h i j) := by
    intro i j
    exact ((hf.eval i).eval j).ae_eq_of_forall_setIntegral_eq
      (fun h => f h i j) (fun h => clean h i j) ((hclean_int.eval i).eval j)
      (fun s hs _ => by rw [hfcoord s hs i j, hclean_coord s hs i j])
  have hall : ∀ᵐ h ∂M.traceMeasure, ∀ i j : I, f h i j = clean h i j :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hentry i))
  filter_upwards [hall] with h hh
  funext i j
  exact hh i j

/-- The scalar reference measure is forced by positivity of the coordinate
history measure; it is not independent protocol data. -/
theorem positive_history_density_from_coordinates
    (coordinate : I → I → ComplexMeasure H)
    (hpositive : ∀ s, MeasurableSet s →
      Matrix.PosSemidef (fun i j => coordinate i j s : Matrix I I ℂ))
    (base : Matrix I I ℂ) (hbase : Matrix.PosSemidef base)
    (hbase_trace : Matrix.trace base = 1) :
    ∃ μ : Measure H, IsFiniteMeasure μ ∧
      (∀ s, MeasurableSet s →
        Matrix.trace (fun i j => coordinate i j s : Matrix I I ℂ) =
          ((μ s).toReal : ℂ)) ∧
      ∃ ρ : H → Matrix I I ℂ,
        Measurable ρ ∧ Integrable ρ μ ∧
        (∀ h, Matrix.PosSemidef (ρ h) ∧ Matrix.trace (ρ h) = 1) ∧
        (∀ s, MeasurableSet s →
          ∀ i j, (∫ h in s, ρ h i j ∂μ) = coordinate i j s) ∧
        (∀ f : H → Matrix I I ℂ, Integrable f μ →
          (∀ s, MeasurableSet s →
            ∀ i j, (∫ h in s, f h i j ∂μ) = coordinate i j s) →
          f =ᵐ[μ] ρ) := by
  classical
  let τ : SignedMeasure H := ∑ i : I, (coordinate i i).re
  have hτ (s : Set H) :
      τ s = (Matrix.trace (fun i j => coordinate i j s : Matrix I I ℂ)).re := by
    calc
      τ s = ∑ i : I, (coordinate i i).re s := by simp [τ]
      _ = ∑ i : I, (coordinate i i s).re := by
        apply Finset.sum_congr rfl
        intro i _
        simp [ComplexMeasure.re, VectorMeasure.mapRangeₗ,
          VectorMeasure.mapRange_apply]
      _ = (Matrix.trace (fun i j => coordinate i j s : Matrix I I ℂ)).re := by
        simp [Matrix.trace, Matrix.diag, Complex.re_sum]
  have hτ_nonneg : 0 ≤[Set.univ] τ := by
    apply (VectorMeasure.restrict_le_restrict_iff
      (0 : SignedMeasure H) τ MeasurableSet.univ).2
    intro s hs _
    have hp := (hpositive s hs).trace_nonneg
    simpa [hτ s] using (Complex.nonneg_iff.mp hp).1
  let μ : Measure H :=
    τ.toMeasureOfZeroLE Set.univ MeasurableSet.univ hτ_nonneg
  have hμfinite : IsFiniteMeasure μ := by
    constructor
    simp [μ, SignedMeasure.toMeasureOfZeroLE_apply τ hτ_nonneg
      MeasurableSet.univ MeasurableSet.univ]
  have htrace (s : Set H) (hs : MeasurableSet s) :
      Matrix.trace (fun i j => coordinate i j s : Matrix I I ℂ) =
        ((μ s).toReal : ℂ) := by
    have hp := (hpositive s hs).trace_nonneg
    have hre :
        (Matrix.trace (fun i j => coordinate i j s : Matrix I I ℂ)).re = μ.real s := by
      rw [← hτ s]
      simpa [μ] using (τ.toMeasureOfZeroLE_real_apply hτ_nonneg
        MeasurableSet.univ hs).symm
    apply Complex.ext
    · simpa [Measure.real] using hre
    · simpa using (Complex.nonneg_iff.mp hp).2.symm
  let M : PositiveHistoryMeasure H I :=
    { coordinate := coordinate
      traceMeasure := μ
      finite_trace := hμfinite
      positive := hpositive
      trace_eq := htrace }
  obtain ⟨ρ, hmeas, hint, hgood, hcoord, hinvariant⟩ :=
    positive_history_density M base hbase hbase_trace
  exact ⟨μ, hμfinite, htrace, ρ, hmeas, hint, hgood, hcoord, hinvariant⟩

#print axioms positive_history_density
#print axioms positive_history_density_from_coordinates

end D5.S3.Quantum.Measurement.MeasurableInstrumentHistory

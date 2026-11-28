/- GID: D5/S3/LatticeGauge/TransferOperator
   generality: G
   mirror-B: none(waiver:covered-by-lattice-reflection-positivity4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The OS separation quotient, boundary reduction, and the one-step Wilson operator. -/

import D5.S3.LatticeGauge.ReflectionPositivity
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
Omega original.

The OS separation quotient, boundary reduction, and the one-step Wilson operator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Matrix Filter

namespace Omega.LatticeGauge

noncomputable section

section Transfer

variable {X : Type*} [MeasurableSpace X]

/-- The complex vector space of Bochner-integrable boundary observables. -/
def integrableObservables (μ : Measure X) : Submodule ℂ (X → ℂ) where
  carrier := {f | Integrable f μ}
  zero_mem' := integrable_zero X ℂ μ
  add_mem' hf hg := Integrable.add hf hg
  smul_mem' c _ hf := Integrable.smul c hf

/-- A bounded, measurable, symmetric real boundary kernel. -/
structure BoundaryKernel (X : Type*) [MeasurableSpace X] where
  toFun : X × X → ℝ
  measurable : Measurable toFun
  bound : ℝ
  norm_le : ∀ p, ‖toFun p‖ ≤ bound
  symm : ∀ x y, toFun (x, y) = toFun (y, x)

variable {μ : Measure X}

theorem observable_integrable (f : integrableObservables μ) : Integrable f.1 μ := f.property

private theorem conj_integrable (f : integrableObservables μ) :
    Integrable (fun x => conj (f.1 x)) μ :=
  Complex.conjCLE.toContinuousLinearMap.integrable_comp (observable_integrable f)

variable [IsFiniteMeasure μ] (K : BoundaryKernel X)

omit [IsFiniteMeasure μ] in
private theorem kernel_section (f : integrableObservables μ) (x : X) :
    Integrable (fun y => (K.toFun (x, y) : ℂ) * f.1 y) μ :=
  (observable_integrable f).bdd_mul
    (K.measurable.comp (measurable_const.prodMk measurable_id)).complex_ofReal.aestronglyMeasurable
    (ae_of_all _ fun y => by simpa using K.norm_le (x, y))

private def transferFun (f : integrableObservables μ) (x : X) : ℂ :=
  ∫ y, (K.toFun (x, y) : ℂ) * f.1 y ∂μ

omit [IsFiniteMeasure μ] in
private theorem transferFun_bound (f : integrableObservables μ) (x : X) :
    ‖transferFun K f x‖ ≤ K.bound * ∫ y, ‖f.1 y‖ ∂μ := calc
  _ ≤ ∫ y, ‖(K.toFun (x, y) : ℂ) * f.1 y‖ ∂μ := norm_integral_le_integral_norm _
  _ ≤ ∫ y, K.bound * ‖f.1 y‖ ∂μ := integral_mono
    (kernel_section K f x).norm ((observable_integrable f).norm.const_mul _) fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (by simpa using K.norm_le (x, y)) (norm_nonneg _)
  _ = _ := integral_const_mul _ _

private theorem transferFun_meas (f : integrableObservables μ) :
    AEStronglyMeasurable (transferFun K f) μ :=
  (K.measurable.complex_ofReal.aestronglyMeasurable.mul
    (observable_integrable f).aestronglyMeasurable.comp_snd).integral_prod_right'

/-- The one-step integral operator on integrable boundary observables. -/
def boundaryTransfer : integrableObservables μ →ₗ[ℂ] integrableObservables μ where
  toFun f := ⟨transferFun K f, (integrable_const (K.bound * ∫ y, ‖f.1 y‖ ∂μ)).mono'
    (transferFun_meas K f) (ae_of_all _ (transferFun_bound K f))⟩
  map_add' f g := Subtype.ext <| funext fun x => by
    change transferFun K (f + g) x = transferFun K f x + transferFun K g x
    simpa only [transferFun, Submodule.coe_add, Pi.add_apply, mul_add] using
      integral_add (kernel_section K f x) (kernel_section K g x)
  map_smul' c f := Subtype.ext <| funext fun x => by
    change transferFun K (c • f) x = c * transferFun K f x
    simp only [transferFun, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
      integral_const_mul]

/-- The unnormalized Osterwalder–Schrader pairing on the boundary. -/
def osPair (f g : integrableObservables μ) : ℂ :=
  ∫ x, conj (f.1 x) * (boundaryTransfer K g).1 x ∂μ

private theorem pairing_integrable (f g : integrableObservables μ) :
    Integrable (fun x => conj (f.1 x) * (boundaryTransfer K g).1 x) μ :=
  (conj_integrable f).mul_bdd (transferFun_meas K g) (ae_of_all _ (transferFun_bound K g))

omit [IsFiniteMeasure μ] in
private theorem kernel_integrable (f g : integrableObservables μ) :
    Integrable (fun p : X × X => (K.toFun p : ℂ) * (conj (f.1 p.1) * g.1 p.2)) (μ.prod μ) :=
  ((conj_integrable f).mul_prod (observable_integrable g)).bdd_mul
    K.measurable.complex_ofReal.aestronglyMeasurable
    (ae_of_all _ fun p => by simpa using K.norm_le p)

private theorem osPair_integral_prod (f g : integrableObservables μ) :
    osPair K f g = ∫ p : X × X, (K.toFun p : ℂ) * (conj (f.1 p.1) * g.1 p.2) ∂μ.prod μ := by
  rw [integral_prod _ (kernel_integrable K f g)]
  apply integral_congr_ae (ae_of_all _ fun x => ?_)
  change conj (f.1 x) * transferFun K g x = _
  rw [transferFun, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

private theorem osPair_flip (f g : integrableObservables μ) :
    osPair K f g = ∫ y, conj ((boundaryTransfer K f).1 y) * g.1 y ∂μ := by
  rw [osPair_integral_prod K f g, integral_prod_symm _ (kernel_integrable K f g)]
  apply integral_congr_ae (ae_of_all _ fun y => ?_)
  change _ = conj (transferFun K f y) * g.1 y
  rw [transferFun, ← integral_conj, ← integral_mul_const]
  apply integral_congr_ae (ae_of_all _ fun x => ?_)
  rw [K.symm x y, map_mul, Complex.conj_ofReal, mul_assoc]

private theorem osPair_hermitian (f g : integrableObservables μ) :
    conj (osPair K g f) = osPair K f g := by
  rw [osPair_flip K f g, osPair, ← integral_conj]
  exact integral_congr_ae (ae_of_all _ fun x => by simp [mul_comm])

variable (hK : ∀ f : integrableObservables μ, 0 ≤ (osPair K f f).re)

@[instance_reducible] private def osCore : PreInnerProductSpace.Core ℂ (integrableObservables μ) where
  inner := osPair K
  conj_inner_symm := osPair_hermitian K
  re_inner_nonneg := hK
  add_left f g h := by
    simpa only [osPair, Submodule.coe_add, Pi.add_apply, map_add, add_mul] using
      integral_add (pairing_integrable K f h) (pairing_integrable K g h)
  smul_left f g c := by
    simp only [osPair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc,
      integral_const_mul]

include hK in
theorem os_cauchy_schwarz (f g : integrableObservables μ) :
    ‖osPair K f g‖ ^ 2 ≤ (osPair K f f).re * (osPair K g g).re := by
  let := osCore K hK
  have h := InnerProductSpace.Core.inner_mul_inner_self_le f g (𝕜 := ℂ)
  rw [← InnerProductSpace.Core.norm_inner_symm f g (𝕜 := ℂ), ← sq] at h
  exact h

private theorem osPair_transfer (f g : integrableObservables μ) :
    osPair K f (boundaryTransfer K g) = osPair K (boundaryTransfer K f) g := by
  rw [osPair_flip K f (boundaryTransfer K g)]
  rfl

@[instance_reducible] private def osSeminormed : SeminormedAddCommGroup (integrableObservables μ) :=
  letI := osCore K hK
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

@[instance_reducible] private def osInner : @InnerProductSpace ℂ (integrableObservables μ) _ (osSeminormed K hK) :=
  InnerProductSpace.ofCore (osCore K hK)

private abbrev osTopology : TopologicalSpace (integrableObservables μ) :=
  (osSeminormed K hK).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The OS pre-Hilbert space, obtained by quotienting by inseparability in the OS seminorm. -/
def physicalSpace := @SeparationQuotient (integrableObservables μ) (osTopology K hK)

instance : NormedAddCommGroup (physicalSpace K hK) :=
  @SeparationQuotient.instNormedAddCommGroup _ (osSeminormed K hK)

instance : InnerProductSpace ℂ (physicalSpace K hK) :=
  @SeparationQuotient.instInnerProductSpace ℂ _ _ (osSeminormed K hK) (osInner K hK)

private theorem transfer_inseparable :
    letI := osTopology K hK
    ∀ f g : integrableObservables μ, Inseparable f g →
      Inseparable (boundaryTransfer K f) (boundaryTransfer K g) := by
  let := osSeminormed K hK
  let := osInner K hK
  intro f g h
  have hn : ‖f - g‖ = 0 := by simpa [dist_eq_norm] using h.dist_eq_zero
  have hzero : (osPair K (f - g) (f - g)).re = 0 := by
    change RCLike.re (inner ℂ (f - g) (f - g)) = 0
    rw [← InnerProductSpace.norm_sq_eq_re_inner, hn, zero_pow (by decide : 2 ≠ 0)]
  apply Metric.inseparable_iff.mpr
  rw [dist_eq_norm, ← map_sub]
  suffices hs : ‖boundaryTransfer K (f - g)‖ ^ 2 = 0 by nlinarith
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (osPair K (boundaryTransfer K (f - g)) (boundaryTransfer K (f - g))).re = 0
  rw [← osPair_transfer]
  have hc := os_cauchy_schwarz K hK (f - g) (boundaryTransfer K (boundaryTransfer K (f - g)))
  rw [hzero, zero_mul] at hc
  have hz : osPair K (f - g) (boundaryTransfer K (boundaryTransfer K (f - g))) = 0 :=
    norm_eq_zero.mp (by nlinarith)
  rw [hz, Complex.zero_re]

/-- The quotient map from boundary representatives to the physical space. -/
def physicalClass (f : integrableObservables μ) : physicalSpace K hK :=
  @SeparationQuotient.mk _ (osTopology K hK) f

theorem norm_physicalClass (f : integrableObservables μ) :
    ‖physicalClass K hK f‖ = Real.sqrt (osPair K f f).re := rfl

private theorem physicalClass_ae {f g : integrableObservables μ}
    (h : f.1 =ᵐ[μ] g.1) : physicalClass K hK f = physicalClass K hK g := by
  let := osSeminormed K hK
  apply (@SeparationQuotient.mk_eq_mk _ (osTopology K hK) f g).mpr
  apply Metric.inseparable_iff.mpr
  rw [dist_eq_norm]
  have hz : (boundaryTransfer K (f - g)).1 = 0 := by
    funext x
    change (∫ y, (K.toFun (x, y) : ℂ) * (f.1 y - g.1 y) ∂μ) = 0
    rw [← integral_zero]
    exact integral_congr_ae (h.mono fun y hy => by simp [hy])
  change Real.sqrt (osPair K (f - g) (f - g)).re = 0
  rw [osPair, hz]
  simp

theorem physicalClass_surjective : Function.Surjective (physicalClass K hK) :=
  @SeparationQuotient.surjective_mk _ (osTopology K hK)

/-- The integral transfer operator descends to the OS pre-Hilbert space. -/
def physicalTransfer : physicalSpace K hK →ₗ[ℂ] physicalSpace K hK := by
  letI := osTopology K hK
  let T := SeparationQuotient.lift (fun f => physicalClass K hK (boundaryTransfer K f))
    (fun f g h => SeparationQuotient.mk_eq_mk.mpr (transfer_inseparable K hK f g h))
  exact ⟨⟨T, Quotient.ind₂ fun f g => congrArg (physicalClass K hK)
      (map_add (boundaryTransfer K) f g)⟩,
    fun c => Quotient.ind fun f => congrArg (physicalClass K hK) ((boundaryTransfer K).map_smul c f)⟩

theorem physical_transfer_square (f : integrableObservables μ) :
    (inner ℂ (physicalClass K hK f) (physicalTransfer K hK (physicalClass K hK f))).re =
      ∫ x, ‖(boundaryTransfer K f).1 x‖ ^ 2 ∂μ := by
  change (osPair K f (boundaryTransfer K f)).re = _
  rw [osPair_flip]
  let g := boundaryTransfer K f
  have hi := (conj_integrable g).mul_bdd (transferFun_meas K f) (ae_of_all _ (transferFun_bound K f))
  change RCLike.re (∫ x, conj (g.1 x) * transferFun K f x ∂μ) = _
  rw [← integral_re hi]
  apply integral_congr_ae (ae_of_all _ fun x => ?_)
  change (conj (g.1 x) * g.1 x).re = ‖g.1 x‖ ^ 2
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

section Fiber

variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]

private def pullbackKernel : BoundaryKernel (X × Y) where
  toFun p := K.toFun (p.1.1, p.2.1)
  measurable := K.measurable.comp (by fun_prop)
  bound := K.bound
  norm_le p := K.norm_le (p.1.1, p.2.1)
  symm p q := K.symm p.1 q.1

private def boundaryMarginal (f : integrableObservables (μ.prod ν)) : integrableObservables μ :=
  ⟨fun x => ∫ y, f.1 (x, y) ∂ν, (observable_integrable f).integral_prod_left⟩

private theorem transfer_pullback (f : integrableObservables (μ.prod ν)) (x : X × Y) :
    transferFun (pullbackKernel K) f x = transferFun K (boundaryMarginal ν f) x.1 := by
  rw [transferFun, integral_prod _ (kernel_section (pullbackKernel K) f x)]
  apply integral_congr_ae (ae_of_all _ fun y => ?_)
  change (∫ z, (K.toFun (x.1, y) : ℂ) * f.1 (y, z) ∂ν) =
    (K.toFun (x.1, y) : ℂ) * ∫ z, f.1 (y, z) ∂ν
  exact integral_const_mul _ _

private theorem osPair_pullback (f g : integrableObservables (μ.prod ν)) :
    osPair (pullbackKernel K) f g = osPair K (boundaryMarginal ν f) (boundaryMarginal ν g) := by
  rw [osPair, integral_prod _ (pairing_integrable (pullbackKernel K) f g)]
  apply integral_congr_ae (ae_of_all _ fun x => ?_)
  change (∫ y, conj (f.1 (x, y)) * transferFun (pullbackKernel K) g (x, y) ∂ν) =
    conj (∫ y, f.1 (x, y) ∂ν) * transferFun K (boundaryMarginal ν g) x
  simp_rw [transfer_pullback K ν]
  rw [integral_mul_const, integral_conj]

omit [IsFiniteMeasure μ] in
private def weightObservable (w : X × Y → ℝ) (hw : Measurable w)
    {M : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) (f : integrableObservables (μ.prod ν)) :
    integrableObservables (μ.prod ν) :=
  ⟨fun p => (w p : ℂ) * f.1 p,
    (observable_integrable f).bdd_mul hw.complex_ofReal.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa using hb p)⟩

variable [IsProbabilityMeasure ν]

omit [IsFiniteMeasure μ] in
private theorem weightedBoundaryMarginal_surjective (w : X × Y → ℝ) (hw : Measurable w)
    {M N : ℝ} (hb : ∀ p, ‖w p‖ ≤ M) (hInv : ∀ p, ‖(w p)⁻¹‖ ≤ N)
    (h0 : ∀ p, w p ≠ 0) :
    Function.Surjective (fun f => boundaryMarginal ν (weightObservable ν w hw hb f :
      integrableObservables (μ.prod ν))) := by
  intro g
  have hg : Integrable (fun p : X × Y => g.1 p.1) (μ.prod ν) := by
    simpa using (observable_integrable g).mul_prod (integrable_const (μ := ν) (1 : ℂ))
  refine ⟨weightObservable ν (fun p => (w p)⁻¹) hw.inv hInv ⟨_, hg⟩, Subtype.ext ?_⟩
  funext x
  change (∫ y, (w (x, y) : ℂ) * ((((w (x, y))⁻¹ : ℝ) : ℂ) * g.1 x) ∂ν) = g.1 x
  have he (y : Y) : (w (x, y) : ℂ) * (((w (x, y))⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (h0 (x, y)), Complex.ofReal_one]
  rw [show (fun y => (w (x, y) : ℂ) * ((((w (x, y))⁻¹ : ℝ) : ℂ) * g.1 x)) =
    (fun _ : Y => g.1 x) from funext fun y => by rw [← mul_assoc, he, one_mul]]
  simp

end Fiber

end Transfer

end

variable {n : Fin 4 → ℕ} {G : Type*} [Group G] {d : ℕ}
variable [MeasurableSpace G]

noncomputable section

private theorem probability_invInvariant {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] (μ : Measure G)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] : μ.IsInvInvariant := by
  have h : MeasurePreserving (fun q : G × G => q.1⁻¹ * q.2) (μ.prod μ) μ :=
    measurePreserving_snd.comp (measurePreserving_prod_inv_mul μ μ)
  have h' : MeasurePreserving (fun q : G × G => q.2⁻¹ * q.1) (μ.prod μ) μ :=
    measurePreserving_snd.comp (measurePreserving_prod_inv_mul_swap μ μ)
  refine ⟨?_⟩
  unfold Measure.inv
  conv_lhs => rw [← h.map_eq, Measure.map_map measurable_inv h.measurable]
  simpa only [Function.comp_def, _root_.mul_inv_rev, inv_inv] using h'.map_eq

section WilsonBoundary

variable [MeasurableMul₂ G] [MeasurableInv G]
variable (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

private local instance {E : Type*} [Fintype E] : (configMeasure μ E).IsInvInvariant := by
  let := probability_invInvariant μ
  unfold configMeasure
  infer_instance

abbrev BoundaryConfig (n : Fin 4 → ℕ) (G : Type*) := BoundaryLink n → G
private abbrev InteriorLink (n : Fin 4 → ℕ) :=
  {e : Link n // ¬ (e.val.1 0 = 0 ∧ e.val.2 ≠ 0)}
private abbrev InteriorConfig (n : Fin 4 → ℕ) (G : Type*) := InteriorLink n → G

noncomputable def halfSplit :
    (Link n → G) ≃ᵐ BoundaryConfig n G × InteriorConfig n G := by
  classical
  exact MeasurableEquiv.piEquivPiSubtypeProd (fun _ => G) (fun e : Link n =>
    e.val.1 0 = 0 ∧ e.val.2 ≠ 0)

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] [μ.IsMulLeftInvariant] in
private theorem measurePreserving_halfSplit :
    MeasurePreserving (halfSplit (n := n) (G := G)) (configMeasure μ (Link n))
      ((configMeasure μ (BoundaryLink n)).prod (configMeasure μ (InteriorLink n))) := by
  classical
  exact measurePreserving_piEquivPiSubtypeProd (fun _ => μ) _

omit [Group G] [MeasurableMul₂ G] [MeasurableInv G] in
private theorem boundary_halfSplit (u : Link n → G) : (halfSplit u).1 = boundary u := rfl

private noncomputable def spatialAction (D : GaugeData G d) (s : BoundaryConfig n G) : ℝ := by
  classical
  exact ∑ p ∈ Finset.univ.filter (fun p : Plaquette n =>
      p.val.1 0 = 0 ∧ p.val.2.1 ≠ 0 ∧ p.val.2.2 ≠ 0),
    (D.rep (squareHolonomy (halfSplit.symm (s, 1)) p)).trace.re

private theorem spatial_measurable (D : GaugeData G d) :
    Measurable (spatialAction D : BoundaryConfig n G → ℝ) := by
  classical
  unfold spatialAction
  exact Finset.measurable_sum _ fun p _ => (measurable_weight D).comp
    ((measurable_square p).comp (halfSplit.symm.measurable.comp
      (measurable_id.prodMk measurable_const)))

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem abs_spatial_le (D : GaugeData G d) (s : BoundaryConfig n G) :
    |spatialAction D s| ≤ Fintype.card (Plaquette n) * d := by
  classical
  unfold spatialAction
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ Finset.univ.filter (fun p : Plaquette n =>
        p.val.1 0 = 0 ∧ p.val.2.1 ≠ 0 ∧ p.val.2.2 ≠ 0), (d : ℝ) :=
      Finset.sum_le_sum fun _ _ => (Complex.abs_re_le_norm _).trans (norm_trace_le D _)
    _ ≤ ∑ _p : Plaquette n, (d : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
    _ = _ := by simp [mul_comm]

private def stepAction (D : GaugeData G d)
    (q : (BoundaryConfig n G × BoundaryConfig n G) × (BoundarySite n → G)) : ℝ :=
  spatialAction D q.1.1 / 2 + spatialAction D q.1.2 / 2 +
    ∑ e : BoundaryLink n, (D.rep (seamHolonomy q.1.1 q.1.2 q.2 e)).trace.re

private theorem stepAction_measurable (D : GaugeData G d) :
    Measurable (stepAction (n := n) D) := by
  unfold stepAction
  refine (((spatial_measurable D).comp (measurable_fst.comp measurable_fst)).div_const 2
    |>.add (((spatial_measurable D).comp (measurable_snd.comp measurable_fst)).div_const 2)).add ?_
  apply Finset.measurable_sum
  intro e _
  apply (measurable_weight D).comp
  unfold seamHolonomy
  fun_prop

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem abs_stepAction_le (D : GaugeData G d)
    (q : (BoundaryConfig n G × BoundaryConfig n G) × (BoundarySite n → G)) :
    |stepAction D q| ≤ (Fintype.card (Plaquette n) + Fintype.card (BoundaryLink n)) * d := by
  have h : |∑ e : BoundaryLink n, (D.rep (seamHolonomy q.1.1 q.1.2 q.2 e)).trace.re| ≤
      Fintype.card (BoundaryLink n) * d :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun _ _ =>
      (Complex.abs_re_le_norm _).trans (norm_trace_le D _)).trans_eq (by simp [mul_comm]))
  have hs (s : BoundaryConfig n G) :
      |spatialAction D s / 2| ≤ Fintype.card (Plaquette n) * d / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact div_le_div_of_nonneg_right (abs_spatial_le D _) (by norm_num)
  unfold stepAction
  exact (abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans
    (add_le_add (hs q.1.1) (hs q.1.2))) h |>.trans_eq (by ring))

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem stepAction_symm (D : GaugeData G d) (s t : BoundaryConfig n G)
    (h : BoundarySite n → G) :
    stepAction D ((s, t), h) = stepAction D ((t, s), h⁻¹) := by
  unfold stepAction
  rw [add_comm (spatialAction D s / 2)]
  congr 1
  exact Finset.sum_congr rfl fun e _ => (seamWeight_reflect D s t h e).symm

/-- The Wilson one-step boundary kernel, including the product Haar average over seam sites. -/
noncomputable def wilsonBoundaryKernel (D : GaugeData G d) (β : ℝ) :
    BoundaryKernel (BoundaryConfig n G) where
  toFun p := ∫ h, Real.exp (β * stepAction D (p, h)) ∂configMeasure μ (BoundarySite n)
  measurable := ((Real.measurable_exp.comp ((stepAction_measurable D).const_mul β)).stronglyMeasurable.integral_prod_right'
    (ν := configMeasure μ (BoundarySite n))).measurable
  bound := Real.exp (|β| * ((Fintype.card (Plaquette n) + Fintype.card (BoundaryLink n)) * d))
  norm_le p := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := configMeasure μ (BoundarySite n))
        (f := fun h => Real.exp (β * stepAction D (p, h)))
        (ae_of_all _ fun h => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact exp_bound (b := β) (abs_stepAction_le D (p, h)))
  symm s t := by
    simp only [show ∀ h, Real.exp (β * stepAction D ((s, t), h)) =
      Real.exp (β * stepAction D ((t, s), h⁻¹)) from fun h => by rw [stepAction_symm]]
    exact integral_inv_eq_self (fun h => Real.exp (β * stepAction D ((t, s), h))) _

private noncomputable def restAction (D : GaugeData G d)
    (p : BoundaryConfig n G × InteriorConfig n G) : ℝ :=
  halfAction D (halfSplit.symm p) - spatialAction D p.1 / 2

private theorem rest_measurable (D : GaugeData G d) :
    Measurable (restAction (n := n) D) :=
  ((measurable_halfAction D).comp halfSplit.symm.measurable).sub
    (((spatial_measurable D).comp measurable_fst).div_const 2)

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem rest_abs_le (D : GaugeData G d) (p : BoundaryConfig n G × InteriorConfig n G) :
    |restAction D p| ≤ Fintype.card (Plaquette n) * d + Fintype.card (Plaquette n) * d / 2 := by
  unfold restAction
  refine (abs_sub _ _).trans (add_le_add (abs_halfAction_le D _) ?_)
  rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact div_le_div_of_nonneg_right (abs_spatial_le D _) (by norm_num)

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem splitAction (D : GaugeData G d) (p : Box n G) :
    wilsonAction D p = restAction D (halfSplit p.1.1) + restAction D (halfSplit p.1.2) +
      stepAction D (((halfSplit p.1.1).1, (halfSplit p.1.2).1), p.2) := by
  simp [wilsonAction, restAction, stepAction, boundary_halfSplit]
  ring

local notation "boundaryμ" => configMeasure μ (BoundaryLink n)
local notation "interiorμ" => configMeasure μ (InteriorLink n)
local notation "seamμ" => configMeasure μ (BoundarySite n)

private noncomputable def halfRemainderWeight (D : GaugeData G d) (β : ℝ)
    (p : BoundaryConfig n G × InteriorConfig n G) : ℝ :=
  Real.exp (β * restAction D p)

private theorem halfRemainderWeight_measurable (D : GaugeData G d) (β : ℝ) :
    Measurable (halfRemainderWeight (n := n) D β) :=
  Real.measurable_exp.comp ((rest_measurable D).const_mul β)

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem halfRemainderWeight_bound (D : GaugeData G d) (β : ℝ)
    (p : BoundaryConfig n G × InteriorConfig n G) :
    ‖halfRemainderWeight D β p‖ ≤
      Real.exp (|β| * (Fintype.card (Plaquette n) * d + Fintype.card (Plaquette n) * d / 2)) := by
  rw [halfRemainderWeight, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_bound (rest_abs_le D p)

omit [MeasurableMul₂ G] [MeasurableInv G] in
private theorem halfRemainderWeight_inv_bound (D : GaugeData G d) (β : ℝ)
    (p : BoundaryConfig n G × InteriorConfig n G) :
    ‖(halfRemainderWeight D β p)⁻¹‖ ≤
      Real.exp (|β| * (Fintype.card (Plaquette n) * d + Fintype.card (Plaquette n) * d / 2)) := by
  simpa [halfRemainderWeight, neg_mul, Real.exp_neg] using halfRemainderWeight_bound D (-β) p

private noncomputable def weightedHalf (D : GaugeData G d) (β : ℝ)
    (F : integrableObservables ((boundaryμ).prod interiorμ)) :=
  weightObservable interiorμ (halfRemainderWeight D β) (halfRemainderWeight_measurable D β)
    (halfRemainderWeight_bound D β) F

noncomputable def boundaryReduction (D : GaugeData G d) (β : ℝ)
    (F : integrableObservables ((boundaryμ).prod interiorμ)) :
    integrableObservables boundaryμ :=
  boundaryMarginal interiorμ (weightedHalf μ D β F)

omit [μ.IsMulLeftInvariant] in
private theorem boundaryReduction_surjective (D : GaugeData G d) (β : ℝ) :
    Function.Surjective (boundaryReduction (n := n) μ D β) :=
  weightedBoundaryMarginal_surjective interiorμ _ (halfRemainderWeight_measurable D β)
    (halfRemainderWeight_bound D β) (halfRemainderWeight_inv_bound D β) (fun _ => (Real.exp_pos _).ne')

theorem wilsonOS_boundary_pair (D : GaugeData G d) (β : ℝ)
    (F H : integrableObservables ((boundaryμ).prod interiorμ)) :
    wilsonOSPair μ D β (F.1 ∘ halfSplit) (H.1 ∘ halfSplit) * (partition (n := n) μ D β : ℂ) =
      osPair (wilsonBoundaryKernel μ D β) (boundaryReduction μ D β F) (boundaryReduction μ D β H) := by
  let equiv := ((halfSplit (n := n) (G := G)).prodCongr (halfSplit (n := n) (G := G))).prodCongr
    (MeasurableEquiv.refl (BoundarySite n → G))
  have hp : MeasurePreserving equiv (boxMeasure μ n)
      ((((boundaryμ).prod interiorμ).prod ((boundaryμ).prod interiorμ)).prod seamμ) :=
    ((measurePreserving_halfSplit μ).prod (measurePreserving_halfSplit μ)).prod
       (MeasurePreserving.id seamμ)
  unfold wilsonOSPair
  rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (partition_pos μ D β).ne')]
  rw [← (hp.symm equiv).integral_comp' _]
  have hi := (hp.symm equiv).integrable_comp_of_integrable
    (wilson_product_integrable μ D β _ _
      ((measurePreserving_halfSplit μ).integrable_comp_of_integrable (observable_integrable F))
      ((measurePreserving_halfSplit μ).integrable_comp_of_integrable (observable_integrable H)))
  simp only [Function.comp_def] at hi ⊢
  rw [integral_prod _ hi]
  simp only [boundaryReduction]
  rw [← osPair_pullback, osPair_integral_prod]
  apply integral_congr_ae (ae_of_all _ fun p => ?_)
  have hpull : (pullbackKernel (wilsonBoundaryKernel μ D β)).toFun p =
      ∫ h, Real.exp (β * stepAction D ((p.1.1, p.2.1), h)) ∂seamμ := rfl
  rw [hpull, ← integral_complex_ofReal, ← integral_mul_const]
  apply integral_congr_ae (ae_of_all _ fun h => ?_)
  have hsplit := splitAction D (equiv.symm (p, h))
  have heq : equiv.symm (p, h) = ((halfSplit.symm p.1, halfSplit.symm p.2), h) := rfl
  rw [heq] at hsplit ⊢
  simp only [MeasurableEquiv.apply_symm_apply] at hsplit
  simp only [MeasurableEquiv.apply_symm_apply, hsplit, mul_add, Real.exp_add, Complex.ofReal_mul,
    weightedHalf, weightObservable, halfRemainderWeight, map_mul, Complex.conj_ofReal]
  ring

theorem wilsonOS_boundary (D : GaugeData G d) (β : ℝ)
    (F : integrableObservables ((boundaryμ).prod interiorμ)) :
    wilsonOS μ D β (F.1 ∘ halfSplit) * (partition (n := n) μ D β : ℂ) =
      osPair (wilsonBoundaryKernel μ D β) (boundaryReduction μ D β F) (boundaryReduction μ D β F) :=
  wilsonOS_boundary_pair μ D β F F

theorem wilsonBoundaryKernel_pos (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β)
    (f : integrableObservables boundaryμ) : 0 ≤ (osPair (wilsonBoundaryKernel μ D β) f f).re := by
  obtain ⟨F, rfl⟩ := boundaryReduction_surjective μ D β f
  rw [← wilsonOS_boundary]
  obtain ⟨r, hr, heq⟩ := wilson_reflected_integral_nonneg μ D β hβ (F.1 ∘ halfSplit)
    ((measurePreserving_halfSplit μ).integrable_comp_of_integrable (observable_integrable F))
  rw [wilsonOS, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (partition_pos μ D β).ne'),
    heq, Complex.ofReal_re]
  exact hr

/-- The physical boundary pre-Hilbert space for the Wilson one-step kernel. -/
noncomputable abbrev wilsonPhysicalSpace (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β) :=
  physicalSpace (wilsonBoundaryKernel (n := n) μ D β) (wilsonBoundaryKernel_pos μ D β hβ)

/-- The Wilson transfer operator on the physical boundary pre-Hilbert space. -/
noncomputable def wilsonPhysicalTransfer (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β) :
    wilsonPhysicalSpace (n := n) μ D β hβ →ₗ[ℂ] wilsonPhysicalSpace (n := n) μ D β hβ :=
  physicalTransfer (wilsonBoundaryKernel μ D β) (wilsonBoundaryKernel_pos μ D β hβ)

noncomputable def pullbackHalf : integrableObservables (configMeasure μ (Link n)) →ₗ[ℂ]
      integrableObservables ((boundaryμ).prod interiorμ) where
  toFun F := ⟨F.1 ∘ halfSplit.symm,
    ((measurePreserving_halfSplit μ).symm halfSplit).integrable_comp_of_integrable
      (observable_integrable F)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private noncomputable def splitHalfClass (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β) :
    integrableObservables ((boundaryμ).prod interiorμ) →ₗ[ℂ] wilsonPhysicalSpace (n := n) μ D β hβ where
  toFun F := physicalClass (wilsonBoundaryKernel μ D β) (wilsonBoundaryKernel_pos μ D β hβ)
    (boundaryReduction μ D β F)
  map_add' F G := by
    let L := boundaryReduction (n := n) μ D β
    let C := physicalClass (wilsonBoundaryKernel (n := n) μ D β) (wilsonBoundaryKernel_pos μ D β hβ)
    change C (L (F + G)) = C (L F + L G)
    apply physicalClass_ae
    filter_upwards [(observable_integrable (weightedHalf μ D β F)).prod_right_ae,
      (observable_integrable (weightedHalf μ D β G)).prod_right_ae] with x hf hg
    simpa only [L, boundaryReduction, boundaryMarginal, weightedHalf, weightObservable,
      Submodule.coe_add, Pi.add_apply, mul_add] using integral_add hf hg
  map_smul' c F := by
    let L := boundaryReduction (n := n) μ D β
    let C := physicalClass (wilsonBoundaryKernel (n := n) μ D β) (wilsonBoundaryKernel_pos μ D β hβ)
    change C (L (c • F)) = C (c • L F)
    apply physicalClass_ae
    exact ae_of_all _ fun x => by
      simp only [L, boundaryReduction, boundaryMarginal, weightedHalf, weightObservable,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

/-- The physical class of an integrable observable in the positive half. -/
noncomputable def wilsonHalfClass (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β) :
    integrableObservables (configMeasure μ (Link n)) →ₗ[ℂ] wilsonPhysicalSpace (n := n) μ D β hβ :=
  (splitHalfClass μ D β hβ).comp (pullbackHalf μ)

/-- The seminorm of a half observable for the normalized Wilson probability. -/
noncomputable def wilsonOSSeminorm (D : GaugeData G d) (β : ℝ) (hβ : 0 ≤ β) :
    Seminorm ℂ (integrableObservables (configMeasure μ (Link n))) :=
  (Real.toNNReal ((Real.sqrt (partition (n := n) μ D β))⁻¹)) •
    (normSeminorm ℂ _).comp (wilsonHalfClass μ D β hβ)

end WilsonBoundary

end

end Omega.LatticeGauge

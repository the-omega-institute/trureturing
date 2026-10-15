/- GID: D5/S3/Quantum/Analysis/ContractionSemigroup
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/ContractionSemigroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: General strong contraction-semigroup generator closedness and uniqueness. -/

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license; see
 docs/reports/heat-suppliers/markovprocess-LICENSE.txt.
Source: scottnarmstrong/MarkovProcess at dbade0d12c4f84179441a9df7d7147df7a8bcaa0,
Semigroup/{Basic,StrongOperatorLimit,Generator,OrbitContinuity,GeneratorClosed,GeneratorUniqueness}.
The selected original proofs have no claimed new mathematical content. They are consumed
by PhysicalHeatGenerator. The donor and receiver use Lean v4.33.0 and mathlib
 db584cd6d46c92f209a44c0f1c829460d327499d.
Retire this selection when the receiver's actually adopted mathlib revision provides
matching strongly continuous contraction-semigroup closedness and uniqueness statements.
The upstream tree has no NOTICE file. Source selection changes imports and removes
unused declarations; it does not add an external dependency.
-/
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.ODE.Gronwall

open Filter Topology
open scoped NNReal
namespace MarkovProcess.Semigroup

/-- A strongly continuous contraction semigroup on a real normed space. -/
structure StronglyContinuousContractionSemigroup (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The continuous linear time-evolution operator. -/
  operator : NNReal → E →L[ℝ] E
  operator_zero : operator 0 = ContinuousLinearMap.id ℝ E
  operator_add : ∀ s t, operator (s + t) = (operator s).comp (operator t)
  opNorm_le_one : ∀ t, ‖operator t‖ ≤ 1
  continuous_orbit : ∀ x, Continuous (fun t ↦ operator t x)

namespace StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : CoeFun (StronglyContinuousContractionSemigroup E)
    (fun _ ↦ NNReal → E →L[ℝ] E) where
  coe S := S.operator

@[ext]
theorem ext {S T : StronglyContinuousContractionSemigroup E}
    (h : ∀ t, S t = T t) : S = T := by
  cases S with
  | mk S _ _ _ _ =>
    cases T with
    | mk T _ _ _ _ =>
      have : S = T := funext h
      cases this
      rfl

variable (S : StronglyContinuousContractionSemigroup E)

@[simp]
theorem zero : S 0 = ContinuousLinearMap.id ℝ E :=
  S.operator_zero

@[simp]
theorem zero_apply (x : E) : S 0 x = x := by
  rw [S.zero]
  rfl

@[simp]
theorem add (s t : NNReal) : S (s + t) = (S s).comp (S t) :=
  S.operator_add s t

@[simp]
theorem add_apply (s t : NNReal) (x : E) : S (s + t) x = S s (S t x) := by
  rw [S.add]
  rfl

theorem norm_operator_le_one (t : NNReal) : ‖S t‖ ≤ 1 :=
  S.opNorm_le_one t

theorem norm_apply_le (t : NNReal) (x : E) : ‖S t x‖ ≤ ‖x‖ := by
  calc
    ‖S t x‖ ≤ ‖S t‖ * ‖x‖ := (S t).le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (S.norm_operator_le_one t) (norm_nonneg x)
    _ = ‖x‖ := one_mul _


theorem continuous (x : E) : Continuous (fun t ↦ S t x) :=
  S.continuous_orbit x



theorem commute (s t : NNReal) : (S s).comp (S t) = (S t).comp (S s) := by
  rw [← S.add, ← S.add, add_comm]

theorem commute_apply (s t : NNReal) (x : E) : S s (S t x) = S t (S s x) := by
  change ((S s).comp (S t)) x = ((S t).comp (S s)) x
  rw [S.commute]

end StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup

namespace MarkovProcess.Semigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A pointwise operator limit may be evaluated along a convergent family of vectors, provided
the approximating operators are contractions.  Only the convergence of the operators at the
limiting vector is needed. -/
theorem tendsto_apply_of_opNorm_le_one {ι : Type*} {l : Filter ι}
    (T : ι → E →L[ℝ] E) (Tlim : E →L[ℝ] E) (v : ι → E) (w : E)
    (hT : ∀ i, ‖T i‖ ≤ 1)
    (hTlim : Tendsto (fun i ↦ T i w) l (nhds (Tlim w)))
    (hv : Tendsto v l (nhds w)) :
    Tendsto (fun i ↦ T i (v i)) l (nhds (Tlim w)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [Metric.tendsto_nhds.mp hv (ε / 2) hε2,
    Metric.tendsto_nhds.mp hTlim (ε / 2) hε2] with i hvi hTi
  have hcontract : dist (T i (v i)) (T i w) ≤ dist (v i) w := by
    calc
      dist (T i (v i)) (T i w) ≤ ‖T i‖ * dist (v i) w := (T i).dist_le_opNorm _ _
      _ ≤ 1 * dist (v i) w := mul_le_mul_of_nonneg_right (hT i) dist_nonneg
      _ = dist (v i) w := one_mul _
  calc
    dist (T i (v i)) (Tlim w) ≤ dist (T i (v i)) (T i w) + dist (T i w) (Tlim w) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hcontract.trans_lt hvi) hTi
    _ = ε := add_halves ε


end MarkovProcess.Semigroup
open Filter Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

section DifferenceQuotient

/-- The difference quotient `t⁻¹ • (S t f - f)` of the orbit of `f` at time zero. -/
def differenceQuotient (f : E) (t : NNReal) : E := (t : ℝ)⁻¹ • (S t f - f)

/-- The difference quotient, unfolded. -/
theorem differenceQuotient_apply (f : E) (t : NNReal) :
    S.differenceQuotient f t = (t : ℝ)⁻¹ • (S t f - f) := rfl

/-- Difference quotients are additive in the vector. -/
theorem differenceQuotient_add (f g : E) (t : NNReal) :
    S.differenceQuotient (f + g) t = S.differenceQuotient f t + S.differenceQuotient g t := by
  rw [differenceQuotient, differenceQuotient, differenceQuotient, map_add, add_sub_add_comm,
    smul_add]

/-- Difference quotients are homogeneous in the vector. -/
theorem differenceQuotient_smul (c : ℝ) (f : E) (t : NNReal) :
    S.differenceQuotient (c • f) t = c • S.differenceQuotient f t := by
  rw [differenceQuotient, differenceQuotient, map_smul, ← smul_sub, smul_comm]

/-- The difference quotient of the zero vector vanishes. -/
theorem differenceQuotient_zero (t : NNReal) : S.differenceQuotient 0 t = 0 := by
  rw [differenceQuotient, map_zero, sub_zero, smul_zero]

/-- The operator `S s` commutes with difference quotients. -/
theorem differenceQuotient_operator (f : E) (s t : NNReal) :
    S.differenceQuotient (S s f) t = S s (S.differenceQuotient f t) := by
  rw [differenceQuotient, differenceQuotient, map_smul, map_sub, S.commute_apply]

end DifferenceQuotient

section Domain

/-- The generator domain of `S`: the vectors whose difference quotients `t⁻¹ • (S t f - f)`
converge as `t → 0⁺`.  It is a linear subspace of `E`. -/
def generatorDomain : Submodule ℝ E where
  carrier := {f | ∃ g : E, Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g)}
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, (ha.add hb).congr fun t ↦ ?_⟩
    exact (S.differenceQuotient_add f g t).symm
  zero_mem' := by
    refine ⟨0, ?_⟩
    have hzero : S.differenceQuotient 0 = fun _ ↦ 0 := funext (S.differenceQuotient_zero)
    rw [hzero]
    exact tendsto_const_nhds
  smul_mem' := by
    rintro c f ⟨a, ha⟩
    refine ⟨c • a, (ha.const_smul c).congr fun t ↦ ?_⟩
    exact (S.differenceQuotient_smul c f t).symm

/-- Membership in the generator domain, unfolded. -/
theorem mem_generatorDomain_iff {f : E} :
    f ∈ S.generatorDomain ↔ ∃ g : E, Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g) :=
  Iff.rfl

/-- A vector whose difference quotients converge lies in the generator domain. -/
theorem mem_generatorDomain_of_tendsto {f g : E}
    (h : Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 g)) :
    f ∈ S.generatorDomain :=
  ⟨g, h⟩

end Domain

section Generator

/-- The limit of the difference quotients, for a vector of the domain. -/
private noncomputable def generatorFun (f : S.generatorDomain) : E :=
  limUnder (𝓝[>] (0 : NNReal)) (S.differenceQuotient f)

private theorem tendsto_generatorFun (f : S.generatorDomain) :
    Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 (S.generatorFun f)) :=
  tendsto_nhds_limUnder (S.mem_generatorDomain_iff.mp f.2)

private theorem generatorFun_eq_of_tendsto (f : S.generatorDomain) {g : E}
    (h : Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 g)) : S.generatorFun f = g :=
  tendsto_nhds_unique (S.tendsto_generatorFun f) h

/-- The generator of `S`, as a linear map on its domain: `S.generator f` is the limit of the
difference quotients `t⁻¹ • (S t f - f)` as `t → 0⁺`. -/
noncomputable def generator : S.generatorDomain →ₗ[ℝ] E where
  toFun := S.generatorFun
  map_add' f g := by
    apply S.generatorFun_eq_of_tendsto
    refine ((S.tendsto_generatorFun f).add (S.tendsto_generatorFun g)).congr fun t ↦ ?_
    rw [Submodule.coe_add, differenceQuotient_add]
  map_smul' c f := by
    apply S.generatorFun_eq_of_tendsto
    refine ((S.tendsto_generatorFun f).const_smul c).congr fun t ↦ ?_
    rw [Submodule.coe_smul, differenceQuotient_smul]

/-- The defining property of the generator: the difference quotients of a vector of the domain
converge to its generator. -/
theorem tendsto_generator (f : S.generatorDomain) :
    Tendsto (S.differenceQuotient f) (𝓝[>] 0) (𝓝 (S.generator f)) :=
  S.tendsto_generatorFun f

/-- The defining property of the generator, with the difference quotient written out. -/
theorem tendsto_generator' (f : S.generatorDomain) :
    Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 (S.generator f)) :=
  S.tendsto_generatorFun f

/-- The generator is the unique limit of the difference quotients. -/
theorem generator_eq_of_tendsto (f : S.generatorDomain) {g : E}
    (h : Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 g)) :
    S.generator f = g :=
  S.generatorFun_eq_of_tendsto f h


end Generator

section Invariance

/-- The generator domain is invariant under the semigroup. -/
theorem operator_mem_generatorDomain (f : S.generatorDomain) (t : NNReal) :
    S t f ∈ S.generatorDomain := by
  refine ⟨S t (S.generator f), ?_⟩
  refine (((S t).continuous.tendsto _).comp (S.tendsto_generator f)).congr fun h ↦ ?_
  exact (S.differenceQuotient_operator f t h).symm


/-- Right differentiability of orbits: for `f` in the generator domain and every time `t`, the
difference quotients of `h ↦ S (t + h) f` at `h = 0⁺` converge to `S t (S.generator f)`. -/
theorem tendsto_differenceQuotient_add (f : S.generatorDomain) (t : NNReal) :
    Tendsto (fun h : NNReal ↦ (h : ℝ)⁻¹ • (S (t + h) f - S t f)) (𝓝[>] 0)
      (𝓝 (S t (S.generator f))) := by
  refine (((S t).continuous.tendsto _).comp (S.tendsto_generator f)).congr fun h ↦ ?_
  show S t ((h : ℝ)⁻¹ • (S h f - f)) = (h : ℝ)⁻¹ • (S (t + h) f - S t f)
  rw [map_smul, map_sub, S.add_apply]

end Invariance

section RealVariable

/-- Reading `NNReal` times from the right of a real time: `y ↦ Real.toNNReal (y - t)` sends the
right neighbourhood filter of `t` to the right neighbourhood filter of `0`. -/
theorem tendsto_toNNReal_sub (t : NNReal) :
    Tendsto (fun y : ℝ ↦ Real.toNNReal (y - t)) (𝓝[>] (t : ℝ)) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun y : ℝ ↦ Real.toNNReal (y - t)) (𝓝 (t : ℝ))
        (𝓝 (Real.toNNReal ((t : ℝ) - t))) :=
      (continuous_real_toNNReal.tendsto _).comp ((continuous_id.sub continuous_const).tendsto _)
    rw [sub_self, Real.toNNReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact Set.mem_Ioi.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr hy))

/-- The orbit of any vector, read in the real variable, is continuous. -/
theorem continuous_operator_toNNReal (f : E) :
    Continuous fun s : ℝ ↦ S (Real.toNNReal s) f :=
  (S.continuous f).comp continuous_real_toNNReal

/-- Right derivative in the real variable: for `f` in the generator domain and every
`t : NNReal`, the orbit `s ↦ S (Real.toNNReal s) f` has right derivative `S t (S.generator f)`
at `t`. -/
theorem hasDerivWithinAt_Ioi (f : S.generatorDomain) (t : NNReal) :
    HasDerivWithinAt (fun s : ℝ ↦ S (Real.toNNReal s) f) (S t (S.generator f))
      (Set.Ioi (t : ℝ)) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdiff : Set.Ioi (t : ℝ) \ {(t : ℝ)} = Set.Ioi (t : ℝ) := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact fun hy ↦ ne_of_gt hy
  rw [hdiff]
  refine ((S.tendsto_differenceQuotient_add f t).comp (tendsto_toNNReal_sub t)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyt : (t : ℝ) < y := hy
  have hy0 : (0 : ℝ) ≤ y := le_trans t.coe_nonneg hyt.le
  have hcoe : ((Real.toNNReal (y - t) : NNReal) : ℝ) = y - t :=
    Real.coe_toNNReal _ (sub_nonneg.mpr hyt.le)
  have htoNN : Real.toNNReal y = t + Real.toNNReal (y - t) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, hcoe, Real.coe_toNNReal y hy0]
    ring
  show ((Real.toNNReal (y - t) : NNReal) : ℝ)⁻¹ •
      (S (t + Real.toNNReal (y - t)) f - S t f) =
    slope (fun s : ℝ ↦ S (Real.toNNReal s) f) (t : ℝ) y
  rw [slope_def_module, hcoe, Real.toNNReal_coe, htoNN]


variable [CompleteSpace E]

/-- **The fundamental identity of the generator.**  For `f` in the generator domain and every
time `t`, `S t f - f = ∫₀ᵗ S s (S.generator f) ds`, the integral being the Bochner interval
integral of the continuous orbit of `S.generator f`. -/
theorem operator_sub_eq_integral (f : S.generatorDomain) (t : NNReal) :
    S t f - f = ∫ s in (0 : ℝ)..t, S (Real.toNNReal s) (S.generator f) := by
  have hcont : ContinuousOn (fun s : ℝ ↦ S (Real.toNNReal s) f) (Set.Icc 0 t) :=
    (S.continuous_operator_toNNReal f).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun s : ℝ ↦ S (Real.toNNReal s) f)
        (S (Real.toNNReal x) (S.generator f)) (Set.Ioi x) x := by
    intro x hx
    have h := S.hasDerivWithinAt_Ioi f (Real.toNNReal x)
    rwa [Real.coe_toNNReal x hx.1.le] at h
  have hint : IntervalIntegrable (fun s : ℝ ↦ S (Real.toNNReal s) (S.generator f))
      MeasureTheory.volume 0 t :=
    (S.continuous_operator_toNNReal _).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg hcont
    hderiv hint
  rw [hftc, Real.toNNReal_coe, Real.toNNReal_zero, S.zero_apply]

end RealVariable

section OrbitIntegral

/-- The right difference quotients of a differentiable function, indexed by `NNReal` increments,
converge to its derivative. -/
theorem tendsto_slope_add_of_hasDerivAt {F : ℝ → E} {F' : E} {u : ℝ}
    (hF : HasDerivAt F F' u) :
    Tendsto (fun h : NNReal ↦ (h : ℝ)⁻¹ • (F (u + h) - F u)) (𝓝[>] 0) (𝓝 F') := by
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hF)
  have hmap : Tendsto (fun h : NNReal ↦ u + (h : ℝ)) (𝓝[>] 0) (𝓝[≠] u) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Tendsto (fun h : NNReal ↦ u + (h : ℝ)) (𝓝 0) (𝓝 (u + ((0 : NNReal) : ℝ))) :=
        (continuous_const.add NNReal.continuous_coe).tendsto _
      rw [NNReal.coe_zero, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have hpos : (0 : ℝ) < h := NNReal.coe_pos.mpr hh
      exact ne_of_gt (lt_add_of_pos_right u hpos)
  refine (hslope.comp hmap).congr fun h ↦ ?_
  show slope F u (u + h) = (h : ℝ)⁻¹ • (F (u + h) - F u)
  rw [slope_def_module, add_sub_cancel_left]

/-- The orbit integral `∫₀ᵘ S s f ds` of a vector `f`, as a function of the real upper limit
`u` (the semigroup is read at `Real.toNNReal s`). -/
def orbitIntegral (f : E) (u : ℝ) : E := ∫ s in (0 : ℝ)..u, S (Real.toNNReal s) f

/-- The orbit integral, unfolded. -/
theorem orbitIntegral_apply (f : E) (u : ℝ) :
    S.orbitIntegral f u = ∫ s in (0 : ℝ)..u, S (Real.toNNReal s) f := rfl

/-- The orbit integral over an empty window vanishes. -/
theorem orbitIntegral_zero (f : E) : S.orbitIntegral f 0 = 0 :=
  intervalIntegral.integral_same

variable [CompleteSpace E]

/-- The orbit integral is differentiable in its upper limit, with derivative the orbit. -/
theorem hasDerivAt_orbitIntegral (f : E) (u : ℝ) :
    HasDerivAt (S.orbitIntegral f) (S (Real.toNNReal u) f) u :=
  ((S.continuous_operator_toNNReal f).integral_hasStrictDerivAt 0 u).hasDerivAt

/-- The semigroup acting on an orbit integral shifts the integration window. -/
theorem operator_orbitIntegral (f : E) (t h : NNReal) :
    S h (S.orbitIntegral f t) = S.orbitIntegral f (t + h) - S.orbitIntegral f h := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ ↦ S (Real.toNNReal s) f)
      MeasureTheory.volume a b :=
    fun a b ↦ (S.continuous_operator_toNNReal f).intervalIntegrable a b
  have hshift : Set.EqOn (fun s : ℝ ↦ S h (S (Real.toNNReal s) f))
      (fun s : ℝ ↦ S (Real.toNNReal (s + h)) f) (Set.uIcc (0 : ℝ) t) := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := by
      rw [Set.uIcc_of_le t.coe_nonneg] at hs
      exact hs.1
    have hcoe : Real.toNNReal (s + h) = h + Real.toNNReal s := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal s hs0, Real.coe_toNNReal _ (add_nonneg hs0 h.coe_nonneg),
        add_comm]
    show S h (S (Real.toNNReal s) f) = S (Real.toNNReal (s + h)) f
    rw [hcoe, S.add_apply]
  rw [orbitIntegral, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hint 0 t),
    intervalIntegral.integral_congr hshift,
    intervalIntegral.integral_comp_add_right (fun s : ℝ ↦ S (Real.toNNReal s) f) (h : ℝ), zero_add,
    orbitIntegral, orbitIntegral, intervalIntegral.integral_interval_sub_left (hint 0 _) (hint 0 _)]

/-- The difference quotients of an orbit integral converge to the increment of the orbit. -/
theorem tendsto_differenceQuotient_orbitIntegral (f : E) (t : NNReal) :
    Tendsto (fun h : NNReal ↦ (h : ℝ)⁻¹ • (S h (S.orbitIntegral f t) - S.orbitIntegral f t))
      (𝓝[>] 0) (𝓝 (S t f - f)) := by
  have ht := tendsto_slope_add_of_hasDerivAt (S.hasDerivAt_orbitIntegral f t)
  have h0 := tendsto_slope_add_of_hasDerivAt (S.hasDerivAt_orbitIntegral f 0)
  rw [Real.toNNReal_coe] at ht
  rw [Real.toNNReal_zero, S.zero_apply] at h0
  refine (ht.sub h0).congr fun h ↦ ?_
  rw [S.operator_orbitIntegral, zero_add, S.orbitIntegral_zero, sub_zero, ← smul_sub,
    sub_right_comm]

/-- Every orbit integral lies in the generator domain. -/
theorem orbitIntegral_mem_generatorDomain (f : E) (t : NNReal) :
    S.orbitIntegral f t ∈ S.generatorDomain :=
  S.mem_generatorDomain_of_tendsto (S.tendsto_differenceQuotient_orbitIntegral f t)


/-- Time averages of the orbit converge to the vector: `t⁻¹ • ∫₀ᵗ S s f ds → f` as `t → 0⁺`. -/
theorem tendsto_inv_smul_orbitIntegral (f : E) :
    Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • S.orbitIntegral f t) (𝓝[>] 0) (𝓝 f) := by
  have h0 := tendsto_slope_add_of_hasDerivAt (S.hasDerivAt_orbitIntegral f 0)
  rw [Real.toNNReal_zero, S.zero_apply] at h0
  refine h0.congr fun t ↦ ?_
  rw [zero_add, S.orbitIntegral_zero, sub_zero]

/-- **The generator domain is dense.** -/
theorem dense_generatorDomain : Dense (S.generatorDomain : Set E) := by
  intro f
  refine mem_closure_of_tendsto (S.tendsto_inv_smul_orbitIntegral f) ?_
  exact Eventually.of_forall fun t ↦
    S.generatorDomain.smul_mem _ (S.orbitIntegral_mem_generatorDomain f t)

end OrbitIntegral

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem continuous_operator_apply (S : StronglyContinuousContractionSemigroup E)
    {X : Type*} [TopologicalSpace X] {u : X → NNReal} {v : X → E}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x ↦ S (u x) (v x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact tendsto_apply_of_opNorm_le_one (fun z ↦ S (u z)) (S (u x)) v (v x)
    (fun z ↦ S.norm_operator_le_one (u z)) ((S.continuous (v x)).comp hu).continuousAt
    hv.continuousAt
end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

/-- The orbit integral is additive in the vector. -/
theorem orbitIntegral_sub (f g : E) (u : ℝ) :
    S.orbitIntegral f u - S.orbitIntegral g u = S.orbitIntegral (f - g) u := by
  simp only [orbitIntegral_apply, map_sub]
  exact (intervalIntegral.integral_sub ((S.continuous_operator_toNNReal f).intervalIntegrable _ _)
    ((S.continuous_operator_toNNReal g).intervalIntegrable _ _)).symm

/-- The orbit integral over `[0, t]` is bounded by `t` times the norm of the vector. -/
theorem norm_orbitIntegral_le (f : E) (t : NNReal) : ‖S.orbitIntegral f t‖ ≤ ‖f‖ * t := by
  rw [orbitIntegral_apply]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
    (C := ‖f‖) (f := fun s : ℝ ↦ S (Real.toNNReal s) f) (fun s _ ↦ S.norm_apply_le _ f)
  rwa [sub_zero, abs_of_nonneg t.coe_nonneg] at h

/-- The orbit integral over `[0, t]` is continuous in the vector. -/
theorem tendsto_orbitIntegral {ι : Type*} {l : Filter ι} {v : ι → E} {g : E}
    (hv : Tendsto v l (𝓝 g)) (t : NNReal) :
    Tendsto (fun i ↦ S.orbitIntegral (v i) t) l (𝓝 (S.orbitIntegral g t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun i ↦ ‖v i - g‖ * (t : ℝ)) (fun i ↦ norm_nonneg _) (fun i ↦ ?_) ?_
  · rw [S.orbitIntegral_sub]
    exact S.norm_orbitIntegral_le _ t
  · simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hv).mul_const (t : ℝ)

section Closed

variable [CompleteSpace E]
variable {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → S.generatorDomain} {f g : E}

/-- Passing to the limit in the fundamental identity of the generator. -/
theorem operator_sub_eq_orbitIntegral_of_tendsto_generator
    (hu : Tendsto (fun i ↦ (u i : E)) l (𝓝 f))
    (hL : Tendsto (fun i ↦ S.generator (u i)) l (𝓝 g)) (t : NNReal) :
    S t f - f = S.orbitIntegral g t := by
  have h1 : Tendsto (fun i ↦ S t (u i : E) - (u i : E)) l (𝓝 (S t f - f)) :=
    (((S t).continuous.tendsto f).comp hu).sub hu
  have h2 : Tendsto (fun i ↦ S t (u i : E) - (u i : E)) l (𝓝 (S.orbitIntegral g t)) := by
    refine (S.tendsto_orbitIntegral hL t).congr fun i ↦ ?_
    rw [orbitIntegral_apply]
    exact (S.operator_sub_eq_integral (u i) t).symm
  exact tendsto_nhds_unique h1 h2

/-- The difference quotients of the limit vector converge to the limit of the generators. -/
theorem tendsto_differenceQuotient_of_tendsto_generator
    (hu : Tendsto (fun i ↦ (u i : E)) l (𝓝 f))
    (hL : Tendsto (fun i ↦ S.generator (u i)) l (𝓝 g)) :
    Tendsto (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S t f - f)) (𝓝[>] 0) (𝓝 g) := by
  refine (S.tendsto_inv_smul_orbitIntegral g).congr fun t ↦ ?_
  rw [S.operator_sub_eq_orbitIntegral_of_tendsto_generator hu hL t]


end Closed
end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

open Filter Set Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S T : StronglyContinuousContractionSemigroup E)

/-- The interpolation `s ↦ S (t - s) (T s f)` between the orbit of `f` under `T` and its orbit
under `S`, read at real times. -/
private def transferOrbit (f : E) (t s : ℝ) : E :=
  S (Real.toNNReal (t - s)) (T (Real.toNNReal s) f)

private theorem transferOrbit_apply (f : E) (t s : ℝ) :
    S.transferOrbit T f t s = S (Real.toNNReal (t - s)) (T (Real.toNNReal s) f) := rfl

private theorem continuous_transferOrbit (f : E) (t : ℝ) :
    Continuous (S.transferOrbit T f t) :=
  S.continuous_operator_apply
    (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
    (T.continuous_operator_toNNReal f)

private theorem transferOrbit_zero (f : E) (t : ℝ) :
    S.transferOrbit T f t 0 = S (Real.toNNReal t) f := by
  rw [transferOrbit_apply, sub_zero, Real.toNNReal_zero, T.zero_apply]

private theorem transferOrbit_self (f : E) (t : ℝ) :
    S.transferOrbit T f t t = T (Real.toNNReal t) f := by
  rw [transferOrbit_apply, sub_self, Real.toNNReal_zero, S.zero_apply]

/-- The interpolation has vanishing right derivative at every time of `[0, t)`. -/
private theorem hasDerivWithinAt_transferOrbit
    (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : E) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩)
    {f : E} (hf : f ∈ S.generatorDomain) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    HasDerivWithinAt (S.transferOrbit T f t) 0 (Ici s) s := by
  have hfT : f ∈ T.generatorDomain := by rwa [← hdom]
  have hgT : T (Real.toNNReal s) f ∈ T.generatorDomain :=
    T.operator_mem_generatorDomain ⟨f, hfT⟩ (Real.toNNReal s)
  have hgS : T (Real.toNNReal s) f ∈ S.generatorDomain := by rwa [hdom]
  have hto : Tendsto (fun y : ℝ ↦ Real.toNNReal (y - s)) (𝓝[>] s) (𝓝[>] 0) := by
    have h := tendsto_toNNReal_sub (Real.toNNReal s)
    rwa [Real.coe_toNNReal s hs] at h
  have hbound : Tendsto (fun y : ℝ ↦
      ‖T.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s)) -
        S.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s))‖)
      (𝓝[>] s) (𝓝 0) := by
    have hT' := (T.tendsto_generator ⟨T (Real.toNNReal s) f, hgT⟩).comp hto
    have hS' := (S.tendsto_generator ⟨T (Real.toNNReal s) f, hgS⟩).comp hto
    have hdiff := hT'.sub hS'
    rw [← hgen _ hgS hgT, sub_self] at hdiff
    simpa using hdiff.norm
  have hslope : ∀ y ∈ Ioo s t, slope (S.transferOrbit T f t) s y =
      S (Real.toNNReal (t - y))
        (T.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s)) -
          S.differenceQuotient (T (Real.toNNReal s) f) (Real.toNNReal (y - s))) := by
    intro y hy
    have hsy : (0 : ℝ) ≤ y - s := sub_nonneg.mpr hy.1.le
    have hcoe : ((Real.toNNReal (y - s) : NNReal) : ℝ) = y - s := Real.coe_toNNReal _ hsy
    have hy0 : (0 : ℝ) ≤ y := hs.trans hy.1.le
    have hsplit : Real.toNNReal y = Real.toNNReal (y - s) + Real.toNNReal s := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, hcoe, Real.coe_toNNReal s hs, Real.coe_toNNReal y hy0]
      ring
    have hwindow : Real.toNNReal (t - s) = Real.toNNReal (t - y) + Real.toNNReal (y - s) := by
      apply NNReal.coe_injective
      rw [NNReal.coe_add, hcoe, Real.coe_toNNReal _ (sub_nonneg.mpr hy.2.le),
        Real.coe_toNNReal _ (sub_nonneg.mpr (hy.1.trans hy.2).le)]
      ring
    have key : S.transferOrbit T f t y - S.transferOrbit T f t s =
        S (Real.toNNReal (t - y))
          (T (Real.toNNReal (y - s)) (T (Real.toNNReal s) f) -
            S (Real.toNNReal (y - s)) (T (Real.toNNReal s) f)) := by
      rw [transferOrbit_apply, transferOrbit_apply, hsplit, T.add_apply, hwindow, S.add_apply,
        ← map_sub]
    rw [slope_def_module, key, T.differenceQuotient_apply, S.differenceQuotient_apply, hcoe,
      ← smul_sub, map_smul, sub_sub_sub_cancel_right]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hdiff : Ici s \ {s} = Ioi s := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun hy ↦ lt_of_le_of_ne hy.1 (Ne.symm hy.2), fun hy ↦ ⟨hy.le, hy.ne'⟩⟩
  rw [hdiff]
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [Ioo_mem_nhdsGT hst] with y hy
  rw [hslope y hy]
  exact S.norm_apply_le _ _

variable [CompleteSpace E]

/-- **The generator determines the semigroup.**  Two strongly continuous contraction semigroups
with the same generator domain, on which their generators agree, are equal. -/
theorem ext_of_generator (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : E) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩) :
    S = T := by
  have hcore : ∀ (t : NNReal) (f : E), f ∈ S.generatorDomain → S t f = T t f := by
    intro t f hf
    have hconst := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := fun s ↦ S.transferOrbit T f t s - S.transferOrbit T f t 0)
      (f' := fun _ ↦ (0 : E)) (K := 0) (a := 0) (b := (t : ℝ))
      (((S.continuous_transferOrbit T f t).sub continuous_const).continuousOn)
      (fun s hs ↦
        (S.hasDerivWithinAt_transferOrbit T hdom hgen hf hs.1 hs.2).sub_const _)
      (sub_self _)
      (fun s _ ↦ by rw [norm_zero, zero_mul])
      (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩
    rw [sub_eq_zero, transferOrbit_self, transferOrbit_zero, Real.toNNReal_coe] at hconst
    exact hconst.symm
  refine StronglyContinuousContractionSemigroup.ext fun t ↦ ?_
  refine DFunLike.coe_injective ?_
  refine Continuous.ext_on S.dense_generatorDomain (S t).continuous (T t).continuous ?_
  intro f hf
  exact hcore t f hf

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
#print axioms MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto_differenceQuotient_of_tendsto_generator
#print axioms MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.ext_of_generator


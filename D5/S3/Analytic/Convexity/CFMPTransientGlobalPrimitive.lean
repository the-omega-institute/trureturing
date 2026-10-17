import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order
import Mathlib.Tactic

/-!
Transient B4 source candidate. Prepared against Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d / Lean v4.33.0.
No compiler, axiom audit, admission, or upstream publication is asserted.

The bundle topology, covering theorem, and lifting theorem are Mathlib's.
The local primitive and inverse data remain explicit inputs to the application.
No differentiability of the covector field or of a homotopy is used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped Classical unitInterval

namespace CFMP137Transient

/-- Assembly data for additive coordinates. Continuity of q is unnecessary:
only the constant overlap differences enter the discrete bundle topology. -/
structure AdditiveAtlas (ι X : Type*) [TopologicalSpace X] where
  domain : ι → Set X
  isOpen_domain : ∀ i, IsOpen (domain i)
  indexAt : X → ι
  mem_domain : ∀ x, x ∈ domain (indexAt x)
  q : ι → X → ℝ
  overlap : ∀ i j, ∃ d : ℝ, ∀ x ∈ domain i ∩ domain j, q i x - q j x = d

namespace AdditiveAtlas

variable {ι X : Type*} [TopologicalSpace X] (A : AdditiveAtlas ι X)

/-- Definition assembly using the actual separate discrete wrapper for ℝ. -/
def core : FiberBundleCore ι X (WithDiscreteTopology ℝ) where
  baseSet := A.domain
  isOpen_baseSet := A.isOpen_domain
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_domain
  coordChange := fun i j x c => WithTopology.toTopology ⊥ (c.ofTopology + A.q i x - A.q j x)
  coordChange_self := by
    intro i x hx c
    apply WithTopology.ext
    change c.ofTopology + A.q i x - A.q i x = c.ofTopology
    ring
  continuousOn_coordChange := by
    intro i j
    obtain ⟨d, hd⟩ := A.overlap i j
    have hc : Continuous (fun p : X × WithDiscreteTopology ℝ =>
        (WithTopology.toTopology ⊥ (p.2.ofTopology + d) : WithDiscreteTopology ℝ)) :=
      (continuous_of_discreteTopology : Continuous (fun c : WithDiscreteTopology ℝ =>
        (WithTopology.toTopology ⊥ (c.ofTopology + d) : WithDiscreteTopology ℝ))).comp continuous_snd
    refine hc.continuousOn.congr ?_
    intro p hp
    apply WithTopology.ext
    change p.2.ofTopology + A.q i p.1 - A.q j p.1 = p.2.ofTopology + d
    rw [← hd p.1 hp.1]
    ring
  coordChange_comp := by
    intro i j k x hx c
    apply WithTopology.ext
    change (c.ofTopology + A.q i x - A.q j x) + A.q j x - A.q k x =
      c.ofTopology + A.q i x - A.q k x
    ring

/-- Read the preferred-chart coordinate; no separate topology is assigned. -/
def value (p : A.core.TotalSpace) : ℝ :=
  A.q (A.indexAt p.1) p.1 + p.2.ofTopology

/-- The actual core chart formula preserves the additive value. The chart
formula is globally defined, so this algebraic equality needs no membership. -/
theorem value_eq_chart (i : ι) (p : A.core.TotalSpace) :
    A.value p = A.q i p.1 + ((A.core.localTriv i) p).2.ofTopology := by
  rw [FiberBundleCore.localTriv_apply]
  change A.q (A.indexAt p.1) p.1 + p.2.ofTopology =
    A.q i p.1 + (p.2.ofTopology + A.q (A.indexAt p.1) p.1 - A.q i p.1)
  ring

/-- Internal consumer of a section, not a new section premise of the global
theorem. The supplied section below is obtained from the actual covering. -/
theorem section_local_eq (s : C(X, A.core.TotalSpace))
    (hs : ∀ x, A.core.proj (s x) = x) (i : ι) (x : X) (hx : x ∈ A.domain i) :
    ∃ c : ℝ, ∀ᶠ y in 𝓝 x, A.value (s y) = c + A.q i y := by
  let offset : X → WithDiscreteTopology ℝ := fun y => ((A.core.localTriv i) (s y)).2
  have hsource : s x ∈ (A.core.localTriv i).source := by
    change A.core.proj (s x) ∈ A.domain i
    rw [hs x]
    exact hx
  have hc : ContinuousAt offset x :=
    ((A.core.localTriv i).toOpenPartialHomeomorph.continuousAt hsource).snd.comp
      s.continuous.continuousAt
  have he : ∀ᶠ y in 𝓝 x, offset y = offset x := by
    change Tendsto offset (𝓝 x) (𝓝 (offset x)) at hc
    simpa only [nhds_discrete, tendsto_pure] using hc
  refine ⟨(offset x).ofTopology, ?_⟩
  filter_upwards [he] with y hy
  rw [A.value_eq_chart i (s y)]
  change A.q i (A.core.proj (s y)) + (offset y).ofTopology =
    (offset x).ofTopology + A.q i y
  rw [hs y, hy]
  exact add_comm _ _

/-- Bind-only covering/lifting application followed by the chart readout.
There is no covering or section among the input assumptions. -/
theorem exists_glued_normalized [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (x₀ : X) :
    ∃ F : X → ℝ, F x₀ = 0 ∧
      ∀ i x, x ∈ A.domain i → ∃ c : ℝ, ∀ᶠ y in 𝓝 x, F y = c + A.q i y := by
  let e₀ : A.core.TotalSpace :=
    ⟨x₀, WithTopology.toTopology ⊥ (-A.q (A.indexAt x₀) x₀)⟩
  have hcover : IsCoveringMap A.core.proj :=
    FiberBundle.isCoveringMap (F := WithDiscreteTopology ℝ) (E := A.core.Fiber)
  obtain ⟨s, hs, _⟩ :=
    hcover.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ e₀ rfl
  have hsection : ∀ x, A.core.proj (s x) = x := fun x => congr_fun hs.2 x
  refine ⟨fun x => A.value (s x), ?_, ?_⟩
  · change A.value (s x₀) = 0
    rw [hs.1]
    change A.q (A.indexAt x₀) x₀ + (-A.q (A.indexAt x₀) x₀) = 0
    exact add_neg_cancel _
  · intro i x hx
    exact A.section_local_eq s hsection i x hx

end AdditiveAtlas

section Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : Set E} {ω : E → E →L[ℝ] ℝ}

/-- Chosen local data, with derivatives restricted to the domain subtype.
Containment is used to return ambient overlap points to that subtype. -/
def atlasOfPrimitiveBalls (r : Ω → ℝ) (hr : ∀ a, 0 < r a)
    (q : Ω → E → ℝ) (hsub : ∀ (a : Ω), ball (a : E) (r a) ⊆ Ω)
    (hd : ∀ (a : Ω) (z : Ω), (z : E) ∈ ball (a : E) (r a) →
      HasFDerivAt (q a) (ω z) (z : E)) : AdditiveAtlas Ω Ω where
  domain := fun a => Subtype.val ⁻¹' ball (a : E) (r a)
  isOpen_domain := fun _ => isOpen_ball.preimage continuous_subtype_val
  indexAt := id
  mem_domain := fun a => by simpa using hr a
  q := fun a z => q a z
  overlap := by
    intro a b
    have ha : ∀ z ∈ ball (a : E) (r a) ∩ ball (b : E) (r b),
        HasFDerivAt (q a) (ω z) z := fun z hz => hd a ⟨z, hsub a hz.1⟩ hz.1
    have hb : ∀ z ∈ ball (a : E) (r a) ∩ ball (b : E) (r b),
        HasFDerivAt (q b) (ω z) z := fun z hz => hd b ⟨z, hsub b hz.2⟩ hz.2
    obtain ⟨c, hc⟩ := (isOpen_ball.inter isOpen_ball).exists_eq_add_of_fderiv_eq
      ((convex_ball (a : E) (r a)).inter (convex_ball (b : E) (r b))).isPreconnected
      (fun z hz => (ha z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hb z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (ha z hz).fderiv.trans (hb z hz).fderiv.symm)
    refine ⟨c, ?_⟩
    intro z hz
    have heq : q a z = q b z + c := hc hz
    change q a (z : E) - q b (z : E) = c
    rw [heq]
    ring

/-- Ambient totalization bridge. Openness upgrades the subtype neighborhood
equality to an ambient one before applying derivative congruence. -/
theorem totalize_hasFDerivAt (hΩ : IsOpen Ω) (F : Ω → ℝ) (q : E → ℝ)
    (x : Ω) (c : ℝ) (he : ∀ᶠ y in 𝓝 x, F y = c + q y)
    (hq : HasFDerivAt q (ω x) (x : E)) :
    HasFDerivAt (fun z => if hz : z ∈ Ω then F ⟨z, hz⟩ else 0) (ω x) (x : E) := by
  classical
  let Q : E → ℝ := fun z => if hz : z ∈ Ω then F ⟨z, hz⟩ else 0
  have he' : ∀ᶠ (y : Ω) in 𝓝 x, Q (y : E) = c + q (y : E) := by
    filter_upwards [he] with y hy
    simpa only [Q, dif_pos y.property] using hy
  have heAmbient : Q =ᶠ[𝓝 (x : E)] (fun z => c + q z) := by
    rw [← hΩ.isOpenEmbedding_subtypeVal.map_nhds_eq x]
    exact Filter.eventually_map.mpr he'
  exact (hq.const_add c).congr_of_eventuallyEq heAmbient

/-- The normalized nonempty branch, still for arbitrary real normed spaces.
The local primitive hypotheses already imply all analytic regularity used. -/
theorem exists_global_primitive_normalized (hΩ : IsOpen Ω) (hsc : IsSimplyConnected Ω)
    (x₀ : Ω)
    (hlocal : ∀ a ∈ Ω, ∃ r > 0, ∃ q : E → ℝ,
      ball a r ⊆ Ω ∧ ∀ z ∈ ball a r, HasFDerivAt q (ω z) z) :
    ∃ Q : E → ℝ, Q x₀ = 0 ∧ ∀ z ∈ Ω, HasFDerivAt Q (ω z) z := by
  classical
  letI : SimplyConnectedSpace Ω := hsc.simplyConnectedSpace
  letI : LocallyPathConnectedSpace E := LocallyPathConnectedSpace.of_bases
    (fun x : E => Metric.nhds_basis_ball)
    (fun x r hr => (convex_ball x r).isPathConnected ⟨x, by simpa using hr⟩)
  letI : LocallyPathConnectedSpace Ω := hΩ.locallyPathConnectedSpace
  have hdata : ∀ a : Ω, ∃ r > 0, ∃ q : E → ℝ,
      ball (a : E) r ⊆ Ω ∧ ∀ z ∈ ball (a : E) r, HasFDerivAt q (ω z) z :=
    fun a => hlocal a a.property
  choose r hr q hsub hd using hdata
  let A : AdditiveAtlas Ω Ω := atlasOfPrimitiveBalls r hr q hsub (fun a z hz => hd a z hz)
  obtain ⟨F, hF₀, hF⟩ := A.exists_glued_normalized x₀
  let Q : E → ℝ := fun z => if hz : z ∈ Ω then F ⟨z, hz⟩ else 0
  refine ⟨Q, ?_, ?_⟩
  · simpa only [Q, dif_pos x₀.property] using hF₀
  · intro z hz
    let x : Ω := ⟨z, hz⟩
    have hx : x ∈ A.domain x := A.mem_domain x
    obtain ⟨c, hc⟩ := hF x x hx
    have hxball : z ∈ ball (x : E) (r x) := by
      change z ∈ ball z (r x)
      exact mem_ball_self (hr x)
    have hq : HasFDerivAt (q x) (ω z) z := hd x z hxball
    exact totalize_hasFDerivAt hΩ F (q x) x c hc hq

/-- Exact B4 analytic target, including the empty domain and dimension zero.
No global Q, covering, section, finite dimension, or continuity of ω is input. -/
theorem exists_global_primitive (hΩ : IsOpen Ω) (hsc : Ω = ∅ ∨ IsSimplyConnected Ω)
    (hlocal : ∀ a ∈ Ω, ∃ r > 0, ∃ q : E → ℝ,
      ball a r ⊆ Ω ∧ ∀ z ∈ ball a r, HasFDerivAt q (ω z) z) :
    ∃ Q : E → ℝ, ∀ z ∈ Ω, HasFDerivAt Q (ω z) z := by
  rcases hsc with hempty | hsc
  · refine ⟨fun _ => 0, ?_⟩
    intro z hz
    rw [hempty] at hz
    exact False.elim hz
  · obtain ⟨z, hz⟩ := hsc.nonempty
    obtain ⟨Q, _, hQ⟩ := exists_global_primitive_normalized hΩ hsc ⟨z, hz⟩ hlocal
    exact ⟨Q, hQ⟩

/-- An arbitrary continuous contraction suffices. Its center need not remain
fixed during the homotopy. This is a bind-only contractibility application. -/
theorem exists_global_primitive_of_contraction (hΩ : IsOpen Ω)
    (b : Ω) (K : C(I × Ω, Ω)) (hK₀ : ∀ z, K (0, z) = z)
    (hK₁ : ∀ z, K (1, z) = b)
    (hlocal : ∀ a ∈ Ω, ∃ r > 0, ∃ q : E → ℝ,
      ball a r ⊆ Ω ∧ ∀ z ∈ ball a r, HasFDerivAt q (ω z) z) :
    ∃ Q : E → ℝ, ∀ z ∈ Ω, HasFDerivAt Q (ω z) z := by
  let H : (ContinuousMap.id Ω).Homotopy (ContinuousMap.const Ω b) :=
    { toContinuousMap := K
      map_zero_left := hK₀
      map_one_left := hK₁ }
  letI : ContractibleSpace Ω :=
    (contractible_iff_id_nullhomotopic Ω).mpr ⟨b, ⟨H⟩⟩
  have hsc : IsSimplyConnected Ω := (inferInstance : SimplyConnectedSpace Ω)
  exact exists_global_primitive hΩ (Or.inr hsc) hlocal

/-- The formula is exactly T((1-t) T⁻¹(z) + t c), in subtype coordinates.
The source need only be convex and contain c; source openness is unused. -/
def convexHomeomorphContraction {D : Set E} (hD : Convex ℝ D)
    (T : D ≃ₜ Ω) (c : D) : C(I × Ω, Ω) where
  toFun p := T ⟨(1 - (p.1 : ℝ)) • (T.symm p.2 : E) + (p.1 : ℝ) • (c : E),
    hD (T.symm p.2).property c.property
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩
  continuous_toFun := by
    apply T.continuous.comp
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (T.symm.continuous.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const)

theorem convexHomeomorphContraction_zero {D : Set E} (hD : Convex ℝ D)
    (T : D ≃ₜ Ω) (c : D) (z : Ω) : convexHomeomorphContraction hD T c (0, z) = z := by
  calc
    convexHomeomorphContraction hD T c (0, z) = T (T.symm z) := by
      change T _ = T (T.symm z)
      apply congrArg T
      apply Subtype.ext
      simp
    _ = z := T.apply_symm_apply z

theorem convexHomeomorphContraction_one {D : Set E} (hD : Convex ℝ D)
    (T : D ≃ₜ Ω) (c : D) (z : Ω) : convexHomeomorphContraction hD T c (1, z) = T c := by
  change T _ = T c
  apply congrArg T
  apply Subtype.ext
  simp

/-- Live use of the explicit contraction, for any covector field satisfying
the actual local primitive data. There is no derivative of T or K. -/
theorem exists_global_primitive_of_homeomorph {D : Set E} (hΩ : IsOpen Ω)
    (hD : Convex ℝ D) (hne : D.Nonempty) (T : D ≃ₜ Ω)
    (hlocal : ∀ a ∈ Ω, ∃ r > 0, ∃ q : E → ℝ,
      ball a r ⊆ Ω ∧ ∀ z ∈ ball a r, HasFDerivAt q (ω z) z) :
    ∃ Q : E → ℝ, ∀ z ∈ Ω, HasFDerivAt Q (ω z) z := by
  obtain ⟨c, hc⟩ := hne
  exact exists_global_primitive_of_contraction hΩ (T ⟨c, hc⟩)
    (convexHomeomorphContraction hD T ⟨c, hc⟩)
    (convexHomeomorphContraction_zero hD T ⟨c, hc⟩)
    (convexHomeomorphContraction_one hD T ⟨c, hc⟩) hlocal

end Analysis

end CFMP137Transient

end

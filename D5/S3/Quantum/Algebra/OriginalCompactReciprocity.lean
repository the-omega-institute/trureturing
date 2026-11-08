/- GID: D5/S3/Quantum/Algebra/OriginalCompactReciprocity
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/OriginalCompactReciprocity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual original matrix-group velocities and the complete first-order relation. -/

import D5.S3.Quantum.Algebra.OriginalCompactActionMetric
import D5.S3.Quantum.Algebra.RankOneInvariantMetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Field
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace D5.S3.Quantum.Algebra.OriginalCompactReciprocity

set_option backward.isDefEq.respectTransparency false

attribute [local instance] LieRing.ofAssociativeRing

open OriginalCompactActionMetric Module
open scoped Topology InnerProductSpace
noncomputable section
universe u
variable {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
variable (G : MatrixGroup W)

/-- Velocities in the actual ambient matrix space of actual G-valued curves at 1. -/
def velocitySpace : Submodule ℝ (W →L[ℝ] W) where
  carrier := {K | ∃ c : ℝ → G, c 0 = 1 ∧ HasDerivAt (fun t => (c t).val.val) K 0}
  zero_mem' := ⟨fun _ => 1,rfl,hasDerivAt_const 0 1⟩
  add_mem' := by
    rintro K L ⟨c,hc,hK⟩ ⟨d,hd,hL⟩
    refine ⟨fun t => c t * d t,by simp [hc,hd],?_⟩
    simpa [hc,hd] using! hK.mul hL
  smul_mem' := by
    rintro r K ⟨c,hc,hK⟩
    refine ⟨fun t => c (r*t),by simpa using hc,?_⟩
    have hr : HasDerivAt (fun t : ℝ => r*t) r 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
    have hk : HasDerivAt (fun t => (c t).val.val) K (r*0) := by simpa using hK
    have hh := hk.scomp (0 : ℝ) hr
    simpa using! hh

/-- Actual curve velocities are exactly the generators whose entire real
exponential curve has values in the original compact subgroup. -/
theorem mem_velocitySpace_iff_exp (hG : IsCompact (G : Set (W →L[ℝ] W)ˣ)) (K : W →L[ℝ] W) :
    K ∈ velocitySpace G ↔ ∀ t : ℝ, ∃ u : (W →L[ℝ] W)ˣ, u ∈ G ∧ (u : W →L[ℝ] W) = NormedSpace.exp (t • K) := by
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  constructor
  · rintro ⟨c, hc, hK⟩ t
    let E := W →L[ℝ] W
    letI : NormedAlgebra ℚ E := .restrictScalars ℚ ℝ E
    have hexp : HasStrictFDerivAt (NormedSpace.exp : E → E)
        (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 := by
      simpa using! (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := E))
    let ell : E → E := hexp.localInverse NormedSpace.exp (ContinuousLinearEquiv.refl ℝ E) 0
    have hell0 : ell 1 = 0 := by simpa [ell] using hexp.localInverse_apply_image
    have hell : HasFDerivAt ell (ContinuousLinearMap.id ℝ E) 1 := by simpa [ell] using! hexp.to_localInverse.hasFDerivAt
    have hc0 : (c 0).val.val = (1 : E) := by simp [hc]
    have hd : HasDerivAt (fun s => ell ((c s).val.val)) K 0 := by
      simpa only [Function.comp_apply, ContinuousLinearMap.id_apply] using!
        hell.comp_hasDerivAt_of_eq (0 : ℝ) hK hc0.symm
    have hscale : Filter.Tendsto (fun n : ℕ => (n : ℝ) • ell ((c (t / n)).val.val))
        Filter.atTop (𝓝 (t • K)) := by
      have hn : Filter.Tendsto (fun n : ℕ => ‖(n : ℝ)‖) Filter.atTop Filter.atTop := by
        simpa using (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa [hc0, hell0, div_eq_mul_inv, mul_comm] using hd.hasFDerivAt.lim t hn
    have hinv : ∀ᶠ y in 𝓝 (1 : E), NormedSpace.exp (ell y) = y := by simpa [ell] using hexp.eventually_right_inverse
    have hsample : Filter.Tendsto (fun n : ℕ => (c (t / n)).val.val)
        Filter.atTop (𝓝 (1 : E)) := by
      simpa only [hc0, Function.comp_def] using! hK.continuousAt.tendsto.comp
        (tendsto_const_div_atTop_nhds_zero_nat t)
    have hpow : Filter.Tendsto (fun n : ℕ => ((c (t / n)).val.val) ^ n)
        Filter.atTop (𝓝 (NormedSpace.exp (t • K))) := by
      apply hscale.exp.congr'
      filter_upwards [hsample.eventually hinv] with n hn
      rw [Nat.cast_smul_eq_nsmul ℝ, NormedSpace.exp_nsmul, hn]
    have hclosed : IsClosed ((Units.val : Eˣ → E) '' (G : Set Eˣ)) := (hG.image Units.continuous_val).isClosed
    exact hclosed.mem_of_tendsto hpow (Filter.Eventually.of_forall fun n =>
      ⟨(c (t / n)).val ^ n, G.pow_mem (c (t / n)).property n, rfl⟩)
  · intro h
    choose u hu he using h
    refine ⟨fun t => ⟨u t, hu t⟩, ?_, ?_⟩
    · apply Subtype.ext
      apply Units.ext
      simpa using he 0
    · have heq : (fun t => (u t).val) = fun t => NormedSpace.exp (t • K) := funext he
      change HasDerivAt (fun t => (u t).val) K 0
      rw [heq]
      simpa using (hasDerivAt_exp_smul_const K (0 : ℝ))

private def exponentialUnit (K : W →L[ℝ] W) : (W →L[ℝ] W)ˣ := by
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  letI : NormedAlgebra ℚ (W →L[ℝ] W) := .restrictScalars ℚ ℝ _
  exact (NormedSpace.isUnit_exp K).unit

private theorem exponentialUnit_val (K : W →L[ℝ] W) : (exponentialUnit K : W →L[ℝ] W) = NormedSpace.exp K := by
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  letI : NormedAlgebra ℚ (W →L[ℝ] W) := .restrictScalars ℚ ℝ _
  exact IsUnit.unit_spec _

private theorem exponentialUnit_inv_val (K : W →L[ℝ] W) : ((exponentialUnit K)⁻¹).val = NormedSpace.exp (-K) := by
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  letI : NormedAlgebra ℚ (W →L[ℝ] W) := .restrictScalars ℚ ℝ _
  rw [← Ring.inverse_unit, exponentialUnit_val, Ring.inverse_exp]

private theorem continuous_exponentialUnit (K : W →L[ℝ] W) : Continuous (fun t : ℝ => exponentialUnit (t • K)) := by
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  letI : NormedAlgebra ℚ (W →L[ℝ] W) := .restrictScalars ℚ ℝ _
  have hc : Continuous (fun t : ℝ => t • K) := continuous_id.smul continuous_const
  have he : Continuous (NormedSpace.exp : (W →L[ℝ] W) → (W →L[ℝ] W)) := NormedSpace.exp_continuous
  apply Units.continuous_iff.mpr
  constructor
  · simpa only [Function.comp_def, exponentialUnit_val] using! he.comp hc
  · simpa only [Function.comp_def, exponentialUnit_inv_val] using! he.comp hc.neg

private theorem exponential_in_identityComponent (hG : IsCompact (G : Set (W →L[ℝ] W)ˣ)) (K : W →L[ℝ] W)
    (hK : K ∈ velocitySpace G) (t : ℝ) : ∃ g : G, g ∈ connectedComponent (1 : G) ∧
      g.val.val = NormedSpace.exp (t • K) := by
  have hm (s : ℝ) : exponentialUnit (s • K) ∈ G := by
    obtain ⟨u, hu, he⟩ := (mem_velocitySpace_iff_exp G hG K).mp hK s
    have hu_eq : u = exponentialUnit (s • K) := by
      apply Units.ext
      exact he.trans (exponentialUnit_val _).symm
    exact hu_eq ▸ hu
  let c : ℝ → G := fun s => ⟨exponentialUnit (s • K), hm s⟩
  have hc : Continuous c := (continuous_exponentialUnit K).subtype_mk _
  have hc0 : c 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simp [c, exponentialUnit_val]
  refine ⟨c t, ?_, exponentialUnit_val _⟩
  exact (isPreconnected_range hc).subset_connectedComponent ⟨0, hc0⟩ ⟨t, rfl⟩

omit [FiniteDimensional ℝ W] in
private theorem conjugate_velocity (g : G) (K : W →L[ℝ] W) (hK : K ∈ velocitySpace G) :
    (g.val.val * K * g⁻¹.val.val) ∈ velocitySpace G := by
  obtain ⟨c,hc,hcK⟩ := hK
  refine ⟨fun t => g * c t * g⁻¹,by simp [hc],?_⟩
  simpa [hc] using ((hasDerivAt_const (0 : ℝ) g.val.val).mul hcK).mul_const g⁻¹.val.val

private theorem bracket_velocity (K L : W →L[ℝ] W) (hK : K ∈ velocitySpace G) (hL : L ∈ velocitySpace G) :
    ⁅K,L⁆ ∈ velocitySpace G := by
  obtain ⟨c,hc,hcK⟩ := hK
  have hinv : HasDerivAt (fun t => (c t)⁻¹.val.val) (-K) 0 := by
    have hh := (hasFDerivAt_ringInverse (𝕜 := ℝ) (c 0).val).comp_hasDerivAt
      (0 : ℝ) hcK
    simpa [hc,Function.comp_def,Ring.inverse_unit,ContinuousLinearMap.mulLeftRight_apply] using! hh
  have hd := (hcK.mul_const L).mul hinv
  have hh : HasDerivAt (fun t => (c t).val.val * L * (c t)⁻¹.val.val)
      (K*L-L*K) 0 := by
    simpa [hc,sub_eq_add_neg] using! hd
  have hm : ∀ t : ℝ, (c t).val.val * L * (c t)⁻¹.val.val ∈ velocitySpace G := fun t => conjugate_velocity G (c t) L hL
  have hz := mem_closure_of_tendsto hh.tendsto_slope
    (Filter.Eventually.of_forall fun t => (velocitySpace G).smul_mem _ ((velocitySpace G).sub_mem (hm t) (hm 0)))
  rw [(velocitySpace G).closed_of_finiteDimensional.closure_eq] at hz
  exact hz

/-- The actual curve velocities form a Lie algebra under the actual matrix commutator. -/
def curveLieAlgebra : LieSubalgebra ℝ (W →L[ℝ] W) := { velocitySpace G with
    lie_mem' := fun hK hL => bracket_velocity G _ _ hK hL }

abbrev OriginalLie := curveLieAlgebra G

/-- Evaluation uses the same actual matrices and the same full W. -/
def evaluation (x : W) : OriginalLie G →ₗ[ℝ] W where
  toFun K := K.val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The full relation is the image of all solutions, with no selected branch. -/
def fullRelation (A : OriginalLie G) (x : W) :
    Submodule ℝ ((OriginalLie G ⧸ Submodule.span ℝ {A}) × (W ⧸ Submodule.span ℝ {x})) :=
  (LinearMap.ker ((evaluation G x).coprod A.val.toLinearMap)).map
    ((Submodule.span ℝ {A}).mkQ.prodMap (Submodule.span ℝ {x}).mkQ)

/-- The first canonical projection of the entire solution relation. -/
def firstProjection (A : OriginalLie G) (x : W) : fullRelation G A x →ₗ[ℝ] (OriginalLie G ⧸ Submodule.span ℝ {A}) :=
  (LinearMap.fst ℝ _ _).comp (fullRelation G A x).subtype

/-- The second canonical projection of the entire solution relation. -/
def secondProjection (A : OriginalLie G) (x : W) : fullRelation G A x →ₗ[ℝ] (W ⧸ Submodule.span ℝ {x}) :=
  (LinearMap.snd ℝ _ _).comp (fullRelation G A x).subtype

/-- Both projections of the full relation must be bijective. -/
def FullReciprocity (A : OriginalLie G) (x : W) : Prop :=
  Function.Bijective (firstProjection G A x) ∧ Function.Bijective (secondProjection G A x)

private theorem relation_mem (A K : OriginalLie G) (x y : W) (h : K.val x + A.val y = 0) :
    ((Submodule.span ℝ {A}).mkQ K,(Submodule.span ℝ {x}).mkQ y) ∈ fullRelation G A x :=
  ⟨(K,y),h,rfl⟩

private theorem fullReciprocity_of_kernels_ranges (A : OriginalLie G) (x : W)
    (hA : LinearMap.ker A.val.toLinearMap = Submodule.span ℝ {x})
    (hE : LinearMap.ker (evaluation G x) = Submodule.span ℝ {A})
    (hrange : LinearMap.range A.val.toLinearMap = LinearMap.range (evaluation G x)) : FullReciprocity G A x := by
  constructor
  · constructor
    · rw [injective_iff_map_eq_zero]
      intro r hr
      obtain ⟨⟨K,y⟩, hsol, heq⟩ := r.property
      change K.val x + A.val y = 0 at hsol
      have hKq : (Submodule.span ℝ {A}).mkQ K = 0 := by exact (congrArg Prod.fst heq).trans hr
      have hKker : K ∈ LinearMap.ker (evaluation G x) := by
        rw [hE]
        exact (Submodule.Quotient.mk_eq_zero _).mp hKq
      have hKx : K.val x = 0 := hKker
      have hAy : A.val y = 0 := by simpa [hKx] using hsol
      have hyq : (Submodule.span ℝ {x}).mkQ y = 0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        rw [← hA]
        exact hAy
      apply Subtype.ext
      apply Prod.ext
      · exact hr
      · exact (congrArg Prod.snd heq).symm.trans hyq
    · intro q
      refine Submodule.Quotient.induction_on _ q ?_
      intro K
      have hneg : -(K.val x) ∈ LinearMap.range A.val.toLinearMap := by
        rw [hrange]
        exact (LinearMap.range (evaluation G x)).neg_mem ⟨K,rfl⟩
      obtain ⟨y, hy⟩ := hneg
      refine ⟨⟨((Submodule.span ℝ {A}).mkQ K, (Submodule.span ℝ {x}).mkQ y), relation_mem G A K x y ?_⟩, rfl⟩
      change K.val x + A.val y = 0
      change A.val y = -K.val x at hy
      rw [hy]
      simp
  · constructor
    · rw [injective_iff_map_eq_zero]
      intro r hr
      obtain ⟨⟨K,y⟩, hsol, heq⟩ := r.property
      change K.val x + A.val y = 0 at hsol
      have hyq : (Submodule.span ℝ {x}).mkQ y = 0 := (congrArg Prod.snd heq).trans hr
      have hyker : y ∈ LinearMap.ker A.val.toLinearMap := by
        rw [hA]
        exact (Submodule.Quotient.mk_eq_zero _).mp hyq
      have hAy : A.val y = 0 := hyker
      have hKx : K.val x = 0 := by simpa [hAy] using hsol
      have hKq : (Submodule.span ℝ {A}).mkQ K = 0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        rw [← hE]
        exact hKx
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg Prod.fst heq).symm.trans hKq
      · exact hr
    · intro q
      refine Submodule.Quotient.induction_on _ q ?_
      intro y
      have hneg : -(A.val y) ∈ LinearMap.range (evaluation G x) := by
        rw [← hrange]
        exact (LinearMap.range A.val.toLinearMap).neg_mem ⟨y,rfl⟩
      obtain ⟨K, hK⟩ := hneg
      refine ⟨⟨((Submodule.span ℝ {A}).mkQ K, (Submodule.span ℝ {x}).mkQ y), relation_mem G A K x y ?_⟩, rfl⟩
      change K.val x + A.val y = 0
      change K.val x = -A.val y at hK
      rw [hK]
      simp

private theorem kernel_lines (A : OriginalLie G) (x : W) (h : FullReciprocity G A x) :
    (∀ y : W, A.val y = 0 → y ∈ Submodule.span ℝ {x}) ∧
    (∀ K : OriginalLie G, K.val x = 0 → K ∈ Submodule.span ℝ {A}) := by
  constructor
  · intro y hy
    let z : fullRelation G A x := ⟨(0,(Submodule.span ℝ {x}).mkQ y),
      by simpa using relation_mem G A 0 x y (by simpa using hy)⟩
    have hz : z = 0 := h.1.1 (by rfl)
    have hq := congrArg (fun q : fullRelation G A x => q.val.2) hz
    exact (Submodule.Quotient.mk_eq_zero (Submodule.span ℝ {x})).mp hq
  · intro K hK
    let z : fullRelation G A x := ⟨((Submodule.span ℝ {A}).mkQ K,0),
      by simpa using relation_mem G A K x 0 (by simpa using hK)⟩
    have hz : z = 0 := h.2.1 (by rfl)
    have hq := congrArg (fun q : fullRelation G A x => q.val.1) hz
    exact (Submodule.Quotient.mk_eq_zero (Submodule.span ℝ {A})).mp hq

private theorem dimension_transfer (A : OriginalLie G) (x : W) (ha : A ≠ 0) (hx : x ≠ 0) (h : FullReciprocity G A x) :
    finrank ℝ (OriginalLie G) = finrank ℝ W := by
  let e := (LinearEquiv.ofBijective (firstProjection G A x) h.1).symm.trans
    (LinearEquiv.ofBijective (secondProjection G A x) h.2)
  have hq := e.finrank_eq
  have hA := (Submodule.span ℝ {A}).finrank_quotient_add_finrank
  have hx' := (Submodule.span ℝ {x}).finrank_quotient_add_finrank
  rw [finrank_span_singleton ha] at hA
  rw [finrank_span_singleton hx] at hx'
  omega

private theorem centralizer_line (B : InnerProductSpace.Core ℝ W)
    (hskew : ∀ K : OriginalLie G, ∀ u v : W, B.inner (K.val u) v = -B.inner u (K.val v))
    (A : OriginalLie G) (x : W) (hx : x ≠ 0) (hAx : A.val x = 0) (h : FullReciprocity G A x) :
    ∀ K : OriginalLie G, ⁅A,K⁆ = 0 → ∃ c : ℝ, K = c • A := by
  intro K hcomm
  have hAK : A.val (K.val x) = 0 := by
    have hh := congrArg (fun J : OriginalLie G => J.val x) hcomm
    change A.val (K.val x) - K.val (A.val x) = 0 at hh
    simpa [hAx] using hh
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp ((kernel_lines G A x h).1 _ hAK)
  have hs := hskew K x x
  have hb := B.conj_inner_symm x (K.val x)
  simp only [conj_trivial] at hb
  have hzero : B.inner (K.val x) x = 0 := by linarith
  have hxx : B.inner x x ≠ 0 := fun hz => hx (B.definite x hz)
  have hc0 : c = 0 := by
    rw [← hc,B.smul_left] at hzero
    simpa only [conj_trivial] using (mul_eq_zero.mp hzero).resolve_right hxx
  have hKx : K.val x = 0 := by simpa [hc0] using hc.symm
  obtain ⟨d,hd⟩ := Submodule.mem_span_singleton.mp ((kernel_lines G A x h).2 K hKx)
  exact ⟨d,hd.symm⟩

private theorem trace_square_positive {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : InnerProductSpace.Core ℝ V) (T : V →ₗ[ℝ] V) (hT : T ≠ 0)
    (hskew : ∀ u v : V, B.inner (T u) v = -B.inner u (T v)) : 0 < -LinearMap.trace ℝ V (T*T) := by
  classical
  let : NormedAddCommGroup V := B.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore B.toCore
  let b := stdOrthonormalBasis ℝ V
  have ht : -LinearMap.trace ℝ V (T*T) = ∑ i, ⟪T (b i),T (b i)⟫_ℝ := by
    rw [LinearMap.trace_eq_sum_inner (T*T) b,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (hskew (b i) (T (b i))).symm
  obtain ⟨i,hi⟩ : ∃ i, T (b i) ≠ 0 := by
    by_contra! hn
    apply hT
    apply b.toBasis.ext
    intro i
    exact hn i
  rw [ht]
  exact Finset.sum_pos' (fun i _ => real_inner_self_nonneg)
    ⟨i,Finset.mem_univ i,real_inner_self_pos.mpr hi⟩

private def tracePair (K L : OriginalLie G) : ℝ :=
  -(1/2 : ℝ) * LinearMap.trace ℝ W (K.val.toLinearMap * L.val.toLinearMap)

@[instance_reducible] private def traceCore (B : InnerProductSpace.Core ℝ W)
    (hskew : ∀ K : OriginalLie G, ∀ u v : W, B.inner (K.val u) v = -B.inner u (K.val v)) :
    InnerProductSpace.Core ℝ (OriginalLie G) where
  inner := tracePair G
  conj_inner_symm K L := by simp only [conj_trivial,tracePair,LinearMap.trace_mul_comm ℝ L.val.toLinearMap]
  re_inner_nonneg K := by
    change 0 ≤ tracePair G K K
    by_cases hK : K = 0
    · simp [hK,tracePair]
    · have hn : K.val.toLinearMap ≠ 0 := by
        intro hz
        apply hK
        apply Subtype.ext
        ext u
        exact LinearMap.congr_fun hz u
      have hp := trace_square_positive B K.val.toLinearMap hn (hskew K)
      dsimp [tracePair]
      linarith
  add_left K L J := by
    change -(1/2 : ℝ) * LinearMap.trace ℝ W
      ((K.val.toLinearMap+L.val.toLinearMap)*J.val.toLinearMap) = _
    simp only [add_mul,map_add,tracePair]
    ring
  smul_left K L r := by
    change -(1/2 : ℝ) * LinearMap.trace ℝ W
      ((r • K.val.toLinearMap)*L.val.toLinearMap) = _
    simp only [smul_mul_assoc,map_smul,smul_eq_mul,conj_trivial,tracePair]
    ring
  definite K hK := by
    by_contra hn
    have hT : K.val.toLinearMap ≠ 0 := by
      intro hz
      apply hn
      apply Subtype.ext
      ext u
      exact LinearMap.congr_fun hz u
    have hp := trace_square_positive B K.val.toLinearMap hT (hskew K)
    change tracePair G K K = 0 at hK
    dsimp [tracePair] at hK
    linarith

private theorem trace_invariant (B : InnerProductSpace.Core ℝ W)
    (hskew : ∀ K : OriginalLie G, ∀ u v : W, B.inner (K.val u) v = -B.inner u (K.val v)) (X Y Z : OriginalLie G) :
    (traceCore G B hskew).inner ⁅X,Y⁆ Z = -(traceCore G B hskew).inner Y ⁅X,Z⁆ := by
  change -(1/2 : ℝ) * LinearMap.trace ℝ W
    ((X.val.toLinearMap*Y.val.toLinearMap-Y.val.toLinearMap*X.val.toLinearMap)*Z.val.toLinearMap) =
    -(-(1/2 : ℝ) * LinearMap.trace ℝ W
      (Y.val.toLinearMap*(X.val.toLinearMap*Z.val.toLinearMap-Z.val.toLinearMap*X.val.toLinearMap)))
  simp only [sub_mul,mul_sub,map_sub]
  have hh := LinearMap.trace_mul_cycle ℝ Y.val.toLinearMap Z.val.toLinearMap X.val.toLinearMap
  simp only [mul_assoc] at hh ⊢
  linarith

/-- On the full original W and the actual curve Lie algebra of its compact matrix
subgroup, both projections of the full relation force dimension three. -/
theorem finrank_eq_three (hG : IsCompact (G : Set (W →L[ℝ] W)ˣ))
    (A : OriginalLie G) (x : W) (ha : A ≠ 0) (hx : x ≠ 0) (hAx : A.val x = 0) (h : FullReciprocity G A x) :
    finrank ℝ W = 3 ∧ finrank ℝ (OriginalLie G) = 3 := by
  obtain ⟨B,_hB,hcurves⟩ := compact_action_metric G hG
  have hskew : ∀ K : OriginalLie G, ∀ u v : W, B.inner (K.val u) v = -B.inner u (K.val v) := by
    intro K
    obtain ⟨c,hc,hcK⟩ := K.property
    exact hcurves c hc K.val hcK
  have hdim := dimension_transfer G A x ha hx h
  have hd := RankOneInvariantMetric.finrank_eq_one_or_three (traceCore G B hskew)
    (trace_invariant G B hskew) A ha (centralizer_line G B hskew A x hx hAx h)
  have hthree : finrank ℝ (OriginalLie G) = 3 := by
    rcases hd with hone | hthree
    · have hW : finrank ℝ W = 1 := hdim.symm.trans hone
      have hspan : Submodule.span ℝ {x} = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [finrank_span_singleton hx,hW])
      have hAz : A.val = 0 := by
        ext y
        have hy : y ∈ Submodule.span ℝ {x} := by rw [hspan]; trivial
        obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hy
        rw [← hr,map_smul,hAx,smul_zero]
        rfl
      exact False.elim (ha (Subtype.ext hAz))
    · exact hthree
  exact ⟨hdim.symm.trans hthree,hthree⟩

/-- The full orthogonal Lie algebra as actual skew endomorphisms of the same space. -/
def skewEndomorphisms {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : InnerProductSpace.Core ℝ V) : Submodule ℝ (V →ₗ[ℝ] V) := by
  let : NormedAddCommGroup V := B.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore B.toCore
  exact {
    carrier := {T | ∀ u v : V, ⟪T u,v⟫_ℝ = -⟪u,T v⟫_ℝ}
    zero_mem' := by simp
    add_mem' := by
      intro T U hT hU u v
      change ∀ u v : V, ⟪T u,v⟫_ℝ = -⟪u,T v⟫_ℝ at hT
      change ∀ u v : V, ⟪U u,v⟫_ℝ = -⟪u,U v⟫_ℝ at hU
      simp only [LinearMap.add_apply,inner_add_left,inner_add_right,hT,hU]
      ring
    smul_mem' := by
      intro r T hT u v
      change ∀ u v : V, ⟪T u,v⟫_ℝ = -⟪u,T v⟫_ℝ at hT
      simp only [LinearMap.smul_apply,real_inner_smul_left,real_inner_smul_right,hT]
      ring }

private theorem skew_plane_frame {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : InnerProductSpace.Core ℝ V) (hV : finrank ℝ V = 3) :
    ∃ (T : V →ₗ[ℝ] V) (x : V), T ∈ skewEndomorphisms B ∧ T ≠ 0 ∧ x ≠ 0 ∧ B.inner x x = 1 ∧ T x = 0 ∧
      LinearMap.ker T = Submodule.span ℝ {x} ∧ (∀ y, y ∈ LinearMap.range T ↔ B.inner x y = 0) := by
  classical
  let : NormedAddCommGroup V := B.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore B.toCore
  let b : OrthonormalBasis (Fin 3) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
  let T : V →ₗ[ℝ] V := (innerSL ℝ (b 0)).toLinearMap.smulRight (b 1) - (innerSL ℝ (b 1)).toLinearMap.smulRight (b 0)
  have hT (y : V) : T y = ⟪b 0,y⟫_ℝ • b 1 - ⟪b 1,y⟫_ℝ • b 0 := rfl
  have hs : T ∈ skewEndomorphisms B := by
    intro u v
    change ⟪T u,v⟫_ℝ = -⟪u,T v⟫_ℝ
    simp only [hT, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_comm u (b 0), real_inner_comm u (b 1)]
    ring
  have hT0 : T (b 0) = b 1 := by simp [hT, b.inner_eq_ite]
  have hT1 : T (b 1) = -b 0 := by simp [hT, b.inner_eq_ite]
  have hT2 : T (b 2) = 0 := by simp [hT, b.inner_eq_ite]
  have hTne : T ≠ 0 := by
    intro hz
    have := congrArg (fun f : V →ₗ[ℝ] V => f (b 0)) hz
    simp only [hT0, LinearMap.zero_apply] at this
    exact b.orthonormal.ne_zero 1 this
  have hexp (y : V) : y = ⟪b 0,y⟫_ℝ • b 0 + ⟪b 1,y⟫_ℝ • b 1 + ⟪b 2,y⟫_ℝ • b 2 := by
    simpa [Fin.sum_univ_succ, add_assoc] using (b.sum_repr' y).symm
  have hker : LinearMap.ker T = Submodule.span ℝ {b 2} := by
    apply le_antisymm
    · intro y hy
      change T y = 0 at hy
      have h0 : ⟪b 0,y⟫_ℝ = 0 := by
        have := congrArg (fun z => ⟪b 1,z⟫_ℝ) hy
        simpa [hT, inner_sub_right, real_inner_smul_right, b.inner_eq_ite] using this
      have h1 : ⟪b 1,y⟫_ℝ = 0 := by
        have := congrArg (fun z => ⟪b 0,z⟫_ℝ) hy
        simpa [hT, inner_sub_right, real_inner_smul_right, b.inner_eq_ite] using this
      apply Submodule.mem_span_singleton.mpr
      refine ⟨⟪b 2,y⟫_ℝ, ?_⟩
      simpa [h0,h1] using (hexp y).symm
    · apply Submodule.span_le.mpr
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hT2
  refine ⟨T, b 2, hs, hTne, b.orthonormal.ne_zero 2, ?_, hT2, hker, ?_⟩
  · change ⟪b 2,b 2⟫_ℝ = 1
    simp [b.inner_eq_ite]
  · intro y
    constructor
    · rintro ⟨z,rfl⟩
      change ⟪b 2,T z⟫_ℝ = 0
      simp [hT, inner_sub_right, real_inner_smul_right, b.inner_eq_ite]
    · intro hy
      change ⟪b 2,y⟫_ℝ = 0 at hy
      refine ⟨⟪b 1,y⟫_ℝ • b 0 - ⟪b 0,y⟫_ℝ • b 1, ?_⟩
      rw [map_sub, map_smul, map_smul, hT0, hT1, smul_neg, sub_neg_eq_add]
      simpa [hy, add_comm] using (hexp y).symm

private theorem skew_realizes_perp {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : InnerProductSpace.Core ℝ V) (x y : V) (hxx : B.inner x x = 1) (hxy : B.inner x y = 0) :
    ∃ S : V →ₗ[ℝ] V, S ∈ skewEndomorphisms B ∧ S x = y := by
  let : NormedAddCommGroup V := B.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore B.toCore
  let S : V →ₗ[ℝ] V := (innerSL ℝ x).toLinearMap.smulRight y - (innerSL ℝ y).toLinearMap.smulRight x
  have hS (u : V) : S u = ⟪x,u⟫_ℝ • y - ⟪y,u⟫_ℝ • x := rfl
  refine ⟨S, ?_, ?_⟩
  · intro u v
    change ⟪S u,v⟫_ℝ = -⟪u,S v⟫_ℝ
    simp only [hS, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    simp only [real_inner_comm u x, real_inner_comm u y]
    ring
  · change ⟪x,x⟫_ℝ = 1 at hxx
    change ⟪x,y⟫_ℝ = 0 at hxy
    have hyx : ⟪y,x⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact hxy
    simp only [hS, hxx, hyx, one_smul, zero_smul, sub_zero]

private theorem skew_dimension_le_three {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : InnerProductSpace.Core ℝ V) (hV : finrank ℝ V = 3) (S : Submodule ℝ (V →ₗ[ℝ] V))
    (hS : ∀ T : S, ∀ u v : V, B.inner (T.val u) v = -B.inner u (T.val v)) : finrank ℝ S ≤ 3 := by
  classical
  let : NormedAddCommGroup V := B.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore B.toCore
  let b : OrthonormalBasis (Fin 3) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
  let f : S →ₗ[ℝ] (ℝ × ℝ × ℝ) := {
    toFun T := (⟪T.val (b 0),b 1⟫_ℝ,⟪T.val (b 0),b 2⟫_ℝ,⟪T.val (b 1),b 2⟫_ℝ)
    map_add' := by intro T U; ext <;> simp [inner_add_left]
    map_smul' := by intro r T; ext <;> simp [real_inner_smul_left] }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro T hT
    have h01 : ⟪T.val (b 0),b 1⟫_ℝ = 0 := congrArg Prod.fst hT
    have h02 : ⟪T.val (b 0),b 2⟫_ℝ = 0 := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hT
    have h12 : ⟪T.val (b 1),b 2⟫_ℝ = 0 := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hT
    have hdiag (v : V) : ⟪T.val v,v⟫_ℝ = 0 := by
      have hh := hS T v v
      change ⟪T.val v,v⟫_ℝ = -⟪v,T.val v⟫_ℝ at hh
      have hs := real_inner_comm (T.val v) v
      linarith
    have hswap (i j : Fin 3) : ⟪T.val (b i),b j⟫_ℝ = -⟪T.val (b j),b i⟫_ℝ := by
      rw [hS T (b i) (b j),real_inner_comm (b i) (T.val (b j))]
    have hall (i j : Fin 3) : ⟪T.val (b i),b j⟫_ℝ = 0 := by
      fin_cases i <;> fin_cases j
      · exact hdiag _
      · exact h01
      · exact h02
      · rw [hswap]; simpa using congrArg (fun z : ℝ => -z) h01
      · exact hdiag _
      · exact h12
      · rw [hswap]; simpa using congrArg (fun z : ℝ => -z) h02
      · rw [hswap]; simpa using congrArg (fun z : ℝ => -z) h12
      · exact hdiag _
    apply Subtype.ext
    apply b.toBasis.ext
    intro i
    change T.val (b i) = 0
    apply b.repr.injective
    ext j
    simp only [map_zero, PiLp.zero_apply]
    rw [b.repr_apply_apply,real_inner_comm]
    exact hall i j
  have hh := LinearMap.finrank_le_finrank_of_injective hf
  simpa using hh

/-- The faithful original inclusion, without a replacement representation. -/
def originalAction : OriginalLie G →ₗ[ℝ] (W →ₗ[ℝ] W) where
  toFun K := K.val.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original full relation gives both dimensions and exactly the full
orthogonal Lie algebra of a metric constructed from the original compact group. -/
theorem original_rigidity (hG : IsCompact (G : Set (W →L[ℝ] W)ˣ))
    (A : OriginalLie G) (x : W) (ha : A ≠ 0) (hx : x ≠ 0) (hAx : A.val x = 0) (h : FullReciprocity G A x) :
    ∃ B : InnerProductSpace.Core ℝ W, (∀ (g : G) (u v : W), B.inner (g.val.val u) (g.val.val v) = B.inner u v) ∧
      finrank ℝ W = 3 ∧ finrank ℝ (OriginalLie G) = 3 ∧ LinearMap.range (originalAction G) = skewEndomorphisms B := by
  obtain ⟨B,hB,hcurves⟩ := compact_action_metric G hG
  have hskew : ∀ K : OriginalLie G, ∀ u v : W, B.inner (K.val u) v = -B.inner u (K.val v) := by
    intro K
    obtain ⟨c,hc,hcK⟩ := K.property
    exact hcurves c hc K.val hcK
  have hd := finrank_eq_three G hG A x ha hx hAx h
  refine ⟨B,hB,hd.1,hd.2,?_⟩
  have hinj : Function.Injective (originalAction G) := by
    intro K L hKL
    apply Subtype.ext
    ext u
    exact LinearMap.congr_fun hKL u
  have hle : LinearMap.range (originalAction G) ≤ skewEndomorphisms B := by
    rintro T ⟨K,rfl⟩
    exact hskew K
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [LinearMap.finrank_range_of_inj hinj,hd.2]
  exact skew_dimension_le_three B hd.1 (skewEndomorphisms B) (fun T => T.property)

private theorem determinant_sq_of_preserves {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : InnerProductSpace.Core ℝ V) (e : V ≃ₗ[ℝ] V)
    (he : ∀ u v : V, B.inner (e u) (e v) = B.inner u v) : LinearMap.det e.toLinearMap ^ 2 = 1 := by
  classical
  let : NormedAddCommGroup V := B.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore B.toCore
  let f : V ≃ₗᵢ[ℝ] V := e.isometryOfInner he
  let b := stdOrthonormalBasis ℝ V
  have hh := (Matrix.det_of_mem_unitary (f.toMatrix_mem_unitaryGroup b b)).2
  change star (Matrix.det (LinearMap.toMatrix b.toBasis b.toBasis e.toLinearMap)) *
    Matrix.det (LinearMap.toMatrix b.toBasis b.toBasis e.toLinearMap) = 1 at hh
  simpa only [star_trivial, ← sq, LinearMap.det_toMatrix] using hh

private theorem determinant_one_on_component (B : InnerProductSpace.Core ℝ W)
    (hB : ∀ (g : G) (u v : W), B.inner (g.val.val u) (g.val.val v) = B.inner u v) :
    ∀ g ∈ connectedComponent (1 : G), g.val.val.det = 1 := by
  let d : G → ℝ := fun g => g.val.val.det
  have hd : Continuous d := ContinuousLinearMap.continuous_det.comp
    (Units.continuous_val.comp continuous_subtype_val)
  have hsq : Set.EqOn (d ^ 2) 1 (connectedComponent (1 : G)) := by
    intro g _
    exact determinant_sq_of_preserves B
      (ContinuousLinearEquiv.unitsEquiv ℝ W g.val).toLinearEquiv (hB g)
  have hone : d (1 : G) = 1 := by
    change LinearMap.det (1 : W →ₗ[ℝ] W) = 1
    exact map_one _
  rcases isPreconnected_connectedComponent.eq_one_or_eq_neg_one_of_sq_eq
      hd.continuousOn hsq with heq | heq
  · exact fun g hg => heq hg
  · have hh : (1 : ℝ) = -1 := hone.symm.trans (heq mem_connectedComponent)
    norm_num at hh

/-- Every skew generator for the derived metric exponentiates inside the actual
identity component of the original group, on the same full W. -/
theorem original_exponential_rigidity (hG : IsCompact (G : Set (W →L[ℝ] W)ˣ))
    (A : OriginalLie G) (x : W) (ha : A ≠ 0) (hx : x ≠ 0) (hAx : A.val x = 0) (h : FullReciprocity G A x) :
    ∃ B : InnerProductSpace.Core ℝ W, (∀ (g : G) (u v : W), B.inner (g.val.val u) (g.val.val v) = B.inner u v) ∧
      finrank ℝ W = 3 ∧ finrank ℝ (OriginalLie G) = 3 ∧ LinearMap.range (originalAction G) = skewEndomorphisms B ∧
      (∀ g ∈ connectedComponent (1 : G), g.val.val.det = 1) ∧ ∀ K : W →L[ℝ] W, K.toLinearMap ∈ skewEndomorphisms B →
        ∀ t : ℝ, ∃ g : G, g ∈ connectedComponent (1 : G) ∧ g.val.val = NormedSpace.exp (t • K) := by
  obtain ⟨B, hB, hW, hL, hrange⟩ := original_rigidity G hG A x ha hx hAx h
  refine ⟨B, hB, hW, hL, hrange, determinant_one_on_component G B hB, ?_⟩
  intro K hK t
  rw [← hrange] at hK
  obtain ⟨L, hLK⟩ := hK
  have he : L.val = K := by
    ext u
    exact LinearMap.congr_fun hLK u
  apply exponential_in_identityComponent G hG K _ t
  have hLmem : L.val ∈ velocitySpace G := L.property
  exact he ▸ hLmem
/-- The reverse Q8 implication uses both projections of the entire original
relation on the original W and original group tangent algebra. -/
theorem fullReciprocity_of_full_skew (B : InnerProductSpace.Core ℝ W) (hW : finrank ℝ W = 3)
    (hfull : LinearMap.range (originalAction G) = skewEndomorphisms B) : ∃ (A : OriginalLie G) (x : W),
      A ≠ 0 ∧ x ≠ 0 ∧ A.val x = 0 ∧ FullReciprocity G A x := by
  obtain ⟨T,x,hT,hTne,hx,hxx,hTx,hkerT,hrT⟩ := skew_plane_frame B hW
  have hTrange : T ∈ LinearMap.range (originalAction G) := by
    rw [hfull]
    exact hT
  obtain ⟨A,hAT⟩ := hTrange
  change A.val.toLinearMap = T at hAT
  have hAne : A ≠ 0 := by
    intro hz
    apply hTne
    simpa [hz] using hAT.symm
  have hAx : A.val x = 0 := (LinearMap.congr_fun hAT x).trans hTx
  have hkerA : LinearMap.ker A.val.toLinearMap = Submodule.span ℝ {x} := by
    rw [hAT]
    exact hkerT
  have hErange : LinearMap.range (evaluation G x) = LinearMap.range T := by
    apply le_antisymm
    · rintro y ⟨K,rfl⟩
      apply (hrT _).mpr
      have hs : K.val.toLinearMap ∈ skewEndomorphisms B := by
        rw [← hfull]
        exact ⟨K,rfl⟩
      have hd : B.inner (K.val x) x = -B.inner x (K.val x) := hs x x
      have hc := B.conj_inner_symm x (K.val x)
      simp only [conj_trivial] at hc
      change B.inner x (K.val x) = 0
      linarith
    · intro y hy
      obtain ⟨S,hS,hSx⟩ := skew_realizes_perp B x y hxx ((hrT y).mp hy)
      rw [← hfull] at hS
      obtain ⟨K,hK⟩ := hS
      refine ⟨K, ?_⟩
      exact (LinearMap.congr_fun hK x).trans hSx
  have hErank : finrank ℝ (LinearMap.range (evaluation G x)) = 2 := by
    have hr := T.finrank_range_add_finrank_ker
    rw [hkerT, finrank_span_singleton hx, hW] at hr
    rw [hErange]
    omega
  have hinj : Function.Injective (originalAction G) := by
    intro K L hKL
    apply Subtype.ext
    ext v
    exact LinearMap.congr_fun hKL v
  have hLle : finrank ℝ (OriginalLie G) ≤ 3 := by
    rw [← LinearMap.finrank_range_of_inj hinj, hfull]
    exact skew_dimension_le_three B hW (skewEndomorphisms B) (fun S => S.property)
  have hspan : Submodule.span ℝ {A} ≤ LinearMap.ker (evaluation G x) := by
    apply Submodule.span_le.mpr
    intro K hK
    obtain rfl := Set.mem_singleton_iff.mp hK
    exact hAx
  have hkerE : LinearMap.ker (evaluation G x) = Submodule.span ℝ {A} := by
    apply (Submodule.eq_of_le_of_finrank_le hspan ?_).symm
    rw [finrank_span_singleton hAne]
    have hr := (evaluation G x).finrank_range_add_finrank_ker
    rw [hErank] at hr
    omega
  refine ⟨A,x,hAne,hx,hAx,fullReciprocity_of_kernels_ranges G A x hkerA hkerE ?_⟩
  rw [hAT, hErange]


private def axisPlaneAlgebra (b : Basis (Fin 3) ℝ W) : (ℝ × ℂ) →ₐ[ℝ] (W →L[ℝ] W) := by
  let q : (ℝ × ℂ) →ₐ[ℝ] (W →ₗ[ℝ] W) := {
    toFun := fun z => b.constr ℝ ![z.1 • b 0, z.2.re • b 1 + z.2.im • b 2, -z.2.im • b 1 + z.2.re • b 2]
    map_zero' := by
      apply b.ext
      intro i
      fin_cases i <;> simp
    map_one' := by
      apply b.ext
      intro i
      fin_cases i <;> simp
    map_add' := by
      intro z w
      apply b.ext
      intro i
      fin_cases i <;> simp [add_smul] <;> module
    map_mul' := by
      intro z w
      apply b.ext
      intro i
      apply b.repr.injective
      ext j
      fin_cases i <;> fin_cases j <;> simp [Module.End.mul_apply, map_add, map_smul, map_neg, Complex.mul_re,
          Complex.mul_im] <;> ring
    commutes' := by
      intro r
      apply b.ext
      intro i
      fin_cases i <;> simp }
  exact (Module.End.toContinuousLinearMap (𝕜 := ℝ) W).toAlgHom.comp q

private theorem basis_halfturn_exponential (B : InnerProductSpace.Core ℝ W) (b : Basis (Fin 3) ℝ W)
    (hb : ∀ i j, B.inner (b i) (b j) = if i = j then 1 else 0) : ∃ K : W →L[ℝ] W, K.toLinearMap ∈ skewEndomorphisms B ∧
      ∀ i : Fin 3, NormedSpace.exp (Real.pi • K) (b i) = if i = 0 then b i else -b i := by
  let q := axisPlaneAlgebra b
  let K := q (0, Complex.I)
  have hK0 : K (b 0) = 0 := by simp [K,q,axisPlaneAlgebra, Module.End.toContinuousLinearMap, LinearMap.toContinuousLinearMap]
  have hK1 : K (b 1) = b 2 := by simp [K,q,axisPlaneAlgebra, Module.End.toContinuousLinearMap, LinearMap.toContinuousLinearMap]
  have hK2 : K (b 2) = -b 1 := by simp [K,q,axisPlaneAlgebra, Module.End.toContinuousLinearMap, LinearMap.toContinuousLinearMap]
  have he (u : W) : u = b.repr u 0 • b 0 + b.repr u 1 • b 1 + b.repr u 2 • b 2 := by
    simpa only [Fin.sum_univ_three] using (b.sum_repr u).symm
  refine ⟨K, ?_, ?_⟩
  · intro u v
    change B.inner (K u) v = -B.inner u (K v)
    letI : AddCommGroup W := inferInstance
    letI : Module ℝ W := inferInstance
    let : NormedAddCommGroup W := B.toNormedAddCommGroup
    let : InnerProductSpace ℝ W := InnerProductSpace.ofCore B.toCore
    change ⟪K u,v⟫_ℝ = -⟪u,K v⟫_ℝ
    have hbi (i j : Fin 3) : ⟪b i,b j⟫_ℝ = if i = j then 1 else 0 := hb i j
    rw [he u, he v]
    simp only [map_add, map_smul, hK0, hK1, hK2, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, inner_neg_left, inner_neg_right,
      zero_smul, add_zero, zero_add, inner_zero_left, inner_zero_right, hbi]
    norm_num
    <;> ring
  · have hz : NormedSpace.exp (Real.pi • ((0, Complex.I) : ℝ × ℂ)) = (1,-1) := by
      ext <;> simp [Complex.real_smul, ← Complex.exp_eq_exp_ℂ, Complex.exp_pi_mul_I]
    letI : CompleteSpace W := FiniteDimensional.complete ℝ W
    letI : NormedAlgebra ℚ (W →L[ℝ] W) := .restrictScalars ℚ ℝ _
    have hq : Continuous q := q.toLinearMap.continuous_of_finiteDimensional
    have hexp : NormedSpace.exp (Real.pi • K) = q (1,-1) := by
      change NormedSpace.exp (Real.pi • q (0,Complex.I)) = _
      rw [← map_smul, ← NormedSpace.map_exp q hq, hz]
    intro i
    rw [hexp]
    fin_cases i <;> simp [q,axisPlaneAlgebra, Module.End.toContinuousLinearMap, LinearMap.toContinuousLinearMap]


private theorem halfturns_generate (H : Subgroup (W ≃ₗ[ℝ] W))
    (hhalf : ∀ v : W, v ≠ 0 → (ℝ ∙ v).reflection.toLinearEquiv ∈ H)
    (e : W ≃ₗᵢ[ℝ] W) (he : LinearMap.det e.toLinearMap = 1) : e.toLinearEquiv ∈ H := by
  classical
  let R (v : W) := (ℝ ∙ v)ᗮ.reflection
  have hword (l : List W) : ∃ a : W ≃ₗ[ℝ] W, a ∈ H ∧
      (l.map R).prod.toLinearMap = LinearMap.det (l.map R).prod.toLinearMap • a.toLinearMap := by
    induction l with
    | nil =>
      refine ⟨1,H.one_mem,?_⟩
      change (1 : W →ₗ[ℝ] W) = LinearMap.det (1 : W →ₗ[ℝ] W) • (1 : W →ₗ[ℝ] W)
      simp
    | cons v l ih =>
      obtain ⟨a,ha,hea⟩ := ih
      by_cases hv : v = 0
      · have hz : R v = 1 := by
          subst v
          ext w
          apply Submodule.reflection_mem_subspace_eq_self
          simp
        simpa [hz] using ⟨a,ha,hea⟩
      · let t := (ℝ ∙ v).reflection.toLinearEquiv
        have ht : t ∈ H := hhalf v hv
        have hd : LinearMap.det (R v).toLinearMap = -1 := by
          change LinearMap.det (ℝ ∙ v)ᗮ.reflection.toLinearMap = -1
          rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hv]
          norm_num
        have hR : (R v).toLinearMap = -t.toLinearMap := by
          ext w
          exact Submodule.reflection_orthogonal_apply (ℝ ∙ v) w
        refine ⟨t*a,H.mul_mem ht ha,?_⟩
        change (R v).toLinearMap * (l.map R).prod.toLinearMap =
          LinearMap.det ((R v).toLinearMap * (l.map R).prod.toLinearMap) •
            (t.toLinearMap * a.toLinearMap)
        rw [map_mul, hd]
        conv_lhs => rw [hea, hR]
        simp only [mul_smul_comm, neg_mul, smul_neg, neg_smul, one_mul]
  obtain ⟨l,_hl,hel⟩ := e.reflections_generate_dim
  obtain ⟨a,ha,hea⟩ := hword l
  have hel' : (l.map R).prod = e := hel.symm
  have hmap : e.toLinearMap = a.toLinearMap := by
    rw [hel', he, one_smul] at hea
    exact hea
  have hae : e.toLinearEquiv = a := by
    ext w
    exact LinearMap.congr_fun hmap w
  exact hae ▸ ha

private def originalUnitHom : (W ≃ₗ[ℝ] W) →* (W →L[ℝ] W)ˣ where
  toFun e := e.toContinuousLinearEquiv.toUnit
  map_one' := by ext w; rfl
  map_mul' _ _ := by ext w; rfl

private theorem special_orthogonal_in_component (B : InnerProductSpace.Core ℝ W) (hW : finrank ℝ W = 3)
    (hexp : ∀ K : W →L[ℝ] W, K.toLinearMap ∈ skewEndomorphisms B → ∀ t : ℝ, ∃ g : G, g ∈ connectedComponent (1 : G) ∧
        g.val.val = NormedSpace.exp (t • K))
    (u : (W →L[ℝ] W)ˣ)
    (hu : ∀ v w : W, B.inner (u.val v) (u.val w) = B.inner v w)
    (hdet : u.val.det = 1) :
    ∃ g : G, g ∈ connectedComponent (1 : G) ∧ g.val = u := by
  classical
  let U := originalUnitHom (W := W)
  let C := (Module.End.toContinuousLinearMap (𝕜 := ℝ) W).symm.toEquiv
  let H := (Subgroup.connectedComponentOfOne G).map G.subtype
  let e := (ContinuousLinearEquiv.unitsEquiv ℝ W u).toLinearEquiv
  have hframe := basis_halfturn_exponential (W := W) B
  letI : AddCommGroup W := inferInstance
  letI : Module ℝ W := inferInstance
  let : NormedAddCommGroup W := B.toNormedAddCommGroup
  let : InnerProductSpace ℝ W := InnerProductSpace.ofCore B.toCore
  have hhalf (v : W) (hv : v ≠ 0) : (ℝ ∙ v).reflection.toLinearEquiv ∈ H.comap U := by
    let f : Fin 3 → W := fun _ => (‖v‖⁻¹ : ℝ) • v
    have hn : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      simp [norm_smul, abs_of_nonneg (norm_nonneg v), norm_ne_zero_iff.mpr hv]
    have hf : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict f) := by
      rw [orthonormal_iff_ite]
      intro i j
      have hij : i = j := Subtype.ext ((Set.mem_singleton_iff.mp i.property).trans
        (Set.mem_singleton_iff.mp j.property).symm)
      subst j
      simp [f, real_inner_self_eq_norm_sq, hn]
    obtain ⟨b,hb⟩ := hf.exists_orthonormalBasis_extension_of_card_eq
      (by simpa using hW)
    have hb0 : b 0 = (‖v‖⁻¹ : ℝ) • v := hb 0 (by simp)
    have hline : ℝ ∙ v = ℝ ∙ b 0 := by
      rw [hb0, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr
        (inv_ne_zero (norm_ne_zero_iff.mpr hv)))]
    obtain ⟨K,hK,hKi⟩ := hframe b.toBasis (fun i j => b.inner_eq_ite i j)
    obtain ⟨g,hg,hgv⟩ := hexp K hK Real.pi
    have hKi' (i : Fin 3) : g.val.val (b i) = if i = 0 then b i else -b i := by
      rw [hgv]
      exact hKi i
    have hval : U (ℝ ∙ v).reflection.toLinearEquiv = g.val := by
      apply Units.ext
      apply C.injective
      apply b.toBasis.ext
      intro i
      change (ℝ ∙ v).reflection (b i) = g.val.val (b i)
      rw [hKi']
      fin_cases i
      · apply Submodule.reflection_mem_subspace_eq_self
        rw [hline]
        exact Submodule.mem_span_singleton_self _
      · apply Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
        rw [hline, Submodule.mem_orthogonal_singleton_iff_inner_left]
        simp [b.inner_eq_ite]
      · apply Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
        rw [hline, Submodule.mem_orthogonal_singleton_iff_inner_left]
        simp [b.inner_eq_ite]
    change U (ℝ ∙ v).reflection.toLinearEquiv ∈ H
    rw [hval]
    exact ⟨g,hg,rfl⟩
  let eB : W ≃ₗᵢ[ℝ] W := e.isometryOfInner hu
  have he : eB.toLinearEquiv ∈ H.comap U :=
    halfturns_generate (H.comap U) hhalf eB hdet
  have heq : U eB.toLinearEquiv = u := by ext w; rfl
  change U eB.toLinearEquiv ∈ H at he
  rw [heq] at he
  obtain ⟨g,hg,hgu⟩ := he
  exact ⟨g,hg,hgu⟩


/-- The actual intrinsic identity component is the full special orthogonal group
for the metric derived from G; the same original G is either SO or O. -/
theorem original_group_rigidity
    (hG : IsCompact (G : Set (W →L[ℝ] W)ˣ))
    (A : OriginalLie G) (x : W) (ha : A ≠ 0) (hx : x ≠ 0) (hAx : A.val x = 0)
    (h : FullReciprocity G A x) :
    ∃ B : InnerProductSpace.Core ℝ W,
      (∀ (g : G) (u v : W), B.inner (g.val.val u) (g.val.val v) = B.inner u v) ∧
      finrank ℝ W = 3 ∧ finrank ℝ (OriginalLie G) = 3 ∧
      LinearMap.range (originalAction G) = skewEndomorphisms B ∧
      G.subtype '' connectedComponent (1 : G) =
        {u : (W →L[ℝ] W)ˣ | (∀ v w, B.inner (u.val v) (u.val w) = B.inner v w) ∧
          u.val.det = 1} ∧
      ((G : Set (W →L[ℝ] W)ˣ) =
        {u | (∀ v w, B.inner (u.val v) (u.val w) = B.inner v w) ∧ u.val.det = 1} ∨
       (G : Set (W →L[ℝ] W)ˣ) =
        {u | ∀ v w, B.inner (u.val v) (u.val w) = B.inner v w}) := by
  obtain ⟨B,hB,hW,hL,hrange,hcomponent,hexp⟩ :=
    original_exponential_rigidity G hG A x ha hx hAx h
  have hSO := special_orthogonal_in_component G B hW hexp
  refine ⟨B,hB,hW,hL,hrange,?_,?_⟩
  · ext u
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact ⟨hB g,hcomponent g hg⟩
    · rintro ⟨hu,hd⟩
      obtain ⟨g,hg,hgu⟩ := hSO u hu hd
      exact ⟨g,hg,hgu⟩
  · by_cases hpositive : ∀ g : G, g.val.val.det = 1
    · left
      ext u
      constructor
      · intro hu
        exact ⟨hB ⟨u,hu⟩,hpositive ⟨u,hu⟩⟩
      · rintro ⟨hu,hd⟩
        obtain ⟨g,_hg,hgu⟩ := hSO u hu hd
        exact hgu ▸ g.property
    · push_neg at hpositive
      obtain ⟨r,hr⟩ := hpositive
      have hrneg : r.val.val.det = -1 := by
        have hs := determinant_sq_of_preserves B
          (ContinuousLinearEquiv.unitsEquiv ℝ W r.val).toLinearEquiv (hB r)
        rcases (sq_eq_one_iff.mp hs) with hp | hm
        · exact (hr hp).elim
        · exact hm
      have hinv (v : W) : r.val.val ((r.val⁻¹).val v) = v := by
        change (r.val * r.val⁻¹).val v = v
        rw [mul_inv_cancel]
        rfl
      have hrinv : ∀ v w : W,
          B.inner ((r.val⁻¹).val v) ((r.val⁻¹).val w) = B.inner v w := by
        intro v w
        simpa only [hinv] using (hB r ((r.val⁻¹).val v) ((r.val⁻¹).val w)).symm
      have hrdetinv : (r.val⁻¹).val.det = -1 := by
        have hm : r.val.val.det * (r.val⁻¹).val.det = 1 := by
          rw [← map_mul]
          change (r.val * r.val⁻¹).val.det = 1
          rw [mul_inv_cancel]
          change LinearMap.det (1 : W →ₗ[ℝ] W) = 1
          exact map_one _
        rw [hrneg] at hm
        linarith
      right
      ext u
      constructor
      · intro hu
        exact hB ⟨u,hu⟩
      · intro hu
        by_cases hd : u.val.det = 1
        · obtain ⟨g,_hg,hgu⟩ := hSO u hu hd
          exact hgu ▸ g.property
        · have hudet : u.val.det = -1 := by
            have hs := determinant_sq_of_preserves B
              (ContinuousLinearEquiv.unitsEquiv ℝ W u).toLinearEquiv hu
            rcases sq_eq_one_iff.mp hs with hp | hm
            · exact (hd hp).elim
            · exact hm
          have hprod : ∀ v w : W,
              B.inner ((u*r.val⁻¹).val v) ((u*r.val⁻¹).val w) = B.inner v w := by
            intro v w
            exact (hu _ _).trans (hrinv v w)
          have hprod_det : (u*r.val⁻¹).val.det = 1 := by
            change LinearMap.det (u.val.toLinearMap * (r.val⁻¹).val.toLinearMap) = 1
            rw [map_mul]
            change u.val.det * (r.val⁻¹).val.det = 1
            rw [hudet,hrdetinv]
            norm_num
          obtain ⟨g,_hg,hgu⟩ := hSO (u*r.val⁻¹) hprod hprod_det
          have hmem : u*r.val⁻¹ ∈ G := hgu ▸ g.property
          simpa using G.mul_mem hmem r.property


end
end D5.S3.Quantum.Algebra.OriginalCompactReciprocity

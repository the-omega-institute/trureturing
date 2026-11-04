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

namespace D5.S3.Quantum.Algebra.OriginalCompactReciprocity

set_option backward.isDefEq.respectTransparency false

attribute [local instance] LieRing.ofAssociativeRing

open OriginalCompactActionMetric Module
open scoped Topology InnerProductSpace
noncomputable section
universe u
variable {W : Type u} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]
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
theorem mem_velocitySpace_iff_exp
    (hG : IsCompact (G : Set (W →L[ℝ] W)ˣ)) (K : W →L[ℝ] W) :
    K ∈ velocitySpace G ↔ ∀ t : ℝ, ∃ u : (W →L[ℝ] W)ˣ,
      u ∈ G ∧ (u : W →L[ℝ] W) = NormedSpace.exp (t • K) := by
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  constructor
  · rintro ⟨c, hc, hK⟩ t
    let E := W →L[ℝ] W
    have hexp : HasStrictFDerivAt (NormedSpace.exp : E → E)
        (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 := by
      simpa using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := E))
    let ell : E → E := hexp.localInverse NormedSpace.exp (ContinuousLinearEquiv.refl ℝ E) 0
    have hell0 : ell 1 = 0 := by
      simpa [ell] using hexp.localInverse_apply_image
    have hell : HasFDerivAt ell (1 : E →L[ℝ] E) 1 := by
      simpa [ell] using hexp.to_localInverse.hasFDerivAt
    have hc0 : (c 0).val.val = (1 : E) := by simp [hc]
    have hd : HasDerivAt (fun s => ell ((c s).val.val)) K 0 := by
      simpa only [Function.comp_apply, ContinuousLinearMap.one_apply] using
        hell.comp_hasDerivAt_of_eq hK hc0.symm
    have hscale : Filter.Tendsto (fun n : ℕ => (n : ℝ) • ell ((c (t / n)).val.val))
        Filter.atTop (𝓝 (t • K)) := by
      have hn : Filter.Tendsto (fun n : ℕ => ‖(n : ℝ)‖) Filter.atTop Filter.atTop := by
        simpa using (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa [hc0, hell0, div_eq_mul_inv, mul_comm] using hd.hasFDerivAt.lim t hn
    have hinv : ∀ᶠ y in 𝓝 (1 : E), NormedSpace.exp (ell y) = y := by
      simpa [ell] using hexp.eventually_right_inverse
    have hsample : Filter.Tendsto (fun n : ℕ => (c (t / n)).val.val)
        Filter.atTop (𝓝 (1 : E)) := by
      simpa only [hc0] using hK.continuousAt.tendsto.comp
        (tendsto_const_div_atTop_nhds_zero_nat t)
    have hpow : Filter.Tendsto (fun n : ℕ => ((c (t / n)).val.val) ^ n)
        Filter.atTop (𝓝 (NormedSpace.exp (t • K))) := by
      apply hscale.exp.congr'
      filter_upwards [hsample.eventually hinv] with n hn
      rw [Nat.cast_smul_eq_nsmul ℝ, NormedSpace.exp_nsmul, hn]
    have hclosed : IsClosed ((Units.val : Eˣ → E) '' (G : Set Eˣ)) :=
      (hG.image Units.continuous_val).isClosed
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

omit [FiniteDimensional ℝ W] in
private theorem conjugate_velocity (g : G) (K : W →L[ℝ] W)
    (hK : K ∈ velocitySpace G) :
    (g.val.val * K * g⁻¹.val.val) ∈ velocitySpace G := by
  obtain ⟨c,hc,hcK⟩ := hK
  refine ⟨fun t => g * c t * g⁻¹,by simp [hc],?_⟩
  simpa [hc] using ((hasDerivAt_const (0 : ℝ) g.val.val).mul hcK).mul_const g⁻¹.val.val

private theorem bracket_velocity (K L : W →L[ℝ] W)
    (hK : K ∈ velocitySpace G) (hL : L ∈ velocitySpace G) :
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
  have hm : ∀ t : ℝ, (c t).val.val * L * (c t)⁻¹.val.val ∈ velocitySpace G :=
    fun t => conjugate_velocity G (c t) L hL
  have hz := mem_closure_of_tendsto hh.tendsto_slope
    (Filter.Eventually.of_forall fun t =>
      (velocitySpace G).smul_mem _ ((velocitySpace G).sub_mem (hm t) (hm 0)))
  rw [(velocitySpace G).closed_of_finiteDimensional.closure_eq] at hz
  exact hz

/-- The actual curve velocities form a Lie algebra under the actual matrix commutator. -/
def curveLieAlgebra : LieSubalgebra ℝ (W →L[ℝ] W) :=
  { velocitySpace G with
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
def firstProjection (A : OriginalLie G) (x : W) :
    fullRelation G A x →ₗ[ℝ] (OriginalLie G ⧸ Submodule.span ℝ {A}) :=
  (LinearMap.fst ℝ _ _).comp (fullRelation G A x).subtype

/-- The second canonical projection of the entire solution relation. -/
def secondProjection (A : OriginalLie G) (x : W) :
    fullRelation G A x →ₗ[ℝ] (W ⧸ Submodule.span ℝ {x}) :=
  (LinearMap.snd ℝ _ _).comp (fullRelation G A x).subtype

/-- Both projections of the full relation must be bijective. -/
def FullReciprocity (A : OriginalLie G) (x : W) : Prop :=
  Function.Bijective (firstProjection G A x) ∧ Function.Bijective (secondProjection G A x)

private theorem relation_mem (A K : OriginalLie G) (x y : W)
    (h : K.val x + A.val y = 0) :
    ((Submodule.span ℝ {A}).mkQ K,(Submodule.span ℝ {x}).mkQ y) ∈ fullRelation G A x :=
  ⟨(K,y),h,rfl⟩

private theorem kernel_lines (A : OriginalLie G) (x : W)
    (h : FullReciprocity G A x) :
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

private theorem dimension_transfer (A : OriginalLie G) (x : W)
    (ha : A ≠ 0) (hx : x ≠ 0) (h : FullReciprocity G A x) :
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
    (A : OriginalLie G) (x : W) (hx : x ≠ 0) (hAx : A.val x = 0)
    (h : FullReciprocity G A x) :
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
    [FiniteDimensional ℝ V] (B : InnerProductSpace.Core ℝ V)
    (T : V →ₗ[ℝ] V) (hT : T ≠ 0)
    (hskew : ∀ u v : V, B.inner (T u) v = -B.inner u (T v)) :
    0 < -LinearMap.trace ℝ V (T*T) := by
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
  conj_inner_symm K L := by
    simp only [conj_trivial,tracePair,LinearMap.trace_mul_comm ℝ L.val.toLinearMap]
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
    (hskew : ∀ K : OriginalLie G, ∀ u v : W, B.inner (K.val u) v = -B.inner u (K.val v))
    (X Y Z : OriginalLie G) :
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
    (A : OriginalLie G) (x : W) (ha : A ≠ 0) (hx : x ≠ 0) (hAx : A.val x = 0)
    (h : FullReciprocity G A x) :
    finrank ℝ W = 3 ∧ finrank ℝ (OriginalLie G) = 3 := by
  obtain ⟨B,_hB,hcurves⟩ := compact_action_metric G hG
  have hskew : ∀ K : OriginalLie G, ∀ u v : W,
      B.inner (K.val u) v = -B.inner u (K.val v) := by
    intro K
    obtain ⟨c,hc,hcK⟩ := K.property
    exact hcurves c hc K.val hcK
  have hdim := dimension_transfer G A x ha hx h
  have hd := RankOneInvariantMetric.finrank_eq_one_or_three (traceCore G B hskew)
    (trace_invariant G B hskew) A ha (centralizer_line G B hskew A x hx hAx h)
  have hthree : finrank ℝ (OriginalLie G) = 3 := by
    rcases hd with hone | hthree
    · have hW : finrank ℝ W = 1 := hdim.symm.trans hone
      have hspan : Submodule.span ℝ {x} = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [finrank_span_singleton hx,hW])
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

private theorem skew_dimension_le_three {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : InnerProductSpace.Core ℝ V) (hV : finrank ℝ V = 3)
    (S : Submodule ℝ (V →ₗ[ℝ] V))
    (hS : ∀ T : S, ∀ u v : V, B.inner (T.val u) v = -B.inner u (T.val v)) :
    finrank ℝ S ≤ 3 := by
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
    (A : OriginalLie G) (x : W) (ha : A ≠ 0) (hx : x ≠ 0) (hAx : A.val x = 0)
    (h : FullReciprocity G A x) :
    ∃ B : InnerProductSpace.Core ℝ W,
      (∀ (g : G) (u v : W),
        B.inner (g.val.val u) (g.val.val v) = B.inner u v) ∧
      finrank ℝ W = 3 ∧ finrank ℝ (OriginalLie G) = 3 ∧
      LinearMap.range (originalAction G) = skewEndomorphisms B := by
  obtain ⟨B,hB,hcurves⟩ := compact_action_metric G hG
  have hskew : ∀ K : OriginalLie G, ∀ u v : W,
      B.inner (K.val u) v = -B.inner u (K.val v) := by
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

end
end D5.S3.Quantum.Algebra.OriginalCompactReciprocity

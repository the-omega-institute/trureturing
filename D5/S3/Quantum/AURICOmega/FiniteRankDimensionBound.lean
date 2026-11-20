/- GID: D5/S3/Quantum/AURICOmega/FiniteRankDimensionBound
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/FiniteRankDimensionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Noncommutative rank-r ternary comparisons locally injecting into R^d: d >= 3, r >= 5. -/

import D5.S3.Topology.LowDimensionalBorsukUlam
import D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart
import D5.S3.Quantum.AURICOmega.InvariantGramRepresentation
import D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
import D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import D5.S3.Quantum.Algebra.InvariantMetric.LowDimensionInvariantMetric
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Normed
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Dimension bound for finite-rank ternary comparison structures

Let `G` be a preconnected, locally compact topological group with a continuous injective
homomorphism `ρ` into the orthogonal group `O(n)`, and suppose that some neighbourhood `V` of `1`
admits a map `f : G → ℝ^d` that is continuous and injective on `V`. If `G` is noncommutative,
then `3 ≤ d` (`three_le_of_orthogonal`). A group locally homeomorphic to `ℝ^d` is an instance:
its charts give local compactness, and the chart at `1` is such a map on its source. The matrix
algebra is normed by the `L∞` operator norm (`Matrix.linftyOpNormedRing`, a local instance),
whose topology is the product topology, and `ρ` is read as a homomorphism into the units of this
normed algebra.

* The one-parameter generators of `ρ` are skew-adjoint: `star (exp (t • X)) * exp (t • X) = 1`
  for all real `t`, and the derivative at `t = 0` gives `star X + X = 0`.
* The trace form `(X, Y) ↦ tr (X * Y)` is invariant on every Lie algebra of matrices, by
  cyclicity of the trace, and it is separating on skew-adjoint matrices, since
  `tr (X * X) = -tr (Xᴴ * X)`. By the low-dimensional theorem for invariant forms, a generator
  algebra of dimension at most two is abelian.
* If the generator algebra is abelian, the exponential chart maps an open neighbourhood of `0`
  onto an open neighbourhood of `1` of pairwise commuting elements. The subgroup it generates is
  open, hence closed, hence all of the preconnected group `G`, so `G` is commutative.
* Hence the generator algebra has dimension `m ≥ 3`. The exponential chart is injective on an
  open neighbourhood of `0`, so its composition with `f` is a continuous injection of a nonempty
  open subset of `ℝ^m` into `ℝ^d`, which the low-dimensional Borsuk--Ulam theorem excludes when
  `d ≤ 2 < m`.

A ternary comparison structure on a preconnected space whose reading is continuous in each
variable is chain-connected (`chainConnected_of_connected`): a reading close to one is an open
condition near the diagonal.

Let the structure live on a preconnected, locally compact space, with continuous transfer and a
reading continuous in each variable, and let a neighbourhood `V` of a point `o` admit a map into
`ℝ^d` that is continuous and injective on `V`. The group `groupAt o`, whose identity is `o`, is a
topological group. A feature map `φ` of rank `r`, `kappa x y = ⟪φ x, φ y⟫`, satisfies
`‖φ x - φ y‖ ^ 2 = 2 - 2 * kappa y x`, so it is continuous and injective, and its Gram kernel is
left invariant. The orthogonal representation of the invariant Gram kernel has the stabilizer of
the family `φ` as its kernel, which is trivial since `φ` is injective. A noncommutative structure
therefore has `3 ≤ d`, and, being chain-connected, feature rank `5 ≤ r`
(`three_le_dim_of_hasFeatureRank`).
-/

open Filter Set
open scoped Topology Matrix InnerProductSpace

namespace D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound

open D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
open D5.S3.Quantum.Analysis.LinearGroups.ExponentialChart
open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.Algebra.InvariantMetric.LowDimensionInvariantMetric

section Generators

attribute [local instance] LieRing.ofAssociativeRing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  {G : Type*} [TopologicalSpace G] [Group G]

/-- If `ρ` takes unitary values in a finite-dimensional real star algebra, every one-parameter
generator `X` is skew-adjoint: the curve `star (exp (t • X)) * exp (t • X) = exp (t • star X) *
exp (t • X)` is constant, and its derivative at `0` is `star X + X`. -/
private theorem star_eq_neg_of_isOneParameterGenerator [StarRing A] [StarModule ℝ A]
    (ρ : G →* Aˣ) (hρ : ∀ g, star ((ρ g : Aˣ) : A) * ((ρ g : Aˣ) : A) = 1) {X : A}
    (hX : IsOneParameterGenerator ρ X) : star X = -X := by
  let s : A →ₗ[ℝ] A :=
    { toFun := star
      map_add' := star_add
      map_smul' := fun r x => by
        rw [star_smul, star_trivial]
        rfl }
  have : ContinuousStar A := ⟨s.continuous_of_finiteDimensional⟩
  obtain ⟨γ, -, hγ⟩ := hX
  have h1 : ∀ t : ℝ, NormedSpace.exp (t • star X) * NormedSpace.exp (t • X) = 1 := by
    intro t
    have h := hρ (γ t)
    rw [hγ t, NormedSpace.star_exp, star_smul, star_trivial] at h
    exact h
  have hd := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (star X) 0).mul
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  have hd0 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • star X) * NormedSpace.exp (t • X))
      0 0 := by
    simp only [h1]
    exact hasDerivAt_const 0 1
  have h := hd.unique hd0
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h
  exact eq_neg_of_add_eq_zero_left h

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- If the Lie algebra of one-parameter generators of `ρ` is abelian, a preconnected `G` is
commutative: the exponential chart maps an open neighbourhood of `0` onto an open neighbourhood
of `1` whose elements pairwise commute, and the subgroup generated by it is open, hence closed,
hence all of `G`. -/
private theorem mul_comm_of_isLieAbelian [PreconnectedSpace G] (ρ : G →* Aˣ)
    (hc : Continuous ρ) (hi : Function.Injective ρ)
    (hab : IsLieAbelian (generatorSubalgebra ρ hc hi)) (a b : G) : a * b = b * a := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨ε, -, hρε, U, -, hU0, hU⟩ := exists_exp_chart ρ hc hi
  have hε0 : ε 0 = 1 := hi (Units.ext (by
    rw [hρε, ZeroMemClass.coe_zero, NormedSpace.exp_zero, map_one, Units.val_one]))
  have hcomm : ∀ X Y : generatorSubalgebra ρ hc hi, Commute (ε X) (ε Y) := by
    intro X Y
    have hXY : Commute (X : A) (Y : A) := by
      have h := congrArg (fun Z : generatorSubalgebra ρ hc hi => (Z : A))
        (trivial_lie_zero (generatorSubalgebra ρ hc hi) (generatorSubalgebra ρ hc hi) X Y)
      simp only [LieSubalgebra.coe_bracket, Ring.lie_def, ZeroMemClass.coe_zero] at h
      exact sub_eq_zero.1 h
    refine hi (Units.ext ?_)
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hρε, hρε,
      ← NormedSpace.exp_add_of_commute hXY, ← NormedSpace.exp_add_of_commute hXY.symm, add_comm]
  have hSo : IsOpen (ε '' U) := by
    rw [← Set.range_domRestrict]
    exact hU.isOpen_range
  set H := Subgroup.closure (ε '' U)
  have hHo : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hSo.mem_nhds ⟨0, hU0, hε0⟩)
      Subgroup.subset_closure)
  have hH : (H : Set G) = Set.univ :=
    IsClopen.eq_univ ⟨H.isClosed_of_isOpen hHo, hHo⟩ ⟨1, H.one_mem⟩
  have hpair : (ε '' U).Pairwise Commute := by
    rintro _ ⟨X, -, rfl⟩ _ ⟨Y, -, rfl⟩ -
    exact hcomm X Y
  have hle := Subgroup.closure_le_centralizer_centralizer (ε '' U)
  have ha : a ∈ H := by
    rw [← SetLike.mem_coe, hH]
    trivial
  have hb : b ∈ H := by
    rw [← SetLike.mem_coe, hH]
    trivial
  exact Set.centralizer_centralizer_comm_of_comm hpair a (hle ha) b (hle hb)

/-- If `f : G → ℝ^d` is continuous and injective on a neighbourhood `V` of `1` and `d ≤ 2`, the
Lie algebra of one-parameter generators of `ρ` has dimension at most `d`: otherwise `f`, composed
with the exponential chart and a linear identification of the generator algebra with `ℝ^m`,
would be a continuous injection of a nonempty open subset of `ℝ^m` into `ℝ^d` with `d < m`. -/
private theorem finrank_le_of_le_two {d : ℕ} {V : Set G} (hV : V ∈ 𝓝 (1 : G))
    (f : G → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f V) (hfi : Set.InjOn f V)
    (hd : d ≤ 2) (ρ : G →* Aˣ) (hc : Continuous ρ) (hi : Function.Injective ρ) :
    Module.finrank ℝ (generatorSubalgebra ρ hc hi) ≤ d := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨ε, hε, hρε, U, hUo, hU0, hU⟩ := exists_exp_chart ρ hc hi
  have hε0 : ε 0 = 1 := hi (Units.ext (by
    rw [hρε, ZeroMemClass.coe_zero, NormedSpace.exp_zero, map_one, Units.val_one]))
  let e : EuclideanSpace ℝ (Fin (Module.finrank ℝ (generatorSubalgebra ρ hc hi))) ≃ₗ[ℝ]
      generatorSubalgebra ρ hc hi := LinearEquiv.ofFinrankEq _ _ (by simp)
  have hψ : Continuous fun y => e y :=
    continuous_induced_rng.2
      ((generatorSubalgebra ρ hc hi).incl.toLinearMap.comp
        e.toLinearMap).continuous_of_finiteDimensional
  have hO : IsOpen ((fun y => e y) ⁻¹' (U ∩ ε ⁻¹' interior V)) :=
    (hUo.inter (isOpen_interior.preimage hε)).preimage hψ
  have hne : ((fun y => e y) ⁻¹' (U ∩ ε ⁻¹' interior V)).Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · simpa using hU0
    · simp only [Set.mem_preimage, map_zero, hε0]
      exact mem_interior_iff_mem_nhds.2 hV
  have hinj : Set.InjOn ε U := Set.injOn_iff_injective.2 hU.injective
  refine D5.S3.Topology.LowDimensionalBorsukUlam.not_injOn_of_lt hd hlt hO hne
    (fun y => f (ε (e y))) ?_ ?_
  · exact hf.comp (hε.comp hψ).continuousOn fun y hy => interior_subset hy.2
  · intro y hy z hz h
    exact e.injective (hinj hy.1 hz.1 (hfi (interior_subset hy.2) (interior_subset hz.2) h))

end Generators

section Orthogonal

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  LieRing.ofAssociativeRing

variable {n : ℕ}

/-- The trace form `(X, Y) ↦ tr (X * Y)` on a Lie subalgebra of real square matrices. -/
private noncomputable def traceForm (L : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    LinearMap.BilinForm ℝ L :=
  ((LinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ)).compr₂
    (Matrix.traceLinearMap (Fin n) ℝ ℝ)).compl₁₂ L.incl.toLinearMap L.incl.toLinearMap

private theorem traceForm_apply (L : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) (X Y : L) :
    traceForm L X Y =
      Matrix.trace ((X : Matrix (Fin n) (Fin n) ℝ) * (Y : Matrix (Fin n) (Fin n) ℝ)) := rfl

/-- The trace form is invariant: `tr ((X * Y - Y * X) * Z) = -tr (Y * (X * Z - Z * X))`, by
cyclicity of the trace. -/
private theorem traceForm_lieInvariant (L : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    (traceForm L).lieInvariant L := by
  intro X Y Z
  simp only [traceForm_apply, LieSubalgebra.coe_bracket, Ring.lie_def, sub_mul, mul_sub,
    Matrix.trace_sub, mul_assoc]
  have h := Matrix.trace_mul_comm (X : Matrix (Fin n) (Fin n) ℝ)
    ((Y : Matrix (Fin n) (Fin n) ℝ) * (Z : Matrix (Fin n) (Fin n) ℝ))
  rw [mul_assoc] at h
  linarith

/-- On a Lie algebra of skew-adjoint real matrices the trace form is separating:
`tr (X * X) = -tr (Xᴴ * X)` vanishes only for `X = 0`. -/
private theorem traceForm_separatingLeft (L : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hL : ∀ X ∈ L, star X = -X) : LinearMap.SeparatingLeft (traceForm L) := by
  intro X hX
  have h0 := hX X
  rw [traceForm_apply] at h0
  have h1 : ((X : Matrix (Fin n) (Fin n) ℝ)ᴴ * X).trace = 0 := by
    rw [← Matrix.star_eq_conjTranspose, hL X X.2, neg_mul, Matrix.trace_neg, h0, neg_zero]
  exact Subtype.ext (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h1)

variable {G : Type*} [TopologicalSpace G] [Group G]

/-- A continuous homomorphism into the orthogonal group is continuous as a homomorphism into the
units of the matrix algebra: the inverse of an orthogonal matrix is its transpose. -/
private theorem continuous_toUnits_comp (ρ : G →* Matrix.orthogonalGroup (Fin n) ℝ)
    (hc : Continuous ρ) : Continuous (Unitary.toUnits.comp ρ) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val.comp hc, (continuous_subtype_val.comp hc).star⟩

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- For a noncommutative preconnected `G`, the Lie algebra of one-parameter generators of a
continuous injective homomorphism into `O(n)` has dimension at least three: its elements are
skew-adjoint, so the trace form is invariant and separating on it, and in dimension at most two
it would be abelian, which would make `G` commutative. -/
private theorem three_le_finrank [PreconnectedSpace G]
    (ρ : G →* Matrix.orthogonalGroup (Fin n) ℝ) (hc : Continuous ρ)
    (hi : Function.Injective ρ) (hnc : ∃ a b : G, a * b ≠ b * a) :
    3 ≤ Module.finrank ℝ (generatorSubalgebra (Unitary.toUnits.comp ρ)
      (continuous_toUnits_comp ρ hc) (Unitary.toUnits_injective.comp hi)) := by
  by_contra h
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (mul_comm_of_isLieAbelian (Unitary.toUnits.comp ρ) (continuous_toUnits_comp ρ hc)
    (Unitary.toUnits_injective.comp hi) (isLieAbelian_of_finrank_le_two (traceForm _)
      (traceForm_lieInvariant _) (traceForm_separatingLeft _ fun _ hX =>
        star_eq_neg_of_isOneParameterGenerator (Unitary.toUnits.comp ρ) (fun g => (ρ g).2.1) hX)
      (by omega)) a b)

/-- The dimension bound: the generator algebra has dimension at least three, and at most `d`
if `d ≤ 2`. -/
private theorem three_le_of_orthogonal_aux {d : ℕ} [PreconnectedSpace G] {V : Set G}
    (hV : V ∈ 𝓝 (1 : G)) (f : G → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f V)
    (hfi : Set.InjOn f V) (ρ : G →* Matrix.orthogonalGroup (Fin n) ℝ) (hc : Continuous ρ)
    (hi : Function.Injective ρ) (hnc : ∃ a b : G, a * b ≠ b * a) : 3 ≤ d := by
  by_contra hd
  have h3 := three_le_finrank ρ hc hi hnc
  have h2 := finrank_le_of_le_two hV f hf hfi (by omega : d ≤ 2) (Unitary.toUnits.comp ρ)
    (continuous_toUnits_comp ρ hc) (Unitary.toUnits_injective.comp hi)
  omega

end Orthogonal

/-- A noncommutative preconnected, locally compact topological group with a continuous injective
homomorphism into an orthogonal group, some neighbourhood of `1` of which admits a map into
`ℝ^d` that is continuous and injective on it, has `d ≥ 3`. -/
theorem three_le_of_orthogonal {d n : ℕ} {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [PreconnectedSpace G] {V : Set G}
    (hV : V ∈ 𝓝 (1 : G)) (f : G → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f V)
    (hfi : Set.InjOn f V) (ρ : G →* Matrix.orthogonalGroup (Fin n) ℝ) (hc : Continuous ρ)
    (hi : Function.Injective ρ) (hnc : ∃ a b : G, a * b ≠ b * a) : 3 ≤ d :=
  three_le_of_orthogonal_aux hV f hf hfi ρ hc hi hnc

/-- On a preconnected space, a ternary comparison structure whose reading is continuous in each
variable is chain-connected: for every `a`, the points `b` with `1 - ε < kappa a b` form a
neighbourhood of `a`, since `kappa a a = 1`. -/
theorem chainConnected_of_connected {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
    (C : TernaryComparison M) (hkappa : ∀ x, Continuous (C.kappa x)) : C.ChainConnected := by
  intro ε hε x y
  refine PreconnectedSpace.induction₂' _ (fun a => ?_)
    ⟨fun _ _ _ => Relation.ReflTransGen.trans⟩ x y
  have hlt : 1 - ε < C.kappa a a := by
    rw [C.kappa_self]
    linarith
  filter_upwards [((hkappa a).tendsto a).eventually (lt_mem_nhds hlt)] with b hb
  exact ⟨Relation.ReflTransGen.single hb,
    Relation.ReflTransGen.single (by rwa [C.kappa_symm])⟩

/-- With a continuous transfer, the group at a base point is a topological group: its product
is `tri x o y` and its inverse is `tri o x o`. -/
private theorem isTopologicalGroup_groupAt {M : Type*} [TopologicalSpace M]
    (C : TernaryComparison M)
    (htri : Continuous fun p : M × M × M => C.tri p.1 p.2.1 p.2.2) (o : M) :
    @IsTopologicalGroup M _ (C.groupAt o) :=
  let _ : Group M := C.groupAt o
  { continuous_mul := htri.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
    continuous_inv := htri.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const)) }

/-- A feature map of a reading that is continuous in each variable is continuous:
`‖φ x - φ y‖ = √(2 - 2 * kappa y x)` tends to `0` as `x` tends to `y`. -/
private theorem continuous_feature {M : Type*} [TopologicalSpace M] (C : TernaryComparison M)
    (hkappa : ∀ x, Continuous (C.kappa x)) {r : ℕ} (φ : M → EuclideanSpace ℝ (Fin r))
    (hφ : ∀ x y : M, C.kappa x y = ⟪φ x, φ y⟫_ℝ) : Continuous φ := by
  have hnorm : ∀ x y : M, ‖φ x - φ y‖ = Real.sqrt (2 - 2 * C.kappa y x) := by
    intro x y
    have hx : ⟪φ x, φ x⟫_ℝ = 1 := by rw [← hφ, C.kappa_self]
    have hy : ⟪φ y, φ y⟫_ℝ = 1 := by rw [← hφ, C.kappa_self]
    have hxy : ⟪φ x, φ y⟫_ℝ = C.kappa y x := by rw [← hφ, C.kappa_symm]
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, hx, hy, hxy]
    ring_nf
  refine continuous_iff_continuousAt.2 fun y => tendsto_iff_norm_sub_tendsto_zero.2 ?_
  simp only [hnorm]
  have h : Tendsto (fun x => 2 - 2 * C.kappa y x) (𝓝 y) (𝓝 (2 - 2 * C.kappa y y)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul ((hkappa y).tendsto y))
  rw [C.kappa_self, mul_one, sub_self] at h
  have h' := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h'
  exact h'

/-- A noncommutative ternary comparison structure of finite feature rank `r` on a preconnected,
locally compact space, with continuous transfer and a reading continuous in each variable, one
neighbourhood of which admits a map into `ℝ^d` that is continuous and injective on it, has
`d ≥ 3` and `r ≥ 5`. -/
theorem three_le_dim_of_hasFeatureRank {d : ℕ} {M : Type*} [TopologicalSpace M]
    [LocallyCompactSpace M] [PreconnectedSpace M] (C : TernaryComparison M)
    (htri : Continuous fun p : M × M × M => C.tri p.1 p.2.1 p.2.2)
    (hkappa : ∀ x, Continuous (C.kappa x))
    (hnc : C.Noncommutative) {r : ℕ} (hr : C.HasFeatureRank r)
    {o : M} {V : Set M} (hV : V ∈ 𝓝 o) (f : M → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f V) (hfi : Set.InjOn f V) : 3 ≤ d ∧ 5 ≤ r := by
  refine ⟨?_, D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive.five_le_of_hasFeatureRank C hnc
    (chainConnected_of_connected C hkappa) r hr⟩
  obtain ⟨φ, hφ⟩ := hr
  let _ : Group M := C.groupAt o
  have : IsTopologicalGroup M := isTopologicalGroup_groupAt C htri o
  have hφc : Continuous φ := continuous_feature C hkappa φ hφ
  have hinv : ∀ g x y : M, ⟪φ (g * x), φ (g * y)⟫_ℝ = ⟪φ x, φ y⟫_ℝ := fun g x y => by
    rw [← hφ, ← hφ]
    exact C.kappa_tri_left g o x y
  obtain ⟨ρ, hρc, hρker⟩ :=
    D5.S3.Quantum.AURICOmega.InvariantGramRepresentation.exists_orthogonal_rep_ker_eq φ
      (fun x => hφc.comp (continuous_id.mul continuous_const)) hinv
  have hρi : Function.Injective ρ := (injective_iff_map_eq_one ρ).2 fun g hg => by
    have h := (hρker g).1 hg 1
    rw [mul_one] at h
    exact (C.kappa_eq_one_iff g 1).1 (by rw [hφ, h, ← hφ, C.kappa_self])
  obtain ⟨x, y, hxy⟩ := (C.noncommutative_iff o).1 hnc
  exact three_le_of_orthogonal hV f hf hfi ρ hρc hρi ⟨x, y, hxy⟩

end D5.S3.Quantum.AURICOmega.FiniteRankDimensionBound

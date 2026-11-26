/- GID: D5/S3/Quantum/AURICOmega/TernaryComparisonRankFive
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/TernaryComparisonRankFive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rank bound five and unit-quaternion embedding for ternary comparison structures. -/

import D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates
import D5.S3.Quantum.AURICOmega.GramIsometryExtension
import D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector
import D5.S3.Quantum.AURICOmega.SmallInvariantSubspaceExclusion
import D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Feature rank of noncommutative ternary comparison structures.

Let `C` be a ternary comparison structure that is noncommutative and chain connected, whose
reading is the Gram kernel of a map `φ` into Euclidean `r`-space, and fix a base point `o`.

The image of `φ` spans a space `W` and consists of unit vectors with pairwise nonnegative inner
products. Left translations of the group at `o` extend to isometries of `W` permuting the image,
so they fix the least-norm point `m ≠ 0` of its closed convex hull, and `⟪m, φ x⟫ = ‖m‖ ^ 2` for
every `x`. The centered vectors `φ x - m` span the orthogonal complement `E` of `m` in `W`, of
dimension less than `r`, and their Gram kernel is `kappa - ‖m‖ ^ 2`. On `E`, left and right
translations give two commuting families of isometries. The left translations have no common
nonzero fixed vector and, by chain connectedness, generate their group from elements close to
the identity, which send no nonzero vector to its negative; the right translations do not
commute. If `E` had dimension at most four, these facts would give quaternionic coordinates on
`E` in which left translations act by right multiplication by unit quaternions, and `E` would
have dimension exactly four. Hence `r ≥ 5`.

For `r = 5`, the coordinates give a product-reversing injective map `q` into the unit
quaternions with `kappa x y = a + (1 - a) * ⟪q x, q y⟫`, where `a = ‖m‖ ^ 2 < 1`. Readings
arbitrarily close to zero give `a ≤ 1 / 2`. A unit quaternion `p ≠ 1` has a power whose real
part is at most `-re p`, so every reading between distinct points is at most `2 * a`; readings
arbitrarily close to one between distinct points then give `a ≥ 1 / 2`. The conjugate of `q` is
the required embedding. -/

open scoped InnerProductSpace Quaternion
open Module

namespace D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive

open D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open D5.S3.Quantum.AURICOmega.GramIsometryExtension
open D5.S3.Quantum.AURICOmega.NonobtuseFamilyFixedVector
open D5.S3.Quantum.AURICOmega.SmallInvariantSubspaceExclusion
open D5.S3.Quantum.AURICOmega.CommutantQuaternionCoordinates

section Span

variable {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A vector orthogonal to every member of a spanning family is zero. -/
private lemma eq_zero_of_forall_inner_eq_zero {ψ : ι → V}
    (hspan : Submodule.span ℝ (Set.range ψ) = ⊤) {w : V} (hw : ∀ i, ⟪w, ψ i⟫_ℝ = 0) :
    w = 0 := by
  have h : innerₛₗ ℝ w = 0 := LinearMap.ext_on_range hspan fun i => by
    rw [innerₛₗ_apply_apply, hw, LinearMap.zero_apply]
  have hww := LinearMap.congr_fun h w
  rwa [innerₛₗ_apply_apply, LinearMap.zero_apply, inner_self_eq_zero] at hww

/-- Two linear isometry equivalences that agree on a spanning family are equal. -/
private lemma isometry_ext {ψ : ι → V} (hspan : Submodule.span ℝ (Set.range ψ) = ⊤)
    {S T : V ≃ₗᵢ[ℝ] V} (h : ∀ i, S (ψ i) = T (ψ i)) : S = T :=
  LinearIsometryEquiv.toLinearEquiv_injective
    (LinearEquiv.toLinearMap_injective (LinearMap.ext_on_range hspan h))

end Span

section Translations

variable {M : Type*} (C : TernaryComparison M)

/-- Left translation `x ↦ tri g o x` by `g` in the group at `o`, as a permutation. -/
private def leftPerm (o g : M) : Equiv.Perm M where
  toFun x := C.tri g o x
  invFun x := C.tri (C.tri o g o) o x
  left_inv x := by
    change C.tri (C.tri o g o) o (C.tri g o x) = x
    rw [C.tri_assoc, C.tri_self_left, ← C.tri_assoc, C.tri_self_right, C.tri_self_left]
  right_inv x := by
    change C.tri g o (C.tri (C.tri o g o) o x) = x
    rw [← C.tri_assoc, ← C.tri_assoc, C.tri_self_right, C.tri_self_left, C.tri_self_left]

end Translations

section Center

variable {M : Type*} (C : TernaryComparison M)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- For a spanning family `ψ` whose Gram kernel is the reading, the least-norm point `m` of the
closed convex hull of the image is nonzero, has inner product `‖m‖ ^ 2` with every `ψ x`, and
lies on every affine hyperplane `⟪w, ·⟫ = c` containing the image. -/
private lemma exists_center (o : M) (ψ : M → V) (hspan : Submodule.span ℝ (Set.range ψ) = ⊤)
    (hψ : ∀ x y, ⟪ψ x, ψ y⟫_ℝ = C.kappa x y) :
    ∃ m : V, m ≠ 0 ∧ (∀ x, ⟪m, ψ x⟫_ℝ = ‖m‖ ^ 2) ∧
      ∀ w : V, ∀ c : ℝ, (∀ x, ⟪w, ψ x⟫_ℝ = c) → ⟪w, m⟫_ℝ = c := by
  have hunit : ∀ s ∈ Set.range ψ, ‖s‖ = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [norm_eq_sqrt_real_inner, hψ, C.kappa_self, Real.sqrt_one]
  have hpos : ∀ s ∈ Set.range ψ, ∀ t ∈ Set.range ψ, 0 ≤ ⟪s, t⟫_ℝ := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hψ]
    exact C.kappa_nonneg x y
  obtain ⟨m, hm0, hmK, -, -, hfix⟩ :=
    exists_fixed_ne_zero_of_pairwise_inner_nonneg (Set.range ψ) ⟨ψ o, o, rfl⟩ hunit hpos
  have haff : ∀ w : V, ∀ c : ℝ, (∀ x, ⟪w, ψ x⟫_ℝ = c) → ⟪w, m⟫_ℝ = c := by
    intro w c hw
    have hconv : Convex ℝ {v : V | ⟪w, v⟫_ℝ = c} := by
      intro u hu v hv s t _ _ hst
      simp only [Set.mem_ofPred_eq, inner_add_right, real_inner_smul_right] at hu hv ⊢
      rw [hu, hv, ← add_mul, hst, one_mul]
    have hclosed : IsClosed {v : V | ⟪w, v⟫_ℝ = c} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsub : closure (convexHull ℝ (Set.range ψ)) ⊆ {v : V | ⟪w, v⟫_ℝ = c} :=
      closure_minimal (convexHull_min (by rintro _ ⟨x, rfl⟩; exact hw x) hconv) hclosed
    exact hsub hmK
  choose L hL using fun g => (existsUnique_linearIsometryEquiv_of_gram_preserving ψ hspan
    (leftPerm C o g) fun x y => by
      rw [hψ, hψ]
      exact C.kappa_tri_left g o x y).exists
  have hLm : ∀ g, L g m = m := fun g => hfix (L g) (by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, (hL g x).symm⟩)
  have hconst : ∀ x, ⟪m, ψ x⟫_ℝ = ⟪m, ψ o⟫_ℝ := fun x => by
    rw [← (L x).inner_map_map m (ψ o), hLm, hL]
    exact congrArg (fun z => ⟪m, ψ z⟫_ℝ) (C.tri_self_right x o).symm
  refine ⟨m, hm0, fun x => ?_, haff⟩
  rw [hconst x, ← real_inner_self_eq_norm_sq, haff m _ hconst]

/-- Centering a spanning realization of the reading at the point of `exists_center`: the vectors
`ψ x - m` lie in the orthogonal complement of `m`, span it, have Gram kernel `kappa - ‖m‖ ^ 2`,
and no nonzero vector of the complement has constant inner product with all of them. -/
private lemma exists_centered (o : M) (ψ : M → V) (hspan : Submodule.span ℝ (Set.range ψ) = ⊤)
    (hψ : ∀ x y, ⟪ψ x, ψ y⟫_ℝ = C.kappa x y) :
    ∃ m : V, m ≠ 0 ∧ ∃ ψ' : M → (ℝ ∙ m)ᗮ, Submodule.span ℝ (Set.range ψ') = ⊤ ∧
      (∀ x y, ⟪ψ' x, ψ' y⟫_ℝ = C.kappa x y - ‖m‖ ^ 2) ∧
      ∀ w : (ℝ ∙ m)ᗮ, ∀ c : ℝ, (∀ x, ⟪w, ψ' x⟫_ℝ = c) → w = 0 := by
  obtain ⟨m, hm0, hm, haff⟩ := exists_center C o ψ hspan hψ
  have hmem : ∀ x, ψ x - m ∈ (ℝ ∙ m)ᗮ := fun x => by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, hm,
      real_inner_self_eq_norm_sq, sub_self]
  let ψ' : M → (ℝ ∙ m)ᗮ := fun x => ⟨ψ x - m, hmem x⟩
  have hwm : ∀ w : (ℝ ∙ m)ᗮ, ⟪(w : V), m⟫_ℝ = 0 := fun w => by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
  have hcoe : ∀ (w : (ℝ ∙ m)ᗮ) (x : M), ⟪w, ψ' x⟫_ℝ = ⟪(w : V), ψ x⟫_ℝ := fun w x => by
    change ⟪(w : V), ψ x - m⟫_ℝ = _
    rw [inner_sub_right, hwm, sub_zero]
  have hspan' : Submodule.span ℝ (Set.range ψ') = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro w hw
    have h0 : (w : V) = 0 := eq_zero_of_forall_inner_eq_zero hspan fun x => by
      rw [← hcoe]
      exact (Submodule.mem_orthogonal' _ _).mp hw _ (Submodule.subset_span ⟨x, rfl⟩)
    exact (Submodule.coe_eq_zero).mp h0
  refine ⟨m, hm0, ψ', hspan', fun x y => ?_, fun w c hw => ?_⟩
  · change ⟪ψ x - m, ψ y - m⟫_ℝ = _
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hψ, real_inner_comm m (ψ x), hm, hm,
      real_inner_self_eq_norm_sq]
    ring
  · have h1 : ∀ x, ⟪(w : V), ψ x⟫_ℝ = c := fun x => (hcoe w x).symm.trans (hw x)
    have hc : c = 0 := (haff (w : V) c h1).symm.trans (hwm w)
    exact eq_zero_of_forall_inner_eq_zero hspan' fun x => (hw x).trans hc

end Center

section Reduction

variable {M : Type*} (C : TernaryComparison M)

/-- A reading of feature rank `r` is the Gram kernel of a family spanning a subspace of
Euclidean `r`-space. -/
private lemma exists_spanning_realization {r : ℕ} (hr : C.HasFeatureRank r) :
    ∃ W : Submodule ℝ (EuclideanSpace ℝ (Fin r)), finrank ℝ W ≤ r ∧
      ∃ ψ : M → W, Submodule.span ℝ (Set.range ψ) = ⊤ ∧
        ∀ x y, ⟪ψ x, ψ y⟫_ℝ = C.kappa x y := by
  obtain ⟨φ, hφ⟩ := hr
  let W := Submodule.span ℝ (Set.range φ)
  let ψ : M → W := fun x => ⟨φ x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hrange : Set.range ψ = ((↑) : W → EuclideanSpace ℝ (Fin r)) ⁻¹' Set.range φ := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hspan : Submodule.span ℝ (Set.range ψ) = ⊤ := by
    rw [hrange]
    exact Submodule.span_span_coe_preimage
  refine ⟨W, ?_, ψ, hspan, fun x y => (hφ x y).symm⟩
  calc finrank ℝ W ≤ finrank ℝ (EuclideanSpace ℝ (Fin r)) := Submodule.finrank_le W
    _ = r := finrank_euclideanSpace_fin

end Reduction

section Core

variable {M : Type*} (C : TernaryComparison M)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a spanning family with Gram kernel `kappa - a` and isometries `L g` realizing left
translations, `L h` sends no nonzero vector to its negative as soon as `kappa o h` is close
enough to one: then `L h` moves every vector `v` by at most `‖v‖`. -/
private lemma exists_no_antipodal [FiniteDimensional ℝ E] (o : M) (ψ : M → E) (a : ℝ)
    (hspan : Submodule.span ℝ (Set.range ψ) = ⊤) (hψ : ∀ x y, ⟪ψ x, ψ y⟫_ℝ = C.kappa x y - a)
    (L : M → E ≃ₗᵢ[ℝ] E) (hL : ∀ g x, L g (ψ x) = ψ (C.tri g o x)) :
    ∃ η : ℝ, 0 < η ∧ ∀ h, 1 - η < C.kappa o h → ∀ v, L h v = -v → v = 0 := by
  let b := Basis.ofSpan hspan.ge
  have := Module.Finite.finite_basis b
  obtain ⟨K, hK, hop⟩ := b.exists_opNorm_le (F := E)
  have hK1 : 0 < 1 / K := one_div_pos.mpr hK
  refine ⟨(1 / K) ^ 2 / 2, div_pos (pow_pos hK1 2) two_pos, fun h hh v hv => ?_⟩
  let T : E →L[ℝ] E :=
    (L h).toContinuousLinearEquiv.toContinuousLinearMap - ContinuousLinearMap.id ℝ E
  have hT : ∀ w, T w = L h w - w := fun w => rfl
  have hTb : ∀ i, ‖T (b i)‖ ≤ 1 / K := by
    intro i
    obtain ⟨x, hx⟩ : b i ∈ Set.range ψ := Basis.ofSpan_subset hspan.ge ⟨i, rfl⟩
    have hk : C.kappa (C.tri h o x) x = C.kappa o h := by
      have h1 := C.kappa_tri_right h o o x
      rw [C.tri_self_left] at h1
      rw [h1, C.kappa_symm]
    have hsq : ‖T (b i)‖ ^ 2 = 2 - 2 * C.kappa o h := by
      rw [hT, ← hx, hL, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, hψ, hψ, hψ, C.kappa_self, C.kappa_self, hk]
      ring
    refine (lt_of_pow_lt_pow_left₀ 2 hK1.le ?_).le
    rw [hsq]
    linarith
  have hTv : ‖T v‖ ≤ ‖v‖ :=
    calc ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
      _ ≤ K * (1 / K) * ‖v‖ := mul_le_mul_of_nonneg_right (hop hK1.le hTb) (norm_nonneg v)
      _ = ‖v‖ := by rw [mul_one_div_cancel hK.ne', one_mul]
  rw [hT, hv, show -v - v = (-2 : ℝ) • v by module, norm_smul] at hTv
  norm_num at hTv
  exact norm_le_zero_iff.mp (by linarith)

/-- By chain connectedness, the group generated by the isometries `L g` realizing left
translations is generated by its elements sending no nonzero vector to its negative. -/
private lemma closure_no_antipodal_eq [FiniteDimensional ℝ E] (hconn : C.ChainConnected)
    (o : M) (ψ : M → E) (a : ℝ) (hspan : Submodule.span ℝ (Set.range ψ) = ⊤)
    (hψ : ∀ x y, ⟪ψ x, ψ y⟫_ℝ = C.kappa x y - a)
    (L : M → E ≃ₗᵢ[ℝ] E) (hL : ∀ g x, L g (ψ x) = ψ (C.tri g o x))
    (hLmul : ∀ g h, L (C.tri g o h) = L g * L h) (hLone : L o = 1) :
    Subgroup.closure {T : E ≃ₗᵢ[ℝ] E | T ∈ Subgroup.closure (Set.range L) ∧
      ∀ v : E, T v = -v → v = 0} = Subgroup.closure (Set.range L) := by
  obtain ⟨η, hη, hneg⟩ := exists_no_antipodal C o ψ a hspan hψ L hL
  refine le_antisymm ((Subgroup.closure_le _).mpr fun T hT => hT.1)
    ((Subgroup.closure_le _).mpr ?_)
  rintro _ ⟨g, rfl⟩
  rw [SetLike.mem_coe]
  have hch := hconn η hη o g
  induction hch with
  | refl =>
    rw [hLone]
    exact one_mem _
  | @tail b c _ hbc ih =>
    have hc : C.tri b o (C.tri o b c) = c := by
      rw [← C.tri_assoc, C.tri_self_right, C.tri_self_left]
    have hk : C.kappa o (C.tri o b c) = C.kappa b c := by
      have h1 := C.kappa_tri_left b o o (C.tri o b c)
      rw [C.tri_self_right, hc] at h1
      exact h1.symm
    rw [← hc, hLmul]
    refine mul_mem ih (Subgroup.subset_closure
      ⟨Subgroup.subset_closure ⟨_, rfl⟩, hneg _ ?_⟩)
    rw [hk]
    exact hbc

/-- A vector fixed by every isometry realizing a left translation is zero, when no nonzero
vector has constant inner product with the family. -/
private lemma eq_zero_of_forall_fixed (o : M) (ψ : M → E)
    (hconst : ∀ w : E, ∀ c : ℝ, (∀ x, ⟪w, ψ x⟫_ℝ = c) → w = 0)
    (L : M → E ≃ₗᵢ[ℝ] E) (hL : ∀ g x, L g (ψ x) = ψ (C.tri g o x)) (v : E)
    (hv : ∀ T ∈ Subgroup.closure (Set.range L), T v = v) : v = 0 :=
  hconst v ⟪v, ψ o⟫_ℝ fun x => by
    rw [← (L x).inner_map_map v (ψ o), hv (L x) (Subgroup.subset_closure ⟨x, rfl⟩), hL,
      C.tri_self_right]

/-- On a centered spanning realization of dimension at most four, the group generated by left
translations and the commutant containing right translations satisfy the hypotheses of
`exists_quaternion_coordinates`. The resulting coordinates give `finrank = 4`, `a < 1` and a
product-reversing injective map `q` into the unit quaternions with
`kappa x y = a + (1 - a) * ⟪q x, q y⟫`. -/
private theorem exists_quaternion_reading [FiniteDimensional ℝ E] (hnc : C.Noncommutative)
    (hconn : C.ChainConnected) (o : M) (ψ : M → E) (a : ℝ)
    (hspan : Submodule.span ℝ (Set.range ψ) = ⊤) (hψ : ∀ x y, ⟪ψ x, ψ y⟫_ℝ = C.kappa x y - a)
    (hconst : ∀ w : E, ∀ c : ℝ, (∀ x, ⟪w, ψ x⟫_ℝ = c) → w = 0)
    (hdim : finrank ℝ E ≤ 4) :
    finrank ℝ E = 4 ∧ a < 1 ∧ ∃ q : M → ℍ, (∀ g, ‖q g‖ = 1) ∧ q o = 1 ∧
      (∀ g h, q (C.tri g o h) = q h * q g) ∧ Function.Injective q ∧
      ∀ x y, C.kappa x y = a + (1 - a) * ⟪q x, q y⟫_ℝ := by
  have hinj : Function.Injective ψ := fun x y hxy => (C.kappa_eq_one_iff x y).mp (by
    have h := hψ x y
    rw [← hxy, hψ, C.kappa_self] at h
    linarith)
  obtain ⟨x₀, y₀, hxy₀⟩ := (C.noncommutative_iff o).mp hnc
  choose L hL using fun g => (existsUnique_linearIsometryEquiv_of_gram_preserving ψ hspan
    (leftPerm C o g) fun x y => by
      rw [hψ, hψ]
      exact congrArg (· - a) (C.kappa_tri_left g o x y)).exists
  replace hL : ∀ g x, L g (ψ x) = ψ (C.tri g o x) := hL
  choose R hR using fun g => (existsUnique_linearIsometryEquiv_of_gram_preserving ψ hspan
    (Equiv.ofBijective _ (C.baseChange_bijective o g)) fun x y => by
      rw [hψ, hψ]
      exact congrArg (· - a) (C.kappa_tri_right x y o g)).exists
  replace hR : ∀ g x, R g (ψ x) = ψ (C.tri x o g) := hR
  have hLmul : ∀ g h, L (C.tri g o h) = L g * L h := fun g h => isometry_ext hspan fun x => by
    rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, hL (C.tri g o h) x, hL h x,
      hL g (C.tri h o x), C.tri_assoc]
  have hLone : L o = 1 := isometry_ext hspan fun x => by
    rw [hL, C.tri_self_left]
    rfl
  have hLR : ∀ g h, L g * R h = R h * L g := fun g h => isometry_ext hspan fun x => by
    rw [LinearIsometryEquiv.coe_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply,
      Function.comp_apply, hR h x, hL g (C.tri x o h), hL g x, hR h (C.tri g o x), C.tri_assoc]
  have hRmem : ∀ h, R h ∈ Subgroup.centralizer (Set.range L) := fun h =>
    Subgroup.mem_centralizer_iff.mpr (by
      rintro _ ⟨g, rfl⟩
      exact hLR g h)
  have hcomm : ∀ S ∈ Subgroup.closure (Set.range L),
      ∀ T ∈ Subgroup.centralizer (Set.range L), S * T = T * S := fun S hS T hT => by
    rw [← Subgroup.centralizer_closure] at hT
    exact Subgroup.mem_centralizer_iff.mp hT S hS
  have hU : ∃ S ∈ Subgroup.closure (Set.range L), ∃ T ∈ Subgroup.closure (Set.range L),
      S * T ≠ T * S :=
    ⟨L x₀, Subgroup.subset_closure ⟨x₀, rfl⟩, L y₀, Subgroup.subset_closure ⟨y₀, rfl⟩,
      fun h => hxy₀ (hinj (by
        have h1 := DFunLike.congr_fun h (ψ o)
        simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, hL, C.tri_self_right]
          at h1
        exact h1))⟩
  have hV : ∃ S ∈ Subgroup.centralizer (Set.range L), ∃ T ∈ Subgroup.centralizer (Set.range L),
      S * T ≠ T * S :=
    ⟨R x₀, hRmem x₀, R y₀, hRmem y₀, fun h => hxy₀ (hinj (by
        have h1 := DFunLike.congr_fun h (ψ o)
        simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, hR, C.tri_self_left]
          at h1
        exact h1.symm))⟩
  have hirr := invariant_submodule_eq_bot_or_top (Subgroup.closure (Set.range L)) hdim
    (eq_zero_of_forall_fixed C o ψ hconst L hL)
    (closure_no_antipodal_eq C hconn o ψ a hspan hψ L hL hLmul hLone) hU
  have hnorm : ∀ x, ‖ψ x‖ ^ 2 = 1 - a := fun x => by
    rw [← real_inner_self_eq_norm_sq, hψ, C.kappa_self]
  have ha : a < 1 := by
    by_contra h
    have h' := not_lt.mp h
    have hz : ∀ x, ψ x = 0 := fun x => norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp
      (le_antisymm (by rw [hnorm]; linarith) (sq_nonneg _)))
    exact hxy₀ (by rw [hinj ((hz x₀).trans (hz y₀).symm)])
  have hs0 : ‖ψ o‖ ≠ 0 := fun h => by
    have h2 := hnorm o
    rw [h, zero_pow two_ne_zero] at h2
    linarith
  have he : ‖‖ψ o‖⁻¹ • ψ o‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs0]
  obtain ⟨hfin, hcoord⟩ := exists_quaternion_coordinates
    (Subgroup.closure (Set.range L)) (Subgroup.centralizer (Set.range L)) hdim hirr hcomm hV
  obtain ⟨Φ, hΦe, -, hΦU⟩ := hcoord (‖ψ o‖⁻¹ • ψ o) he
  choose q hq1 hq using fun g => hΦU (L g) (Subgroup.subset_closure ⟨g, rfl⟩)
  have hΦo : Φ (ψ o) = ‖ψ o‖ • (1 : ℍ) := by
    have hψo : ψ o = ‖ψ o‖ • (‖ψ o‖⁻¹ • ψ o) := (smul_inv_smul₀ hs0 (ψ o)).symm
    conv_lhs => rw [hψo]
    rw [map_smul, hΦe]
  have hΦψ : ∀ x, Φ (ψ x) = ‖ψ o‖ • q x := fun x => by
    have h1 := hq x (ψ o)
    rw [hL, C.tri_self_right, hΦo, smul_mul_assoc, one_mul] at h1
    exact h1
  have hqo : q o = 1 := smul_right_injective ℍ hs0 ((hΦψ o).symm.trans hΦo)
  have hqmul : ∀ g h, q (C.tri g o h) = q h * q g := fun g h => by
    have h1 := hq g (ψ h)
    rw [hL, hΦψ (C.tri g o h), hΦψ h, smul_mul_assoc] at h1
    exact smul_right_injective ℍ hs0 h1
  have hqinj : Function.Injective q := fun g h hgh =>
    hinj (Φ.injective (by rw [hΦψ, hΦψ, hgh]))
  have hread : ∀ x y, C.kappa x y = a + (1 - a) * ⟪q x, q y⟫_ℝ := fun x y => by
    have h1 := hψ x y
    rw [← Φ.inner_map_map (ψ x) (ψ y), hΦψ, hΦψ, real_inner_smul_left,
      real_inner_smul_right] at h1
    linear_combination -h1 + ⟪q x, q y⟫_ℝ * hnorm o
  exact ⟨hfin, ha, q, hq1, hqo, hqmul, hqinj, hread⟩

end Core

section Realization

variable {M : Type*} (C : TernaryComparison M)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A spanning family of a real inner product space of dimension at most five whose Gram
kernel is the reading forces the dimension to be five, and yields `a < 1` and a
product-reversing injective map `q` into the unit quaternions with
`kappa x y = a + (1 - a) * ⟪q x, q y⟫`. The centered family lives in the orthogonal complement
of the point of `exists_center`, of dimension at most four. -/
private theorem exists_reading (hnc : C.Noncommutative) (hconn : C.ChainConnected) (o : M)
    (ψ : M → V) (hspan : Submodule.span ℝ (Set.range ψ) = ⊤)
    (hψ : ∀ x y, ⟪ψ x, ψ y⟫_ℝ = C.kappa x y) (hdim : finrank ℝ V ≤ 5) :
    finrank ℝ V = 5 ∧ ∃ a : ℝ, a < 1 ∧ ∃ q : M → ℍ, (∀ g, ‖q g‖ = 1) ∧ q o = 1 ∧
      (∀ g h, q (C.tri g o h) = q h * q g) ∧ Function.Injective q ∧
      ∀ x y, C.kappa x y = a + (1 - a) * ⟪q x, q y⟫_ℝ := by
  obtain ⟨m, hm0, ψ', hspan', hψ', hconst'⟩ := exists_centered C o ψ hspan hψ
  have hlt : finrank ℝ (ℝ ∙ m)ᗮ < finrank ℝ V := Submodule.finrank_lt (by
    rwa [Ne, Submodule.orthogonal_eq_top_iff, Submodule.span_singleton_eq_bot])
  obtain ⟨h4, ha, q, hq⟩ :=
    exists_quaternion_reading C hnc hconn o ψ' _ hspan' hψ' hconst' (by omega)
  exact ⟨by omega, _, ha, q, hq⟩

end Realization

section Quaternion

/-- For a unit quaternion `p`, the real parts of the powers of `p` satisfy the recurrence
`re (p ^ (k + 2)) = 2 * re p * re (p ^ (k + 1)) - re (p ^ k)`, since
`p * p = (2 * re p) • p - 1`. -/
private lemma re_pow_succ_succ (p : ℍ) (hp : ‖p‖ = 1) (k : ℕ) :
    (p ^ (k + 1 + 1)).re = 2 * p.re * (p ^ (k + 1)).re - (p ^ k).re := by
  have hps : p * star p = 1 := by
    rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, hp, mul_one,
      Quaternion.coe_one]
  have hsq : p * p = (2 * p.re) • p - 1 := by
    rw [← Quaternion.mul_coe_eq_smul, ← Quaternion.self_add_star', mul_add, hps,
      add_sub_cancel_right]
  have h : p ^ (k + 1 + 1) = (2 * p.re) • p ^ (k + 1) - p ^ k := by
    rw [pow_succ, pow_succ, mul_assoc, hsq, mul_sub, mul_one, mul_smul_comm]
  rw [h, Quaternion.re_sub, Quaternion.re_smul, smul_eq_mul]

/-- The real parts of the powers of a unit quaternion `p` are `cos (k * arccos (re p))`. -/
private lemma re_pow_eq_cos (p : ℍ) (hp : ‖p‖ = 1) (hre : -1 ≤ p.re ∧ p.re ≤ 1) (k : ℕ) :
    (p ^ k).re = Real.cos (k * Real.arccos p.re) ∧
      (p ^ (k + 1)).re = Real.cos (((k + 1 : ℕ) : ℝ) * Real.arccos p.re) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [pow_zero, Quaternion.re_one, Nat.cast_zero, zero_mul, Real.cos_zero]
    · rw [zero_add, pow_one, Nat.cast_one, one_mul, Real.cos_arccos hre.1 hre.2]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [re_pow_succ_succ p hp k, ih.1, ih.2]
    have hc : Real.cos (Real.arccos p.re) = p.re := Real.cos_arccos hre.1 hre.2
    have h2 : ∀ x y : ℝ, Real.cos (x + y) = 2 * Real.cos y * Real.cos x - Real.cos (x - y) :=
      fun x y => by
        rw [Real.cos_add, Real.cos_sub]
        ring
    have e1 : ((k + 1 + 1 : ℕ) : ℝ) * Real.arccos p.re =
        ((k + 1 : ℕ) : ℝ) * Real.arccos p.re + Real.arccos p.re := by
      push_cast
      ring
    have e2 : (k : ℝ) * Real.arccos p.re =
        ((k + 1 : ℕ) : ℝ) * Real.arccos p.re - Real.arccos p.re := by
      push_cast
      ring
    rw [e1, e2, h2, hc]

/-- A unit quaternion `p ≠ 1` has a power whose real part is at most `-re p`: with
`θ = arccos (re p) ∈ (0, π]` and `k = ⌊π / θ⌋`, the angle `k * θ` lies in `[π - θ, π]`. -/
private lemma exists_re_pow_le_neg_re (p : ℍ) (hp : ‖p‖ = 1) (hp1 : p ≠ 1) :
    ∃ k : ℕ, (p ^ k).re ≤ -p.re := by
  have hre : ⟪p, 1⟫_ℝ = p.re := by
    rw [Quaternion.inner_def, star_one, mul_one]
  have hle : p.re ≤ 1 := by
    have h := real_inner_le_norm p 1
    rwa [hre, hp, norm_one, one_mul] at h
  have hge : -1 ≤ p.re := by
    have h := neg_le_of_abs_le (abs_real_inner_le_norm p 1)
    rwa [hre, hp, norm_one, one_mul] at h
  have hlt : p.re < 1 := by
    refine lt_of_le_of_ne hle fun h => hp1 ?_
    have h0 : ‖p - 1‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hre, h, hp, norm_one]
      norm_num
    exact sub_eq_zero.mp (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))
  have hθ0 : 0 < Real.arccos p.re := Real.arccos_pos.mpr hlt
  have hθπ : Real.arccos p.re ≤ Real.pi := Real.arccos_le_pi p.re
  refine ⟨⌊Real.pi / Real.arccos p.re⌋₊, ?_⟩
  rw [(re_pow_eq_cos p hp ⟨hge, hle⟩ _).1]
  have h1 : (⌊Real.pi / Real.arccos p.re⌋₊ : ℝ) * Real.arccos p.re ≤ Real.pi := by
    calc (⌊Real.pi / Real.arccos p.re⌋₊ : ℝ) * Real.arccos p.re
        ≤ Real.pi / Real.arccos p.re * Real.arccos p.re :=
          mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg Real.pi_pos.le hθ0.le)) hθ0.le
      _ = Real.pi := div_mul_cancel₀ _ hθ0.ne'
  have h2 : Real.pi - Real.arccos p.re ≤
      (⌊Real.pi / Real.arccos p.re⌋₊ : ℝ) * Real.arccos p.re := by
    have h3 : Real.pi < ((⌊Real.pi / Real.arccos p.re⌋₊ : ℝ) + 1) * Real.arccos p.re := by
      calc Real.pi = Real.pi / Real.arccos p.re * Real.arccos p.re :=
            (div_mul_cancel₀ _ hθ0.ne').symm
        _ < ((⌊Real.pi / Real.arccos p.re⌋₊ : ℝ) + 1) * Real.arccos p.re :=
            mul_lt_mul_of_pos_right (Nat.lt_floor_add_one _) hθ0
    linarith
  calc Real.cos ((⌊Real.pi / Real.arccos p.re⌋₊ : ℝ) * Real.arccos p.re)
      ≤ Real.cos (Real.pi - Real.arccos p.re) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) h1 h2
    _ = -p.re := by rw [Real.cos_pi_sub, Real.cos_arccos hge hle]

/-- Quaternion conjugation preserves the real inner product. -/
private lemma inner_star_star (p q : ℍ) : ⟪star p, star q⟫_ℝ = ⟪p, q⟫_ℝ := by
  simp only [Quaternion.inner_def, star_star, Quaternion.re_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  ring

end Quaternion

section Coefficient

variable {M : Type*} (C : TernaryComparison M)

/-- If the reading is `a + (1 - a) * ⟪q x, q y⟫` for a product-reversing injective map `q` into
the unit quaternions with `q o = 1` and `a < 1`, and the reading touches zero and is chain
connected on a set with a point other than `o`, then `a = 1 / 2`. -/
private lemma coeff_eq_half (hconn : C.ChainConnected) (hzero : C.TouchesZero) (o g₀ : M)
    (hg₀ : g₀ ≠ o) (q : M → ℍ) (hq1 : ∀ g, ‖q g‖ = 1) (hqo : q o = 1)
    (hqmul : ∀ g h, q (C.tri g o h) = q h * q g) (hqinj : Function.Injective q) (a : ℝ)
    (ha : a < 1) (hread : ∀ x y, C.kappa x y = a + (1 - a) * ⟪q x, q y⟫_ℝ) : a = 1 / 2 := by
  have hle : a ≤ 1 / 2 := by
    by_contra h
    obtain ⟨x, y, hxy⟩ := hzero (2 * a - 1) (by linarith [not_le.mp h])
    have h1 : -1 ≤ ⟪q x, q y⟫_ℝ := by
      have h2 := neg_le_of_abs_le (abs_real_inner_le_norm (q x) (q y))
      rwa [hq1, hq1, one_mul] at h2
    rw [hread] at hxy
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.le) (neg_le_iff_add_nonneg.mp h1)]
  have hpow : ∀ (h : M) (k : ℕ), ∃ m, q m = q h ^ k := by
    intro h k
    induction k with
    | zero => exact ⟨o, by rw [hqo, pow_zero]⟩
    | succ k ih =>
      obtain ⟨m, hm⟩ := ih
      exact ⟨C.tri h o m, by rw [hqmul, hm, pow_succ]⟩
  have hone : ∀ p : ℍ, ⟪(1 : ℍ), p⟫_ℝ = p.re := fun p => by
    rw [Quaternion.inner_def, one_mul, Quaternion.re_star]
  have hupper : ∀ h, h ≠ o → C.kappa o h ≤ 2 * a := by
    intro h hh
    obtain ⟨k, hk⟩ :=
      exists_re_pow_le_neg_re (q h) (hq1 h) fun e => hh (hqinj (e.trans hqo.symm))
    obtain ⟨m, hm⟩ := hpow h k
    have h0 := C.kappa_nonneg o m
    rw [hread, hqo, hm, hone] at h0
    rw [hread, hqo, hone]
    nlinarith [mul_le_mul_of_nonneg_left hk (sub_nonneg.mpr ha.le)]
  have hdist : ∀ x z, x ≠ z → C.kappa x z ≤ 2 * a := by
    intro x z hxz
    have hc : C.tri x o (C.tri o x z) = z := by
      rw [← C.tri_assoc, C.tri_self_right, C.tri_self_left]
    have hk : C.kappa x z = C.kappa o (C.tri o x z) := by
      have h1 := C.kappa_tri_left x o o (C.tri o x z)
      rwa [C.tri_self_right, hc] at h1
    rw [hk]
    refine hupper _ fun h => hxz ?_
    rw [← hc, h, C.tri_self_right]
  have hstep : ∀ ε, 0 < ε → ∃ x z, x ≠ z ∧ 1 - ε < C.kappa x z := by
    intro ε hε
    have key : ∀ y, Relation.ReflTransGen (fun u v => 1 - ε < C.kappa u v) o y → y ≠ o →
        ∃ x z, x ≠ z ∧ 1 - ε < C.kappa x z := by
      intro y hy
      induction hy with
      | refl => exact fun h => absurd rfl h
      | @tail b c _ hbc ih =>
        intro hc
        by_cases hb : b = c
        · exact ih (by rw [hb]; exact hc)
        · exact ⟨b, c, hb, hbc⟩
    exact key g₀ (hconn ε hε o g₀) hg₀
  have hge : 1 / 2 ≤ a := by
    by_contra h
    obtain ⟨x, z, hxz, hk⟩ := hstep (1 - 2 * a) (by linarith [not_le.mp h])
    linarith [hdist x z hxz]
  linarith

end Coefficient

/-- A noncommutative, chain-connected ternary comparison structure whose reading is the Gram
kernel of a map into Euclidean `r`-space has `r ≥ 5`. -/
theorem five_le_of_hasFeatureRank {M : Type*} (C : TernaryComparison M)
    (hnc : C.Noncommutative) (hconn : C.ChainConnected)
    (r : ℕ) (hr : C.HasFeatureRank r) : 5 ≤ r := by
  obtain ⟨o, -, -, -⟩ := id hnc
  obtain ⟨W, hW, ψ, hspan, hψ⟩ := exists_spanning_realization C hr
  by_contra h
  have h5 := (exists_reading C hnc hconn o ψ hspan hψ (by omega)).1
  omega

/-- A noncommutative, chain-connected ternary comparison structure whose reading touches zero
and has feature rank five embeds injectively into the unit quaternions, carrying the transfer
to `u x * (u y)⁻¹ * u z` and the reading to `(1 + ⟪u x, u y⟫) / 2`. -/
theorem exists_unitQuaternion_embedding {M : Type*} (C : TernaryComparison M)
    (hnc : C.Noncommutative) (hconn : C.ChainConnected) (hzero : C.TouchesZero)
    (hr : C.HasFeatureRank 5) :
    ∃ u : M → unitary ℍ[ℝ], Function.Injective u ∧
      (∀ x y z : M, u (C.tri x y z) = u x * (u y)⁻¹ * u z) ∧
      (∀ x y : M, C.kappa x y = (1 + ⟪(u x : ℍ[ℝ]), (u y : ℍ[ℝ])⟫_ℝ) / 2) := by
  obtain ⟨o, -, -, -⟩ := id hnc
  obtain ⟨W, hW, ψ, hspan, hψ⟩ := exists_spanning_realization C hr
  obtain ⟨-, a, ha, q, hq1, hqo, hqmul, hqinj, hread⟩ :=
    exists_reading C hnc hconn o ψ hspan hψ hW
  obtain ⟨x₀, y₀, hxy₀⟩ := (C.noncommutative_iff o).mp hnc
  have hx₀ : x₀ ≠ o := fun h => hxy₀ (by rw [h, C.tri_self_left, C.tri_self_right])
  have hhalf := coeff_eq_half C hconn hzero o x₀ hx₀ q hq1 hqo hqmul hqinj _ ha hread
  have hnq : ∀ g, Quaternion.normSq (q g) = 1 := fun g => by
    rw [Quaternion.normSq_eq_norm_mul_self, hq1, mul_one]
  let u : M → unitary ℍ[ℝ] := fun g => ⟨star (q g), Unitary.mem_iff.mpr
    ⟨by rw [star_star, Quaternion.self_mul_star, hnq, Quaternion.coe_one],
      by rw [star_star, Quaternion.star_mul_self, hnq, Quaternion.coe_one]⟩⟩
  have hu : ∀ g, (u g : ℍ[ℝ]) = star (q g) := fun g => rfl
  have humul : ∀ g h, u (C.tri g o h) = u g * u h := fun g h => Subtype.ext (by
    rw [Submonoid.coe_mul, hu, hu, hu, hqmul, star_mul])
  have huone : u o = 1 := Subtype.ext (by
    rw [hu, hqo, star_one]
    rfl)
  have huinv : ∀ y, u (C.tri o y o) = (u y)⁻¹ := fun y => eq_inv_of_mul_eq_one_left (by
    rw [← humul, C.tri_assoc, C.tri_self_left, C.tri_self_right, huone])
  refine ⟨u, fun g h e => hqinj (star_injective (congrArg Subtype.val e)), fun x y z => ?_,
    fun x y => ?_⟩
  · have htri : C.tri x y z = C.tri (C.tri x o (C.tri o y o)) o z :=
      C.tri_eq_mul_inv_mul o x y z
    rw [htri, humul, humul, huinv]
  · rw [hread, hu, hu, inner_star_star, hhalf]
    ring

end D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive

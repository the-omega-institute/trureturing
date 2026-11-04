/- GID: D5/S3/Combinatorics/Graph/Laman/TrivialMotions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/TrivialMotions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional]
   utility: none
   digest: Independent translations and skew rotations bound the rigidity kernel at affinely spanning placements. -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/laman-henneberg/LICENSE.txt.
Authors: Bryan Gin-ge Chen
Modified file: selected source declarations reorganized for trureturing;
receiver imports and API adaptations; unconsumed declarations omitted.
Source: CombinatorialRigidity@021c2284bc387efee3c3b20a18eb5f769638b578.
-/
import D5.S3.Combinatorics.Graph.Laman.Framework
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# TrivialMotions

Translations and elementary skew rotations are infinitesimal motions for every graph. Their joint linear independence at an affinely spanning placement bounds the dimension of the rigidity kernel.
-/

@[expose] public section

open scoped InnerProductSpace

open Module

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-! ### Translations -/

/-- The constant motion translating every vertex by `t`. Every translation lies in the kernel of
`G.RigidityMap p` (`translationMotion_mem_ker`): edge-length derivatives all vanish because
`p'_u - p'_v = t - t = 0` for any edge `s(u, v)`. -/
@[expose] def translationMotion (t : EuclideanSpace ℝ (Fin d)) : Framework V d :=
  fun _ => t



theorem translationMotion_mem_ker (G : SimpleGraph V) (p : Framework V d)
    (t : EuclideanSpace ℝ (Fin d)) :
    (translationMotion t : Framework V d) ∈ LinearMap.ker (G.RigidityMap p) := by
  rw [LinearMap.mem_ker]
  funext ⟨e, he⟩
  induction e with
  | h u v => simp [rigidityMap_apply, translationMotion]

/-! ### Infinitesimal rotations -/

/-- The infinitesimal-rotation motion at placement `p` driven by a linear map `A`. For the motion
to lie in the rigidity-map kernel (cf.\ `infinitesimalRotation_mem_ker`), `A` must satisfy the
"skew-adjoint" condition `⟪x, A x⟫_ℝ = 0` for every `x`; in dimension `d` such `A`'s form a
`d (d − 1) / 2`-dimensional space (skew-symmetric matrices), recovering the textbook count
$d + d(d - 1)/2 = d(d+1)/2$ for the trivial-motions dimension. -/
@[expose] def infinitesimalRotation
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) (p : Framework V d) :
    Framework V d := fun v => A (p v)



theorem infinitesimalRotation_mem_ker (G : SimpleGraph V) (p : Framework V d)
    {A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (hA : ∀ x, ⟪x, A x⟫_ℝ = 0) :
    infinitesimalRotation A p ∈ LinearMap.ker (G.RigidityMap p) := by
  rw [LinearMap.mem_ker]
  funext ⟨e, he⟩
  induction e with
  | h u v =>
    simp only [rigidityMap_apply, Pi.zero_apply, infinitesimalRotation]
    rw [← map_sub A]
    exact hA _

/-! ### The submodule of trivial motions -/

/-- The submodule of **trivial infinitesimal motions** at placement `p`: the span of all
translations together with all infinitesimal rotations by skew-adjoint linear maps.

For every graph `G` this submodule lies in the kernel of `G.RigidityMap p`
(`trivialMotions_le_ker`). At a placement that affinely spans `EuclideanSpace ℝ (Fin d)` it has
dimension at least `d (d + 1) / 2` (`trivialMotions_finrank_ge_of_affinelySpanning`), the
dimension of the Euclidean rigid motions; the matching upper bound is not proved here. -/
def trivialMotions (p : Framework V d) : Submodule ℝ (Framework V d) :=
  Submodule.span ℝ <|
    Set.range (translationMotion (V := V) : EuclideanSpace ℝ (Fin d) → Framework V d) ∪
    {m | ∃ A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
        (∀ x, ⟪x, A x⟫_ℝ = 0) ∧ m = infinitesimalRotation A p}

theorem translationMotion_mem_trivialMotions (p : Framework V d)
    (t : EuclideanSpace ℝ (Fin d)) :
    (translationMotion t : Framework V d) ∈ trivialMotions p :=
  Submodule.subset_span (Or.inl ⟨t, rfl⟩)

theorem infinitesimalRotation_mem_trivialMotions (p : Framework V d)
    {A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)}
    (hA : ∀ x, ⟪x, A x⟫_ℝ = 0) :
    infinitesimalRotation A p ∈ trivialMotions p :=
  Submodule.subset_span (Or.inr ⟨A, hA, rfl⟩)

/-- **Trivial motions lie in the rigidity-map kernel** for any graph `G` and any placement `p`. -/
theorem trivialMotions_le_ker (G : SimpleGraph V) (p : Framework V d) :
    trivialMotions p ≤ LinearMap.ker (G.RigidityMap p) := by
  rw [trivialMotions, Submodule.span_le]
  rintro m (⟨t, rfl⟩ | ⟨A, hA, rfl⟩)
  · exact translationMotion_mem_ker G p t
  · exact infinitesimalRotation_mem_ker G p hA

/-! ### The d-general finrank lower bound at an affinely-spanning placement

This section proves `d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)` at an affinely-spanning
placement, via an explicit family of `d` translations (the coordinate translations) and
`d (d - 1) / 2` elementary skew-symmetric rotations (one per ordered pair `(i, j)` with `j < i`).
The planar case is its instance at `d = 2`, where the bound is `3`. -/

/-- The "elementary skew-adjoint" linear map indexed by a pair `i, j : Fin d`, sending
`x ↦ x_j • e_i - x_i • e_j` (where `e_k = EuclideanSpace.single k 1`). Skew-adjoint:
`⟪x, elemSkewMap i j x⟫_ℝ = 0` (`inner_elemSkewMap_self`). For `i = j` it is the zero map; for
`i ≠ j` it corresponds to the elementary skew-symmetric matrix `E_{i, j} - E_{j, i}`. The
collection of `elemSkewMap i j` for `j < i` spans the `d (d - 1) / 2`-dim space of skew-symmetric
linear maps and supplies the rotation generators of `trivialMotions`. -/
def elemSkewMap (i j : Fin d) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun x := x j • PiLp.single 2 i (1 : ℝ) - x i • PiLp.single 2 j (1 : ℝ)
  map_add' u v := by
    ext k
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.ofLp_single, Pi.single_apply]
    split_ifs <;> ring
  map_smul' c v := by
    ext k
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, PiLp.ofLp_single,
      Pi.single_apply, RingHom.id_apply]
    split_ifs <;> ring

@[simp] theorem elemSkewMap_apply (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) (k : Fin d) :
    (elemSkewMap i j x) k = (if k = i then x j else 0) - (if k = j then x i else 0) := by
  simp only [elemSkewMap, LinearMap.coe_mk, AddHom.coe_mk, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, PiLp.ofLp_single, Pi.single_apply]
  split_ifs <;> ring

/-- **`elemSkewMap i j` is skew-adjoint.** The inner product `⟪x, elemSkewMap i j x⟫_ℝ` vanishes
for every `x`, so `infinitesimalRotation (elemSkewMap i j) p` lies in the rigidity-map kernel
(`infinitesimalRotation_mem_ker`). -/
theorem inner_elemSkewMap_self (i j : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪x, elemSkewMap i j x⟫_ℝ = 0 := by
  rcases eq_or_ne i j with rfl | hij
  · suffices h : elemSkewMap i i x = 0 by simp [h]
    ext k
    simp [elemSkewMap_apply]
  · simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, elemSkewMap_apply,
      sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ i, Finset.sum_ite_eq' Finset.univ j]
    grind

/-! ### The d-general motion family and linear independence

The d-general trivial-motion family is indexed by `Fin d ⊕ Σ i : Fin d, Fin i.val`: the left half
contributes the `d` coordinate translations, and the right half contributes one elementary skew
rotation per ordered pair `(i, j)` with `j < i` (so `j : Fin i.val`). Linear independence holds
whenever the placement `p` affinely spans `EuclideanSpace ℝ (Fin d)`; the joint LI argument
combines:

1. *Translation/rotation split.* The combination at vertex `v` decomposes as `t + S(p v)` in
   `EuclideanSpace ℝ (Fin d)`, where `t = ∑ i, c.inl i • e_i` is the translation vector and
   `S = ∑ ⟨i, j⟩, c.inr ⟨i, j⟩ • elemSkewMap i j'` is the rotation linear map (`j' : Fin d` is the
   embedding of `j : Fin i.val`).
2. *Rotation kill via affine spanning.* Subtracting `t + S(p v) = 0` and `t + S(p w) = 0` gives
   `S(p v - p w) = 0`; affine spanning implies the vector span of `{p v - p w}` is `⊤`, so `S = 0`
   as a linear map (`LinearMap.eqOn_span`).
3. *Coefficient extraction.* From `S = 0`, evaluating `S` at the standard basis vectors picks out
   each rotation coefficient. With those gone, the surviving equation `t = 0` then yields the
   translation coefficients via the standard-basis coord-read. -/

/-- **Cross-term vanishing for the ordered-pair indexing.** Evaluating
`elemSkewMap s.1 ⟨s.2.val, _⟩` (the generator at ordered-pair index `s : Σ x : Fin d, Fin x.val`)
at the standard basis vector `e_{⟨j.val, _⟩}` and reading off coordinate `i` produces `1` exactly
when `s = ⟨i, j⟩` and `0` for every other index.

The strict inequalities `s.2.val < s.1.val` and `j.val < i.val` baked into the ordered-pair type
rule out the symmetric cross-term in `elemSkewMap_apply`: that term would require both
`i.val = s.2.val < s.1.val` and `s.1.val = j.val < i.val`, giving `i.val < s.1.val < i.val`. This
lemma is the substantive content of *"the other cross-terms vanish for the ordered-pair index
range"* used in `trivialMotionFamily_linearIndependent`. -/
theorem elemSkewMap_ofLp_inr_apply (i : Fin d) (j : Fin i.val)
    (s : Σ x : Fin d, Fin x.val) :
    (elemSkewMap s.1 ⟨s.2.val, s.2.isLt.trans s.1.isLt⟩
        (PiLp.single 2 (⟨j.val, j.isLt.trans i.isLt⟩ : Fin d) (1 : ℝ))).ofLp i
      = if s = ⟨i, j⟩ then 1 else 0 := by
  obtain ⟨a, b⟩ := s
  -- Case-split on `i = a`; `grind` then dispatches the nested `if`s plus the sigma-equality
  -- RHS using `b.isLt` / `j.isLt` to rule out the symmetric cross-term in `elemSkewMap_apply`.
  rcases eq_or_ne i a with rfl | hia <;> simp [elemSkewMap_apply] <;> grind

/-- The d-general trivial-motion family at a placement `p`. The left summand of the index type
contributes the `d` coordinate translations (one per `i : Fin d`); the right summand contributes
one elementary skew rotation per ordered pair `⟨i, j⟩` with `j : Fin i.val` (so `j.val < i.val`),
using `elemSkewMap i ⟨j.val, _⟩` for the skew generator. Each value lies in `trivialMotions p`
(`trivialMotionFamily_mem_trivialMotions`). -/
@[expose] def trivialMotionFamily (p : Framework V d) :
    (Fin d ⊕ Σ i : Fin d, Fin i.val) → Framework V d
  | .inl i => translationMotion (PiLp.single 2 i (1 : ℝ))
  | .inr ⟨i, j⟩ =>
      infinitesimalRotation (elemSkewMap i ⟨j.val, j.isLt.trans i.isLt⟩) p





theorem trivialMotionFamily_mem_trivialMotions (p : Framework V d)
    (s : Fin d ⊕ Σ i : Fin d, Fin i.val) :
    trivialMotionFamily p s ∈ trivialMotions p := by
  rcases s with i | ⟨i, j⟩
  · exact translationMotion_mem_trivialMotions p _
  · exact infinitesimalRotation_mem_trivialMotions p (inner_elemSkewMap_self _ _)

/-- **Joint linear independence** of the d-general trivial-motion family at an affinely-spanning
placement. The translation/rotation split combined with affine spanning kills the rotation part,
leaving the translation part identifiable coord-by-coord. -/
theorem trivialMotionFamily_linearIndependent {p : Framework V d}
    (hp : affineSpan ℝ (Set.range p) = ⊤) :
    LinearIndependent ℝ (trivialMotionFamily p) := by
  obtain ⟨_, v₀, rfl⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top _ _ _ hp
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- The "skew sum" linear map and "translation vector" assembled from coefficients.
  set S : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    ∑ s : Σ i : Fin d, Fin i.val,
      c (.inr s) • elemSkewMap s.1 ⟨s.2.val, s.2.isLt.trans s.1.isLt⟩ with hS_def
  set t : EuclideanSpace ℝ (Fin d) :=
    ∑ i : Fin d, c (.inl i) • PiLp.single 2 i (1 : ℝ) with ht_def
  -- Coordinate `m` of `t` is the translation coefficient `c (.inl m)`.
  have ht_coord : ∀ m : Fin d, t.ofLp m = c (.inl m) := fun m => by
    simp [ht_def, Pi.single_apply]
  -- Step 1: at every `v`, `t + S (p v) = 0`. Evaluate `hc` at `v` and split the index sum.
  have h_combine : ∀ v : V, t + S (p v) = 0 := fun v => by
    simpa [hS_def, ht_def, trivialMotionFamily, translationMotion, infinitesimalRotation,
      Fintype.sum_sum_type,
      LinearMap.sum_apply] using congrFun hc v
  -- Step 2: `S` vanishes on differences `p v - p w`.
  have h_S_diff : ∀ v w : V, S (p v - p w) = 0 := fun v w => by
    rw [map_sub, eq_neg_of_add_eq_zero_right (h_combine v),
      eq_neg_of_add_eq_zero_right (h_combine w), sub_self]
  -- Step 3: `S = 0` as a linear map (vanishes on the vector span of `Set.range p`).
  have : Nonempty V := ⟨v₀⟩
  have h_S_zero : S = 0 := by
    have hvspan : Submodule.span ℝ ((Set.range p) -ᵥ (Set.range p)) = ⊤ := by
      rw [← vectorSpan_def]
      exact (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _
        (Set.range_nonempty p)).mp hp
    refine LinearMap.ext_on hvspan ?_
    rintro _ ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
    simpa [vsub_eq_sub] using h_S_diff v w
  -- Step 4: `t = 0`.
  have h_t_zero : t = 0 := by simpa [h_S_zero] using h_combine v₀
  -- Step 5: extract coefficients.
  intro s
  rcases s with i | ⟨i, j⟩
  · -- Translation coefficient: from `t = 0`, read coordinate `i`.
    simpa [ht_coord i] using congrArg (·.ofLp i) h_t_zero
  · -- Rotation coefficient: from `S = 0`, apply at `e_{j'}` and read coord `i`.
    -- The sum collapses via `elemSkewMap_ofLp_inr_apply` (cross-term vanishing) + `sum_ite_eq'`.
    have h_extract : (S (PiLp.single 2 (⟨j.val, j.isLt.trans i.isLt⟩ : Fin d) (1 : ℝ))).ofLp i
        = c (.inr ⟨i, j⟩) := by
      rw [hS_def, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [elemSkewMap_ofLp_inr_apply i j, mul_ite, mul_one, mul_zero]
      simp
    rw [h_S_zero] at h_extract
    simpa using h_extract.symm

/-- Cardinality of the d-general trivial-motion index: `d` coordinate translations plus
`d * (d - 1) / 2 = ∑_{i < d} i` skew rotations gives `d * (d + 1) / 2`. -/
theorem fintype_card_trivialMotionFamilyIndex :
    Fintype.card (Fin d ⊕ Σ i : Fin d, Fin i.val) = d * (d + 1) / 2 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [show (∑ i : Fin d, i.val) = ∑ i ∈ Finset.range d, i from Fin.sum_univ_eq_sum_range id d]
  rw [show d + ∑ i ∈ Finset.range d, i = ∑ i ∈ Finset.range (d + 1), i by
    rw [Finset.sum_range_succ]; ring]
  rw [Finset.sum_range_id]
  rw [Nat.add_sub_cancel, Nat.mul_comm]

/-- **The d-general finrank lower bound for trivial motions at an affinely-spanning placement.**
At any placement `p : Framework V d` whose image affinely spans `EuclideanSpace ℝ (Fin d)`, the
trivial-motions submodule has dimension at least `d (d + 1) / 2` (the textbook dimension of
Euclidean rigid motions). The argument exhibits an explicit family of `d` coordinate translations
and `d (d - 1) / 2` elementary skew rotations and shows it is linearly independent. -/
theorem trivialMotions_finrank_ge_of_affinelySpanning [Finite V]
    {p : Framework V d} (hp : affineSpan ℝ (Set.range p) = ⊤) :
    d * (d + 1) / 2 ≤ Module.finrank ℝ (trivialMotions p) := by
  have : Fintype V := Fintype.ofFinite V
  -- Lift the trivial-motion family into the `trivialMotions p` submodule.
  let f : (Fin d ⊕ Σ i : Fin d, Fin i.val) → (trivialMotions p) :=
    fun s => ⟨trivialMotionFamily p s, trivialMotionFamily_mem_trivialMotions p s⟩
  have h_LI : LinearIndependent ℝ f := by
    have h_amb : LinearIndependent ℝ (trivialMotionFamily p) :=
      trivialMotionFamily_linearIndependent hp
    have h_eq : (fun s => (f s).val) = trivialMotionFamily p := by
      funext s; rfl
    rw [← h_eq] at h_amb
    exact h_amb.of_comp (trivialMotions p).subtype
  have h_card := h_LI.fintype_card_le_finrank
  rw [fintype_card_trivialMotionFamilyIndex] at h_card
  exact h_card

/-- **d-general finrank lower bound for the rigidity-map kernel at an affinely-spanning placement.**
For any graph `G`, any dimension `d`, and any placement `p` whose image affinely spans
`EuclideanSpace ℝ (Fin d)`, the kernel of `G.RigidityMap p` has dimension at least
`d (d + 1) / 2`, the dimension of the infinitesimal rigid motions (Jordán 2016, p. 36; the
generators are Whiteley's, 1996, §11.1).

Combines the d-general `trivialMotions_finrank_ge_of_affinelySpanning` with the unconditional
inclusion `trivialMotions_le_ker`. Plugs into rank-nullity to give the d-general rank upper
bound `rigidityMap_finrank_range_le_of_affinelySpanning` on `G.RigidityMap p`'s range. -/
theorem rigidityMap_ker_finrank_ge_of_affinelySpanning [Finite V]
    (G : SimpleGraph V) {p : Framework V d}
    (hp : affineSpan ℝ (Set.range p) = ⊤) :
    d * (d + 1) / 2 ≤ Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) :=
  (trivialMotions_finrank_ge_of_affinelySpanning hp).trans
    (Submodule.finrank_mono (trivialMotions_le_ker G p))

end SimpleGraph

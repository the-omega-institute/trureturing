/- GID: D5/S3/Combinatorics/Graph/Laman/Framework
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/Framework
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2, mathlib/module/Mathlib.Analysis.Normed.Module.FiniteDimension]
   utility: none
   digest: Frameworks, rigidity rows, openness, and real infinitesimal rigidity maps for finite simple graphs. -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/laman-henneberg/LICENSE.txt.
Authors: Bryan Gin-ge Chen
Modified file: selected source declarations reorganized for trureturing;
receiver imports and API adaptations; unconsumed declarations omitted.
Source: CombinatorialRigidity@021c2284bc387efee3c3b20a18eb5f769638b578.
-/
import D5.S3.Combinatorics.Graph.Laman.SparseSets
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Frameworks and infinitesimal rigidity

A `d`-dimensional **framework** on a vertex set `V` is a placement
`p : V → EuclideanSpace ℝ (Fin d)`. Given a graph `G : SimpleGraph V`, the
**rigidity map** at `p` sends an infinitesimal motion `p' : Framework V d`
to the family of edge-length derivatives `e ↦ ⟪p u - p v, p' u - p' v⟫`
indexed by the edges `e = s(u, v) ∈ G.edgeSet`. Geometrically, this is the
differential at `p` of the squared-edge-length map (modulo a factor of two);
we define it directly via the explicit entry formula to avoid `fderiv` and
the differentiability machinery — none of which the rank/kernel arguments
downstream need.

A framework is **infinitesimally rigid** when the kernel of the rigidity
map has dimension at most `d (d+1) / 2`, the dimension of the space of trivial
Euclidean motions (translations and infinitesimal rotations). It is **generically
rigid** when *some* placement is infinitesimally rigid. We follow Jordán (2016, §1.2);
the definition of infinitesimal rigidity agrees with his when `|V| ≥ d` or `|V| ≤ 1`, so
always in the plane, and is weaker otherwise (`IsInfinitesimallyRigid`).

These definitions are stated for general dimension `d`; Laman's theorem
(`PlanarLaman.lean`) takes `d = 2`.

## Main definitions

* `Framework V d` — placement type, `abbrev` for `V → EuclideanSpace ℝ (Fin d)`.
* `SimpleGraph.RigidityMap G p` — the rigidity map as an `ℝ`-linear map.
* `SimpleGraph.IsInfinitesimallyRigid G p` — kernel-dimension bound.
* `SimpleGraph.IsGenericallyRigid G d` — existence of a rigid placement.
* `SimpleGraph.IsGenericallyRigidInj G d` — existence of a rigid *injective*
  placement; the predicate the Henneberg induction of Laman's theorem maintains.

The corresponding Framework Blueprint presents this file.
-/

@[expose] public section

open scoped InnerProductSpace Topology

namespace SimpleGraph

variable {V : Type*} {d : ℕ}

/-- A `d`-dimensional **framework** on a vertex set `V` is a placement of `V`
into `EuclideanSpace ℝ (Fin d)`.

`abbrev` so that the Pi-`Module ℝ`, `AddCommGroup`, and finite-dimensional
instances on `V → EuclideanSpace ℝ (Fin d)` apply transparently. -/
abbrev Framework (V : Type*) (d : ℕ) : Type _ := V → EuclideanSpace ℝ (Fin d)

/-- The dimension of the framework space: `#V` copies of `EuclideanSpace ℝ (Fin d)`. -/
@[simp]
theorem Framework.finrank [Fintype V] :
    Module.finrank ℝ (Framework V d) = Fintype.card V * d := by
  simp [Module.finrank_pi_fintype]

/-- The `(u, v)`-row of the rigidity matrix as a linear functional on framework
motions: `x ↦ ⟪p u - p v, x u - x v⟫_ℝ`. Internal building block for
`RigidityMap`; consumers go through `rigidityMap_apply` instead. -/
-- Non-`private` because `RigidityMap`'s exposed body references `edgeRow` / `edgeRow_symm`
-- through `Sym2.lift`, which trips the module system's private-in-public check.
noncomputable def edgeRow (p : Framework V d) (u v : V) :
    Framework V d →ₗ[ℝ] ℝ :=
  ((innerSL ℝ (p u - p v)).toLinearMap).comp
    ((LinearMap.proj u : Framework V d →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) -
      LinearMap.proj v)

@[simp]
theorem edgeRow_apply (p : Framework V d) (u v : V) (x : Framework V d) :
    edgeRow p u v x = ⟪p u - p v, x u - x v⟫_ℝ := rfl

theorem edgeRow_symm (p : Framework V d) (u v : V) :
    edgeRow p u v = edgeRow p v u := by
  ext x
  rw [edgeRow_apply, edgeRow_apply, ← neg_sub (p u) (p v), ← neg_sub (x u) (x v),
      inner_neg_neg]

/-- The **rigidity map** of a framework `p`: an `ℝ`-linear map sending an
infinitesimal motion `p' : Framework V d` to the family
`e ↦ ⟪p u - p v, p' u - p' v⟫_ℝ` indexed by the edges `e = s(u, v) ∈ G.edgeSet`.

Built compositionally as `LinearMap.pi` over the per-edge `edgeRow`s, so
linearity in `p'` is inherited from the existing `LinearMap` API. -/
noncomputable def RigidityMap (G : SimpleGraph V) (p : Framework V d) :
    Framework V d →ₗ[ℝ] (G.edgeSet → ℝ) :=
  LinearMap.pi fun e : G.edgeSet =>
    Sym2.lift ⟨edgeRow p, edgeRow_symm p⟩ e.val

/-- The rigidity map evaluated at an explicit edge `s(u, v)` is the inner product
`⟪p u - p v, p' u - p' v⟫_ℝ`. -/
@[simp]
theorem rigidityMap_apply (G : SimpleGraph V) (p p' : Framework V d) (u v : V)
    (huv : s(u, v) ∈ G.edgeSet) :
    G.RigidityMap p p' ⟨s(u, v), huv⟩ = ⟪p u - p v, p' u - p' v⟫_ℝ := by
  simp [RigidityMap]

/-- Continuity of `RigidityMap` in its placement: for a fixed motion `x` and edge `e`, the entry
`G.RigidityMap p x e` is a continuous function of `p`. The entry expands to the inner product
`⟪p u - p v, x u - x v⟫`, jointly continuous in `(p, x)` and *a fortiori* continuous in `p` alone
with `x` fixed; the proof inducts on `e : Sym2 V` to expose `s(u, v)`.

Building block for `IsInfinitesimallyRigid.eventually`. Tagged `@[fun_prop]` so downstream
continuity goals involving `RigidityMap` close via the `fun_prop` tactic. -/
@[fun_prop]
theorem continuous_rigidityMap_apply (G : SimpleGraph V) (x : Framework V d)
    (e : G.edgeSet) : Continuous (fun p : Framework V d => G.RigidityMap p x e) := by
  obtain ⟨e, he⟩ := e
  induction e with
  | h u v => simp only [rigidityMap_apply G _ x u v he]; fun_prop

/-- The rigidity map's kernel shrinks under graph inclusion: adding edges can only
add constraints, never remove them. -/
theorem rigidityMap_ker_mono {G G' : SimpleGraph V} (h : G ≤ G') (p : Framework V d) :
    LinearMap.ker (G'.RigidityMap p) ≤ LinearMap.ker (G.RigidityMap p) := by
  intro p' hp'
  rw [LinearMap.mem_ker] at hp' ⊢
  funext ⟨e, he⟩
  exact congr_fun hp' ⟨e, edgeSet_mono h he⟩

/-- A framework `p` is **infinitesimally rigid** for `G` if the kernel of the
rigidity map has dimension at most `d (d+1) / 2`, the dimension of the space of trivial
Euclidean motions (translations and infinitesimal rotations).

When the points `p v` affinely span `ℝ^d`, the trivial infinitesimal motions of `p` lie in the
kernel and have that dimension, so the bound says that every infinitesimal motion is trivial,
Jordán's definition (2016, p. 36). In general it says that the rigidity map has rank at least
`d|V| − d(d+1)/2`, where Jordán's equivalent rank form (pp. 36–37) asks for his bound
`S(|V|, d)`. The two agree when `|V| ≥ d` or `|V| ≤ 1`, so always at `d = 2`; when
`2 ≤ |V| ≤ d − 1` this definition is weaker (two vertices with no edge, anywhere in `ℝ³`,
satisfy it). The kernel
bound is the form the rank–nullity arguments downstream use. -/
-- Finiteness ensures that finrank measures the actual kernel dimension.
@[nolint unusedArguments]
def IsInfinitesimallyRigid [Finite V] (G : SimpleGraph V) (p : Framework V d) : Prop :=
  Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ d * (d + 1) / 2

/-- A graph `G` is **generically rigid** in dimension `d` if some placement is
infinitesimally rigid.

Defining it through a single placement avoids generic placements (those whose coordinates are
algebraically independent over `ℚ`), which neither direction of Laman's theorem
needs. No declaration relates it to rigidity at generic placements; the existential predicate alone is used here. -/
def IsGenericallyRigid [Finite V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ p : Framework V d, G.IsInfinitesimallyRigid p

/-- Adding edges preserves infinitesimal rigidity at the same placement. -/
theorem IsInfinitesimallyRigid.mono [Finite V] {G G' : SimpleGraph V} (h : G ≤ G')
    {p : Framework V d} (hG : G.IsInfinitesimallyRigid p) : G'.IsInfinitesimallyRigid p :=
  (Submodule.finrank_mono (rigidityMap_ker_mono h p)).trans hG

/-- Adding edges preserves generic rigidity. -/
theorem IsGenericallyRigid.mono [Finite V] {G G' : SimpleGraph V} (h : G ≤ G')
    (hG : G.IsGenericallyRigid d) : G'.IsGenericallyRigid d :=
  hG.imp fun _ => IsInfinitesimallyRigid.mono h

/-- Iso transport for infinitesimal rigidity: a graph iso `φ : G ≃g H` carries
an infinitesimally rigid placement `p` of `G` to the placement `p ∘ φ.symm` of
`H`, which is also infinitesimally rigid.

The proof builds a linear equivalence between the two rigidity-map kernels by
precomposition with `φ` and uses `LinearEquiv.finrank_eq` to transport the
kernel-dimension bound. -/
theorem IsInfinitesimallyRigid.iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) {p : Framework V d}
    (h : G.IsInfinitesimallyRigid p) : H.IsInfinitesimallyRigid (p ∘ φ.symm) := by
  -- Per-edge correspondence: `q' ∈ ker H ↔ q' ∘ φ ∈ ker G`.
  have hH_to_G : ∀ q' : Framework W d,
      (H.RigidityMap (p ∘ φ.symm)) q' = 0 → (G.RigidityMap p) (q' ∘ φ.toEquiv) = 0 := by
    intro q' hq'
    ext ⟨e, he⟩
    induction e with
    | h a b =>
      have hH : s(φ a, φ b) ∈ H.edgeSet := by
        rw [mem_edgeSet] at he ⊢; exact φ.map_adj_iff.mpr he
      have key := congr_fun hq' ⟨s(φ a, φ b), hH⟩
      simpa using key
  have hG_to_H : ∀ p' : Framework V d,
      (G.RigidityMap p) p' = 0 →
        (H.RigidityMap (p ∘ φ.symm)) (p' ∘ φ.symm.toEquiv) = 0 := by
    intro p' hp'
    ext ⟨e, he⟩
    induction e with
    | h u v =>
      have hG : s(φ.symm u, φ.symm v) ∈ G.edgeSet := by
        rw [mem_edgeSet] at he ⊢; exact φ.symm.map_adj_iff.mpr he
      have key := congr_fun hp' ⟨s(φ.symm u, φ.symm v), hG⟩
      simpa using key
  -- Linear equiv between the two kernels.
  let kerEquiv : LinearMap.ker (H.RigidityMap (p ∘ φ.symm)) ≃ₗ[ℝ]
      LinearMap.ker (G.RigidityMap p) :=
    { toFun := fun q' => ⟨q'.1 ∘ φ.toEquiv,
        LinearMap.mem_ker.mpr (hH_to_G q'.1 (LinearMap.mem_ker.mp q'.2))⟩
      invFun := fun p' => ⟨p'.1 ∘ φ.symm.toEquiv,
        LinearMap.mem_ker.mpr (hG_to_H p'.1 (LinearMap.mem_ker.mp p'.2))⟩
      left_inv := fun _ => Subtype.ext <| funext fun _ => by simp
      right_inv := fun _ => Subtype.ext <| funext fun _ => by simp
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact kerEquiv.finrank_eq.le.trans h

/-- **Openness of infinitesimal rigidity in the placement.** If `p₀` is infinitesimally rigid for
`G`, then every placement `p` in some neighborhood of `p₀` is also infinitesimally rigid.

The proof picks a basis of `LinearMap.range (G.RigidityMap p₀)` of size `r = rank (G.RigidityMap
p₀)`, lifts each basis vector to a preimage in `Framework V d`, and uses
`LinearIndependent.eventually` plus continuity of `p ↦ G.RigidityMap p (preimg i)` to conclude that
the lifted images stay linearly independent in a neighborhood of `p₀`. Combined with rank-nullity
on both `p₀` and the nearby `p`, this gives the kernel-dim bound. -/
theorem IsInfinitesimallyRigid.eventually [Finite V] {G : SimpleGraph V}
    {p₀ : Framework V d} (h₀ : G.IsInfinitesimallyRigid p₀) :
    ∀ᶠ p in 𝓝 p₀, G.IsInfinitesimallyRigid p := by
  have : Fintype V := Fintype.ofFinite V
  have : Fintype G.edgeSet := Set.Finite.fintype G.edgeSet.toFinite
  set r := Module.finrank ℝ (LinearMap.range (G.RigidityMap p₀)) with hr_def
  -- Lift a basis of `LinearMap.range (G.RigidityMap p₀)` to preimages.
  let e := Module.finBasis ℝ (LinearMap.range (G.RigidityMap p₀))
  let preimg : Fin r → Framework V d := fun i =>
    Classical.choose (LinearMap.mem_range.mp (e i).property)
  have h_preimg_eq : ∀ i, G.RigidityMap p₀ (preimg i) = (e i).val := fun i =>
    Classical.choose_spec (LinearMap.mem_range.mp (e i).property)
  -- LI of the basis ⇒ LI of `(e i).val` in the ambient space (subtype injective)
  --                  ⇒ LI of `G.RigidityMap p₀ ∘ preimg`.
  have h_subtype_li : LinearIndependent ℝ (fun i => (e i).val) :=
    e.linearIndependent.map' (LinearMap.range (G.RigidityMap p₀)).subtype
      (Submodule.ker_subtype _)
  have h_preimg_li : LinearIndependent ℝ (fun i => G.RigidityMap p₀ (preimg i)) := by
    convert h_subtype_li using 1
    funext i; exact h_preimg_eq i
  -- Continuity of `p ↦ (G.RigidityMap p (preimg i))_i` into `Fin r → (G.edgeSet → ℝ)`.
  have h_cont : Continuous
      (fun p : Framework V d => fun i => G.RigidityMap p (preimg i)) := by fun_prop
  -- Filter pullback of `LinearIndependent.eventually`.
  have h_event_li : ∀ᶠ p in 𝓝 p₀,
      LinearIndependent ℝ (fun i => G.RigidityMap p (preimg i)) :=
    h_cont.continuousAt.tendsto.eventually h_preimg_li.eventually
  filter_upwards [h_event_li] with p hp_li
  -- Lift LI back to the range submodule of `RigidityMap p`, then apply
  -- `LinearIndependent.fintypeCard_le_finrank` to get `r ≤ rank (RigidityMap p)`.
  let lift : Fin r → LinearMap.range (G.RigidityMap p) :=
    fun i => ⟨G.RigidityMap p (preimg i), LinearMap.mem_range_self _ _⟩
  have h_lift_li : LinearIndependent ℝ lift := by
    have h_eq : (fun i => G.RigidityMap p (preimg i)) =
        (LinearMap.range (G.RigidityMap p)).subtype ∘ lift := rfl
    rw [h_eq] at hp_li
    exact hp_li.of_comp _
  have h_card_le := h_lift_li.fintype_card_le_finrank
  rw [Fintype.card_fin] at h_card_le
  -- Combine with rank-nullity on both `p₀` and `p`.
  unfold IsInfinitesimallyRigid
  have h_rn₀ := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p₀)
  have h_rn := LinearMap.finrank_range_add_finrank_ker (G.RigidityMap p)
  have h₀_unfold : Module.finrank ℝ (LinearMap.ker (G.RigidityMap p₀)) ≤ d * (d + 1) / 2 := h₀
  omega

/-- A graph `G` is **generically rigid with an injective placement** in dimension `d` if some
infinitesimally rigid placement is also injective. It implies `IsGenericallyRigid`
(`IsGenericallyRigidInj.toIsGenericallyRigid`), strictly at `d = 0`, where `K₂` has no injective
placement; the blueprint's remark after `def:isGenericallyRigidInj` compares the two. The
Henneberg induction of Laman's theorem (`PlanarForward.lean`) maintains the injective placement at
each step (the per-move arguments of `HennebergRigidity.lean` need `p a ≠ p b`, which
`IsGenericallyRigid` does not supply) and weakens to `IsGenericallyRigid` at the end. -/
def IsGenericallyRigidInj [Finite V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ p : Framework V d, G.IsInfinitesimallyRigid p ∧ Function.Injective p

/-- An injectively-generic-rigid graph is generically rigid. -/
theorem IsGenericallyRigidInj.toIsGenericallyRigid [Finite V] {G : SimpleGraph V}
    (h : G.IsGenericallyRigidInj d) : G.IsGenericallyRigid d :=
  h.imp fun _ hp => hp.1

/-- Iso transport for injective generic rigidity: a graph iso preserves injective generic
rigidity. Injectivity of `p ∘ φ.symm` follows from injectivity of `p` since `φ.symm` is a
bijection. -/
theorem IsGenericallyRigidInj.iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    (h : G.IsGenericallyRigidInj d) : H.IsGenericallyRigidInj d := by
  obtain ⟨p, hp_rig, hp_inj⟩ := h
  exact ⟨p ∘ φ.symm, hp_rig.iso φ, hp_inj.comp φ.symm.toEquiv.injective⟩

/-- The K₂ worked example, *injective* form: the complete graph on two vertices is generically
rigid with an injective placement in every positive dimension `d + 1`. Witnessed by `p 0 = 0`,
`p 1 = e₀` (first standard basis vector). -/
theorem top_fin_two_isGenericallyRigidInj (d : ℕ) :
    (⊤ : SimpleGraph (Fin 2)).IsGenericallyRigidInj (d + 1) := by
  set p : Framework (Fin 2) (d + 1) := ![0, EuclideanSpace.single 0 1] with hp_def
  refine ⟨p, ?_, ?_⟩
  · -- Infinitesimal rigidity.
    change Module.finrank ℝ (LinearMap.ker
      ((⊤ : SimpleGraph (Fin 2)).RigidityMap p)) ≤ (d + 1) * (d + 2) / 2
    have h_edge : s((0 : Fin 2), 1) ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet := by simp
    have h_total : Module.finrank ℝ (Framework (Fin 2) (d + 1)) = 2 * (d + 1) := by
      rw [Framework.finrank]; simp
    have h_rn :=
      LinearMap.finrank_range_add_finrank_ker ((⊤ : SimpleGraph (Fin 2)).RigidityMap p)
    have h_range_pos :
        1 ≤ Module.finrank ℝ (LinearMap.range
          ((⊤ : SimpleGraph (Fin 2)).RigidityMap p)) := by
      rw [Submodule.one_le_finrank_iff, Ne, LinearMap.range_eq_bot]
      intro h_eq
      have h_val :
          (⊤ : SimpleGraph (Fin 2)).RigidityMap p ![EuclideanSpace.single 0 1, 0]
            ⟨s(0, 1), h_edge⟩ = -1 := by
        simp [rigidityMap_apply, hp_def, inner_neg_left]
      have h_zero :
          (⊤ : SimpleGraph (Fin 2)).RigidityMap p ![EuclideanSpace.single 0 1, 0]
            ⟨s(0, 1), h_edge⟩ = 0 := by rw [h_eq]; rfl
      linarith
    -- Bound: `2*(d+1) - 1 = 2d+1 ≤ (d+1)(d+2)/2` for all `d ≥ 0`.
    have h_quadratic : 4 * d + 2 ≤ (d + 1) * (d + 2) := by nlinarith [Nat.le_mul_self d]
    omega
  · -- Injectivity: `p 0 = 0` has norm 0; `p 1 = e₀` has norm 1.
    intro i j hij
    have h_norm : ‖p i‖ = ‖p j‖ := congrArg _ hij
    fin_cases i <;> fin_cases j <;> revert h_norm <;> simp [hp_def]

end SimpleGraph

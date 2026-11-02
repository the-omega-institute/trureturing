/- GID: D5/S3/Combinatorics/Graph/Laman/Framework
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Laman/Framework
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2, mathlib/module/Mathlib.Analysis.Normed.Module.FiniteDimension]
   utility: none
   digest: Frameworks, rigidity rows, and real infinitesimal rigidity maps for finite simple graphs. -/
/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in docs/reports/licenses/laman-henneberg/LICENSE.txt.
Authors: Bryan Gin-ge Chen
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
(`LamanTheorem.lean`) takes `d = 2`.

## Main definitions

* `Framework V d` — placement type, `abbrev` for `V → EuclideanSpace ℝ (Fin d)`.
* `SimpleGraph.RigidityMap G p` — the rigidity map as an `ℝ`-linear map.
* `SimpleGraph.IsInfinitesimallyRigid G p` — kernel-dimension bound.
* `SimpleGraph.IsGenericallyRigid G d` — existence of a rigid placement.
* `SimpleGraph.IsGenericallyRigidInj G d` — existence of a rigid *injective*
  placement; the predicate the Henneberg induction of Laman's theorem maintains.

The blueprint's `sec:frameworks` presents this file.
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

/-- A framework `p` is **infinitesimally rigid** for `G` if the kernel of the
rigidity map has dimension at most `d (d+1) / 2`, the dimension of the space of trivial
Euclidean motions (translations and infinitesimal rotations).

When the points `p v` affinely span `ℝ^d`, the trivial infinitesimal motions of `p` lie in the
kernel and have that dimension, so the bound says that every infinitesimal motion is trivial,
Jordán's definition (2016, p. 36). In general it says that the rigidity map has rank at least
`d|V| − d(d+1)/2`, where Jordán's equivalent rank form (pp. 36–37) asks for his bound
`S(|V|, d)`. The two agree when `|V| ≥ d` or `|V| ≤ 1`, so always at `d = 2`; when
`2 ≤ |V| ≤ d − 1` this definition is weaker (two vertices with no edge, anywhere in `ℝ³`,
satisfy it). The blueprint's `fmlnote:infinitesimal-rigidity` gives the comparison. The kernel
bound is the form the rank–nullity arguments downstream use. -/
-- The `[Finite V]` instance is semantically required (otherwise `Module.finrank`
-- of the kernel is vacuously `0` and the definition is meaningless), but is not
-- consumed by elaboration of the body. The instance acts as a contract guard so
-- callers cannot accidentally apply this with infinite `V`. The
-- `unusedFintypeInType` syntax linter does not yet extend to `def`s
-- (planned upstream improvement, per Thomas Murrills's Dec-2025 Zulip message),
-- so the env-linter's `unusedArguments` rule is what fires today; once the
-- syntax linter extends, this site would migrate to
-- `set_option linter.unusedFintypeInType false` instead.
@[nolint unusedArguments]
def IsInfinitesimallyRigid [Finite V] (G : SimpleGraph V) (p : Framework V d) : Prop :=
  Module.finrank ℝ (LinearMap.ker (G.RigidityMap p)) ≤ d * (d + 1) / 2

/-- A graph `G` is **generically rigid with an injective placement** in dimension `d` if some
infinitesimally rigid placement is also injective. It implies `IsGenericallyRigid`
(`IsGenericallyRigidInj.toIsGenericallyRigid`), strictly at `d = 0`, where `K₂` has no injective
placement; the blueprint's remark after `def:isGenericallyRigidInj` compares the two. The
Henneberg induction of Laman's theorem (`LamanTheorem.lean`) maintains the injective placement at
each step (the per-move arguments of `HennebergRigidity.lean` need `p a ≠ p b`, which
`IsGenericallyRigid` does not supply) and weakens to `IsGenericallyRigid` at the end. -/
def IsGenericallyRigidInj [Finite V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ p : Framework V d, G.IsInfinitesimallyRigid p ∧ Function.Injective p

end SimpleGraph

/- GID: D5/S3/Combinatorics/Graph/Incidence/UnsignedStarFixedCokernel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/UnsignedStarFixedCokernel
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral fixed representatives in the original unsigned star cokernel. -/

import D5.S3.Combinatorics.Graph.Incidence.UnsignedStarTorsion
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Isomorphisms

/-!
The consumed supplier corollary Edges.starMap_injective reuses its owning
module's private nonbipartite_potential theorem and preserves its proof.

Mathematical source: approved native proof P1/P6, SHA256
ed356c4b82a313d22d45def66d4fa89932c0fa9bb212867b5a25bb3f503cca81.
The private finite-coordinate correction adapts the separate UNCOMPILED source
PermutationCocycleFiniteRange.lean, SHA256
a9994bfa430250c44505ba80c3e35d286edb0823f2a707e84209712ba55f1a5f.
That source supplies mathematics and proposed syntax, not kernel/review evidence.

New load-bearing inference: unique integral star lifts form a cocycle on the
original arbitrary group. The differences factor through permutations of
ORIGINAL X, a finite type; injectivity of F gives a finite vector range of
potentials, and hence finite coordinate ranges. Attained integer maxima give
a correction without a finite acting-group assumption. No joint action image
or finite-group action/coercion layer is needed.

Reused: the supplier's private nonbipartite potential proof through its consumed
integer injectivity corollary, quotient representations, invariant submodules,
finite-set APIs, attained maxima and the first isomorphism theorem. The exact
invariant-image kernel and original quotient forward map are preserved.
No external novelty, canonical splitting, support control, or bipartite claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Incidence.UnsignedStarFixedCokernel

open D5.S3.Combinatorics.Graph.Incidence.UnsignedStarTorsion

variable {V X : Type*}

/-- The literal inverse-coordinate action on all integer functions. -/
def coordinateRep {Γ I : Type*} [Group Γ] (σ : Γ →* Equiv.Perm I) :
    Representation ℤ Γ (I → ℤ) where
  toFun γ :=
    { toFun := fun a i => a ((σ γ)⁻¹ i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext a i; simp
  map_mul' γ δ := by ext a i; simp [Equiv.Perm.mul_apply]

/-- Actions on the ORIGINAL vertex and edge-ID sets; orientations may swap
independently at each group element and original ID. -/
structure IndexedAction (g : Edges V X) (Γ : Type*) [Group Γ] where
  vertexPerm : Γ →* Equiv.Perm V
  edgePerm : Γ →* Equiv.Perm X
  endpoints : ∀ γ i,
    (g.left (edgePerm γ i) = vertexPerm γ (g.left i) ∧
      g.right (edgePerm γ i) = vertexPerm γ (g.right i)) ∨
    (g.left (edgePerm γ i) = vertexPerm γ (g.right i) ∧
      g.right (edgePerm γ i) = vertexPerm γ (g.left i))

/-- The actual integer quotient, without saturation or a chosen splitting. -/
abbrev Cokernel (g : Edges V X) := (X → ℤ) ⧸ g.starMap.range

/-- A consumed permutation-lattice correction for an arbitrary group.
Only the actual coordinate ranges of the cocycle need to be finite; the
consumer derives this condition from the original edge-ID action. -/
private theorem finite_coordinate_correction {Γ I : Type*} [Group Γ]
    (σ : Γ →* Equiv.Perm I) (c : Γ → I → ℤ)
    (hc : ∀ q r, c (q * r) = c q + coordinateRep σ q (c r))
    (hfinite : ∀ v, (Set.range (fun q => c q v)).Finite) :
    ∃ d : I → ℤ, ∀ q, c q = d - coordinateRep σ q d := by
  let d : I → ℤ := fun v => sSup (Set.range (fun q => c q v))
  have hd (v : I) : IsGreatest (Set.range (fun q => c q v)) (d v) :=
    (Set.range_nonempty _).isGreatest_csSup (hfinite v)
  have hcoord (q r : Γ) (v : I) :
      c (q * r) v = c q v + c r ((σ q)⁻¹ v) :=
    congrFun (hc q r) v
  refine ⟨d, fun q => funext fun v => ?_⟩
  change c q v = d v - d ((σ q)⁻¹ v)
  apply (eq_sub_iff_add_eq).2
  apply le_antisymm
  · rcases (hd ((σ q)⁻¹ v)).1 with ⟨r, hr⟩
    calc
      c q v + d ((σ q)⁻¹ v) = c q v + c r ((σ q)⁻¹ v) :=
        congrArg (fun t : ℤ => c q v + t) hr.symm
      _ = c (q * r) v := (hcoord q r v).symm
      _ ≤ d v := (hd v).2 ⟨q * r, rfl⟩
  · rcases (hd v).1 with ⟨r, hr⟩
    calc
      d v = c r v := hr.symm
      _ = c (q * (q⁻¹ * r)) v := by rw [mul_inv_cancel_left]
      _ = c q v + c (q⁻¹ * r) ((σ q)⁻¹ v) := hcoord q (q⁻¹ * r) v
      _ ≤ c q v + d ((σ q)⁻¹ v) :=
        add_le_add (le_refl (c q v)) ((hd ((σ q)⁻¹ v)).2 ⟨q⁻¹ * r, rfl⟩)

namespace IndexedAction

variable {Γ : Type*} [Group Γ] {g : Edges V X} (ρ : IndexedAction g Γ)

theorem starMap_equivariant (γ : Γ) (a : V → ℤ) :
    g.starMap (coordinateRep ρ.vertexPerm γ a) =
      coordinateRep ρ.edgePerm γ (g.starMap a) := by
  funext i
  have he :
      a (ρ.vertexPerm γ⁻¹ (g.left i)) + a (ρ.vertexPerm γ⁻¹ (g.right i)) =
        a (g.left (ρ.edgePerm γ⁻¹ i)) + a (g.right (ρ.edgePerm γ⁻¹ i)) := by
    rcases ρ.endpoints γ⁻¹ i with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2, add_comm]
  simpa [coordinateRep, Edges.starMap] using he

/-- The induced action on the actual original integer cokernel. -/
def cokernelRep : Representation ℤ Γ (Cokernel g) :=
  (coordinateRep ρ.edgePerm).quotient g.starMap.range (by
    intro γ z hz
    obtain ⟨a, rfl⟩ := hz
    exact ⟨coordinateRep ρ.vertexPerm γ a, ρ.starMap_equivariant γ a⟩)

/-- Every fixed class in the ACTUAL integer cokernel has an integral fixed
representative. Γ is arbitrary; V and ORIGINAL X alone are finite. -/
theorem exists_fixed_representative [Fintype V] [Fintype X]
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite)
    (x : Cokernel g) (hx : x ∈ ρ.cokernelRep.invariants) :
    ∃ y : X → ℤ, y ∈ (coordinateRep ρ.edgePerm).invariants ∧
      g.starMap.range.mkQ y = x := by
  classical
  obtain ⟨z, rfl⟩ := g.starMap.range.mkQ_surjective x
  have hF : Function.Injective g.starMap := g.starMap_injective hc hn
  have hlift (q : Γ) : ∃ a : V → ℤ,
      g.starMap a = coordinateRep ρ.edgePerm q z - z := by
    have he : g.starMap.range.mkQ (coordinateRep ρ.edgePerm q z) =
        g.starMap.range.mkQ z := hx q
    exact (Submodule.Quotient.eq g.starMap.range).mp he
  choose c hc using hlift
  have hmul (q r : Γ) : c (q * r) = c q + coordinateRep ρ.vertexPerm q (c r) := by
    apply hF
    rw [map_add, ρ.starMap_equivariant]
    simp only [hc, map_sub]
    rw [map_mul]
    change coordinateRep ρ.edgePerm q (coordinateRep ρ.edgePerm r z) - z =
      (coordinateRep ρ.edgePerm q z - z) +
        (coordinateRep ρ.edgePerm q (coordinateRep ρ.edgePerm r z) -
          coordinateRep ρ.edgePerm q z)
    abel
  -- Factor the actual differences through permutations of ORIGINAL X.
  have hdiff :
      (Set.range (fun q : Γ => coordinateRep ρ.edgePerm q z - z)).Finite := by
    refine ((Set.finite_univ : (Set.univ : Set (Equiv.Perm X)).Finite).image
      (fun p : Equiv.Perm X => fun i => z (p⁻¹ i) - z i)).subset ?_
    rintro _ ⟨q, rfl⟩
    exact ⟨ρ.edgePerm q, Set.mem_univ _, rfl⟩
  have hcrange : (Set.range c).Finite := by
    refine (hdiff.preimage hF.injOn).subset ?_
    rintro _ ⟨q, rfl⟩
    exact ⟨q, (hc q).symm⟩
  have hfinite (v : V) : (Set.range (fun q => c q v)).Finite := by
    refine (hcrange.image (fun a : V → ℤ => a v)).subset ?_
    rintro _ ⟨q, rfl⟩
    exact ⟨c q, ⟨q, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := finite_coordinate_correction ρ.vertexPerm c hmul hfinite
  refine ⟨z + g.starMap d, ?_, ?_⟩
  · intro q
    apply sub_eq_zero.mp
    calc
      coordinateRep ρ.edgePerm q (z + g.starMap d) - (z + g.starMap d) =
          (coordinateRep ρ.edgePerm q z - z) +
            (coordinateRep ρ.edgePerm q (g.starMap d) - g.starMap d) := by
              rw [map_add]; abel
      _ = g.starMap (c q + coordinateRep ρ.vertexPerm q d - d) := by
        rw [map_sub, map_add, ρ.starMap_equivariant, hc]
        abel
      _ = 0 := by rw [hd q]; simp
  · apply (Submodule.Quotient.eq g.starMap.range).mpr
    exact ⟨d, by abel⟩

/-- Restriction of the original integral map to the two fixed submodules. -/
def fixedStarMap : (coordinateRep ρ.vertexPerm).invariants →ₗ[ℤ]
    (coordinateRep ρ.edgePerm).invariants where
  toFun a := ⟨g.starMap a, fun γ => by
    rw [← ρ.starMap_equivariant, a.property γ]⟩
  map_add' a b := Subtype.ext (g.starMap.map_add a b)
  map_smul' n a := Subtype.ext (g.starMap.map_smul n a)

/-- The original quotient map restricted to fixed integer edge vectors. -/
def fixedProjection : (coordinateRep ρ.edgePerm).invariants →ₗ[ℤ]
    ρ.cokernelRep.invariants where
  toFun y := ⟨g.starMap.range.mkQ y, fun γ => by
    change g.starMap.range.mkQ (coordinateRep ρ.edgePerm γ y.val) =
      g.starMap.range.mkQ y.val
    rw [y.property γ]⟩
  map_add' y z := Subtype.ext (g.starMap.range.mkQ.map_add y z)
  map_smul' n y := Subtype.ext (g.starMap.range.mkQ.map_smul n y)

/-- Identifies the exact invariant-image kernel; it is consumed by the
canonical comparison below, rather than retained as an unused wrapper. -/
private theorem fixedProjection_ker
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite) :
    ρ.fixedProjection.ker = ρ.fixedStarMap.range := by
  ext y
  constructor
  · intro hy
    have hπ : g.starMap.range.mkQ y.val = 0 := congrArg Subtype.val hy
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero g.starMap.range).mp hπ
    have haf : a ∈ (coordinateRep ρ.vertexPerm).invariants := by
      intro γ
      apply g.starMap_injective hc hn
      calc
        g.starMap (coordinateRep ρ.vertexPerm γ a) =
            coordinateRep ρ.edgePerm γ (g.starMap a) := ρ.starMap_equivariant γ a
        _ = coordinateRep ρ.edgePerm γ y.val :=
          congrArg (coordinateRep ρ.edgePerm γ) ha
        _ = y.val := y.property γ
        _ = g.starMap a := ha.symm
    exact ⟨⟨a, haf⟩, Subtype.ext ha⟩
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    apply (Submodule.Quotient.mk_eq_zero g.starMap.range).mpr
    exact ⟨a.val, rfl⟩

/-- The canonical natural integral comparison
`(ℤ^X)^Γ / F((ℤ^V)^Γ) ≃ₗ[ℤ] (ℤ^X / F(ℤ^V))^Γ`.
Its forward map is induced by the ORIGINAL quotient projection: the
`quotEquivOfEq` and `quotKerEquivOfSurjective` constructors both send the
class of a fixed y to `fixedProjection ρ y`. No splitting is chosen. -/
noncomputable def fixedCokernelEquiv [Fintype V] [Fintype X]
    (hc : (g.graphAfterDeleting ∅).Connected)
    (hn : ¬ (g.graphAfterDeleting ∅).IsBipartite) :
    ((coordinateRep ρ.edgePerm).invariants ⧸ ρ.fixedStarMap.range) ≃ₗ[ℤ]
      ρ.cokernelRep.invariants :=
  (Submodule.quotEquivOfEq _ _ (ρ.fixedProjection_ker hc hn).symm).trans
    (ρ.fixedProjection.quotKerEquivOfSurjective (by
      intro x
      obtain ⟨y, hy, hπ⟩ := ρ.exists_fixed_representative hc hn x.val x.property
      exact ⟨⟨y, hy⟩, Subtype.ext hπ⟩))

end IndexedAction

end D5.S3.Combinatorics.Graph.Incidence.UnsignedStarFixedCokernel

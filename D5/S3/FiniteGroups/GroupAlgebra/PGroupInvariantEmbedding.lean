/- GID: D5/S3/FiniteGroups/GroupAlgebra/PGroupInvariantEmbedding
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/PGroupInvariantEmbedding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Basis.VectorSpace, mathlib/module/Mathlib.LinearAlgebra.Projection, mathlib/module/Mathlib.LinearAlgebra.Pi, mathlib/module/Mathlib.RepresentationTheory.Subrepresentation]
   utility: none
   digest: The orbit of a retraction onto invariants embeds any modular p-group representation. -/

import D5.S3.FiniteGroups.GroupAlgebra.PGroupInvariants
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Subrepresentation

/-!
Choose an ordinary linear retraction r onto the invariants and set
F(v)(h) = r (rho(h)(v)). The representation multiplication convention gives
F(rho(g)(v))(h) = F(v)(h * g), so the kernel is a subrepresentation. A nonzero
kernel vector would yield, by the restricted-action fixed-vector theorem, a
nonzero kernel vector fixed in V. Evaluation at the group identity and the
retraction identity then force that vector to vanish.

This is a structural construction in arbitrary dimension, including V = 0,
with no enumeration, checker, numerical reduction or certified finite
instance; hence utility none. The mechanism and the dimension and regular-
representation consequences explained in Scribe are classical mathematics.
The existing Library note webb2016pgroups supports the augmentation input to
the fixed-vector theorem, not an exact citation of this full embedding
telescope. No novelty or independent-consensus claim is made.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.PGroupInvariantEmbedding

universe uK uP uV

/-- Every representation of a finite p-group over any field of characteristic p
embeds linearly into the functions from the group to its invariant subspace.
The embedding intertwines the given action with right translation of the
argument. The field, group and vector space have independent universes;
the vector space may be zero or infinite-dimensional. -/
theorem exists_injective_linearMap_invariants_rightTranslate
    {k : Type uK} {P : Type uP} {V : Type uV}
    [Field k] [Group P] [Finite P] [AddCommGroup V] [Module k V]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hP : IsPGroup p P) (ρ : Representation k P V) :
    ∃ F : V →ₗ[k] (P → ρ.invariants),
      Function.Injective F ∧ ∀ (g h : P) (v : V), F (ρ g v) h = F v (h * g) := by
  classical
  obtain ⟨C, hC⟩ := ρ.invariants.exists_isCompl
  let r : V →ₗ[k] ρ.invariants := ρ.invariants.projectionOnto C hC
  have hr (v : ρ.invariants) : r (v : V) = v :=
    Submodule.projectionOnto_apply_left hC v
  let F : V →ₗ[k] (P → ρ.invariants) :=
    LinearMap.pi fun h : P => r.comp (ρ h)
  have hF (g h : P) (v : V) : F (ρ g v) h = F v (h * g) := by
    change r (ρ h (ρ g v)) = r (ρ (h * g) v)
    rw [map_mul, Module.End.mul_apply]
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker F
      apply_mem_toSubmodule := by
        intro g v hv
        change F v = 0 at hv
        change F (ρ g v) = 0
        funext h
        rw [hF g h v]
        exact congrFun hv (h * g) }
  have hker : LinearMap.ker F = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    by_contra hxn
    let xK : K.toSubmodule := ⟨x, hx⟩
    have hxK : xK ≠ 0 := by
      intro heq
      exact hxn (congrArg (fun z : K.toSubmodule => (z : V)) heq)
    obtain ⟨y, hy, hyfix⟩ :=
      PGroupInvariants.exists_nonzero_mem_invariants_of_isPGroup
        (R := k) (P := P) (V := K.toSubmodule) p hP K.toRepresentation xK hxK
    have hyfixV : (y : V) ∈ ρ.invariants := by
      apply (Representation.mem_invariants ρ (y : V)).mpr
      intro g
      exact (Subrepresentation.toRepresentation_apply_coe
        (ρ' := K) (g := g) (v := y) (w := y)).mp
          ((Representation.mem_invariants K.toRepresentation y).mp hyfix g)
    let yI : ρ.invariants := ⟨(y : V), hyfixV⟩
    have hyker : F (y : V) = 0 := LinearMap.mem_ker.mp y.property
    have hry0 : r (y : V) = 0 := by
      have hyone := congrFun hyker (1 : P)
      change r (ρ 1 (y : V)) = 0 at hyone
      simpa only [map_one, Module.End.one_apply] using hyone
    have hyI0 : yI = 0 := (hr yI).symm.trans hry0
    apply hy
    apply Subtype.ext
    exact congrArg (fun z : ρ.invariants => (z : V)) hyI0
  exact ⟨F, LinearMap.ker_eq_bot.mp hker, hF⟩

end D5.S3.FiniteGroups.GroupAlgebra.PGroupInvariantEmbedding

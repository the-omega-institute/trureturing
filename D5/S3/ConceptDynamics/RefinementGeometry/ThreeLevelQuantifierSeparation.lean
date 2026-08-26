/- GID: D5/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementGeometry/ThreeLevelQuantifierSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite examples separate three levels; empty and singleton cases are audited. -/

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Searches for `Compatible`, `InverseLimit`, and compatible families found
     `MultilayerIdentityInsufficiency.CompatibleFamily` and
     `CompletionIsomorphismCriterion.CompatibleStageFamily`; both quantify only over
     ordered pairs `i <= j`, and the latter also requires identity and composition laws.
   * `RefinementGeometry.InverseLimitCompletion.InverseThread` handles only adjacent
     natural-number stages. `ProfinitePrimeDecomposition.ProfiniteIntegers` is the
     specialized compatible-residue subtype. None has the source's all-pairs signature.
   * Pinned Mathlib supplies the finite `Fin 2` and `Bool` carriers used below; the
     implication proofs need no library theorem beyond dependent functions and equality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace D5.S3.ConceptDynamics.RefinementGeometry.ThreeLevelQuantifierSeparation

/- The source does not define `Compatible` in this principle. This module fills that
gap by taking compatibility to mean consistency under every specified transition map:
the value at `j`, transported by `t i j`, equals the value at `i`. No identity or
composition laws for the transition maps are silently added. -/
def Compatible {I : Type u} {Y : I -> Type v}
    (t : (i j : I) -> Y j -> Y i) (family : (i : I) -> Y i) : Prop :=
  forall i j, t i j (family j) = family i

/-- Level one: every local type has a witness, without a chosen simultaneous family. -/
def LocalWitnesses {I : Type u} (Y : I -> Type v) : Prop :=
  forall i, Nonempty (Y i)

/-- Level two: one simultaneous local family satisfies every transition equation. -/
def CompatibleFamilyExists {I : Type u} {Y : I -> Type v}
    (t : (i j : I) -> Y j -> Y i) : Prop :=
  exists family : (i : I) -> Y i, Compatible t family

/-- Level three for a specified local family: one global object realizes every value. -/
def GlobalSource {I : Type u} {X : Type w} {Y : I -> Type v}
    (readout : (i : I) -> X -> Y i) (family : (i : I) -> Y i) : Prop :=
  exists x, forall i, readout i x = family i

/-- The missing premise for level three to imply level two: global readouts themselves
commute with every transition map. -/
def ReadoutsCompatible {I : Type u} {X : Type w} {Y : I -> Type v}
    (t : (i j : I) -> Y j -> Y i) (readout : (i : I) -> X -> Y i) : Prop :=
  forall i j x, t i j (readout j x) = readout i x

/-- A globally sourced family is compatible when the global readouts commute with the
transition maps. The readout premise is necessary; it is not present in the source text. -/
theorem global_source_implies_compatible_family_exists
    {I : Type u} {X : Type w} {Y : I -> Type v}
    (t : (i j : I) -> Y j -> Y i) (readout : (i : I) -> X -> Y i)
    (family : (i : I) -> Y i) (hreadout : ReadoutsCompatible t readout)
    (hglobal : GlobalSource readout family) : CompatibleFamilyExists t := by
  rcases hglobal with ⟨x, hx⟩
  refine ⟨family, ?_⟩
  intro i j
  calc
    t i j (family j) = t i j (readout j x) := congrArg (t i j) (hx j).symm
    _ = readout i x := hreadout i j x
    _ = family i := hx i
#print axioms global_source_implies_compatible_family_exists

/-- A chosen compatible family supplies a witness in every local type. -/
theorem compatible_family_exists_implies_local_witnesses
    {I : Type u} {Y : I -> Type v} (t : (i j : I) -> Y j -> Y i)
    (hfamily : CompatibleFamilyExists t) : LocalWitnesses Y := by
  rcases hfamily with ⟨family, _⟩
  exact fun i => ⟨family i⟩
#print axioms compatible_family_exists_implies_local_witnesses

/-- Two Boolean coordinates with one twisted reverse transition. The diagonal maps
are identities, but the two off-diagonal equations cannot hold simultaneously. -/
def twistedTransition (i j : Fin 2) (value : Bool) : Bool :=
  if i = 1 ∧ j = 0 then !value else value

/-- Every Boolean coordinate is inhabited, yet the twisted two-coordinate system has
no compatible family. Thus level one does not imply level two. -/
theorem local_witnesses_do_not_imply_compatible_family_exists :
    LocalWitnesses (fun _ : Fin 2 => Bool) /\
      Not (CompatibleFamilyExists twistedTransition) := by
  constructor
  · exact fun _ => ⟨false⟩
  · rintro ⟨family, hfamily⟩
    have hzeroOne := hfamily (0 : Fin 2) (1 : Fin 2)
    have honeZero := hfamily (1 : Fin 2) (0 : Fin 2)
    have hzeroOneCondition :
        Not ((0 : Fin 2) = 1 ∧ (1 : Fin 2) = 0) := by decide
    simp only [twistedTransition, if_neg hzeroOneCondition] at hzeroOne
    simp only [twistedTransition] at honeZero
    have htrue : True ∧ True := ⟨trivial, trivial⟩
    simp only [if_pos htrue] at honeZero
    rw [hzeroOne] at honeZero
    cases hvalue : family 0
    · simp only [hvalue, Bool.not_false] at honeZero
      cases honeZero
    · simp only [hvalue, Bool.not_true] at honeZero
      cases honeZero
#print axioms local_witnesses_do_not_imply_compatible_family_exists

/-- The all-pairs identity transition on the concrete two-coordinate Boolean family. -/
def identityTransition (_i _j : Fin 2) (value : Bool) : Bool := value

/-- A readout that forgets its global Boolean input at both coordinates. -/
def constantFalseReadout (_i : Fin 2) (_x : Bool) : Bool := false

/-- The constant false local family. -/
def allFalseFamily (_i : Fin 2) : Bool := false

/-- The constant true local family. -/
def allTrueFamily (_i : Fin 2) : Bool := true

/-- Identity transitions have the all-true compatible family, but the constant-false
readout cannot realize it. Thus level two does not imply level three, even with a
nonempty two-element global carrier and transition-compatible readouts. -/
theorem compatible_family_exists_does_not_imply_global_source :
    ReadoutsCompatible identityTransition constantFalseReadout /\
      CompatibleFamilyExists identityTransition /\
      Not (GlobalSource constantFalseReadout allTrueFamily) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j x
    rfl
  · exact ⟨allTrueFamily, by intro i j; rfl⟩
  · rintro ⟨x, hx⟩
    have hzero := hx (0 : Fin 2)
    simp [constantFalseReadout, allTrueFamily] at hzero
#print axioms compatible_family_exists_does_not_imply_global_source

/-- Readout compatibility is genuinely necessary in the first implication: the
constant-false family has a global source, while the twisted transition system has no
compatible family and its readouts do not commute with the reverse transition. -/
theorem readouts_compatible_is_necessary :
    GlobalSource constantFalseReadout allFalseFamily /\
      Not (ReadoutsCompatible twistedTransition constantFalseReadout) /\
      Not (CompatibleFamilyExists twistedTransition) := by
  refine ⟨⟨false, by intros; rfl⟩, ?_,
    local_witnesses_do_not_imply_compatible_family_exists.2⟩
  intro hreadout
  have honeZero := hreadout (1 : Fin 2) (0 : Fin 2) false
  simp [twistedTransition, constantFalseReadout] at honeZero
#print axioms readouts_compatible_is_necessary

/- Degeneracy audit. An empty index makes levels one and two vacuous. Level three
still asks for a global object, so it is equivalent to `Nonempty X`; this reconciles
the empty-index audit with the independently requested empty-`X` audit. -/
example : LocalWitnesses (fun i : Empty => i.elim) := by
  intro i
  exact i.elim

example (t : (i j : Empty) -> Unit -> Unit) : CompatibleFamilyExists t := by
  refine ⟨fun i => i.elim, ?_⟩
  intro i
  exact i.elim

/- The same empty-index audit at the explicit finite size `n = 0`. -/
example (t : (i j : Fin 0) -> Bool -> Bool) :
    LocalWitnesses (fun _ : Fin 0 => Bool) /\ CompatibleFamilyExists t := by
  refine ⟨?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · refine ⟨fun i => Fin.elim0 i, ?_⟩
    intro i
    exact Fin.elim0 i

example {X : Type u} (readout : (i : Empty) -> X -> Unit)
    (family : (i : Empty) -> Unit) :
    GlobalSource readout family <-> Nonempty X := by
  constructor
  · rintro ⟨x, _⟩
    exact ⟨x⟩
  · rintro ⟨x⟩
    exact ⟨x, fun i => i.elim⟩

/- On a singleton index with identity transition and readout, all three levels reduce
to inhabitation of the single carrier. -/
example {Y : Type u} :
    LocalWitnesses (fun _ : Unit => Y) <-> Nonempty Y := by
  constructor
  · intro hwitnesses
    exact hwitnesses ()
  · rintro ⟨y⟩
    exact fun _ => ⟨y⟩

example {Y : Type u} :
    CompatibleFamilyExists (fun _ _ : Unit => (id : Y -> Y)) <-> Nonempty Y := by
  constructor
  · rintro ⟨family, _⟩
    exact ⟨family ()⟩
  · rintro ⟨y⟩
    exact ⟨fun _ => y, by intro i j; rfl⟩

example {Y : Type u} (family : Unit -> Y) :
    GlobalSource (fun _ : Unit => (id : Y -> Y)) family := by
  exact ⟨family (), by intro i; cases i; rfl⟩

/- Singleton local types make compatibility automatic for arbitrary transitions. -/
example {I : Type u} (t : (i j : I) -> Unit -> Unit)
    (family : I -> Unit) : Compatible t family := by
  intro i j
  exact Subsingleton.elim _ _

/- The constant zero transition is compatible with the constant zero family. -/
example {I : Type u} :
    Compatible (fun _ _ : I => fun _ : Nat => 0) (fun _ : I => 0) := by
  intro i j
  rfl

/- An empty global carrier makes level three false, while unit-valued levels one and
two remain true for any index and any transition maps. -/
example {I : Type u} {Y : I -> Type v} (readout : (i : I) -> Empty -> Y i)
    (family : (i : I) -> Y i) : Not (GlobalSource readout family) := by
  rintro ⟨x, _⟩
  exact x.elim

example {I : Type u} (t : (i j : I) -> Unit -> Unit) :
    LocalWitnesses (fun _ : I => Unit) /\ CompatibleFamilyExists t := by
  refine ⟨fun _ => ⟨()⟩, ⟨fun _ => (), ?_⟩⟩
  intro i j
  exact Subsingleton.elim _ _

end D5.S3.ConceptDynamics.RefinementGeometry.ThreeLevelQuantifierSeparation

/- GID: D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Effective concept classes are dual to source equivalence relations. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Antisymmetrization

/- Library-search audit trail (2026-08-22):
   * Exact repository hits `Concept`, `Refines`, and `conceptJoin` are the
     canonical concept-family primitives and are imported directly.
   * Exact pinned-Mathlib hits `Antisymmetrization`, `Setoid.ker_mk_eq`,
     `Setoid.completeLattice`, and `Setoid.sup_eq_eqvGen` supply the quotient,
     relation lattice, and equivalence-closure constructions used below.
   * Repository and pinned-Mathlib searches found no existing order isomorphism
     from effective concept presentations modulo mutual refinement to the dual
     lattice of equivalence relations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

universe u

/-- An effective concept presentation has no unused coordinate values. -/
structure EffectiveConcept (X : Type u) where
  Coordinate : Type u
  readout : Concept X Coordinate
  effective : Function.Surjective readout

instance {X : Type u} : LE (EffectiveConcept X) where
  le C D := Refines C.readout D.readout

private theorem effective_refines_refl {X : Type u} (C : EffectiveConcept X) : C <= C := by
  exact ⟨id, rfl⟩

private theorem effective_refines_trans {X : Type u}
    (A B C : EffectiveConcept X) : A <= B -> B <= C -> A <= C := by
  rintro ⟨forgetAB, hAB⟩ ⟨forgetBC, hBC⟩
  refine ⟨forgetAB ∘ forgetBC, ?_⟩
  rw [hAB, hBC]
  rfl

instance {X : Type u} : Preorder (EffectiveConcept X) where
  le_refl := effective_refines_refl
  le_trans := effective_refines_trans

/-- For effective readouts, factorization is exactly reverse kernel inclusion. -/
theorem effective_refines_iff_reverse_kernel {X : Type u}
    (C D : EffectiveConcept X) :
    Refines C.readout D.readout <-> Setoid.ker D.readout <= Setoid.ker C.readout := by
  constructor
  · rintro ⟨forget, hforget⟩ x y hxy
    calc
      C.readout x = forget (D.readout x) := congrFun hforget x
      _ = forget (D.readout y) := congrArg forget hxy
      _ = C.readout y := (congrFun hforget y).symm
  · intro hkernel
    let representative : D.Coordinate -> X := Function.surjInv D.effective
    have representativeRight : Function.RightInverse representative D.readout :=
      Function.rightInverse_surjInv D.effective
    refine ⟨fun d => C.readout (representative d), ?_⟩
    funext x
    change C.readout x = C.readout (representative (D.readout x))
    exact hkernel (representativeRight (D.readout x)).symm

/-- Mutual-refinement classes of effective concept presentations. -/
abbrev ConceptClass (X : Type u) :=
  Antisymmetrization (EffectiveConcept X) (fun C D => C <= D)

/-- The effective quotient presentation associated with an equivalence relation. -/
def relationConcept {X : Type u} (relation : Setoid X) : EffectiveConcept X where
  Coordinate := Quotient relation
  readout := Quotient.mk''
  effective := Quotient.mk_surjective

/-- The kernel relation represented by a mutual-refinement concept class. -/
noncomputable def conceptClassKernel {X : Type u} :
    ConceptClass X -> OrderDual (Setoid X) :=
  Quotient.lift
    (fun C : EffectiveConcept X => OrderDual.toDual (Setoid.ker C.readout))
    (by
      intro C D equivalent
      exact congrArg OrderDual.toDual (le_antisymm
        ((effective_refines_iff_reverse_kernel D C).1 equivalent.2)
        ((effective_refines_iff_reverse_kernel C D).1 equivalent.1)))

@[simp]
theorem conceptClassKernel_mk {X : Type u} (C : EffectiveConcept X) :
    conceptClassKernel (toAntisymmetrization (fun A B : EffectiveConcept X => A <= B) C) =
      OrderDual.toDual (Setoid.ker C.readout) := rfl

/-- Effective concept classes and source equivalence relations carry opposite orders. -/
noncomputable def conceptKernelOrderIso (X : Type u) :
    ConceptClass X ≃o OrderDual (Setoid X) where
  toFun := conceptClassKernel
  invFun := fun relation =>
    toAntisymmetrization (fun C D : EffectiveConcept X => C <= D)
      (relationConcept (OrderDual.ofDual relation))
  left_inv conceptClass := by
    induction conceptClass using Antisymmetrization.ind with
    | _ C =>
        change toAntisymmetrization (fun A B : EffectiveConcept X => A <= B)
          (relationConcept (Setoid.ker C.readout)) =
            toAntisymmetrization (fun A B : EffectiveConcept X => A <= B) C
        apply Quotient.sound'
        constructor
        · apply (effective_refines_iff_reverse_kernel
            (relationConcept (Setoid.ker C.readout)) C).2
          rw [relationConcept, Setoid.ker_mk_eq]
        · apply (effective_refines_iff_reverse_kernel C
            (relationConcept (Setoid.ker C.readout))).2
          rw [relationConcept, Setoid.ker_mk_eq]
  right_inv relation := by
    change OrderDual.toDual
      (Setoid.ker (relationConcept (OrderDual.ofDual relation)).readout) = relation
    rw [relationConcept, Setoid.ker_mk_eq]
    rfl
  map_rel_iff' := by
    intro left right
    induction left using Antisymmetrization.ind with
    | _ C =>
        induction right using Antisymmetrization.ind with
        | _ D =>
            exact (effective_refines_iff_reverse_kernel C D).symm

/-- The quotient by the equivalence closure of two kernels is their canonical
effective common coarsening. -/
def commonCoarsening {X C D : Type*} (q_C : Concept X C) (q_D : Concept X D) :
    Concept X (Quotient (Setoid.ker q_C ⊔ Setoid.ker q_D)) :=
  Quotient.mk''

/-- Concepts modulo mutual refinement are order-dual to equivalence relations;
the canonical joint and common coarsening realize intersection and equivalence
closure of union, respectively. -/
theorem concept_kernel_order_duality (X : Type u) :
    Function.Bijective (conceptClassKernel (X := X)) ∧
      (forall C D : EffectiveConcept X,
        Refines C.readout D.readout <->
          Setoid.ker D.readout <= Setoid.ker C.readout) ∧
      (forall {C D : Type u} (q_C : Concept X C) (q_D : Concept X D),
        Setoid.ker (conceptJoin q_C q_D) =
          Setoid.ker q_C ⊓ Setoid.ker q_D) ∧
      (forall {C D : Type u} (q_C : Concept X C) (q_D : Concept X D),
        Setoid.ker (commonCoarsening q_C q_D) =
          Relation.EqvGen.setoid
            (fun x y => Setoid.ker q_C x y ∨ Setoid.ker q_D x y)) := by
  refine ⟨(conceptKernelOrderIso X).bijective, ?_, ?_, ?_⟩
  · exact effective_refines_iff_reverse_kernel
  · intro C D q_C q_D
    apply Setoid.ext
    intro x y
    change (q_C x, q_D x) = (q_C y, q_D y) ↔
      q_C x = q_C y ∧ q_D x = q_D y
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨hC, hD⟩
      exact Prod.ext hC hD
  · intro C D q_C q_D
    rw [commonCoarsening, Setoid.ker_mk_eq, Setoid.sup_eq_eqvGen]

/-- Identity and constant readouts give distinct effective concept classes on a
two-state source, so the class carrier is not collapsed. -/
example :
    Not (conceptClassKernel
        (toAntisymmetrization
          (fun C D : EffectiveConcept Bool => C <= D)
          ({ Coordinate := Bool, readout := id,
             effective := Function.surjective_id } : EffectiveConcept Bool)) =
      conceptClassKernel
        (toAntisymmetrization
          (fun C D : EffectiveConcept Bool => C <= D)
          ({ Coordinate := Unit, readout := fun _ => (),
             effective := fun _ => ⟨false, rfl⟩ } : EffectiveConcept Bool))) := by
  intro equalKernels
  have related : (Setoid.ker (id : Bool -> Bool)) false true := by
    have := congrArg OrderDual.ofDual equalKernels
    change Setoid.ker (id : Bool -> Bool) =
      Setoid.ker (fun _ : Bool => ()) at this
    rw [this]
    rfl
  exact Bool.false_ne_true related

#print axioms concept_kernel_order_duality

end D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

/- GID: D5/S3/Topology/FiniteCategoricalCoverCertificate
   generality: G
   mirror-B: D5/B/S3/Topology/FiniteCategoricalCoverCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Hom.Basic, mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Explicit monotone-map zigzags certify categorical open covers of finite posets. -/

module

public import D5.S3.Topology.ConnectedCategoryGraft
public import Mathlib.Order.Hom.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Basic

import OmegaBuild.Commands

/-! Checked finite order tables and explicit categorical cover witnesses. -/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Topology.FiniteCategoricalCoverCertificate

open D5.S3.Topology.ConnectedCategoryGraft

variable {n : ℕ}

/-- The order axioms for a Boolean relation on a fixed finite vertex set. -/
def ValidOrder (le : Fin n → Fin n → Bool) : Prop :=
  (∀ x, le x x = true) ∧
  (∀ x y z, le x y = true → le y z = true → le x z = true) ∧
  (∀ x y, le x y = true → le y x = true → x = y)

instance (le : Fin n → Fin n → Bool) : Decidable (ValidOrder le) := by
  unfold ValidOrder
  infer_instance

/-- The partial order given by a checked relation table. -/
@[instance_reducible] def tableOrder (le : Fin n → Fin n → Bool) (h : ValidOrder le) : PartialOrder (Fin n) where
  le x y := le x y = true
  lt x y := le x y = true ∧ ¬ le y x = true
  lt_iff_le_not_ge := fun _ _ => Iff.rfl
  le_refl := h.1
  le_trans := h.2.1
  le_antisymm := h.2.2

/-- A monotone map on the chosen domain, represented by a total vertex table. -/
def MonotoneOn (le : Fin n → Fin n → Bool) (U : Fin n → Bool) (f : Fin n → Fin n) : Prop :=
  ∀ x y, U x = true → U y = true → le x y = true → le (f x) (f y) = true

instance (le : Fin n → Fin n → Bool) (U : Fin n → Bool) (f : Fin n → Fin n) :
    Decidable (MonotoneOn le U f) := by
  unfold MonotoneOn
  infer_instance

/-- Pointwise order between two tables on just the chosen domain. -/
def BelowOn (le : Fin n → Fin n → Bool) (U : Fin n → Bool) (f g : Fin n → Fin n) : Prop :=
  ∀ x, U x = true → le (f x) (g x) = true

instance (le : Fin n → Fin n → Bool) (U : Fin n → Bool) (f g : Fin n → Fin n) :
    Decidable (BelowOn le U f g) := by
  unfold BelowOn
  infer_instance

/-- Completing the inclusion's zigzag. The constant endpoint is checked on
every vertex of the chosen domain. -/
def Contracts (le : Fin n → Fin n → Bool) (U : Fin n → Bool) (c : Fin n)
    (f : Fin n → Fin n) : List (Fin n → Fin n) → Prop
  | [] => ∀ x, U x = true → f x = c
  | g :: steps =>
    MonotoneOn le U g ∧ (BelowOn le U f g ∨ BelowOn le U g f) ∧ Contracts le U c g steps

instance (le : Fin n → Fin n → Bool) (U : Fin n → Bool) (c : Fin n) (f : Fin n → Fin n)
    (steps : List (Fin n → Fin n)) : Decidable (Contracts le U c f steps) := by
  induction steps generalizing f with
  | nil =>
    unfold Contracts
    infer_instance
  | cons g steps ih =>
    letI := ih g
    unfold Contracts
    infer_instance

private def hom {le : Fin n → Fin n → Bool} (h : ValidOrder le) {U : Fin n → Bool}
    {f : Fin n → Fin n} (hf : MonotoneOn le U f) :
    letI : PartialOrder (Fin n) := tableOrder le h
    {x : Fin n // U x = true} →o Fin n := by
  letI : PartialOrder (Fin n) := tableOrder le h
  exact ⟨fun x => f x.val, fun x y hxy => hf x.val y.val x.property y.property hxy⟩

private theorem homContracts {le : Fin n → Fin n → Bool} (h : ValidOrder le)
    {U : Fin n → Bool} {c : Fin n} {f : Fin n → Fin n} (hf : MonotoneOn le U f)
    {steps : List (Fin n → Fin n)} (hc : Contracts le U c f steps) :
    letI : PartialOrder (Fin n) := tableOrder le h
    Relation.EqvGen (· ≤ ·) (hom h hf) (OrderHom.const {x : Fin n // U x = true} c) := by
  let : PartialOrder (Fin n) := tableOrder le h
  induction steps generalizing f with
  | nil =>
    have hEq : hom h hf = OrderHom.const {x : Fin n // U x = true} c :=
      OrderHom.ext _ _ (funext fun x => hc x.val x.property)
    rw [hEq]
    exact .refl _
  | cons g steps ih =>
    obtain ⟨hg, hd, hn⟩ := hc
    have hstep : Relation.EqvGen (· ≤ ·) (hom h hf) (hom h hg) := by
      rcases hd with hd | hd
      · exact .rel _ _ fun x => hd x.val x.property
      · exact .symm _ _ (.rel _ _ fun x => hd x.val x.property)
    exact .trans _ _ _ hstep (ih hg hn)

/-- An ordinary two-piece categorical cover certified directly by the
inclusion-to-constant zigzags on its two lower sets. -/
theorem hasCategoricalCover_of_tables (le : Fin n → Fin n → Bool) (h : ValidOrder le)
    (U : Fin 2 → Fin n → Bool) (c : Fin 2 → Fin n) (steps : Fin 2 → List (Fin n → Fin n))
    (hlow : ∀ i x y, le x y = true → U i y = true → U i x = true)
    (hcover : ∀ x, ∃ i, U i x = true)
    (hfence : ∀ i, Contracts le (U i) (c i) id (steps i)) :
    @HasCategoricalCover (Fin n) (tableOrder le h) 2 := by
  let : PartialOrder (Fin n) := tableOrder le h
  refine ⟨fun i => {x | U i x = true}, ?_, hcover⟩
  intro i
  refine ⟨fun x y hxy hy => hlow i _ _ hxy hy, c i, ?_⟩
  have hf : MonotoneOn le (U i) id := fun _ _ _ _ hx => hx
  exact homContracts h hf (hfence i)

end D5.S3.Topology.FiniteCategoricalCoverCertificate

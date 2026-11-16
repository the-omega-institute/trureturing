import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Full finite ordered cell families for canonical representatives and colour fibres. -/
namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
open _root_.D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open scoped Classical
noncomputable section
universe u

namespace CanonicalOrbit
abbrev signature : Signature where
  Params := Σ C : Type u, Σ _ : Fintype C, Σ _ : LinearOrder C, ℕ
  State p := p.1 → Fin p.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} :=
  realize signature (fun _ p P => @Canonical p.1 p.2.2.1.toLT p.2.2.2 P)
    (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {C : Type u} [ft : Fintype C] [lo : LinearOrder C]
    {k : ℕ} (P : C → Fin k),
    ∃! Q : C → Fin k, R.readout () ⟨C, ft, lo, k⟩ Q ∧
      ∃ e : Equiv.Perm (Fin k), Q = e ∘ P
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨Q, hQ, _⟩ := h (fun _ : ULift.{u} Unit => (0 : Fin 1))
  exact hQ.1
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance, inferInstance, 2⟩,
    (fun _ => 0), (fun _ => 1), ?_⟩
  change Canonical (fun _ : ULift.{u} Unit => (0 : Fin 2)) ≠
    Canonical (fun _ : ULift.{u} Unit => (1 : Fin 2))
  intro he
  have h0 : Canonical (fun _ : ULift.{u} Unit => (0 : Fin 2)) := by
    intro i b hb
    exact False.elim ((Fin.not_lt_zero b) hb)
  obtain ⟨j, _, hj⟩ := (Eq.mp he h0) ⟨()⟩ 0 (by decide)
  norm_num at hj

def family : Registration arena.{u} (type_of% (@canonical_exists_unique.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@canonical_exists_unique, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@canonical_exists_unique.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.CanonicalOrbit.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.CanonicalOrbit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end CanonicalOrbit

namespace Normalization
abbrev signature : Signature where
  Params := Σ C : Type u, Σ _ : Fintype C, LinearOrder C
  State p := p.1 → Fin 6
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} :=
  realize signature (fun _ p f => @Normal p.1 p.2.2.toLT f) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {C : Type u} [ft : Fintype C] [lo : LinearOrder C]
    (z : C) (_ : ∀ i, z ≤ i) (f : C → Fin 6) (_ : f z = 0),
    R.readout () ⟨C, ft, lo⟩ f ↔ Canonical (beta ∘ f) ∧ FirstSides f
private theorem normal_zero : Normal (fun _ : ULift.{u} Unit => (0 : Fin 6)) := by
  intro i
  constructor <;> simp
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let z : ULift.{u} Unit := ⟨()⟩
  have hz : ∀ i : ULift.{u} Unit, z ≤ i := fun i => le_of_eq (Subsingleton.elim _ _)
  have hh := h z hz (fun _ => 0) rfl
  exact hh.mpr ((normalization_iff z hz (fun _ => 0) rfl).mp normal_zero)
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance, inferInstance⟩,
    (fun _ => 0), (fun _ => 3), ?_⟩
  change Normal (fun _ : ULift.{u} Unit => (0 : Fin 6)) ≠
    Normal (fun _ : ULift.{u} Unit => (3 : Fin 6))
  intro he
  have hh := Eq.mp he normal_zero
  obtain ⟨j, _, hj⟩ := (hh ⟨()⟩).1 (Or.inr (Or.inl rfl))
  norm_num at hj

def family : Registration arena.{u} (type_of% (@normalization_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalization_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normalization_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Normalization.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Normalization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Normalization

namespace Fibres
abbrev signature : Signature where
  Params := Σ C : Type u, Σ _ : Fintype C, LinearOrder C
  State p := p.1 → Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} :=
  realize signature (fun _ p P => Nat.card (@Fibre p.1 p.2.2.toLT P))
    (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ p P => Nat.card (@Fibre p.1 p.2.2.toLT P) + 1)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {C : Type u} [ft : Fintype C] [lo : LinearOrder C] (P : C → Fin 3),
    R.readout () ⟨C, ft, lo⟩ P = 2 ^ (Fintype.card C - Nat.card (Set.range P))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have ha := fibre_card (fun _ : ULift.{u} Unit => (0 : Fin 3))
  have hb := h (fun _ : ULift.{u} Unit => (0 : Fin 3))
  change Nat.card (Fibre (fun _ : ULift.{u} Unit => (0 : Fin 3))) + 1 = _ at hb
  omega
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let P : ULift.{u} (Fin 2) → Fin 3 := fun i => ⟨i.down.val, by omega⟩
  have hi : Function.Injective P := by
    intro i j h
    exact ULift.ext (Fin.ext (congrArg (fun x : Fin 3 => x.val) h))
  have hr : Nat.card (Set.range P) = 2 := by
    have hh := Nat.card_congr (Equiv.ofInjective P hi)
    simpa using hh.symm
  refine ⟨⟨ULift.{u} (Fin 2), inferInstance, inferInstance⟩, (fun _ => 0), P, ?_⟩
  change Nat.card (Fibre (fun _ : ULift.{u} (Fin 2) => (0 : Fin 3))) ≠
    Nat.card (Fibre P)
  rw [fibre_card, fibre_card, hr]
  simp

def family : Registration arena.{u} (type_of% (@fibre_card.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fibre_card, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@fibre_card.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Fibres.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Fibres.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Fibres

namespace PatternCount
abbrev signature : Signature where
  Params := Σ C : Type u, Σ _ : Fintype C, LinearOrder C
  State p := (p.1 → Fin 3) → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} :=
  realize signature (fun _ p S => Nat.card {P : p.1 → Fin 3 // S P})
    (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ p S => Nat.card {P : p.1 → Fin 3 // S P} + 1)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {C : Type u} [ft : Fintype C] [lo : LinearOrder C]
    (S : (C → Fin 3) → Prop),
    (∀ e : Equiv.Perm (Fin 3), ∀ P, S (e ∘ P) ↔ S P) →
    (∀ P, S P → ∃ i j, P i ≠ P j) →
    R.readout () ⟨C, ft, lo⟩ S = 6 * Nat.card {P : C → Fin 3 // S P ∧ Canonical P}
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (fun _ : ULift.{u} Unit → Fin 3 => False)
    (by intros; rfl) (by intro P h; exact h.elim)
  change Nat.card {P : ULift.{u} Unit → Fin 3 // False} + 1 =
    6 * Nat.card {P : ULift.{u} Unit → Fin 3 // False ∧ Canonical P} at hh
  simp at hh
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance, inferInstance⟩,
    (fun _ => False), (fun _ => True), ?_⟩
  change Nat.card {P : ULift.{u} Unit → Fin 3 // False} ≠
    Nat.card {P : ULift.{u} Unit → Fin 3 // True}
  simp [Nat.card_eq_fintype_card]

def family : Registration arena.{u} (type_of% (@canonical_pattern_card.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@canonical_pattern_card, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@canonical_pattern_card.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.PatternCount.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.PatternCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end PatternCount

namespace NormalizedCount
abbrev signature : Signature where
  Params := Σ C : Type u, Σ _ : Fintype C, Σ _ : LinearOrder C, C
  State p := (p.1 → Fin 3) → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} :=
  realize signature (fun _ p S => Nat.card {f : p.1 → Fin 6 //
    S (beta ∘ f) ∧ f p.2.2.2 = 0 ∧ @Normal p.1 p.2.2.1.toLT f})
    (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ p S => Nat.card {f : p.1 → Fin 6 //
    S (beta ∘ f) ∧ f p.2.2.2 = 0 ∧ @Normal p.1 p.2.2.1.toLT f} + 1)
    (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {C : Type u} [ft : Fintype C] [lo : LinearOrder C]
    (z : C) (_ : ∀ i, z ≤ i) (S : (C → Fin 3) → Prop),
    R.readout () ⟨C, ft, lo, z⟩ S =
      ∑ P : {P : C → Fin 3 // S P ∧ Canonical P},
        2 ^ (Fintype.card C - Nat.card (Set.range P.val))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let z : ULift.{u} Unit := ⟨()⟩
  have hz : ∀ i : ULift.{u} Unit, z ≤ i := fun i => le_of_eq (Subsingleton.elim _ _)
  have ha := normalized_card z hz (fun _ => False)
  have hb := h z hz (fun _ => False)
  change Nat.card {f : ULift.{u} Unit → Fin 6 //
    False ∧ f z = 0 ∧ Normal f} + 1 = _ at hb
  omega
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let z : ULift.{u} Unit := ⟨()⟩
  refine ⟨⟨ULift.{u} Unit, inferInstance, inferInstance, z⟩,
    (fun _ => False), (fun _ => True), ?_⟩
  change Nat.card {f : ULift.{u} Unit → Fin 6 // False ∧ f z = 0 ∧ Normal f} ≠
    Nat.card {f : ULift.{u} Unit → Fin 6 // True ∧ f z = 0 ∧ Normal f}
  let : Unique {f : ULift.{u} Unit → Fin 6 // True ∧ f z = 0 ∧ Normal f} := {
    default := ⟨fun _ => 0, trivial, rfl, Normalization.normal_zero⟩
    uniq := fun f => Subtype.ext (funext fun x => by
      change f.val x = 0
      rw [Subsingleton.elim x z]
      exact f.property.2.1) }
  have hc : Nat.card {f : ULift.{u} Unit → Fin 6 // True ∧ f z = 0 ∧ Normal f} = 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_unique]
  rw [hc]
  simp [Nat.card_eq_fintype_card]

def family : Registration arena.{u} (type_of% (@normalized_card.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_card, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@normalized_card.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.NormalizedCount.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.NormalizedCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end NormalizedCount

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

/- GID: D5/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ConjunctionRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Typed finite clauses compile conjunctions over ADMIT readouts and ANCHOR slots. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.RegistrationWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.ConjunctionRegistrationTemplates

open LeanInformationAudit

/-- A closed clause vocabulary: no constructor accepts a proposition or a law. -/
inductive ConjunctionClause (readouts anchors : Nat) where
  | countEq (slot : Fin readouts) (count : Nat)
  | cover (first second third : Fin readouts)
  | disjoint (left right : Fin readouts)
  | member (slot : Fin readouts) (point : Fin anchors)
  | notMember (slot : Fin readouts) (point : Fin anchors)
  | and (left right : ConjunctionClause readouts anchors)

/-- Interpret each clause using the original predicates and finite set operations. -/
def conjunctionStatement {X : Type} [Fintype X] [DecidableEq X] {n m : Nat}
    (P : Fin n → X → Prop) [∀ i, DecidablePred (P i)] (a : Fin m → X) :
    ConjunctionClause n m → Prop
  | .countEq i k => (Finset.univ.filter (P i)).card = k
  | .cover i j k =>
      Finset.univ.filter (P i) ∪ Finset.univ.filter (P j) ∪ Finset.univ.filter (P k) =
        Finset.univ
  | .disjoint i j => Disjoint (Finset.univ.filter (P i)) (Finset.univ.filter (P j))
  | .member i j => P i (a j)
  | .notMember i j => ¬ P i (a j)
  | .and c d => conjunctionStatement P a c ∧ conjunctionStatement P a d

instance conjunctionDecidable {X : Type} [Fintype X] [DecidableEq X] {n m : Nat}
    (P : Fin n → X → Prop) [∀ i, DecidablePred (P i)] (a : Fin m → X) :
    (c : ConjunctionClause n m) → Decidable (conjunctionStatement P a c)
  | .countEq _ _ => by unfold conjunctionStatement; infer_instance
  | .cover _ _ _ => by unfold conjunctionStatement; infer_instance
  | .disjoint _ _ => by unfold conjunctionStatement; infer_instance
  | .member _ _ => by unfold conjunctionStatement; infer_instance
  | .notMember _ _ => by unfold conjunctionStatement; infer_instance
  | .and c d => @instDecidableAnd _ _ (conjunctionDecidable P a c) (conjunctionDecidable P a d)

abbrev conjunctionSignature (X : Type) (n m : Nat) : PrimitiveSignature X where
  Index := Fin n
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .admit
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin m
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def conjunctionRealization {X : Type} {n m : Nat}
    (P : Fin n → X → Prop) [∀ i, DecidablePred (P i)] (a : Fin m → X) :
    PrimitiveRealization (conjunctionSignature X n m) where
  readout i x := decide (P i x)
  anchor := a

def conjunctionArena (A : Arena) {n m : Nat} (c : ConjunctionClause n m) :
    PrimitiveLawArena where
  toArena := A
  signature := conjunctionSignature A.State n m
  Law r := by
    letI := A.stateFintype
    letI := A.stateDecidableEq
    exact conjunctionStatement (fun i x => r.readout i x = true) r.anchor c

/-- Boolean reflection changes no clause, set operation, polarity, or conjunction. -/
theorem conjunctionLegacy (A : Arena) {n m : Nat} (c : ConjunctionClause n m)
    (P : Fin n → A.State → Prop) [∀ i, DecidablePred (P i)] (a : Fin m → A.State) :
    letI := A.stateFintype
    letI := A.stateDecidableEq
    LegacyPrimitiveRealization (conjunctionArena A c) (conjunctionStatement P a c)
      (conjunctionRealization P a) := by
  let _ := A.stateFintype
  let _ := A.stateDecidableEq
  refine ⟨?_⟩
  change conjunctionStatement P a c ↔
    conjunctionStatement (fun i x => decide (P i x) = true) a c
  have h : (fun i x => decide (P i x) = true) = P := by
    funext i x
    exact decide_eq_true_eq (p := P i x)
  simp only [h]

/-- Change one ADMIT slot while preserving every other readout and every anchor. -/
def replaceConjunctionReadout {X : Type} {n m : Nat}
    (r : PrimitiveRealization (conjunctionSignature X n m)) (i : Fin n) (f : X → Bool) :
    PrimitiveRealization (conjunctionSignature X n m) where
  readout j := if j = i then f else r.readout j
  anchor := r.anchor

/-- Change one ANCHOR slot while preserving all readouts and other anchors. -/
def replaceConjunctionAnchor {X : Type} {n m : Nat}
    (r : PrimitiveRealization (conjunctionSignature X n m)) (i : Fin m) (x : X) :
    PrimitiveRealization (conjunctionSignature X n m) where
  readout := r.readout
  anchor j := if j = i then x else r.anchor j

/-- Individually falsifying updates supply checked support for every generated slot. -/
theorem conjunction_sensitivity (A : Arena) {n m : Nat} (c : ConjunctionClause n m)
    (r : PrimitiveRealization (conjunctionSignature A.State n m))
    (badReadout : Fin n → A.State → Bool) (badAnchor : Fin m → A.State)
    (valid : (conjunctionArena A c).Law r)
    (readout_invalid : ∀ i, ¬ (conjunctionArena A c).Law
      (replaceConjunctionReadout r i (badReadout i)))
    (anchor_invalid : ∀ i, ¬ (conjunctionArena A c).Law
      (replaceConjunctionAnchor r i (badAnchor i))) :
    FiniteSlotSensitivity (conjunctionArena A c) := by
  constructor
  · intro i
    refine ⟨r, replaceConjunctionReadout r i (badReadout i), ?_, ?_, ?_⟩
    · intro j hj
      exact (if_neg (show (j : Fin n) ≠ i from hj)).symm
    · intro j; rfl
    · exact ⟨fun _ => readout_invalid i, fun _ => valid⟩
  · intro i
    refine ⟨r, replaceConjunctionAnchor r i (badAnchor i), ?_, ?_, ?_⟩
    · intro j; rfl
    · intro j hj
      exact (if_neg (show (j : Fin m) ≠ i from hj)).symm
    · exact ⟨fun _ => anchor_invalid i, fun _ => valid⟩

#print axioms conjunctionLegacy
#print axioms conjunction_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.ConjunctionRegistrationTemplates

/- GID: D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise relation templates retain both object readouts and provide checked slot sensitivity. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.RegistrationWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates

open RegistrationTemplates LeanInformationAudit

/-- The two sides of a pointwise equation are independent CUT slots. -/
abbrev pointwiseEqSignature (X Y : Type) [DecidableEq Y] := separationSignature X Y Y

def pointwiseEqRealization {X Y : Type} [DecidableEq Y] (f g : X → Y) :
    PrimitiveRealization (pointwiseEqSignature X Y) := separationRealization f g

def pointwiseEqArena (A : Arena) (Y : Type) [DecidableEq Y] : PrimitiveLawArena where
  toArena := A
  signature := pointwiseEqSignature A.State Y
  Law r := ∀ x, r.readout false x = r.readout true x

theorem pointwiseEqLegacy (A : Arena) {Y : Type} [DecidableEq Y] (f g : A.State → Y) :
    LegacyPrimitiveRealization (pointwiseEqArena A Y) (∀ x, f x = g x)
      (pointwiseEqRealization f g) := ⟨Iff.rfl⟩

/-- Each slot can change the law while the other slot and all anchors stay fixed. -/
theorem pointwiseEq_sensitivity (A : Arena) {Y : Type} [DecidableEq Y]
    (x : A.State) (a b : Y) (hne : a ≠ b) : FiniteSlotSensitivity (pointwiseEqArena A Y) := by
  constructor
  · intro i
    cases i with
    | false =>
        refine ⟨pointwiseEqRealization (fun _ => a) (fun _ => a),
          pointwiseEqRealization (fun _ => b) (fun _ => a), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · exact (hj rfl).elim
          · rfl
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => hne (h x).symm, fun _ _ => rfl⟩
    | true =>
        refine ⟨pointwiseEqRealization (fun _ => a) (fun _ => a),
          pointwiseEqRealization (fun _ => a) (fun _ => b), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · rfl
          · exact (hj rfl).elim
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => hne (h x), fun _ _ => rfl⟩
  · intro i; exact Fin.elim0 i

#print axioms pointwiseEqLegacy
#print axioms pointwiseEq_sensitivity

/-- Two CUT slots record the two values which must differ at each state. -/
abbrev pointwiseNeSignature (X Y : Type) [DecidableEq Y] := separationSignature X Y Y

def pointwiseNeRealization {X Y : Type} [DecidableEq Y] (f g : X → Y) :
    PrimitiveRealization (pointwiseNeSignature X Y) := separationRealization f g

def pointwiseNeArena (A : Arena) (Y : Type) [DecidableEq Y] : PrimitiveLawArena where
  toArena := A
  signature := pointwiseNeSignature A.State Y
  Law r := ∀ x, r.readout false x ≠ r.readout true x

theorem pointwiseNeLegacy (A : Arena) {Y : Type} [DecidableEq Y] (f g : A.State → Y) :
    LegacyPrimitiveRealization (pointwiseNeArena A Y) (∀ x, f x ≠ g x)
      (pointwiseNeRealization f g) := ⟨Iff.rfl⟩

theorem pointwiseNe_sensitivity (A : Arena) {Y : Type} [DecidableEq Y]
    (x : A.State) (a b : Y) (hne : a ≠ b) : FiniteSlotSensitivity (pointwiseNeArena A Y) := by
  constructor
  · intro i
    cases i with
    | false =>
        refine ⟨pointwiseNeRealization (fun _ => a) (fun _ => b),
          pointwiseNeRealization (fun _ => b) (fun _ => b), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · exact (hj rfl).elim
          · rfl
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => h x rfl, fun _ _ => hne⟩
    | true =>
        refine ⟨pointwiseNeRealization (fun _ => a) (fun _ => b),
          pointwiseNeRealization (fun _ => a) (fun _ => a), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · rfl
          · exact (hj rfl).elim
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => h x rfl, fun _ _ => hne⟩
  · intro i; exact Fin.elim0 i

#print axioms pointwiseNeLegacy
#print axioms pointwiseNe_sensitivity

/-- Ordered comparison keeps both values as typed CUT readouts. -/
abbrev pointwiseOrderSignature (X Y : Type) [LinearOrder Y] := separationSignature X Y Y

def pointwiseOrderRealization {X Y : Type} [LinearOrder Y] (f g : X → Y) :
    PrimitiveRealization (pointwiseOrderSignature X Y) := separationRealization f g

def pointwiseOrderArena (A : Arena) (Y : Type) [LinearOrder Y]
    (strict : Bool) : PrimitiveLawArena where
  toArena := A
  signature := pointwiseOrderSignature A.State Y
  Law r := ∀ x, if strict then @LT.lt Y _ (r.readout false x) (r.readout true x)
    else @LE.le Y _ (r.readout false x) (r.readout true x)

theorem pointwiseOrderLegacy (A : Arena) {Y : Type} [LinearOrder Y]
    (strict : Bool) (f g : A.State → Y) :
    LegacyPrimitiveRealization (pointwiseOrderArena A Y strict)
      (∀ x, if strict then f x < g x else f x ≤ g x)
      (pointwiseOrderRealization f g) := ⟨Iff.rfl⟩

theorem pointwiseOrder_sensitivity (A : Arena) {Y : Type} [LinearOrder Y]
    (strict : Bool) (x : A.State) (a b : Y) (hab : a < b) :
    FiniteSlotSensitivity (pointwiseOrderArena A Y strict) := by
  constructor
  · intro i
    cases strict with
    | false =>
        cases i with
        | false =>
            refine ⟨pointwiseOrderRealization (fun _ => a) (fun _ => a),
              pointwiseOrderRealization (fun _ => b) (fun _ => a), ?_, ?_, ?_⟩
            · intro j hj; cases j
              · exact (hj rfl).elim
              · rfl
            · intro j; exact Fin.elim0 j
            · exact ⟨fun _ h => (not_le_of_gt hab) (h x), fun _ _ => le_refl a⟩
        | true =>
            refine ⟨pointwiseOrderRealization (fun _ => b) (fun _ => b),
              pointwiseOrderRealization (fun _ => b) (fun _ => a), ?_, ?_, ?_⟩
            · intro j hj; cases j
              · rfl
              · exact (hj rfl).elim
            · intro j; exact Fin.elim0 j
            · exact ⟨fun _ h => (not_le_of_gt hab) (h x), fun _ _ => le_refl b⟩
    | true =>
        cases i with
        | false =>
            refine ⟨pointwiseOrderRealization (fun _ => a) (fun _ => b),
              pointwiseOrderRealization (fun _ => b) (fun _ => b), ?_, ?_, ?_⟩
            · intro j hj; cases j
              · exact (hj rfl).elim
              · rfl
            · intro j; exact Fin.elim0 j
            · exact ⟨fun _ h => lt_irrefl b (h x), fun _ _ => hab⟩
        | true =>
            refine ⟨pointwiseOrderRealization (fun _ => a) (fun _ => b),
              pointwiseOrderRealization (fun _ => a) (fun _ => a), ?_, ?_, ?_⟩
            · intro j hj; cases j
              · rfl
              · exact (hj rfl).elim
            · intro j; exact Fin.elim0 j
            · exact ⟨fun _ h => lt_irrefl a (h x), fun _ _ => hab⟩
  · intro i; exact Fin.elim0 i

#print axioms pointwiseOrderLegacy
#print axioms pointwiseOrder_sensitivity


/-- The two sides of a pointwise equation are independent CUT slots. -/
def homogeneousPointwiseEqSignature (X Y : Type) [dY : DecidableEq Y] :
    PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => dY
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def homogeneousPointwiseEqRealization {X Y : Type} [dY : DecidableEq Y] (f g : X → Y) :
    PrimitiveRealization (homogeneousPointwiseEqSignature X Y) where
  readout := fun b x => Bool.rec (f x) (g x) b
  anchor := Fin.elim0


def homogeneousPointwiseEqArena (A : Arena) (Y : Type) [dY : DecidableEq Y] : PrimitiveLawArena where
  toArena := A
  signature := homogeneousPointwiseEqSignature A.State Y
  Law r := ∀ x, r.readout false x = r.readout true x

theorem homogeneousPointwiseEqLegacy (A : Arena) {Y : Type} [dY : DecidableEq Y] (f g : A.State → Y) :
    LegacyPrimitiveRealization (homogeneousPointwiseEqArena A Y) (∀ x, f x = g x)
      (homogeneousPointwiseEqRealization f g) := ⟨Iff.rfl⟩

/-- Each slot can change the law while the other slot and all anchors stay fixed. -/
theorem homogeneousPointwiseEq_sensitivity (A : Arena) {Y : Type} [dY : DecidableEq Y]
    (x : A.State) (a b : Y) (hne : a ≠ b) : FiniteSlotSensitivity (homogeneousPointwiseEqArena A Y) := by
  constructor
  · intro i
    cases i with
    | false =>
        refine ⟨homogeneousPointwiseEqRealization (fun _ => a) (fun _ => a),
          homogeneousPointwiseEqRealization (fun _ => b) (fun _ => a), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · exact (hj rfl).elim
          · rfl
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => hne (h x).symm, fun _ _ => rfl⟩
    | true =>
        refine ⟨homogeneousPointwiseEqRealization (fun _ => a) (fun _ => a),
          homogeneousPointwiseEqRealization (fun _ => a) (fun _ => b), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · rfl
          · exact (hj rfl).elim
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => hne (h x), fun _ _ => rfl⟩
  · intro i; exact Fin.elim0 i

#print axioms homogeneousPointwiseEqLegacy
#print axioms homogeneousPointwiseEq_sensitivity

/-- Two CUT slots record the two values which must differ at each state. -/
def homogeneousPointwiseNeSignature (X Y : Type) [dY : DecidableEq Y] :
    PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => dY
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def homogeneousPointwiseNeRealization {X Y : Type} [dY : DecidableEq Y] (f g : X → Y) :
    PrimitiveRealization (homogeneousPointwiseNeSignature X Y) where
  readout := fun b x => Bool.rec (f x) (g x) b
  anchor := Fin.elim0


def homogeneousPointwiseNeArena (A : Arena) (Y : Type) [dY : DecidableEq Y] : PrimitiveLawArena where
  toArena := A
  signature := homogeneousPointwiseNeSignature A.State Y
  Law r := ∀ x, r.readout false x ≠ r.readout true x

theorem homogeneousPointwiseNeLegacy (A : Arena) {Y : Type} [dY : DecidableEq Y] (f g : A.State → Y) :
    LegacyPrimitiveRealization (homogeneousPointwiseNeArena A Y) (∀ x, f x ≠ g x)
      (homogeneousPointwiseNeRealization f g) := ⟨Iff.rfl⟩

theorem homogeneousPointwiseNe_sensitivity (A : Arena) {Y : Type} [dY : DecidableEq Y]
    (x : A.State) (a b : Y) (hne : a ≠ b) : FiniteSlotSensitivity (homogeneousPointwiseNeArena A Y) := by
  constructor
  · intro i
    cases i with
    | false =>
        refine ⟨homogeneousPointwiseNeRealization (fun _ => a) (fun _ => b),
          homogeneousPointwiseNeRealization (fun _ => b) (fun _ => b), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · exact (hj rfl).elim
          · rfl
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => h x rfl, fun _ _ => hne⟩
    | true =>
        refine ⟨homogeneousPointwiseNeRealization (fun _ => a) (fun _ => b),
          homogeneousPointwiseNeRealization (fun _ => a) (fun _ => a), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · rfl
          · exact (hj rfl).elim
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => h x rfl, fun _ _ => hne⟩
  · intro i; exact Fin.elim0 i

#print axioms homogeneousPointwiseNeLegacy
#print axioms homogeneousPointwiseNe_sensitivity

/-- Ordered comparison keeps both values as typed CUT readouts. -/
def homogeneousPointwiseOrderSignature (X Y : Type) [dY : DecidableEq Y] :
    PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => dY
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def homogeneousPointwiseOrderRealization {X Y : Type} [dY : DecidableEq Y] (f g : X → Y) :
    PrimitiveRealization (homogeneousPointwiseOrderSignature X Y) where
  readout := fun b x => Bool.rec (f x) (g x) b
  anchor := Fin.elim0


def homogeneousPointwiseOrderArena (A : Arena) (Y : Type) [LinearOrder Y] [dY : DecidableEq Y]
    (strict : Bool) : PrimitiveLawArena where
  toArena := A
  signature := homogeneousPointwiseOrderSignature A.State Y
  Law r := ∀ x, if strict then @LT.lt Y _ (r.readout false x) (r.readout true x)
    else @LE.le Y _ (r.readout false x) (r.readout true x)

theorem homogeneousPointwiseOrderLegacy (A : Arena) {Y : Type} [LinearOrder Y] [dY : DecidableEq Y]
    (strict : Bool) (f g : A.State → Y) :
    LegacyPrimitiveRealization (homogeneousPointwiseOrderArena A Y strict)
      (∀ x, if strict then f x < g x else f x ≤ g x)
      (homogeneousPointwiseOrderRealization f g) := ⟨Iff.rfl⟩

theorem homogeneousPointwiseOrder_sensitivity (A : Arena) {Y : Type} [LinearOrder Y] [dY : DecidableEq Y]
    (strict : Bool) (x : A.State) (a b : Y) (hab : a < b) :
    FiniteSlotSensitivity (homogeneousPointwiseOrderArena A Y strict) := by
  constructor
  · intro i
    cases strict with
    | false =>
        cases i with
        | false =>
            refine ⟨homogeneousPointwiseOrderRealization (fun _ => a) (fun _ => a),
              homogeneousPointwiseOrderRealization (fun _ => b) (fun _ => a), ?_, ?_, ?_⟩
            · intro j hj; cases j
              · exact (hj rfl).elim
              · rfl
            · intro j; exact Fin.elim0 j
            · exact ⟨fun _ h => (not_le_of_gt hab) (h x), fun _ _ => le_refl a⟩
        | true =>
            refine ⟨homogeneousPointwiseOrderRealization (fun _ => b) (fun _ => b),
              homogeneousPointwiseOrderRealization (fun _ => b) (fun _ => a), ?_, ?_, ?_⟩
            · intro j hj; cases j
              · rfl
              · exact (hj rfl).elim
            · intro j; exact Fin.elim0 j
            · exact ⟨fun _ h => (not_le_of_gt hab) (h x), fun _ _ => le_refl b⟩
    | true =>
        cases i with
        | false =>
            refine ⟨homogeneousPointwiseOrderRealization (fun _ => a) (fun _ => b),
              homogeneousPointwiseOrderRealization (fun _ => b) (fun _ => b), ?_, ?_, ?_⟩
            · intro j hj; cases j
              · exact (hj rfl).elim
              · rfl
            · intro j; exact Fin.elim0 j
            · exact ⟨fun _ h => lt_irrefl b (h x), fun _ _ => hab⟩
        | true =>
            refine ⟨homogeneousPointwiseOrderRealization (fun _ => a) (fun _ => b),
              homogeneousPointwiseOrderRealization (fun _ => a) (fun _ => a), ?_, ?_, ?_⟩
            · intro j hj; cases j
              · rfl
              · exact (hj rfl).elim
            · intro j; exact Fin.elim0 j
            · exact ⟨fun _ h => lt_irrefl a (h x), fun _ _ => hab⟩
  · intro i; exact Fin.elim0 i

#print axioms homogeneousPointwiseOrderLegacy
#print axioms homogeneousPointwiseOrder_sensitivity


end D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates

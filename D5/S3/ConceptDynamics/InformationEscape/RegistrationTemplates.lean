/- GID: D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/RegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Typed registration constructors generate primitive inventories and realization-dependent laws on explicit canonical arenas. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

/- The canonical arena is an explicit input. No constructor accepts a Law or a
bundle. Changing a readout changes the generated Law's argument, not its syntax.
Search receipt: TheoremUnit's compiler and ADMIT reflection; Mathlib's Bijective
API. These are presentation constructors, not new proofs of bijection facts. -/

def cutSignature (X Y : Type) [DecidableEq Y] : PrimitiveSignature X where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def cutRealization {X Y : Type} [DecidableEq Y] (f : X → Y) :
    PrimitiveRealization (cutSignature X Y) := ⟨fun _ => f, Fin.elim0⟩

/-- Single-consumer helper in the gold set; all readout functions remain abstract. -/
def bijectiveArena (A : Arena) (Y : Type) [DecidableEq Y] : PrimitiveLawArena where
  toArena := A
  signature := cutSignature A.State Y
  Law := fun r => Function.Bijective (r.readout ())

theorem bijectiveLegacy (A : Arena) {Y : Type} [DecidableEq Y] (f : A.State → Y) :
    LegacyPrimitiveRealization (bijectiveArena A Y) (Function.Bijective f)
      (cutRealization f) := ⟨Iff.rfl⟩

def separationSignature (X Y Z : Type) [DecidableEq Y] [DecidableEq Z] :
    PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output | false => Y | true => Z
  outputDecidableEq := by intro i; cases i <;> infer_instance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def separationRealization {X Y Z : Type} [DecidableEq Y] [DecidableEq Z]
    (coarse : X → Y) (fine : X → Z) : PrimitiveRealization (separationSignature X Y Z) where
  readout | false => coarse | true => fine
  anchor := Fin.elim0

/-- Witness separation, exactly the law shared by the two causal golds. -/
def separationArena (A : Arena) (Y Z : Type) [DecidableEq Y] [DecidableEq Z] :
    PrimitiveLawArena where
  toArena := A
  signature := separationSignature A.State Y Z
  Law := fun r => ∃ x y, r.readout false x = r.readout false y ∧
    r.readout true x ≠ r.readout true y

theorem separationLegacy (A : Arena) {Y Z : Type} [DecidableEq Y] [DecidableEq Z]
    (coarse : A.State → Y) (fine : A.State → Z) :
    LegacyPrimitiveRealization (separationArena A Y Z)
      (∃ x y, coarse x = coarse y ∧ fine x ≠ fine y)
      (separationRealization coarse fine) := ⟨Iff.rfl⟩

def admittedSurjectionSignature (X Y : Type) [DecidableEq Y] : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output | false => Y | true => Bool
  outputDecidableEq := by intro i; cases i <;> infer_instance
  axis | false => .cut | true => .admit
  readoutAxisNotAnchor := by intro i; cases i <;> simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def admittedSurjectionRealization {X Y : Type} [DecidableEq Y]
    (f : X → Y) (P : X → Prop) [DecidablePred P] :
    PrimitiveRealization (admittedSurjectionSignature X Y) where
  readout | false => f | true => fun x => decide (P x)
  anchor := Fin.elim0

/-- Surjectivity on admitted states with a distinct-output witness (one gold consumer). -/
def admittedSurjectionArena (A : Arena) (Y : Type) [DecidableEq Y] : PrimitiveLawArena where
  toArena := A
  signature := admittedSurjectionSignature A.State Y
  Law := fun r => (∀ y, ∃ x, r.readout true x = true ∧ r.readout false x = y) ∧
    ∃ x y, r.readout true x = true ∧ r.readout true y = true ∧ x ≠ y ∧
      r.readout false x ≠ r.readout false y

theorem admittedSurjectionLegacy (A : Arena) {Y : Type} [DecidableEq Y]
    (f : A.State → Y) (P : A.State → Prop) [DecidablePred P] :
    LegacyPrimitiveRealization (admittedSurjectionArena A Y)
      ((∀ y, ∃ x, P x ∧ f x = y) ∧ ∃ x y, P x ∧ P y ∧ x ≠ y ∧ f x ≠ f y)
      (admittedSurjectionRealization f P) := by
  refine ⟨?_⟩
  change _ ↔ ((∀ y, ∃ x, decide (P x) = true ∧ f x = y) ∧
    ∃ x y, decide (P x) = true ∧ decide (P y) = true ∧ x ≠ y ∧ f x ≠ f y)
  simp only [admit_readout_eq_true_iff P]

abbrev anchoredSeparationSignature (X Y Z : Type) [DecidableEq Y] [DecidableEq Z] :
    PrimitiveSignature X where
  Index := Fin 4
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output | 0 => Y | 1 => Z | 2 => Bool | 3 => Bool
  outputDecidableEq | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance | 3 => inferInstance
  axis := fun i => if i < 2 then .cut else .admit
  readoutAxisNotAnchor := by intro i; split <;> simp
  AnchorIndex := Bool
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def anchoredSeparationRealization {X Y Z : Type} [DecidableEq Y] [DecidableEq Z]
    (f : X → Y) (g : X → Z) (P Q : X → Prop) [DecidablePred P] [DecidablePred Q]
    (a b : X) : PrimitiveRealization (anchoredSeparationSignature X Y Z) where
  readout | 0 => f | 1 => g | 2 => fun x => decide (P x) | 3 => fun x => decide (Q x)
  anchor | false => a | true => b

/-- Anchored separation with ADMIT witnesses and no recovery map (one gold consumer). -/
def anchoredSeparationArena (A : Arena) (Y Z : Type) [DecidableEq Y] [DecidableEq Z] :
    PrimitiveLawArena where
  toArena := A
  signature := anchoredSeparationSignature A.State Y Z
  Law := fun r => r.readout 2 (r.anchor false) = true ∧ r.readout 3 (r.anchor true) = true ∧
    r.readout 0 (r.anchor false) = r.readout 0 (r.anchor true) ∧
    r.readout 1 (r.anchor false) ≠ r.readout 1 (r.anchor true) ∧
    ¬ ∃ recover : Y → Z, r.readout 1 = recover ∘ r.readout 0

theorem anchoredSeparationLegacy (A : Arena) {Y Z : Type} [DecidableEq Y] [DecidableEq Z]
    (f : A.State → Y) (g : A.State → Z) (P Q : A.State → Prop)
    [DecidablePred P] [DecidablePred Q] (a b : A.State) :
    LegacyPrimitiveRealization (anchoredSeparationArena A Y Z)
      (P a ∧ Q b ∧ f a = f b ∧ g a ≠ g b ∧ ¬ ∃ recover : Y → Z, g = recover ∘ f)
      (anchoredSeparationRealization f g P Q a b) := by
  refine ⟨?_⟩
  simp only [anchoredSeparationArena, anchoredSeparationRealization,
    admit_readout_eq_true_iff P, admit_readout_eq_true_iff Q]

abbrev contextSelectionSignature (X Y Z : Type) [DecidableEq Y] [DecidableEq Z] :
    PrimitiveSignature X where
  Index := Fin 7
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output | 0 => Y | 1 => Z | 2 => Bool | 3 => Bool | 4 => Bool | 5 => Bool | 6 => Bool
  outputDecidableEq
    | 0 => inferInstance | 1 => inferInstance | 2 => inferInstance
    | 3 => inferInstance | 4 => inferInstance | 5 => inferInstance | 6 => inferInstance
  axis := fun i => if i < 5 then .cut else .admit
  readoutAxisNotAnchor := by intro i; split <;> simp
  AnchorIndex := Bool
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def contextSelectionRealization {X Y Z : Type} [DecidableEq Y] [DecidableEq Z]
    (f : X → Y) (g : X → Z) (p q s : X → Bool) (P Q : X → Prop)
    [DecidablePred P] [DecidablePred Q] (a b : X) :
    PrimitiveRealization (contextSelectionSignature X Y Z) where
  readout
    | 0 => f | 1 => g | 2 => p | 3 => q | 4 => s
    | 5 => fun x => decide (P x) | 6 => fun x => decide (Q x)
  anchor | false => a | true => b

/-- Two shared readouts, three varying parameters, and two anchored ADMITS.
This conjunction helper currently has one gold consumer. -/
def contextSelectionArena (A : Arena) (Y Z : Type) [DecidableEq Y] [DecidableEq Z] :
    PrimitiveLawArena where
  toArena := A
  signature := contextSelectionSignature A.State Y Z
  Law := fun r => r.readout 0 (r.anchor false) = r.readout 0 (r.anchor true) ∧
    r.readout 1 (r.anchor false) = r.readout 1 (r.anchor true) ∧
    r.readout 2 (r.anchor false) ≠ r.readout 2 (r.anchor true) ∧
    r.readout 3 (r.anchor false) ≠ r.readout 3 (r.anchor true) ∧
    r.readout 4 (r.anchor false) ≠ r.readout 4 (r.anchor true) ∧
    r.readout 5 (r.anchor false) = true ∧ r.readout 6 (r.anchor true) = true ∧
    (r.readout 2 (r.anchor false), r.readout 3 (r.anchor false), r.readout 4 (r.anchor false)) ≠
    (r.readout 2 (r.anchor true), r.readout 3 (r.anchor true), r.readout 4 (r.anchor true))

theorem contextSelectionLegacy (A : Arena) {Y Z : Type} [DecidableEq Y] [DecidableEq Z]
    (f : A.State → Y) (g : A.State → Z) (p q s : A.State → Bool) (P Q : A.State → Prop)
    [DecidablePred P] [DecidablePred Q] (a b : A.State) :
    LegacyPrimitiveRealization (contextSelectionArena A Y Z)
      (f a = f b ∧ g a = g b ∧ p a ≠ p b ∧ q a ≠ q b ∧ s a ≠ s b ∧ P a ∧ Q b ∧
        (p a, q a, s a) ≠ (p b, q b, s b))
      (contextSelectionRealization f g p q s P Q a b) := by
  refine ⟨?_⟩
  simp only [contextSelectionArena, contextSelectionRealization,
    admit_readout_eq_true_iff P, admit_readout_eq_true_iff Q]

end D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

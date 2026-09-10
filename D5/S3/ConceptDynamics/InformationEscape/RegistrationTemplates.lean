/- GID: D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/RegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Typed registration constructors generate primitive inventories and realization-dependent laws on explicit canonical arenas. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
import D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

/- The canonical arena is an explicit input. No constructor accepts a Law or a
bundle. Changing a readout changes the generated Law's argument, not its syntax.
Search receipt: TheoremUnit's compiler and ADMIT reflection; Mathlib's Bijective
API. These are presentation constructors, not new proofs of bijection facts.
The library has one reused template (separation, two causal golds) and eight
single-consumer helpers; twoStep retains the binary protocol and minimum costs. -/

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

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open D5.S3.ConceptDynamics.Sufficiency.MinimalPredictiveCompletionQuotient

abbrev exactDesignSignature (X : Type) : PrimitiveSignature X where
  Index := Fin 2
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def exactDesignRealization {X : Type} (f g : X → Bool) :
    PrimitiveRealization (exactDesignSignature X) :=
  ⟨fun i => if i = 0 then f else g, Fin.elim0⟩

/-- Single-consumer helper: individually insufficient readouts with a minimal joint experiment. -/
def exactDesignArena (A : Arena) : PrimitiveLawArena where
  toArena := A
  signature := exactDesignSignature A.State
  Law := fun r =>
    (∀ e : Bool, ¬ Function.Injective (fun x => if e then r.readout 1 x else r.readout 0 x)) ∧
    Function.Injective (jointReadout (fun e : Bool => if e then r.readout 1 else r.readout 0)) ∧
    ∀ selected : Finset Bool,
      Function.Injective (jointReadout (fun e : {e // e ∈ selected} =>
        if e.1 then r.readout 1 else r.readout 0)) → selected = {false, true}

theorem exactDesignLegacy (A : Arena) (f g : A.State → Bool) :
    LegacyPrimitiveRealization (exactDesignArena A)
      ((∀ e : Bool, ¬ Function.Injective (fun x => if e then g x else f x)) ∧
        Function.Injective (jointReadout (fun e : Bool => if e then g else f)) ∧
        ∀ selected : Finset Bool,
          Function.Injective (jointReadout (fun e : {e // e ∈ selected} =>
            if e.1 then g else f)) → selected = {false, true})
      (exactDesignRealization f g) := ⟨Iff.rfl⟩

abbrev completionExchangeSignature (X Y : Type) [DecidableEq X] [DecidableEq Y] :
    PrimitiveSignature X where
  Index := Option Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output | none => Y | some _ => X
  outputDecidableEq := by intro i; cases i <;> infer_instance
  axis | none => .cut | some _ => .flow
  readoutAxisNotAnchor := by intro i; cases i <;> simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def completionExchangeRealization {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (F G : X → X) (f : X → Y) : PrimitiveRealization (completionExchangeSignature X Y) where
  readout | none => f | some false => F | some true => G
  anchor := Fin.elim0

/-- Single-consumer helper; the unbounded completion operation is reused verbatim. -/
def completionExchangeArena (A : Arena) (Y : Type) [DecidableEq Y] : PrimitiveLawArena := by
  letI := A.stateDecidableEq
  exact {
    toArena := A
    signature := completionExchangeSignature A.State Y
    Law := fun r => ¬ Function.Commute (r.readout (some false)) (r.readout (some true)) ∧
      ¬ KernelEquivalent
        (predictiveProjection (r.readout (some false))
          (predictiveProjection (r.readout (some true)) (r.readout none)))
        (predictiveProjection (r.readout (some true))
          (predictiveProjection (r.readout (some false)) (r.readout none))) }

theorem completionExchangeLegacy (A : Arena) {Y : Type} [DecidableEq Y]
    (F G : A.State → A.State) (f : A.State → Y) :
    letI := A.stateDecidableEq
    LegacyPrimitiveRealization (completionExchangeArena A Y)
      (¬ Function.Commute F G ∧ ¬ KernelEquivalent
        (predictiveProjection F (predictiveProjection G f))
        (predictiveProjection G (predictiveProjection F f)))
      (@completionExchangeRealization A.State Y A.stateDecidableEq _ F G f) := ⟨Iff.rfl⟩

abbrev scopeTableSignature (X : Type) : PrimitiveSignature X where
  Index := Fin 3
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .admit
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def scopeTableRealization {X : Type} (P Q R : X → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] :
    PrimitiveRealization (scopeTableSignature X) where
  readout | 0 => fun x => decide (P x) | 1 => fun x => decide (Q x) | 2 => fun x => decide (R x)
  anchor := Fin.elim0

/-- Single-consumer helper: matching local marginals with no joint admitted state.
Coordinates are explicit semantic input, not additional primitive readouts. -/
def scopeTableArena (A : Arena) (first middle last : A.State → Bool) : PrimitiveLawArena where
  toArena := A
  signature := scopeTableSignature A.State
  Law := fun r =>
    (∀ b, (∃ x, r.readout 0 x = true ∧ middle x = b) ↔ (∃ x, r.readout 1 x = true ∧ middle x = b)) ∧
    (∀ b, (∃ x, r.readout 0 x = true ∧ first x = b) ↔ (∃ x, r.readout 2 x = true ∧ first x = b)) ∧
    (∀ b, (∃ x, r.readout 1 x = true ∧ last x = b) ↔ (∃ x, r.readout 2 x = true ∧ last x = b)) ∧
    ¬ ∃ x, r.readout 0 x = true ∧ r.readout 1 x = true ∧ r.readout 2 x = true

theorem scopeTableLegacy (A : Arena) (first middle last : A.State → Bool)
    (P Q R : A.State → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] :
    LegacyPrimitiveRealization (scopeTableArena A first middle last)
      ((∀ b, (∃ x, P x ∧ middle x = b) ↔ (∃ x, Q x ∧ middle x = b)) ∧
        (∀ b, (∃ x, P x ∧ first x = b) ↔ (∃ x, R x ∧ first x = b)) ∧
        (∀ b, (∃ x, Q x ∧ last x = b) ↔ (∃ x, R x ∧ last x = b)) ∧
        ¬ ∃ x, P x ∧ Q x ∧ R x) (scopeTableRealization P Q R) := by
  refine ⟨?_⟩
  simp only [scopeTableArena, scopeTableRealization,
    admit_readout_eq_true_iff P, admit_readout_eq_true_iff Q, admit_readout_eq_true_iff R]

open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification

/- Single-consumer helper family: finite arenas and sensor types are parameters.
Only two_step_adaptive_residue_identification consumes this two-step protocol shape.
The source predicates and BinaryProtocol are reused; dif_pos transports Nat.find. -/
def binaryFamilySignature (X Sensor : Type) [Fintype Sensor] [DecidableEq Sensor] :
    PrimitiveSignature X where
  Index := Sensor
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def binaryFamilyRealization {X Sensor : Type} [Fintype Sensor] [DecidableEq Sensor]
    (r : Sensor → X → Bool) : PrimitiveRealization (binaryFamilySignature X Sensor) :=
  ⟨r, Fin.elim0⟩

noncomputable def firstSuccess (P : Nat → Prop) : Nat := by
  classical
  exact if h : ∃ n, P n then Nat.find h else 0

theorem firstSuccess_eq_find {P : Nat → Prop} (h : ∃ n, P n) :
    firstSuccess P = @Nat.find P (Classical.decPred P) h := by
  classical
  exact dif_pos h

def twoStepStatement {X Sensor : Type} (first low high : Sensor) (a b c d : X)
    (r : Sensor → X → Bool) (adaptive static : Nat) : Prop :=
  (∀ x, r first x = false ↔ x = a ∨ x = b) ∧
  (∀ x, r first x = true ↔ x = c ∨ x = d) ∧
  (∃ protocol : BinaryProtocol X 2,
    (∀ history : Fin 0 → Bool, protocol.question ⟨0, by decide⟩ history = r first) ∧
    (∀ history : Fin 1 → Bool, protocol.question ⟨1, by decide⟩ history =
      if history 0 then r high else r low) ∧
    UsesReadoutFamily r protocol ∧ Function.Injective protocol.transcript) ∧
  (∀ sensor, ¬ Function.Injective (r sensor)) ∧
  (∀ depth, depth < 2 → ¬ ExactAtDepth r depth) ∧
  adaptive = 2 ∧ static = 3 ∧ adaptive < static

def twoStepArena (A : Arena) (Sensor : Type) [Fintype Sensor] [DecidableEq Sensor]
    (first low high : Sensor) (a b c d : A.State) : PrimitiveLawArena where
  toArena := A
  signature := binaryFamilySignature A.State Sensor
  Law := fun r => twoStepStatement first low high a b c d r.readout
    (firstSuccess (ExactAtDepth r.readout)) (firstSuccess (StaticExactAtCardinality r.readout))

theorem twoStepLegacy (A : Arena) {Sensor : Type} [Fintype Sensor] [DecidableEq Sensor]
    (first low high : Sensor) (a b c d : A.State) (r : Sensor → A.State → Bool)
    (ha : ∃ n, ExactAtDepth r n) (hs : ∃ n, StaticExactAtCardinality r n) :
    LegacyPrimitiveRealization (twoStepArena A Sensor first low high a b c d)
      (twoStepStatement first low high a b c d r
        (@Nat.find _ (Classical.decPred _) ha) (@Nat.find _ (Classical.decPred _) hs))
      (binaryFamilyRealization r) := by
  refine ⟨?_⟩
  change _ ↔ twoStepStatement first low high a b c d r
    (firstSuccess (ExactAtDepth r)) (firstSuccess (StaticExactAtCardinality r))
  rw [firstSuccess_eq_find ha, firstSuccess_eq_find hs]


#print axioms firstSuccess_eq_find
#print axioms twoStepLegacy
#print axioms bijectiveLegacy
#print axioms separationLegacy
#print axioms admittedSurjectionLegacy
#print axioms anchoredSeparationLegacy
#print axioms contextSelectionLegacy
#print axioms exactDesignLegacy
#print axioms completionExchangeLegacy
#print axioms scopeTableLegacy

end D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

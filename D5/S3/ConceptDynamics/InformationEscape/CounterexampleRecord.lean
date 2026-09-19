/- GID: D5/S3/ConceptDynamics/InformationEscape/CounterexampleRecord
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/CounterexampleRecord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite predicate witnesses support universal refutations and reverse bridges. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord

open RegistrationTemplates LeanInformationAudit

/-- A finite carrier checks a predicate at selected points of its quantifier domain.
The signature and law are derived below, so an author cannot override either.
The decision family may use `Decidable.isFalse h` for a kernel-checked local failure. -/
structure WitnessArena extends Arena.{0} where
  Domain : Type
  predicate : Domain → Prop
  embed : State → Domain
  decision : ∀ w, Decidable (predicate (embed w))

/-- The witness readout has one Boolean CUT and no anchors. -/
def WitnessArena.signature (a : WitnessArena) := cutSignature a.State Bool

/-- The selected realization fails at some point of the finite carrier. -/
def WitnessArena.Law (a : WitnessArena) (r : PrimitiveRealization a.signature) : Prop :=
  ∃ w, r.readout () w = false

/-- Expose the fixed signature and law on the underlying finite arena. -/
def WitnessArena.toPrimitiveLawArena (a : WitnessArena) : PrimitiveLawArena.{0,0,0} where
  toArena := a.toArena
  signature := a.signature
  Law := a.Law

/-- Build a witness arena from a finite carrier and its per-point predicate decisions. -/
def WitnessArena.ofCarrier (W D : Type) [Fintype W] [DecidableEq W]
    (predicate : D → Prop) (embed : W → D)
    (decision : ∀ w, Decidable (predicate (embed w))) : WitnessArena where
  toArena := Arena.ofFintype W
  Domain := D
  predicate := predicate
  embed := embed
  decision := decision

/-- Strengthen the arena with an infinite quantifier domain and an injective embedding. -/
structure StrictWitnessArena extends WitnessArena where
  domainInfinite : Infinite Domain
  embedInjective : Function.Injective embed

instance instCoeWitnessArena : Coe StrictWitnessArena WitnessArena :=
  ⟨StrictWitnessArena.toWitnessArena⟩

/-- Compute the predicate at the embedded point using its stored decision. -/
def WitnessArena.check (a : WitnessArena) (w : a.State) : Bool :=
  @decide (a.predicate (a.embed w)) (a.decision w)

/-- The enrolled template takes an abstract check, as in
`readout via (@counterexampleRealization W check)`. -/
def counterexampleRealization {State : Type} (check : State → Bool) :
    PrimitiveRealization (cutSignature State Bool) := cutRealization check

register_information_template counterexampleRealization

/-- The arena-computed realization supplies the definitional tie for a selected check. -/
def WitnessArena.realization (a : WitnessArena) : PrimitiveRealization a.signature :=
  cutRealization a.check

/-- A reverse bridge derives the statement from the law of the selected actual realization. -/
structure WitnessPrimitiveRealization (a : WitnessArena) (statement : Prop)
    (actual : PrimitiveRealization a.signature) : Prop where
  backward : a.Law actual → statement

/-- A failed predicate check refutes the universal claim over the quantifier domain.
This Prop-valued definition is a generic record obligation, not an authored corpus theorem. -/
def WitnessArena.law_refutes (a : WitnessArena) :
    a.Law a.realization → ¬ ∀ d, a.predicate d := by
  rintro ⟨w, hw⟩ hall
  let _ := a.decision w
  have htrue : @decide (a.predicate (a.embed w)) (a.decision w) = true :=
    (decide_eq_true_eq).mpr (hall (a.embed w))
  exact Bool.false_ne_true (hw.symm.trans htrue)

/-- A comparison realization whose readout never fails. -/
def WitnessArena.constantTrue (a : WitnessArena) : PrimitiveRealization a.signature :=
  cutRealization (fun _ => true)

/-- Variation retains the law of the selected actual realization and rejects constant true.
This Prop-valued definition is a generic record obligation, not an authored corpus theorem. -/
def WitnessArena.variation (a : WitnessArena) {actual : PrimitiveRealization a.signature}
    (h : a.Law actual) : a.Law actual ∧ ¬ a.Law a.constantTrue := by
  refine ⟨h, ?_⟩
  rintro ⟨w, hw⟩
  exact Bool.noConfusion hw

/-- The selected failure and constant true witness sensitivity of the single CUT slot.
This Prop-valued definition is a generic record obligation, not an authored corpus theorem. -/
def WitnessArena.sensitivity (a : WitnessArena) {actual : PrimitiveRealization a.signature}
    (h : a.Law actual) : FiniteSlotSensitivity a.toPrimitiveLawArena := by
  constructor
  · intro i
    refine ⟨actual, a.constantTrue, ?_, ?_, ?_⟩
    · intro j ne; cases i; cases j; exact (ne rfl).elim
    · intro j; exact Fin.elim0 j
    · exact ⟨fun _ => (a.variation h).2, fun _ => h⟩
  · intro i; exact Fin.elim0 i

/-- Reify the reverse bridge with a law witness and the actual realization's compiled bundle.
This is the record's defining conversion; its proof is obtained from `bridge.backward h`. -/
def WitnessPrimitiveRealization.toTheoremUnit {a : WitnessArena} {statement : Prop}
    {actual : PrimitiveRealization a.signature}
    (bridge : WitnessPrimitiveRealization a statement actual)
    (h : a.Law actual) : TheoremUnit a.toArena := by
  letI := a.stateDecidableEq
  exact
    { primitives := actual.toPrimitiveBundle
      Statement := statement
      proof := bridge.backward h }

#print axioms WitnessArena.law_refutes
#print axioms WitnessArena.constantTrue
#print axioms WitnessArena.variation
#print axioms WitnessArena.sensitivity
#print axioms WitnessPrimitiveRealization.toTheoremUnit

end D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord

import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

namespace LeanInformationAudit.Tests.DeclaredProofIrrelevance
open Lean Meta Elab Command TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

-- Expectations are fixed before observation. Only bound proofs differ.
def termBound {X : Type} : PrimitiveRealization (cutSignature X (Fin 4)) :=
  cutRealization (fun _ => ⟨Nat.zero, (let h : Nat.lt Nat.zero 4 := Nat.zero_lt_succ 3; h)⟩)
def omegaBound {X : Type} : PrimitiveRealization (cutSignature X (Fin 4)) :=
  cutRealization (fun _ => ⟨Nat.zero, (let h : Nat.lt Nat.zero 4 := (by change 0 < 4; omega); h)⟩)
def decideBound {X : Type} : PrimitiveRealization (cutSignature X (Fin 4)) :=
  cutRealization (fun _ => ⟨Nat.zero, (let h : Nat.lt Nat.zero 4 := (by change 0 < 4; decide); h)⟩)

-- Isolate the constructor's implicit cardinality from the bound proposition.
def constructorCardinality {X : Type} : PrimitiveRealization (cutSignature X (Fin 4)) :=
  cutRealization (fun _ => @Fin.mk 4 Nat.zero (Nat.zero_lt_succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
def propositionNumeral {X : Type} : PrimitiveRealization (cutSignature X (Fin 4)) :=
  cutRealization (fun _ => @Fin.mk (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) Nat.zero
    (let h : Nat.lt 0 4 := (by change 0 < 4; decide); h))
def ltPropositionNumeral {X : Type} : PrimitiveRealization (cutSignature X (Fin 4)) :=
  cutRealization (fun _ => @Fin.mk (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) Nat.zero
    (let h : 0 < 4 := (by decide); h))
def valueNumeral {X : Type} : PrimitiveRealization (cutSignature X (Fin 4)) :=
  cutRealization (fun _ => ⟨0, by decide⟩)

def eqTransport {X : Type} (x y : Bool) (h : x = y) :
    PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun _ => @Eq.rec Bool x (fun _ _ => Bool) x y h)
def falseElimination {X : Type} (h : False) : PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun _ => False.elim h)
def absurdData {X : Type} (h : True) (hn : ¬True) : PrimitiveRealization (cutSignature X Bool) :=
  cutRealization (fun _ => absurd h hn)

elab "observe_proof_irrelevance_enrollment" : command => do
  let cases : Array (String × Name × Option String) := #[
    ("fin_term_bound", ``termBound, none),
    ("fin_omega_bound", ``omegaBound, none),
    ("fin_decide_bound", ``decideBound, none),
    ("constructor_cardinality_type_position", ``constructorCardinality, none),
    ("proof_nat_lt_numeral", ``propositionNumeral, none),
    ("proof_lt_numeral", ``ltPropositionNumeral, none),
    ("fin_value_numeral_rejected", ``valueNumeral, some "unclassified_form:E3.index_encoding:OfNat.ofNat"),
    ("proof_eq_transport_rejected", ``eqTransport, some "unclassified_form:E4.recursion:Eq.rec"),
    ("proof_false_elim_rejected", ``falseElimination, some "unclassified_form:E4.recursion:False.rec"),
    ("proof_absurd_data_rejected", ``absurdData, some "unclassified_form:E4.recursion:False.rec")]
  for (label, name, expected) in cases do
    let saved ← get
    let result ← enroll name
    let actual := match result with | .ok () => none | .error text => some text
    let present := (selectedPlan (← getEnv) name).isOk
    set saved
    let ok := actual == expected && present == expected.isNone
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label} result={repr actual}"

observe_proof_irrelevance_enrollment

end LeanInformationAudit.Tests.DeclaredProofIrrelevance

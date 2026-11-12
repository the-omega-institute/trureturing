import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion

set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
open D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion

abbrev comparisonSignature : Signature where
  Params := Unit
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization comparisonSignature :=
  realize comparisonSignature (fun _ _ x => decide (x.1 ≤ x.2)) (fun e => nomatch e)
def rejected : Realization comparisonSignature :=
  realize comparisonSignature (fun _ _ _ => false) (fun e => nomatch e)

/-- The full original telescope and its exact two arithmetic operands. -/
abbrev paddedArena : Arena where
  signature := comparisonSignature
  Law R := ∀ m k : ℕ, R.readout () () (count m * count k, count (m + k + 6)) = true

/-- Typed reconstruction, whole-family variation, sensitivity and real observational dependence. -/
def paddedFamily : Registration paddedArena (type_of% count_padded_supermultiplicative) := by
  have bridge : (type_of% count_padded_supermultiplicative) ↔ paddedArena.Law actual := by
    simp only [paddedArena, actual, realize, decide_eq_true_eq]
  have hp : paddedArena.Law actual := bridge.mp count_padded_supermultiplicative
  have hn : ¬paddedArena.Law rejected := by
    intro h
    have he : false = true := h 0 0
    cases he
  refine { actual := actual, bridge := bridge, variation := ⟨hp, rejected, hn⟩,
    sensitivity := ?_, dependence := ?_ }
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, hn⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  · intro i
    exact ⟨(), (0, 0), (1, 0), by norm_num [actual, realize]⟩

/-- An attempted faithful contract. Raw source-selection binding is explicitly pending;
this declaration alone is not a declared_validated status. -/
def paddedAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@count_padded_supermultiplicative) (Realization comparisonSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion.paddedUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion.paddedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨paddedArena⟩
  objectArena := .source ⟨paddedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source paddedArena ⟨paddedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize comparisonSignature actual.readout actual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]


abbrev certificateSignature : Signature where
  Params := Unit
  State _ := Σ n : ℕ, Word n × (Fin n → ℤ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def certificateActual : Realization certificateSignature :=
  realize certificateSignature (fun _ _ x => decide (Certificate x.2.1 x.2.2))
    (fun e => nomatch e)
def certificateRejected : Realization certificateSignature :=
  realize certificateSignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev certificateArena : Arena where
  signature := certificateSignature
  Law R := ∀ {m k : ℕ} (w : CertifiedWord m) (v : CertifiedWord k),
    R.readout () () ⟨m + k + 6, paddedWord w v, paddedOffset w v⟩ = true

def certificateFamily : Registration certificateArena (type_of% padded_certificate) := by
  have bridge : (type_of% padded_certificate) ↔ certificateArena.Law certificateActual := by
    simp only [certificateArena, certificateActual, realize, decide_eq_true_eq]
  have hp : certificateArena.Law certificateActual := bridge.mp padded_certificate
  have hn : ¬certificateArena.Law certificateRejected := by
    intro h
    let z : CertifiedWord 0 := ⟨Fin.elim0, Fin.elim0, by
      constructor <;> intro i <;> exact Fin.elim0 i⟩
    have he : false = true := h z z
    cases he
  refine { actual := certificateActual, bridge := bridge,
    variation := ⟨hp, certificateRejected, hn⟩, sensitivity := ?_, dependence := ?_ }
  · constructor
    · intro i
      refine ⟨certificateRejected, ?_, rfl, hn⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  · intro i
    let w : Word 1 := fun _ => Equiv.refl _
    have ht : Certificate w (fun _ => 0) := by
      constructor
      · intro j; norm_num
      · intro j k h; exact (h rfl).elim
      · intro j k h; exact (h rfl).elim
      · intro j k hj; have := j.isLt; have := k.isLt; omega
    have hf : ¬Certificate w (fun _ => 3) := by
      intro h
      have hb := h.bounded 0
      norm_num at hb
    exact ⟨(), ⟨1, w, fun _ => 0⟩, ⟨1, w, fun _ => 3⟩, by
      simp [certificateActual, realize, ht, hf]⟩

/-- Full concrete-certificate telescope; source-selection binding remains absent. -/
def certificateAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@padded_certificate) (Realization certificateSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion.certificateUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion.certificateFamily
  realizationSource := none
  generated := false
  arena := .source ⟨certificateArena⟩
  objectArena := .source ⟨certificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source certificateArena ⟨certificateFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize certificateSignature certificateActual.readout certificateActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms certificateFamily
#print axioms certificateAudit

#print axioms paddedFamily
#print axioms paddedAudit
end Reg.D5.S3.Combinatorics.Graph.Roommates.PaddedCompletion

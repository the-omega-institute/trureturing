import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Roommates.TriangleCount

set_option autoImplicit false
noncomputable section
open scoped Classical
open D5.S3.Combinatorics.Graph.Roommates.OpenCertificates
open D5.S3.Combinatorics.Graph.Roommates.TriangleCount
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Graph.Roommates.TriangleCount

abbrev comparisonSignature : Signature where
  Params := Bool
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization comparisonSignature := realize comparisonSignature
  (fun b _ x => if b then decide (x.1 = x.2) else decide (x.1 ≤ x.2)) (fun e => nomatch e)
def rejected : Realization comparisonSignature :=
  realize comparisonSignature (fun _ _ _ => false) (fun e => nomatch e)

abbrev countArena : Arena where
  signature := comparisonSignature
  Law R := R.readout false () (count 3, 13808) = true
abbrev cardArena : Arena where
  signature := comparisonSignature
  Law R := R.readout true () (forbiddenProfiles.card, 16) = true

def countFamily : Registration countArena (type_of% count_three_bound) := by
  have bridge : (type_of% count_three_bound) ↔ countArena.Law actual := by
    simp [countArena, actual, realize]
  have hp := bridge.mp count_three_bound
  have hn : ¬countArena.Law rejected := by simp [countArena, rejected, realize]
  refine { actual := actual, bridge := bridge, variation := ⟨hp, rejected, hn⟩,
    sensitivity := ?_, dependence := ?_ }
  · constructor
    · intro i; refine ⟨rejected, ?_, rfl, hn⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  · intro i; exact ⟨false, (0, 0), (1, 0), by norm_num [actual, realize]⟩

def cardFamily : Registration cardArena (type_of% forbidden_card) := by
  have bridge : (type_of% forbidden_card) ↔ cardArena.Law actual := by
    simp [cardArena, actual, realize]
  have hp := bridge.mp forbidden_card
  have hn : ¬cardArena.Law rejected := by simp [cardArena, rejected, realize]
  refine { actual := actual, bridge := bridge, variation := ⟨hp, rejected, hn⟩,
    sensitivity := ?_, dependence := ?_ }
  · constructor
    · intro i; refine ⟨rejected, ?_, rfl, hn⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  · intro i; exact ⟨true, (0, 0), (1, 0), by norm_num [actual, realize]⟩

abbrev wordSignature : Signature where
  Params := Bool × (Fin 3 → Bool)
  State _ := Word 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def wordActual : Realization wordSignature := realize wordSignature
  (fun _ _ w => decide (¬∃ d, Certificate w d)) (fun e => nomatch e)
def wordRejected : Realization wordSignature :=
  realize wordSignature (fun _ _ _ => false) (fun e => nomatch e)
abbrev wordArena : Arena where
  signature := wordSignature
  Law R := ∀ s, R.readout s () (forbiddenWord s) = true

def wordFamily : Registration wordArena (type_of% forbidden_not_certified) := by
  have bridge : (type_of% forbidden_not_certified) ↔ wordArena.Law wordActual := by
    simp [wordArena, wordActual, realize]
  have hp := bridge.mp forbidden_not_certified
  have hn : ¬wordArena.Law wordRejected := by
    simp [wordArena, wordRejected, realize]
  have hg : Nonempty (CertifiedWord 3) := Fintype.card_pos_iff.mp
    (lt_of_lt_of_le (by norm_num : 0 < 6 ^ 3) (count_lower 3))
  let good : CertifiedWord 3 := Classical.choice hg
  refine { actual := wordActual, bridge := bridge, variation := ⟨hp, wordRejected, hn⟩,
    sensitivity := ?_, dependence := ?_ }
  · constructor
    · intro i; refine ⟨wordRejected, ?_, rfl, hn⟩
      intro j hj; exact (hj (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  · intro i
    refine ⟨(false, fun _ => false), forbiddenWord (false, fun _ => false), good.val, ?_⟩
    have hgood := good.property
    simp [wordActual, realize, forbidden_not_certified, hgood]

/-- Typed reconstruction and variation; native source-selection binding remains unverified. -/
def countAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@count_three_bound) (Realization comparisonSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Roommates.TriangleCount.countUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Roommates.TriangleCount.countFamily
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨countFamily⟩
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

#print axioms countFamily
#print axioms countAudit

/-- Typed reconstruction and variation; native source-selection binding remains unverified. -/
def cardAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@forbidden_card) (Realization comparisonSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Roommates.TriangleCount.cardUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Roommates.TriangleCount.cardFamily
  realizationSource := none
  generated := false
  arena := .source ⟨cardArena⟩
  objectArena := .source ⟨cardArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cardArena ⟨cardFamily⟩
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

#print axioms cardFamily
#print axioms cardAudit

/-- Typed reconstruction and variation; native source-selection binding remains unverified. -/
def wordAudit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@forbidden_not_certified) (Realization wordSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Roommates.TriangleCount.wordUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Roommates.TriangleCount.wordFamily
  realizationSource := none
  generated := false
  arena := .source ⟨wordArena⟩
  objectArena := .source ⟨wordArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source wordArena ⟨wordFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize wordSignature wordActual.readout wordActual.anchor)
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms wordFamily
#print axioms wordAudit

end Reg.D5.S3.Combinatorics.Graph.Roommates.TriangleCount

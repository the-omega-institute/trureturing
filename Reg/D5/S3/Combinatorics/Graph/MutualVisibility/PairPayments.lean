import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.MutualVisibility.PairPayments
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility
universe u
namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.PairPayments

abbrev budgetSignature : Signature where
  Params := Sigma fun V : Type u => Fintype V × DecidableEq V × SimpleGraph V
  State p := Finset (@Configuration p.1 p.2.2.1 p.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def budgetActual : Realization budgetSignature :=
  realize budgetSignature (fun _ _ C => C.card) (fun e => nomatch e)

abbrev budgetArena : Arena where
  signature := budgetSignature
  Law r := ∀ p, letI := p.2.1; letI := p.2.2.1;
    ∀ (C : Finset (Configuration p.2.2.2)) (B Y : Finset p.1), Disjoint Y B →
    ∀ (F : Finset (Configuration p.2.2.2)), F ⊆ C →
    Disjoint F (C.filter fun T => T.val ⊆ B) →
    (∀ y ∈ Y, Disjoint F (localCutClass C B y)) →
    (C.filter fun T => T.val ⊆ B).card +
      (∑ y ∈ Y, (localCutClass C B y).card) + F.card ≤ r.readout () p C

def budgetEvidence : Registration budgetArena (type_of% (@joint_cut_budget.{u})) where
  actual := budgetActual
  bridge := by
    constructor
    · intro h p C B Y hY F hFC hFI hFL
      exact @h p.1 p.2.1 p.2.2.1 p.2.2.2 C B Y hY F hFC hFI hFL
    · intro h V fin inst H C B Y hY F hFC hFI hFL
      exact h ⟨V, fin, inst, H⟩ C B Y hY F hFC hFI hFL

noncomputable def budgetRegistration : Contract.Registration (@joint_cut_budget.{u})
    (type_of% budgetActual) (type_of% (@Finset.card)) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.joint_cut_budget,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.PairPayments.budgetEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨budgetArena⟩, objectArena := .source ⟨budgetArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source budgetArena ⟨budgetEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some budgetActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@Finset.card), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.PairPayments

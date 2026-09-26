import D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer
import Reg.Support.DependentFamily
import Mathlib.Data.Fintype.EquivFin

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer
open _root_.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => d ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original negative statement; only its cardinality readout varies. -/
abbrev arena : Arena where
  signature := signature
  Law r := ¬ ∀ (d : ℕ) (G : Type) [Group G] [Fintype G]
    (π : G → Matrix (Fin d) (Fin d) ℂ)
    (W : Submodule ℂ (EuclideanSpace ℂ (Fin d))),
    IsPEM π → Fintype.card G = r.readout () () d →
    (logicalOps π W).ncard * (stabilizers π W).ncard = Fintype.card G →
    ∀ g : G, ∀ s ∈ stabilizers π W, g * s * g⁻¹ ∈ stabilizers π W

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro d G group finite π W pem cardinality balance g s hs
  change Fintype.card G = 1 at cardinality
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp cardinality
  have equal : g * s * g⁻¹ = s := (hx _).trans (hx _).symm
  simpa only [equal] using hs

def registration : Registration arena
    (¬ _root_.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.claim) where
  actual := actual
  bridge := by rfl
  variation := ⟨_root_.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro ⟨⟩
    exact ⟨(), 1, 2, by decide⟩

register_information_theorem
  _root_.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.result in arena
  readout via (realize signature (fun _ _ d => d ^ 2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer
    «definition» := some {
      owner := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer
      name := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.claim
      path := #["arg"] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer

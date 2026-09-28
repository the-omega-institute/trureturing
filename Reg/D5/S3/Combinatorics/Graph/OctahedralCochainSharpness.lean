import D5.S3.Combinatorics.Graph.OctahedralCochainSharpness
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.OctahedralCochainSharpness
open _root_.D5.S3.Combinatorics.Graph.OctahedralCochainSharpness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Sig : Signature where
  Params := Unit
  State _ := Cochain
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization Sig := realize Sig (fun _ _ F => weight F) (fun e => Empty.elim e)
def rejected : Realization Sig := realize Sig (fun _ _ _ => 0) (fun e => Empty.elim e)

def arena : Arena where
  signature := Sig
  Law r :=
    Fintype.card Cube = 16 ∧ Fintype.card Face = 32 ∧
    Fintype.card ValidTriangle = 32 ∧
    Function.Bijective triangleAsValid ∧
    (∀ b : Cube, (tetraVertices b).card = 4 ∧
      ∀ i : Fin 4, triangleVertices (i, drop i b) ⊆ tetraVertices b) ∧
    weight path = 4 ∧ defects path = 2 ∧
    (∀ b : Cube, d2 path b ≠ 0 ↔
      b = (false, false, false, false) ∨ b = (true, true, true, true)) ∧
    (∀ e : EdgeCochain, 4 ≤ r.readout () () (path + d1 e))

theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have hf := h.2.2.2.2.2.2.2.2 (0 : EdgeCochain)
  simpa [rejected, realize] using hf

theorem dependence : ObservationalDependence Sig actual := by
  intro i
  refine ⟨(), (fun _ => 0), path, ?_⟩
  change weight (fun _ => 0) ≠ weight path
  rw [antipodal_repair_sharpness.2.2.2.2.2.1]
  simp [weight]

def registration : Registration arena (
    Fintype.card Cube = 16 ∧ Fintype.card Face = 32 ∧
    Fintype.card ValidTriangle = 32 ∧
    Function.Bijective triangleAsValid ∧
    (∀ b : Cube, (tetraVertices b).card = 4 ∧
      ∀ i : Fin 4, triangleVertices (i, drop i b) ⊆ tetraVertices b) ∧
    weight path = 4 ∧ defects path = 2 ∧
    (∀ b : Cube, d2 path b ≠ 0 ↔
      b = (false, false, false, false) ∨ b = (true, true, true, true)) ∧
    (∀ e : EdgeCochain, 4 ≤ weight (path + d1 e))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨antipodal_repair_sharpness, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejectedLaw⟩
      · intro j h
        cases i
        cases j
        exact (h rfl).elim
      · funext e
        exact nomatch e
    · intro i
      exact nomatch i
  dependence := dependence

register_information_theorem _root_.D5.S3.Combinatorics.Graph.OctahedralCochainSharpness.antipodal_repair_sharpness in arena
  readout via (realize Sig (fun _ _ F => weight F) (fun e => Empty.elim e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Combinatorics.Graph.OctahedralCochainSharpness
    coordinates := #[]
    readouts := #[{path := #["arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "arg"], stateOperand := some #["arg"]}]
  })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Combinatorics.Graph.OctahedralCochainSharpness

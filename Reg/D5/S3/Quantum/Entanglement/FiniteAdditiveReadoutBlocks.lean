import D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
open scoped Classical

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks

abbrev coefficientSignature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ x => (Real.sqrt x : ℂ)⁻¹) (fun e => nomatch e)

def coefficientRejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => 0) (fun e => nomatch e)

def coefficientArena : Arena where
  signature := coefficientSignature
  Law observation := ∀ {G A B : Type*} [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]
    [Fintype G] [Fintype A] [Fintype B] [DecidableEq G] [DecidableEq A] [DecidableEq B]
    (alpha : G →+ A) (beta : G →+ B)
    (_hpair : Function.Injective (fun x : G => (alpha x, beta x))) (a : A) (b : B),
    actualCoefficient alpha beta a b = observation.readout () () (Fintype.card G : ℝ) *
      ∑ q : BlockQuotient alpha beta,
        if leftBlock alpha beta q a ∧ rightBlock alpha beta q b then (1 : ℂ) else 0

theorem coefficientActualLaw : coefficientArena.Law coefficientActual := by
  intro G A B _ _ _ _ _ _ _ _ _ alpha beta hpair a b
  exact actual_coefficient_block alpha beta hpair a b

theorem coefficientRejectedLaw : ¬ coefficientArena.Law coefficientRejected := by
  intro h
  have hbad := h (G := PUnit) (A := PUnit) (B := PUnit) 0 0
    (by intro x y _; exact Subsingleton.elim x y) PUnit.unit PUnit.unit
  norm_num [coefficientRejected, realize, actualCoefficient] at hbad

theorem coefficientDependence : ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  cases i
  refine ⟨(), 1, 4, ?_⟩
  norm_num [coefficientActual, realize]

def coefficientRegistration : Registration coefficientArena
    (coefficientArena.Law coefficientActual) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨coefficientActualLaw, coefficientRejected, coefficientRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coefficientRejected, ?_, rfl, coefficientRejectedLaw⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := coefficientDependence

register_information_theorem actual_coefficient_block in coefficientArena
  readout via (realize coefficientSignature
    (fun _ _ x => (Real.sqrt x : ℂ)⁻¹) (fun e => nomatch e))
  realizes coefficientRegistration
  escape from source ({
    owner := `D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateOperand := some #["arg", "arg", "arg"] }] })
  escape continues (open)

#print axioms coefficientActualLaw
#print axioms coefficientRejectedLaw
#print axioms coefficientRegistration

end Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks

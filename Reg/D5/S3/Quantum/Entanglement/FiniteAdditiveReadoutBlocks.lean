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

#print axioms coefficientActualLaw
#print axioms coefficientRejectedLaw

end Reg.D5.S3.Quantum.Entanglement.FiniteAdditiveReadoutBlocks

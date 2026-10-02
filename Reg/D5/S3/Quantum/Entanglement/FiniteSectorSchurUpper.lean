import D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper
import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import Reg.Support.DependentFamily
import Reg.Support.FiniteSectorSingleton

open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open _root_.D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper
universe u

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => (x : ℂ)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Sector : Type u} [Fintype Sector] [DecidableEq Sector] {spectralSize : ℕ} [Nonempty Sector] (M : Model Sector spectralSize)
    (encoding : EncodingChannels M),
    ((Matrix.of fun s t => R.readout ⟨()⟩ () (kernel M s t)).PosSemidef ∧
      (∀ s, kernel M s s = 1) ∧ (∀ s t, kernel M s t ≤ 1)) ∧
    ∃ r : Sector → ℝ, r ∈ stdSimplex ℝ Sector ∧
      spectralMinimum M = ∑ s, ∑ t, r s * r t * kernel M s t ∧
      ∀ (C : QuantumChannel Sector (TargetLocal M.d × TargetLocal M.d)),
        (∀ X : Matrix Sector Sector ℂ,
          CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
            targetEncoding M.d * (Matrix.of fun s t => (kernel M s t : ℂ) * X s t) *
              (targetEncoding M.d)ᴴ) →
        diamondDistance C encoding.target ≤ 2 * (1 - spectralMinimum M)

theorem actual_law : arena.{u}.Law actual := by
  intro Sector _ _ spectralSize _ M encoding
  exact schur_upper M encoding

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let M := Reg.Support.FiniteSectorSingleton.model (ULift.{u} Unit)
  obtain ⟨encoding, _⟩ := physical_encoding M
  have hp := (h M encoding).1.1
  have hb := hp.diag_nonneg (i := (⟨()⟩ : ULift.{u} Unit))
  change (0 : ℂ) ≤ -1 at hb
  norm_num [Complex.le_def] at hb

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim (ULift.{u} Unit) _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

#print axioms registration

register_information_theorem schur_upper in arena
  readout via (realize signature.{u} (fun _ _ x => (x : ℂ)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper
    coordinates := #[]
    readouts := #[{path := #[ "body", "body", "body", "body", "body", "body", "body", "fn",
        "arg", "fn", "arg", "arg", "arg", "body", "body" ], stateOperand := some #["arg"]}] })
  escape continues (open)


end Reg.D5.S3.Quantum.Entanglement.FiniteSectorSchurUpper

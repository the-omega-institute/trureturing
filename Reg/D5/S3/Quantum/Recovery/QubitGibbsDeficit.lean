import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.QubitGibbsDeficit

/-! The scalar equality readout for the physical reducing Gibbs deficit. -/

noncomputable section
open LeanInformationAudit
open scoped CStarAlgebra BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.GibbsVariationalIdentity
open _root_.D5.S3.Quantum.Recovery.QubitGibbsDeficit

namespace Reg.D5.S3.Quantum.Recovery.QubitGibbsDeficit

universe u

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [Fintype E] [DecidableEq E] [Nonempty E]
    (B : Fin 2 → CStarMatrix E E ℂ) (hB : ∀ i, IsSelfAdjoint (B i))
    (ρ : DensityState (Fin 2 × E)),
    let g := fun i => Real.log (partitionFunction (B i))
    let m := max (g 0) (g 1)
    R.readout () () (m - gibbsValue B ρ)
      (conditionalLoss ρ (qubitBlockReference (blockGibbs B hB)) +
        ∑ i, (CStarMatrix.ofMatrix.symm (retainedMarginal ρ).1 i i).re * (m - g i))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let B : Fin 2 → CStarMatrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 0
  have hB (i : Fin 2) : IsSelfAdjoint (B i) := by simp [B, IsSelfAdjoint]
  exact h B hB (qubitBlockReference (blockGibbs B hB))

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh : ((0 : ℝ) = 0) = ((1 : ℝ) = 0) := congrFun h 0
  exact one_ne_zero (Eq.mp hh rfl)

def family : Registration arena.{u} (type_of% @reducing_qubit_gibbs_deficit.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reducing_qubit_gibbs_deficit.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reducing_qubit_gibbs_deficit.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.QubitGibbsDeficit.reducing_qubit_gibbs_deficit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.QubitGibbsDeficit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.QubitGibbsDeficit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace Argmax

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [Fintype E] [DecidableEq E] [Nonempty E]
    (B : Fin 2 → CStarMatrix E E ℂ) (hB : ∀ i, IsSelfAdjoint (B i)),
    let γ := blockGibbs B hB
    let g := fun i => Real.log (partitionFunction (B i))
    let m := max (g 0) (g 1)
    IsGreatest (Set.range (gibbsValue B)) m ∧
      (∀ i, g i = m →
        gibbsValue B (gibbsEndpoint B hB i) = m ∧
          CStarMatrix.ofMatrix.symm (retainedMarginal (gibbsEndpoint B hB i)).1 =
            Matrix.single i i 1) ∧
      ∀ ρ, let P := CStarMatrix.ofMatrix.symm (retainedMarginal ρ).1
        R.readout () () (gibbsValue B ρ) m ↔
          (∀ i, (P i i).re = 0 ∨ g i = m) ∧
          (CStarMatrix.ofMatrix.symm ρ.1 =
              retainedBlock (fun i => (P i i).re • CStarMatrix.ofMatrix.symm (γ i).1) ∨
            (γ 0 = γ 1 ∧ CStarMatrix.ofMatrix.symm ρ.1 =
              Matrix.kronecker P (CStarMatrix.ofMatrix.symm (γ 0).1)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let B : Fin 2 → CStarMatrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 0
  have hB (i : Fin 2) : IsSelfAdjoint (B i) := by simp [B, IsSelfAdjoint]
  obtain ⟨ρ, hρ⟩ := (reducing_qubit_gibbs_argmax B hB).1.1
  exact ((h B hB).2.2 ρ).mpr (((reducing_qubit_gibbs_argmax B hB).2.2 ρ).mp hρ)

def family : Registration arena.{u} (type_of% @reducing_qubit_gibbs_argmax.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@reducing_qubit_gibbs_argmax.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@reducing_qubit_gibbs_argmax.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.QubitGibbsDeficit.reducing_qubit_gibbs_argmax.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.QubitGibbsDeficit.Argmax.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.QubitGibbsDeficit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Argmax

end Reg.D5.S3.Quantum.Recovery.QubitGibbsDeficit

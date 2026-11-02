import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.DiamondSingletExclusion
import Reg.Support.DependentFamily

/-! Source-bound observation of the actual full zero-weight ground energy. -/

namespace Reg.D5.S3.Quantum.SpinChains.DiamondSingletExclusion

open _root_.D5.S3.Quantum.SpinChains.DiamondSingletExclusion
open _root_.D5.S3.Quantum.SpinChains.DiamondSpinBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => groundEnergy S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve the full telescope, all singlets and the entire ground eigenspace. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ S : ℕ, 1 ≤ S →
    (∀ v : EuclideanSpace ℂ (Fin 4 → Fin (2 * S + 1)),
      v.ofLp ∈ singletSpace S → ‖v‖ = 1 →
      singletLowerBound S ≤ (star v.ofLp ⬝ᵥ (hamiltonian S *ᵥ v.ofLp)).re) ∧
    R.readout () () S < singletLowerBound S ∧
    groundSpace S ⊓ singletSpace S = ⊥

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 (by norm_num)).2.1
  change (0 : ℝ) < singletLowerBound 1 at hbad
  norm_num [singletLowerBound] at hbad

/-- The actual observation varies even when restricted to positive spins. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 : ℝ) (|groundEnergy 1| + 1))
  have hNpos : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hN1 : 1 ≤ N := by exact_mod_cast hNpos.le
  have hlarge : |groundEnergy 1| + 1 < (N : ℝ) := (le_max_right _ _).trans_lt hN
  have hL : singletLowerBound N ≤ -(N : ℝ) := by
    unfold singletLowerBound
    nlinarith [sq_nonneg (N : ℝ)]
  have hneg : -(N : ℝ) < groundEnergy 1 := by
    have := neg_abs_le (groundEnergy 1)
    linarith
  refine ⟨(), N, 1, ?_⟩
  change groundEnergy N ≠ groundEnergy 1
  exact ne_of_lt (((result N hN1).2.1.trans_le hL).trans hneg)

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.SpinChains.DiamondSingletExclusion.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.DiamondSingletExclusion.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.DiamondSingletExclusion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ S => groundEnergy S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.DiamondSingletExclusion
    definition := some {
      owner := `D5.S3.Quantum.SpinChains.DiamondSingletExclusion
      name := `D5.S3.Quantum.SpinChains.DiamondSingletExclusion.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.SpinChains.DiamondSingletExclusion

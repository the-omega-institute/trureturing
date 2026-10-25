import Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
import D5.S3.Quantum.Fibers.SharedEnergyGapBound

/-! Labelled-degree audit for all indecomposable zero-weight exponents. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Quantum.Fibers.SharedEnergyGapBound
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
open _root_.D5.S3.Quantum.Fibers.SharedEnergyGapBound

abbrev signature : Signature where
  Params := Unit
  State _ := Exponent
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def readoutFunction : Unit → Unit → Exponent → ℕ := fun _ _ alpha => degree alpha
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def shifted : Realization signature := realize signature (fun _ _ alpha => degree alpha + 1)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∀ (alpha : Exponent), Indecomposable m alpha →
    R.readout () () alpha ≤ 2*m-1
private theorem bridge : (type_of% indecomposable_degree_bound) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law shifted := by
  intro h
  have hs := star_indecomposable 2 (by omega)
  have he := h 2 (by omega) (starExponent 2) hs.1
  change degree (starExponent 2) + 1 ≤ 2*2-1 at he
  rw [hs.2.1] at he
  omega
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, starExponent 2, ?_⟩
  intro h
  change degree 0 = degree (starExponent 2) at h
  rw [(star_indecomposable 2 (by omega)).2.1] at h
  norm_num [degree] at h

def family : Registration arena (type_of% indecomposable_degree_bound) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp indecomposable_degree_bound, shifted, rejected⟩
  sensitivity := ⟨fun i => ⟨shifted,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    indecomposable_degree_bound (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyGapBound.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyGapBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature readoutFunction (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.SharedEnergyGapBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end Reg.D5.S3.Quantum.Fibers.SharedEnergyGapBound

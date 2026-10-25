import Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
import D5.S3.Quantum.Fibers.SharedEnergyCompactAction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MatrixOrder ComplexOrder BigOperators
namespace Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
open _root_.D5.S3.Quantum.Fibers.SharedEnergyCompactAction
open _root_.D5.S3.Quantum.Fibers.RealCopyConjugation
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open Reg.D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold

namespace Group
abbrev signature := Hamiltonian.signature
def readoutFunction := Hamiltonian.readoutFunction
def actual : Realization signature := Hamiltonian.actual
def zeroReadout : Realization signature := Hamiltonian.zeroReadout
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ,
    Set.range (fun U : energyGroup m => (U.val : Matrix (Fin 3) (Fin 3) ℂ)) =
      closure (Set.range (fun t : ℝ =>
        NormedSpace.exp ((-Complex.I * (t : ℂ)) • R.readout () 1 m))) ∧
    ∀ (n : ℕ) (t : ℝ),
      matrixCopies (NormedSpace.exp ((-Complex.I * (t : ℂ)) • R.readout () 1 m)) n =
        NormedSpace.exp ((-Complex.I * (t : ℂ)) • R.readout () n m)
private theorem bridge : (type_of% energy_group_realization) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have he := (h 2).1
  have hx : (energyRepresentation 2 (-1 : Circle)).val ∈
      Set.range (fun U : energyGroup 2 => (U.val : Matrix (Fin 3) (Fin 3) ℂ)) :=
    ⟨⟨energyRepresentation 2 (-1 : Circle), ⟨-1, rfl⟩⟩, rfl⟩
  rw [he] at hx
  have ht : (energyRepresentation 2 (-1 : Circle)).val = 1 := by
    simpa [zeroReadout, Hamiltonian.zeroReadout, realize] using hx
  have hh := congrArg (fun X => X (1 : Fin 3) (1 : Fin 3)) ht
  norm_num [energyRepresentation, energy] at hh
private theorem dependence : ObservationalDependence signature actual := Hamiltonian.family.dependence

def family : Registration arena (type_of% energy_group_realization) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp energy_group_realization, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    energy_group_realization (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction.Group.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction.Group.family
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
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCompactAction
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "arg", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Group

namespace Haar
abbrev signature : Signature where
  Params := ℕ × ℕ
  State _ := DensityState (Fin 3)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (CopyIndex (Fin 3) p.2) (CopyIndex (Fin 3) p.2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def readoutFunction : Unit → ∀ p, signature.State p → signature.Output () p :=
  fun _ p r => sharedMoment p.1 p.2 r
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def zeroReadout : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m n : ℕ) (r : DensityState (Fin 3)),
    R.readout () (m,n) r = pinchedCopies m n r
private theorem bridge : (type_of% shared_haar_pinching) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  have he := congrArg (fun X => X PUnit.unit PUnit.unit) (h 2 0 rho)
  rw [(tensor_monomial_bridge 2 0 rho PUnit.unit PUnit.unit).2.2.2.1] at he
  norm_num [zeroReadout, realize, tensorExponent, weight, monomial] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(2,1), rho, Pinching.lowestEnergyState, ?_⟩
  intro h
  cases i
  change sharedMoment 2 1 rho = sharedMoment 2 1 Pinching.lowestEnergyState at h
  rw [shared_haar_pinching, shared_haar_pinching] at h
  have he := congrArg (fun X => X (0 : Fin 3) (0 : Fin 3)) h
  rw [(tensor_monomial_bridge 2 1 rho (0 : Fin 3) (0 : Fin 3)).2.2.2.1,
    (tensor_monomial_bridge 2 1 Pinching.lowestEnergyState (0 : Fin 3) (0 : Fin 3)).2.2.2.1] at he
  norm_num [tensorExponent, coordinateExponent, weight, energy, monomial,
    Fin.sum_univ_succ, Fin.prod_univ_succ] at he
  change sparseMatrix 1 0 0 =
    _root_.D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity
      (Pi.single (0 : Fin 3) (1 : ℂ)) 0 0 at he
  norm_num [sparseMatrix,
    _root_.D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity,
    Matrix.vecMulVec, Pi.single_apply] at he

def family : Registration arena (type_of% shared_haar_pinching) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp shared_haar_pinching, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    shared_haar_pinching (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction.Haar.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction.Haar.family
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
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCompactAction
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Haar

namespace Separation
abbrev signature := Pinching.signature
def readoutFunction := Pinching.readoutFunction
def actual : Realization signature := Pinching.actual
def zeroReadout : Realization signature := realize signature (fun _ _ _ => rho) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, 2 ≤ m →
    ¬ SameEnergyOrbit m rho (R.readout () () m) ∧
    (∀ n : ℕ, n < 2*m-1 → sharedMoment m n rho = sharedMoment m n (R.readout () () m)) ∧
    sharedMoment m (copyOrder m) rho ≠ sharedMoment m (copyOrder m) (R.readout () () m)
private theorem bridge : (type_of% sparse_compact_separation) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law zeroReadout := by
  intro h
  apply (h 2 (by omega)).1
  refine ⟨1, ?_⟩
  simp [zeroReadout, realize]
private theorem dependence : ObservationalDependence signature actual := Pinching.family.dependence

def family : Registration arena (type_of% sparse_compact_separation) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp sparse_compact_separation, zeroReadout, rejected⟩
  sensitivity := ⟨fun i => ⟨zeroReadout,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sparse_compact_separation (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction.Separation.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction.Separation.family
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
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCompactAction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Separation
#print axioms Group.registration
#print axioms Haar.registration
#print axioms Separation.registration

namespace Monomials
abbrev signature := ExponentWords.signature
def readoutFunction := ExponentWords.readoutFunction
def actual : Realization signature := ExponentWords.actual
def shifted : Realization signature := realize signature
  (fun _ r alpha => monomial (stateMatrix r) alpha + stateMatrix r 2 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m N : ℕ) (r s : DensityState (Fin 3)),
    sharedMoment m N r = sharedMoment m N s → ∀ alpha : Exponent,
      degree alpha ≤ N → weight m alpha = 0 → R.readout () r alpha = R.readout () s alpha
private theorem bridge : (type_of% moment_determines_monomials) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law shifted := by
  intro h
  have hzero : sharedMoment 2 0 rho = sharedMoment 2 0 (sigma 2) := by
    rw [shared_haar_pinching, shared_haar_pinching]
    exact sparse_low_pinching 2 0 (by omega) (by omega)
  have he := h 2 0 rho (sigma 2) hzero 0 (by simp [degree]) (by simp [weight])
  change monomial (stateMatrix rho) 0 + stateMatrix rho 2 0 =
    monomial (stateMatrix (sigma 2)) 0 + stateMatrix (sigma 2) 2 0 at he
  norm_num [monomial, stateMatrix, rho, sigma, sparseState, sparseMatrix, phase,
    Circle.coe_exp, Complex.exp_pi_mul_I] at he
private theorem dependence : ObservationalDependence signature actual :=
  ExponentWords.family.dependence

def family : Registration arena (type_of% moment_determines_monomials) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp moment_determines_monomials, shifted, rejected⟩
  sensitivity := ⟨fun i => ⟨shifted,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    moment_determines_monomials (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction.Monomials.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction.Monomials.family
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
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCompactAction
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Monomials

#print axioms Monomials.registration
namespace LeastOrder
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def readoutFunction : Unit → Unit → ℕ → ℕ := fun _ _ m => 2*m-1
def actual : Realization signature := realize signature readoutFunction (fun e => nomatch e)
def shifted : Realization signature := realize signature (fun _ _ m => 2*m-1+1)
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, 2 ≤ m →
    IsLeast {N : ℕ | 0 < N ∧ ∀ r s : DensityState (Fin 3),
      sharedMoment m N r = sharedMoment m N s ↔ SameEnergyOrbit m r s} (R.readout () () m)
private theorem bridge : (type_of% least_uniform_order) ↔ arena.Law actual := Iff.rfl
private theorem rejected : ¬ arena.Law shifted := by
  intro h
  have he := (least_uniform_order 2 (by omega)).unique (h 2 (by omega))
  change 2*2-1 = 2*2-1+1 at he
  omega
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  norm_num [actual, realize, readoutFunction]

def family : Registration arena (type_of% least_uniform_order) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp least_uniform_order, shifted, rejected⟩
  sensitivity := ⟨fun i => ⟨shifted,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    least_uniform_order (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction.LeastOrder.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction.LeastOrder.family
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
    owner := `D5.S3.Quantum.Fibers.SharedEnergyCompactAction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end LeastOrder
#print axioms LeastOrder.registration
end Reg.D5.S3.Quantum.Fibers.SharedEnergyCompactAction

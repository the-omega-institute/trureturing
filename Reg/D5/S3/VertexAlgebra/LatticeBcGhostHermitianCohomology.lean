import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
open LatticeBcGhostHermitianForm LatticeBcGhostHermitianAdjoint LatticeBcGhostHermitianCohomology
open BcGhostFockSupport BcGhostBpZForm BcGhostEnergyRotation BcGhostRotatedForm
open LatticeBcGhostBrstNeutralMatrix
open scoped TensorProduct

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology

noncomputable section

structure Parameters where
  lattice : LatticeData
  matrixH : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  inverseHG : matrixH * gramComplex lattice = 1
  inverseGH : gramComplex lattice * matrixH = 1
  left : State lattice

abbrev signature : Signature where
  Params := Parameters
  State parameter := State parameter.lattice
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter right => F parameter.lattice
    (Q parameter.lattice parameter.matrixH parameter.left) right)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ parameter right => F parameter.lattice
    (Q parameter.lattice parameter.matrixH parameter.left) right + 1)
  (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law realization := ∀ parameter right, realization.readout () parameter right =
    -F parameter.lattice (LatticeBcGhostHermitianAdjoint.Pi parameter.lattice parameter.left)
      (Q parameter.lattice parameter.matrixH right)

def zeroLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro axis; exact Fin.elim0 axis
  even_diagonal := by intro axis; exact Fin.elim0 axis

def witnessParameters : Parameters where
  lattice := zeroLattice
  matrixH := 0
  inverseHG := by ext axis; exact Fin.elim0 axis
  inverseGH := by ext axis; exact Fin.elim0 axis
  left := uState zeroLattice

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  have impossible := law witnessParameters 0
  change F zeroLattice (Q zeroLattice 0 (uState zeroLattice)) 0 + 1 =
    -F zeroLattice (LatticeBcGhostHermitianAdjoint.Pi zeroLattice (uState zeroLattice))
      (Q zeroLattice 0 0) at impossible
  simp [F] at impossible

private theorem witnessNonzero :
    F zeroLattice (Q zeroLattice 0 (uState zeroLattice)) (uState zeroLattice) ≠ 0 := by
  rw [Q_c0_vacuum]
  have uNative : uState zeroLattice =
      Finsupp.single (0 : Charge zeroLattice) (1 : Oscillator zeroLattice) ⊗ₜ[ℂ] basis {3} := by
    simp [uState, vacuumState, LatticeBcGhostBrstVacuumClass.vacuumVector, C, c,
      vacuum, create, Finsupp.linearCombination_single, createBasis, basis, sign]
  have zNative : zState zeroLattice =
      Finsupp.single (0 : Charge zeroLattice) (1 : Oscillator zeroLattice) ⊗ₜ[ℂ]
        (-basis {1, 5}) := by
    simp [zState, vacuumState, LatticeBcGhostBrstVacuumClass.vacuumVector, C, c,
      vacuum, create, Finsupp.linearCombination_single, createBasis, basis, sign,
      Finset.filter_insert, Finset.filter_singleton, Finset.pair_comm 5 1]
  rw [uNative, zNative]
  change tensorForm zeroLattice ((-2 : ℂ) • _) _ ≠ 0
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
  rw [show starRingEnd ℂ (-2 : ℂ) = -2 by simp only [starRingEnd_apply]; norm_num]
  change (-2 : ℂ) * F zeroLattice _ _ ≠ 0
  rw [F_tmul, LatticeChargedFockForms.hermitian_single]
  simp only [if_true, LatticeOscillatorFockForm.fockForm_vacuum_left,
    map_one, one_mul]
  have ghostNonzero : Hplus (-basis {1, 5}) (basis {3}) ≠ 0 := by
    change HplusForm (-basis {1, 5}) (basis {3}) ≠ 0
    rw [map_neg, LinearMap.neg_apply]
    apply neg_ne_zero.mpr
    change BPZ (conjCoeffs (basis {1, 5})) (rotation (basis {3})) ≠ 0
    rw [show conjCoeffs (basis {1, 5}) = basis {1, 5} by simp [conjCoeffs, basis]]
    rw [show rotation (basis {3}) = basis {3} by
      norm_num [basis, rotation_single, phase, BcGhostLZeroSpectrum.energy,
        BcGhostLZeroSpectrum.siteWeight]]
    rw [BPZ_kernel, if_pos (show ({3} : Finset ℕ) = chi {1, 5} by decide)]
    exact eps_nonzero {1, 5}
  exact mul_ne_zero (by norm_num) ghostNonzero

def sourceWitness : Registration arena
    (type_of% (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology.F_Q)) where
  actual := actual
  bridge := by
    constructor
    · intro law parameter right
      exact law parameter.lattice parameter.matrixH parameter.inverseHG parameter.inverseGH
        parameter.left right
    · intro law lattice matrixH inverseHG inverseGH left right
      exact law ⟨lattice, matrixH, inverseHG, inverseGH, left⟩ right
  variation := ⟨fun parameter right => F_Q parameter.lattice parameter.matrixH
    parameter.inverseHG parameter.inverseGH parameter.left right, rejected, rejectedFails⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedFails⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨witnessParameters, uState zeroLattice, 0, ?_⟩
    change F zeroLattice (Q zeroLattice 0 (uState zeroLattice)) (uState zeroLattice) ≠
      F zeroLattice (Q zeroLattice 0 (uState zeroLattice)) 0
    simpa [F] using witnessNonzero

def registration : LeanInformationAudit.Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology.F_Q)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology.F_Q.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology.sourceWitness
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceWitness⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ parameter right => F parameter.lattice
      (Q parameter.lattice parameter.matrixH parameter.left) right)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.VertexAlgebra.LatticeBcGhostHermitianCohomology

import D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber
import D5.S3.VertexAlgebra.BcGhostVacuum
import Reg.Support.DependentFamily
import Mathlib.LinearAlgebra.TensorProduct.Associator

set_option autoImplicit false

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
open _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open _root_.D5.S3.VertexAlgebra.BcGhostStressCurrent
open _root_.D5.S3.VertexAlgebra.BcGhostVacuum
open scoped TensorProduct

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber

noncomputable section

abbrev signature : Signature where
  Params := Σ D : LatticeData, Matrix (Fin D.rank) (Fin D.rank) ℂ
  State parameter := _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameter state => Q parameter.1 parameter.2 state)
    (fun empty => nomatch empty)

def identity : Realization signature :=
  realize signature (fun _ _ state => state) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (state : _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State D),
    J D (readout.readout () ⟨D, H⟩ state) -
      readout.readout () ⟨D, H⟩ (J D state) = readout.readout () ⟨D, H⟩ state

def sourceStatement : Prop :=
  ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ),
    J D * Q D H - Q D H * J D = Q D H

theorem sourceBridge : sourceStatement ↔ arena.Law actual := by
  constructor
  · intro source D H state
    have evaluated := congrArg (fun operator : Module.End ℂ (State D) => operator state)
      (source D H)
    simpa only [actual, realize, LinearMap.sub_apply, Module.End.mul_apply] using evaluated
  · intro law D H
    apply LinearMap.ext
    intro state
    simpa only [actual, realize, LinearMap.sub_apply, Module.End.mul_apply] using law D H state

theorem actualPositive : arena.Law actual := sourceBridge.mp J_Q_commutator

private def probeLattice : LatticeData where
  rank := 0
  G := 0
  symmetric := by intro first second; simp
  even_diagonal := by intro index; exact Fin.elim0 index

private def probeMatter : Carrier probeLattice := Finsupp.single 0 1

private def probeGhost : Fock ℂ := b (-2) vacuum

private def projection : State probeLattice →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map
      ((MvPolynomial.lcoeff ℂ (0 : Index probeLattice →₀ ℕ)).comp
        (Finsupp.lapply (0 : Charge probeLattice)))
      (Finsupp.lapply ({0} : Finset ℕ)))

private theorem projection_probe : projection (probeMatter ⊗ₜ[ℂ] probeGhost) = 1 := by
  norm_num [projection, probeMatter, probeGhost, b, create, createBasis, vacuum, sign,
    Finsupp.linearCombination_single, MvPolynomial.lcoeff_apply]

theorem rejected : ¬ arena.Law identity := by
  intro law
  have equation := law probeLattice 0 (probeMatter ⊗ₜ[ℂ] probeGhost)
  change J probeLattice (probeMatter ⊗ₜ[ℂ] probeGhost) -
    J probeLattice (probeMatter ⊗ₜ[ℂ] probeGhost) =
      probeMatter ⊗ₜ[ℂ] probeGhost at equation
  have value := congrArg projection equation
  rw [sub_self, map_zero, projection_probe] at value
  exact zero_ne_one value

private theorem probeCharge_nonzero : Q probeLattice 0 ≠ 0 := by
  intro zeroCharge
  have zeroMatter : M probeLattice 0 0 = 0 := by
    simp [M, sugawaraMode, sugawaraField]
  have ward := ward_identity probeLattice 0 0
  rw [zeroCharge, zeroMatter] at ward
  have zeroGhost : G probeLattice 0 = 0 := by simpa using ward.symm
  have covariance := congrArg (fun operator : Module.End ℂ (Fock ℂ) => operator vacuum)
    (L_b_commutator (K := ℂ) 0 (-2))
  have eigen : L 0 probeGhost = (2 : ℂ) • probeGhost := by
    simpa [probeGhost, L_vacuum_annihilation (K := ℂ) 0 (by norm_num)] using covariance
  have zeroVector := congrArg (fun operator : Module.End ℂ (State probeLattice) =>
    operator (probeMatter ⊗ₜ[ℂ] probeGhost)) zeroGhost
  change probeMatter ⊗ₜ[ℂ] L 0 probeGhost = 0 at zeroVector
  rw [eigen, TensorProduct.tmul_smul] at zeroVector
  have value := congrArg projection zeroVector
  simp only [map_smul, map_zero, projection_probe, smul_eq_mul, mul_one] at value
  norm_num at value

theorem dependence : ObservationalDependence signature actual := by
  intro role
  obtain ⟨state, nonzero⟩ : ∃ state : State probeLattice, Q probeLattice 0 state ≠ 0 := by
    by_contra missing
    push_neg at missing
    exact probeCharge_nonzero (LinearMap.ext missing)
  refine ⟨⟨probeLattice, 0⟩, state, 0, ?_⟩
  simpa only [actual, realize, map_zero] using nonzero

def evidence : Registration arena sourceStatement where
  actual := actual
  bridge := sourceBridge
  variation := ⟨actualPositive, identity, rejected⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      refine ⟨identity, ?_, rfl, rejected⟩
      rintro ⟨⟩ distinct
      exact (distinct rfl).elim
    · intro empty
      exact Empty.elim empty
  dependence := dependence

#print axioms sourceBridge
#print axioms evidence

end

end Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstGhostNumber

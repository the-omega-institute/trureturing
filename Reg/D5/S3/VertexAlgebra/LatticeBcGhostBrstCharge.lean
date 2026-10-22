import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open scoped BigOperators TensorProduct

namespace Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge

noncomputable section

abbrev summandSignature : Signature where
  Params := Σ lattice : LatticeData, Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  State parameter := _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter :=
    ℤ → _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def summandActual : Realization summandSignature :=
  realize summandSignature (fun _ parameter state mode =>
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.A
      parameter.1 parameter.2 mode state) (fun empty => nomatch empty)

abbrev summandArena : Arena where
  signature := summandSignature
  Law readout := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (state : _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State lattice),
    Function.HasFiniteSupport (readout.readout () ⟨lattice, matrix⟩ state)

def summandSourceStatement : Prop :=
  ∀ (lattice : LatticeData) (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (state : _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State lattice),
    Function.HasFiniteSupport (fun mode : ℤ =>
      _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.A lattice matrix mode state)

theorem summandSourceBridge : summandSourceStatement ↔ summandArena.Law summandActual := Iff.rfl

theorem summandActualPositive : summandArena.Law summandActual :=
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.A_finite

abbrev evaluationSignature : Signature where
  Params := Σ lattice : LatticeData, Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  State parameter := Carrier parameter.1 × Fock ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def evaluationActual : Realization evaluationSignature :=
  realize evaluationSignature (fun _ parameter state =>
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.Q
      parameter.1 parameter.2 (state.1 ⊗ₜ[ℂ] state.2)) (fun empty => nomatch empty)

abbrev evaluationArena : Arena where
  signature := evaluationSignature
  Law readout := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (matter : Carrier lattice) (ghost : Fock ℂ),
    readout.readout () ⟨lattice, matrix⟩ (matter, ghost) =
      (∑ mode ∈ Finset.Icc (-_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound ghost - 2)
          (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.matterCutoff lattice matrix matter),
        _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents.sugawaraMode
          lattice matrix mode matter ⊗ₜ[ℂ] c (-mode) ghost) +
      (2 : ℂ)⁻¹ •
        (∑ mode ∈ Finset.Icc (-_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound ghost - 2)
            (2 * _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound ghost + 4),
          ∑ index ∈ Finset.Icc
              (-(3 * _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound ghost + 8))
              (3 * _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound ghost + 8),
            (mode - index : ℂ) • (matter ⊗ₜ[ℂ]
              _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded ghost (mode, index)))

theorem evaluationActualPositive : evaluationArena.Law evaluationActual :=
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.Q_tmul_expanded

abbrev tensorSummandSignature : Signature where
  Params := Σ lattice : LatticeData, Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ
  State parameter := Carrier parameter.1 × Fock ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter :=
    ℤ → _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def tensorSummandActual : Realization tensorSummandSignature :=
  realize tensorSummandSignature (fun _ parameter state mode =>
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.A
      parameter.1 parameter.2 mode (state.1 ⊗ₜ[ℂ] state.2)) (fun empty => nomatch empty)

abbrev tensorSummandArena : Arena where
  signature := tensorSummandSignature
  Law readout := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (matter : Carrier lattice) (ghost : Fock ℂ),
    Function.support (readout.readout () ⟨lattice, matrix⟩ (matter, ghost)) ⊆
      Set.Icc (-_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound ghost - 2)
        (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.chargeUpper
          lattice matrix matter ghost)

theorem tensorSummandActualPositive : tensorSummandArena.Law tensorSummandActual :=
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.A_support_tmul

abbrev intervalArena : Arena where
  signature := evaluationSignature
  Law readout := ∀ (lattice : LatticeData)
    (matrix : Matrix (Fin lattice.rank) (Fin lattice.rank) ℂ)
    (matter : Carrier lattice) (ghost : Fock ℂ),
    readout.readout () ⟨lattice, matrix⟩ (matter, ghost) =
      ∑ mode ∈ Finset.Icc (-_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound ghost - 2)
          (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.chargeUpper
            lattice matrix matter ghost),
        (_root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents.sugawaraMode
          lattice matrix mode matter ⊗ₜ[ℂ] c (-mode) ghost +
          (2 : ℂ)⁻¹ • (matter ⊗ₜ[ℂ]
            _root_.D5.S3.VertexAlgebra.BcGhostStressTails.outerNormalPair mode ghost))

theorem intervalActualPositive : intervalArena.Law evaluationActual :=
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.Q_tmul

abbrev wardSignature : Signature where
  Params := Σ D : LatticeData, Matrix (Fin D.rank) (Fin D.rank) ℂ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter :=
    Module.End ℂ (_root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.State parameter.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def wardActual : Realization wardSignature :=
  realize wardSignature (fun _ parameter m =>
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.Q parameter.1 parameter.2 *
        _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.B parameter.1 m +
      _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.B parameter.1 m *
        _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.Q parameter.1 parameter.2)
    (fun empty => nomatch empty)

abbrev wardArena : Arena where
  signature := wardSignature
  Law readout := ∀ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ),
    readout.readout () ⟨D, H⟩ m =
      _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.M D H m +
        _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.G D m

def wardSourceStatement : Prop :=
  ∀ (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ),
    _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.Q D H *
        _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.B D m +
      _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.B D m *
        _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.Q D H =
      _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.M D H m +
        _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.G D m

theorem wardSourceBridge : wardSourceStatement ↔ wardArena.Law wardActual := Iff.rfl

theorem wardActualPositive : wardArena.Law wardActual :=
  _root_.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge.ward_identity

#print axioms summandSourceBridge
#print axioms summandActualPositive
#print axioms evaluationActualPositive
#print axioms tensorSummandActualPositive
#print axioms intervalActualPositive
#print axioms wardSourceBridge
#print axioms wardActualPositive

end

end Reg.D5.S3.VertexAlgebra.LatticeBcGhostBrstCharge

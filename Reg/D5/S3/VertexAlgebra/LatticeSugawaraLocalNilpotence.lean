import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open _root_.D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence

namespace Reg.D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence

noncomputable section

abbrev Parameter := Σ data : LatticeData,
  Matrix (Fin data.rank) (Fin data.rank) ℂ × ℕ

abbrev signature : Signature where
  Params := Parameter
  State parameter := Carrier parameter.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := Carrier parameter.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ parameter state => ((sugawaraMode parameter.1 parameter.2.1 1)^parameter.2.2) state)
  (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ state => state) (fun empty => nomatch empty)

abbrev arena : Arena where
  signature := signature
  Law realization := ∀ (parameter : Parameter) (state : Carrier parameter.1),
    oscillatorBound parameter.1 state < parameter.2.2 →
      realization.readout () parameter state = 0

private def emptyData : LatticeData where
  rank := 0
  G := 0
  symmetric := by intros; rfl
  even_diagonal := by intro index; exact Fin.elim0 index

private def emptyGround : Carrier emptyData := carrierBasis emptyData (0, 0)

private theorem emptyGround_bound : oscillatorBound emptyData emptyGround = 0 := by
  classical
  rw [oscillatorBound, emptyGround, carrierCoeffEquiv_basis]
  simp [oscillatorEnergy]

private theorem emptyGround_nonzero : emptyGround ≠ 0 := by
  intro equality
  have coefficient := congrArg (fun state : Carrier emptyData =>
    carrierCoeffEquiv emptyData state (0, 0)) equality
  rw [emptyGround, carrierCoeffEquiv_basis] at coefficient
  norm_num at coefficient

private theorem bridge : arena.Law actual ↔
    ∀ (data : LatticeData) (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
      (state : Carrier data) (power : ℕ), oscillatorBound data state < power →
        ((sugawaraMode data matrix 1)^power) state = 0 := by
  constructor
  · intro law data matrix state power beyond
    exact law ⟨data, matrix, power⟩ state beyond
  · intro law parameter state beyond
    exact law parameter.1 parameter.2.1 state parameter.2.2 beyond

private theorem rejectedFails : ¬ arena.Law rejected := by
  intro law
  exact emptyGround_nonzero (law ⟨emptyData, 0, 1⟩ emptyGround (by rw [emptyGround_bound]; decide))

def sourceWitness : Registration arena
    (∀ (data : LatticeData) (matrix : Matrix (Fin data.rank) (Fin data.rank) ℂ)
      (state : Carrier data) (power : ℕ), oscillatorBound data state < power →
        ((sugawaraMode data matrix 1)^power) state = 0) where
  actual := actual
  bridge := bridge.symm
  variation := ⟨bridge.mpr one_pow_eq_zero, rejected, rejectedFails⟩
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
    refine ⟨⟨emptyData, 0, 0⟩, emptyGround, 0, ?_⟩
    simpa [actual, realize] using emptyGround_nonzero

def one_pow_eq_zero_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence.one_pow_eq_zero)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence.one_pow_eq_zero.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence.sourceWitness
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
    (fun _ parameter state => ((sugawaraMode parameter.1 parameter.2.1 1)^parameter.2.2) state)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[
    { name := `Elab.async, value := .bool true },
    { name := `autoImplicit, value := .bool false },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }]

end
end Reg.D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence

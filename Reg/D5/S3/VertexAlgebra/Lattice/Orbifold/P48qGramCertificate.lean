import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound audit of the P48q inverse and Gram isometry. -/

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate

open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate (nebeOrderThree)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped Matrix

abbrev Matrix48 := Matrix (Fin 48) (Fin 48) ℤ

abbrev signature : Signature where
  Params := Unit
  State _ := Matrix48
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix48
  Anchor := Empty
  finiteAnchor := inferInstance

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem gram_ne_zero : nebeGram ≠ 0 := by
  intro h
  have h₀ := congrArg (fun G : Matrix48 => G 0 0) h
  exact (by decide +kernel : nebeGram 0 0 ≠ (0 : Matrix48) 0 0) h₀

namespace Inverse

def actual : Realization signature :=
  realize signature (fun _ _ X => X * nebeGram) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () nebeGramInverse = 1

private theorem rejected_law : ¬ arena.Law rejected := zero_ne_one

def family : Registration arena (type_of% gram_inverse_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gram_inverse_certificate, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change (0 : Matrix48) * nebeGram ≠ 1 * nebeGram
    simpa using Ne.symm gram_ne_zero

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      gram_inverse_certificate (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate.gram_inverse_certificate.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate.Inverse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => X * nebeGram) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Inverse

namespace Isometry

def actual : Realization signature :=
  realize signature (fun _ _ X => nebeOrderThree * X * nebeOrderThreeᵀ) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () nebeGram = nebeGram

private theorem rejected_law : ¬ arena.Law rejected := Ne.symm gram_ne_zero

def family : Registration arena (type_of% gram_isometry_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gram_isometry_certificate, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro _
    refine ⟨(), 0, nebeGram, ?_⟩
    change nebeOrderThree * (0 : Matrix48) * nebeOrderThreeᵀ ≠
      nebeOrderThree * nebeGram * nebeOrderThreeᵀ
    rw [mul_zero, zero_mul, gram_isometry_certificate]
    exact Ne.symm gram_ne_zero

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      gram_isometry_certificate (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate.gram_isometry_certificate.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate.Isometry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => nebeOrderThree * X * nebeOrderThreeᵀ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Isometry

end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate

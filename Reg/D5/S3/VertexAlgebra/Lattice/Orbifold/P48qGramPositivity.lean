import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the triangular criterion and the concrete P48q Gram form. -/

namespace Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity

open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramCertificate (nebeGram)
open _root_.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev IntegralMatrix48 := Matrix (Fin 48) (Fin 48) ℤ
abbrev RealMatrix48 := Matrix (Fin 48) (Fin 48) ℝ

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => IntegralMatrix48) (fun _ => RealMatrix48)

def actual : Realization signature :=
  realize signature
    (fun _ _ G => G.map (Int.cast : ℤ → ℝ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (R.readout () () nebeGram).PosDef

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : (0 : RealMatrix48).PosDef := h
  have hi := hz.diag_pos (i := 0)
  simp at hi

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 1, 0, ?_⟩
  intro h
  have he := congrArg (fun G : RealMatrix48 => G 0 0) h
  change ((1 : IntegralMatrix48) 0 0 : ℝ) = ((0 : IntegralMatrix48) 0 0 : ℝ) at he
  simp at he

def family : Registration arena (type_of% nebeGram_posDef) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨nebeGram_posDef, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      nebeGram_posDef (Realization signature) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity.nebeGram_posDef.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ G => G.map (Int.cast : ℤ → ℝ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

namespace TriangularCertificate

universe u

abbrev signature : Signature where
  Params := Type u
  State ι := Matrix ι ι ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ ι := Matrix ι ι ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ G => G.map (Int.cast : ℤ → ℝ)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] [LinearOrder ι] (G U : Matrix ι ι ℤ),
    G.IsSymm → U.IsUpperTriangular → (G * U).IsLowerTriangular →
    (∀ i, 0 < U i i) → (∀ i, 0 < (G * U) i i) → (R.readout () ι G).PosDef

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let I := PUnit.{u + 1}
  let A : Matrix I I ℤ := 1
  have hUpper : A.IsUpperTriangular := by
    intro i j hij
    exact (hij.ne (Subsingleton.elim _ _)).elim
  have hLower : (A * A).IsLowerTriangular := by
    intro i j hij
    exact (hij.ne (Subsingleton.elim _ _)).elim
  have hDiag (i : I) : 0 < A i i := by simp [A]
  have hProduct (i : I) : 0 < (A * A) i i := by simpa [A] using hDiag i
  have hz : (0 : Matrix I I ℝ).PosDef :=
    h A A Matrix.isSymm_one hUpper hLower hDiag hProduct
  simpa using hz.diag_pos (i := PUnit.unit)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro _
  let I := PUnit.{u + 1}
  refine ⟨I, 1, 0, ?_⟩
  intro h
  have he := congrArg (fun G : Matrix I I ℝ => G PUnit.unit PUnit.unit) h
  change ((1 : Matrix I I ℤ) PUnit.unit PUnit.unit : ℝ) =
    ((0 : Matrix I I ℤ) PUnit.unit PUnit.unit : ℝ) at he
  simp at he

def family : Registration arena.{u} (type_of% @posDef_intCast_of_triangular.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@posDef_intCast_of_triangular.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@posDef_intCast_of_triangular.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity.posDef_intCast_of_triangular.__information_unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity.TriangularCertificate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ G => G.map (Int.cast : ℤ → ℝ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end TriangularCertificate

end
end Reg.D5.S3.VertexAlgebra.Lattice.Orbifold.P48qGramPositivity

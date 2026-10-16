import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsolutePPT.HildebrandNegativeIndexRefutation
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.HildebrandNegativeIndexRefutation
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.HildebrandNegativeIndexRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the matrix as the spectrum varies, retaining the dimension and both orderings. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Sigma fun d : ℕ => Sigma fun _ : PlusOrdering d => MinusOrdering d)
    (fun p => Fin (p.1 * p.1) → ℝ)
    (fun p => Matrix (Fin p.1) (Fin p.1) ℂ)

def actual : Realization signature :=
  realize signature (fun _ p lam => hildebrandMatrix p.1 lam p.2.1 p.2.2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => Complex.I) (fun e => nomatch e)

/-- Retain the complete Hermitian assertion and its unrestricted parameter telescope. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : ℕ) (lam : Fin (d * d) → ℝ)
    (sigmaP : PlusOrdering d) (sigmaM : MinusOrdering d),
    (R.readout () ⟨d, ⟨sigmaP, sigmaM⟩⟩ lam).IsHermitian

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  have he := (bad 1 0 (Fintype.equivFin _) (Fintype.equivFin _)).apply 0 0
  have hi := congrArg Complex.im he
  norm_num [rejected, realize] at hi

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, ⟨Fintype.equivFin _, Fintype.equivFin _⟩⟩,
    (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hc := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) he
  norm_num [actual, realize, hildebrandMatrix, hildebrandArray,
    Matrix.add_apply, Matrix.conjTranspose_apply] at hc

def source_registration : Registration arena (type_of% @hildebrandMatrix_isHermitian) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨hildebrandMatrix_isHermitian, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hildebrandMatrix_isHermitian) (Realization signature) Unit Unit := {
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.HildebrandNegativeIndexRefutation.unit
  realizationName :=
    .str `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.HildebrandNegativeIndexRefutation
      "source_registration"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p lam => hildebrandMatrix p.1 lam p.2.1 p.2.2)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.HildebrandNegativeIndexRefutation
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.HildebrandNegativeIndexRefutation

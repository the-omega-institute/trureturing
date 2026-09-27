import D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable
open LeanInformationAudit
open scoped BigOperators Matrix

noncomputable section
namespace Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable

def signature : Signature where
  Params := ℝ
  State _ := Fin 2 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 2 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Fin 2 → ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (z : ℝ) (p : Fin 2 → ℝ) (_hz : 0 < z) (_hp : ∀ j, 0 < p j),
    (∀ j, 0 < u z (R.readout () z p) j) ∧
      (∀ i j, 0 < K z p i j) ∧
        ∃ lambda1 lambda2 : ℝ,
          0 < lambda1 ∧ lambda1 < q z p ∧ 0 < lambda2 ∧ lambda2 < q z p ∧
            ∃ S : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ,
              IsUnit S.det ∧
                Q z p * S =
                  S * Matrix.fromBlocks (Matrix.diagonal ![lambda1, lambda2]) 0 0
                    (fun _ _ => q z p)

theorem actual_law : arena.Law actual := by
  intro z p hz hp
  simpa [actual, realize] using
    singular_support_candidate_positive_and_diagonalizable z p hz hp

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Fin 2 → ℝ := fun _ => 1
  have hresult := h 1 p (by norm_num) (by intro j; norm_num [p])
  have hzero := hresult.1 0
  norm_num [rejected, realize, u, q, K, gZero, H, r, Matrix.mulVec, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dotProduct, Fin.sum_univ_two] at hzero

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, funext fun e => Empty.elim e, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(1 : ℝ), (0 : Fin 2 → ℝ), (fun _ => 1), ?_⟩
  intro h
  have hentry := congrFun h 0
  norm_num [actual, realize] at hentry

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem singular_support_candidate_positive_and_diagonalizable in arena
  readout via (realize signature (fun _ _ p => p) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "arg",
        "fn", "arg"]
      stateBinder := 1 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.QuantumContext.SingularSupportCandidateDiagonalizable

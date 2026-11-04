import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Observation.MatrixFirstMomentCoefficientBridge
import Reg.Support.DependentFamily

/-! Faithful full-telescope DependentFamily evidence for the first coefficient bridge.
The actual readout is the matrix whose characteristic coefficient is observed, including every finite
index type and both matrices. Four-slot discovery is attempted separately; compilation
of these terms alone is not a declared_validated audit. -/

/-! UNFINISHED outer four-slot audit: the selected batch failed at the concrete
consumer with `contract.discovery:rigid_universes`; the generic outer assessment
was not completed by that failed batch. Both outer terms genuinely compiled.
See https://github.com/the-omega-institute/trureturing/issues/24448.
The full-telescope family evidence below is kernel checked; it is not a
`declared_validated` outer registration. -/

namespace Reg.D5.S0.Observation.MatrixFirstMomentCoefficientBridge
open _root_.D5.S0.Observation.MatrixFirstMomentCoefficientBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical
universe u

abbrev coefficientSignature : Signature where
  Params := Type u
  State ι := Matrix ι ι ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ ι := Matrix ι ι ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actualCoefficient : Realization coefficientSignature.{u} :=
  realize coefficientSignature (fun _ _ A => A) (fun e => nomatch e)

noncomputable def rejectedCoefficient : Realization coefficientSignature.{u} :=
  realize coefficientSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev coefficientArena : Arena where
  signature := coefficientSignature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ Fintype.card ι)
    (hTrace : ∀ k : ℕ, 0 < k → k < n → Matrix.trace (A^k) = Matrix.trace (B^k)),
    (∀ k : ℕ, k < n →
      (R.readout () ι A).charpoly.coeff (Fintype.card ι - k) =
        (R.readout () ι B).charpoly.coeff (Fintype.card ι - k)) ∧
    (n : ℂ) * ((R.readout () ι B).charpoly.coeff (Fintype.card ι - n) -
      (R.readout () ι A).charpoly.coeff (Fintype.card ι - n)) =
        -(Matrix.trace (B^n) - Matrix.trace (A^n))

private theorem actual_law : coefficientArena.{u}.Law actualCoefficient := by
  exact @matrix_first_moment_coefficient_bridge

-- A lifted singleton keeps this witness at the original arbitrary universe.
private theorem rejected_law : ¬ coefficientArena.{u}.Law rejectedCoefficient := by
  intro h
  letI : Fintype (ULift.{u} Unit) := inferInstance
  have bad := h (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) 1
    (by simp) (by simp) 1 (by omega) (by simp)
    (by intro k hk hkn; omega)
  norm_num [rejectedCoefficient, realize, Matrix.trace] at bad

noncomputable def coefficientSource : Registration coefficientArena.{u}
    (type_of% @matrix_first_moment_coefficient_bridge.{u}) where
  actual := actualCoefficient
  bridge := Iff.rfl
  variation := ⟨actual_law, rejectedCoefficient, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedCoefficient, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} Unit, 0, 1, ?_⟩
    change (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) ≠ 1
    exact zero_ne_one



end Reg.D5.S0.Observation.MatrixFirstMomentCoefficientBridge

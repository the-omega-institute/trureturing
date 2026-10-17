/- Dependent-family evidence for private equations of the original definitions.
These families do not register the original non-Prop definitions. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualResponseAdjoint
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix
open _root_.D5.S3.Arith.Robin.OriginalResidualPartialCellWeights (w v gram response_projection_interface)
open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer (response coefficient)
open _root_.D5.S3.Arith.Robin.OriginalResidualResponseAdjoint
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.Robin.OriginalResidualResponseAdjoint.DefinitionEquations

namespace Rhs

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ × Fin 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => responseAdjointRhs x.1 x.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => responseAdjointRhs x.1 x.2 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) (i : Fin 2), R.readout () () (N, i) =
    ∑ m ∈ Finset.Ico N (2 * N), w m * response N m * v N m i

private theorem source_equation (N : ℕ) (i : Fin 2) : responseAdjointRhs N i =
    ∑ m ∈ Finset.Ico N (2 * N), w m * response N m * v N m i := by
  rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 0
  change responseAdjointRhs 1 0 + 1 = responseAdjointRhs 1 0 at he
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0, 0), (1, 0), ?_⟩
  have h0 : Finset.Ico 0 (2 * 0) = ∅ := by decide
  have h1 : Finset.Ico 1 (2 * 1) = {1} := by decide
  have hd : Finset.Ioc 0 1 = {1} := by decide
  norm_num [actual, realize, responseAdjointRhs, response, coefficient, w, v, h0, h1, hd]

def equationFamily : Registration arena (type_of% (@source_equation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_equation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

end Rhs

namespace Coordinates

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ × Fin 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => responseAdjointCoordinates x.1 x.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => responseAdjointCoordinates x.1 x.2 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) (i : Fin 2),
    R.readout () () (N, i) = ((gram N)⁻¹ *ᵥ responseAdjointRhs N) i

private theorem source_equation (N : ℕ) (i : Fin 2) : responseAdjointCoordinates N i =
    ((gram N)⁻¹ *ᵥ responseAdjointRhs N) i := by
  rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 3 0
  change responseAdjointCoordinates 3 0 + 1 = responseAdjointCoordinates 3 0 at he
  linarith

/-- A concrete separation of two actual observations, computed from the
original full block, original Mobius response and original Gram inverse. -/
private theorem coordinates_gap_at_three :
    (19 / 122 : ℝ) < responseAdjointCoordinates 3 0 - responseAdjointCoordinates 3 1 := by
  have hblock : Finset.Ico 3 (2 * 3) = ({3, 4, 5} : Finset ℕ) := by decide
  have hdiv : Finset.Ioc 0 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have hL3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hLratio : Real.log ((3 : ℝ) / 2) < Real.log (3 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hratio : Real.log ((3 : ℝ) / 2) / Real.log (3 : ℝ) < 1 :=
    (div_lt_one hL3).mpr hLratio
  have hk2 : coefficient 3 2 =
      -(Real.log ((3 : ℝ) / 2) / Real.log (3 : ℝ)) := by
    norm_num [coefficient,
      ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2)] <;> ring
  have hk2lower : (-1 : ℝ) < coefficient 3 2 := by
    rw [hk2]
    linarith only [hratio]
  have hk3 : coefficient 3 3 = 0 := by norm_num [coefficient]

  -- Every original divisor row is kept. The d=1 term cancels its linear
  -- counterpart, and d=3 vanishes at the original cutoff. In particular,
  -- the original CONSTANT +1 does not cancel from the response itself.
  have hr3 : response 3 3 = 1 + coefficient 3 2 / 2 := by
    norm_num [response, hdiv, hk3] <;> ring
  have hr4 : response 3 4 = 1 := by
    norm_num [response, hdiv, hk3] <;> ring
  have hr5 : response 3 5 = 1 + coefficient 3 2 / 2 := by
    norm_num [response, hdiv, hk3] <;> ring
  have hH0 : responseAdjointRhs 3 0 =
      (1 / 6 : ℝ) + (7 / 120 : ℝ) * coefficient 3 2 := by
    norm_num [responseAdjointRhs, hblock, w, v, hr3, hr4, hr5] <;> ring
  have hH1 : responseAdjointRhs 3 1 =
      (37 / 180 : ℝ) + (5 / 72 : ℝ) * coefficient 3 2 := by
    norm_num [responseAdjointRhs, hblock, w, v, hr3, hr4, hr5] <;> ring

  -- Obtain the actual original Gram entries from its public interface;
  -- no private normal-equation helper or copied Gram definition is used.
  rcases (response_projection_interface (N := 3) (by norm_num)).1 with
    ⟨he00, he01, he10, he11⟩
  have hG00 : gram 3 0 0 = (1 / 6 : ℝ) := by
    rw [he00]
    norm_num [hblock, w]
  have hG01 : gram 3 0 1 = (37 / 180 : ℝ) := by
    rw [he01]
    norm_num [hblock, w]
  have hG10 : gram 3 1 0 = (37 / 180 : ℝ) := he10.trans hG01
  have hG11 : gram 3 1 1 = (143 / 540 : ℝ) := by
    rw [he11]
    norm_num [hblock, w]
  have hdet : (gram 3).det = (61 / 32400 : ℝ) := by
    rw [Matrix.det_fin_two, hG00, hG01, hG10, hG11]
    norm_num
  have hu : IsUnit (gram 3).det :=
    isUnit_iff_ne_zero.mpr (by rw [hdet]; norm_num)
  have hnormal : gram 3 *ᵥ responseAdjointCoordinates 3 = responseAdjointRhs 3 := by
    unfold responseAdjointCoordinates
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h0 : (1 / 6 : ℝ) * responseAdjointCoordinates 3 0 +
      (37 / 180 : ℝ) * responseAdjointCoordinates 3 1 =
      (1 / 6 : ℝ) + (7 / 120 : ℝ) * coefficient 3 2 := by
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hG00, hG01, hH0]
      using congrFun hnormal (0 : Fin 2)
  have h1 : (37 / 180 : ℝ) * responseAdjointCoordinates 3 0 +
      (143 / 540 : ℝ) * responseAdjointCoordinates 3 1 =
      (37 / 180 : ℝ) + (5 / 72 : ℝ) * coefficient 3 2 := by
    simpa only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hG10, hG11, hH1]
      using congrFun hnormal (1 : Fin 2)
  have hdiff : responseAdjointCoordinates 3 0 - responseAdjointCoordinates 3 1 =
      1 + (103 / 122 : ℝ) * coefficient 3 2 := by
    linarith only [h0, h1]
  rw [hdiff]
  linarith only [hk2lower]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (3, 0), (3, 1), ?_⟩
  change responseAdjointCoordinates 3 0 ≠ responseAdjointCoordinates 3 1
  intro heq
  have hgap := coordinates_gap_at_three
  rw [heq] at hgap
  linarith

-- The original whole-family registration now has no missing proof parameter.
-- Its full all-N law, actual-plus-one intervention and sensitivity stay intact.
def equationFamily : Registration arena (type_of% (@source_equation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_equation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence


end Coordinates

namespace Residual

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ N m => responseAdjointResidual N m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ N m => responseAdjointResidual N m + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N m : ℕ), R.readout () N m =
    response N m - responseAdjointCoordinates N 0 -
      responseAdjointCoordinates N 1 * ((m : ℝ) / N)

private theorem source_equation (N m : ℕ) : responseAdjointResidual N m =
    response N m - responseAdjointCoordinates N 0 -
      responseAdjointCoordinates N 1 * ((m : ℝ) / N) := by
  rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 3 3
  change responseAdjointResidual 3 3 + 1 = responseAdjointResidual 3 3 at he
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  rcases or6_response_adjoint_identity_and_signs (N := 3) (by norm_num) with
    ⟨_, _, _, _, ⟨p, hp, hpos⟩, ⟨n, hn, hneg⟩, _, _⟩
  refine ⟨3, p, n, ?_⟩
  change responseAdjointResidual 3 p ≠ responseAdjointResidual 3 n
  exact ne_of_gt (hneg.trans hpos)

def equationFamily : Registration arena (type_of% (@source_equation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@source_equation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

end Residual

end Reg.D5.S3.Arith.Robin.OriginalResidualResponseAdjoint.DefinitionEquations

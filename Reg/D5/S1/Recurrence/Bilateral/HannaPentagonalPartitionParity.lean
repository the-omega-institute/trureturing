import D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open PowerSeries
open scoped PowerSeries.WithPiTopology
open _root_.D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := (PowerSeries ℤ)ˣ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ _ state => coeff state.2 (state.1 : PowerSeries ℤ))
    (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ k : ℤ, (exponent k : ℤ) = k * (3 * k + 1) / 2 ∧
      0 ≤ (exponent k : ℤ) ∧ 2 * (exponent k : ℤ) = k * (3 * k + 1)) ∧
    (∀ (A : (PowerSeries ℤ)ˣ) (N : ℕ) (k : ℤ),
      k ∉ Finset.Icc (-(N : ℤ)) N →
      coeff N (X ^ exponent k * (↑(A ^ (3 * k)) : PowerSeries ℤ)) = 0 ∧
      coeff N (X ^ exponent k * (↑(A ^ (-(3 * k + 1))) : PowerSeries ℤ)) = 0) ∧
    (∀ A : (PowerSeries ℤ)ˣ, HasSum (term A) (bilateral A)) ∧
    Original (generatingUnit (R := ℤ)) ∧
    (∀ A : (PowerSeries ℤ)ˣ, Original A →
      constantCoeff (A : PowerSeries ℤ) = 1 ∧ A = generatingUnit ∧
      ∀ n : ℤ, 1 ≤ n → 2 ∣ r.readout () () (A, n.toNat) ∧
        (r.readout () () (A, n.toNat) / 2) % 2 =
          (partitionCount (n - 1).toNat : ℤ) % 2) ∧
    partitionCount 0 = 1 ∧
    (∀ n : ℤ, 0 ≤ n → a n = coeff n.toNat (generatingSeries (R := ℤ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp := (h.2.2.2.2.1 generatingUnit result.2.2.2.1).2.2 1 (by decide)
  have hc := result.2.2.2.2.2.1
  norm_num [rejected, realize, hc] at hp

private theorem actual_law : arena.Law actual := result

/-- The original assertion is reconstructed without removing any clause. -/
def evidence : Registration arena LiteralResolution where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), ((1 : (PowerSeries ℤ)ˣ), 0), ((1 : (PowerSeries ℤ)ˣ), 1), ?_⟩
    simp [actual, realize]

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity.result)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity.informationUnit
  realizationName := `Reg.D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ state => coeff state.2 (state.1 : PowerSeries ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S1.Recurrence.Bilateral.HannaPentagonalPartitionParity

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SubsetSpectrum.RealClassification
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.SubsetSpectrum.RealClassification

open _root_.D5.S3.Combinatorics.SubsetSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun m => Fin m → ℝ)
    (fun _ => Multiset ℝ)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) (_m : ℕ) b => evenSubsetSums Finset.univ b)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) (_m : ℕ) _b => (0 : Multiset ℝ))
    (fun e => nomatch e)

/-- The entire classifier telescope, varying only the observed even spectrum. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ}, 3 ≤ m → Odd m → ∀ b c : Fin m → ℝ,
    R.readout () m b = R.readout () m c ↔
      ∃ σ : Equiv.Perm (Fin m), ∃ I : Finset (Fin m), Even I.card ∧
        (∑ i ∈ I, b i) = 0 ∧ ∀ i, c (σ i) = if i ∈ I then -b i else b i

private theorem zero_one_not_related :
    ¬ ∃ σ : Equiv.Perm (Fin 3), ∃ I : Finset (Fin 3), Even I.card ∧
      (∑ i ∈ I, (0 : ℝ)) = 0 ∧
        ∀ i, (1 : ℝ) = if i ∈ I then -(0 : ℝ) else 0 := by
  rintro ⟨σ, I, _he, _hz, hi⟩
  have h := hi 0
  split_ifs at h <;> norm_num at h

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact zero_one_not_related ((h (m := 3) (by decide) (by decide)
    (fun _ => 0) (fun _ => 1)).mp rfl)

def family : Registration arena (type_of% (@real_even_spectrum_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨real_even_spectrum_classification, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(3 : ℕ), (fun _ => (0 : ℝ)), (fun _ => (1 : ℝ)), ?_⟩
    intro h
    exact zero_one_not_related ((real_even_spectrum_classification
      (m := 3) (by decide) (by decide) (fun _ => 0) (fun _ => 1)).mp h)

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@real_even_spectrum_classification) (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.SubsetSpectrum.real_even_spectrum_classification.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SubsetSpectrum.RealClassification.family
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
    (fun (_ : Unit) (_m : ℕ) b => evenSubsetSums Finset.univ b)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SubsetSpectrum.RealClassification
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.SubsetSpectrum.RealClassification

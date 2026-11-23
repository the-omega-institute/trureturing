import Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
import D5.S3.Fourier.Concentration.DegreeSpectrumPacking

/-! The gap guarantee depends on the frequencies used to evaluate the two degree vectors. -/

namespace Reg.D5.S3.Fourier.Concentration.DegreeSpectrumPacking

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.DegreeSpectrumPacking
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialFrequency)
open FiniteSpectralPerturbation (actual frequencySignature)
open FiniteSineMissingWindow (sensitivity)
open LeanInformationAudit Finset

noncomputable section

universe u

private def rejected : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ q j => q.2 j + 3) (fun e => nomatch e)

abbrev frequencyArena : Arena where
  signature := frequencySignature.{u}
  Law V := ∀ {J : Type u} [Fintype J] (g : J → ℝ) (p : ℕ) {a b : ℝ}
    (_ : ∀ j, g j ∈ Set.Icc a b)
    (_ : 2 ≤ Nat.multichoose (Fintype.card J) p),
    ∃ m n : J → ℕ, m ≠ n ∧ (∑ j, m j) = p ∧ (∑ j, n j) = p ∧
      let gap := |monomialFrequency (V.readout () ⟨J, g⟩) m - monomialFrequency g n|
      gap ≤ (p : ℝ) * (b - a) / ((Nat.multichoose (Fintype.card J) p : ℝ) - 1) ∧
        (3 ≤ Fintype.card J ∧ 2 ≤ p →
          gap ≤ (p : ℝ) * (b - a) / (Nat.multichoose (Fintype.card J) p : ℝ))

private theorem rejected_law : ¬ frequencyArena.{u}.Law rejected := by
  intro law
  let i : ULift.{u} Bool := ULift.up false
  let j : ULift.{u} Bool := ULift.up true
  have hij : i ≠ j := by decide
  have huniv : (univ : Finset (ULift.{u} Bool)) = {i, j} := by
    ext x
    rcases x with ⟨b⟩
    cases b <;> simp [i, j]
  have hsum {A : Type} [AddCommMonoid A] (f : ULift.{u} Bool → A) :
      (∑ x, f x) = f i + f j := by rw [huniv, sum_insert (by simpa using hij), sum_singleton]
  let g : ULift.{u} Bool → ℝ := fun x => if x.down then 1 else 0
  have hg (x : ULift.{u} Bool) : g x ∈ Set.Icc (0 : ℝ) 1 := by
    rcases x with ⟨b⟩
    cases b <;> norm_num [g]
  have hc : Nat.multichoose (Fintype.card (ULift.{u} Bool)) 1 = 2 := by
    simp
  obtain ⟨m, n, _, hm, hn, hgap, _⟩ := law g 1 (a := 0) (b := 1) hg hc.ge
  rw [hsum m] at hm
  rw [hsum n] at hn
  have hmR : (m i : ℝ) + m j = 1 := by exact_mod_cast hm
  have hnR : (n i : ℝ) + n j = 1 := by exact_mod_cast hn
  change |monomialFrequency (fun x => g x + 3) m - monomialFrequency g n| ≤ _ at hgap
  rw [hc] at hgap
  simp only [monomialFrequency, hsum] at hgap
  norm_num [g, i, j] at hgap
  have hmj : 0 ≤ (m j : ℝ) := Nat.cast_nonneg _
  have hni : 0 ≤ (n i : ℝ) := Nat.cast_nonneg _
  linarith [(abs_le.mp hgap).2]

def frequencyEvidence :
    Registration frequencyArena.{u} (type_of% @exists_close_degree_vectors.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_close_degree_vectors.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity frequencyArena.Law actual rejected rejected_law
  dependence := (FiniteSpectralPerturbation.frequencyEvidence.{u}).dependence

def frequencyRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_close_degree_vectors.{u}) (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.DegreeSpectrumPacking.frequencyUnit
  realizationName :=
    `Reg.D5.S3.Fourier.Concentration.DegreeSpectrumPacking.frequencyEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨frequencyArena.{u}⟩
  objectArena := .source ⟨frequencyArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source frequencyArena.{u} ⟨frequencyEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.DegreeSpectrumPacking
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "value",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms frequencyRegistration

end

end Reg.D5.S3.Fourier.Concentration.DegreeSpectrumPacking

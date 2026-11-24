/- GID: D5/S3/Fourier/Concentration/DegreeTwoMomentWitness
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/DegreeTwoMomentWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.degreeOneDeterminesDegreeTwo; result=D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.degree_one_does_not_determine_degree_two; claim=D5/S3/Fourier/Concentration/DegreeTwoMomentWitness.degreeOneDeterminesDegreeTwo
   digest: Matched degree-one data permit different degree-two residual masses. -/

import D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy

/-! First-degree statistics with distinct degree-two residual masses. -/

open Finset
open D5.S3.Fourier.Concentration.DegreeTwoResidualDifferenceEnergy
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (nearCollisionMass)

set_option autoImplicit false

noncomputable section

namespace D5.S3.Fourier.Concentration.DegreeTwoMomentWitness

private def spectrumA : Fin 5 → ℤ := ![0, 1, 5, 6, 13]
private def spectrumB : Fin 5 → ℤ := ![0, 2, 3, 7, 13]

private theorem int_near_eq (a b : ℤ) {η : ℝ} (hη : 0 ≤ η) (hη' : η < 1) :
    |(a : ℝ) - (b : ℝ)| ≤ η ↔ a = b := by
  constructor
  · intro h
    have hcast : (((|a - b| : ℤ) : ℝ)) < 1 := by exact_mod_cast h.trans_lt hη'
    have hlt : |a - b| < (1 : ℤ) := by exact_mod_cast hcast
    have hnonneg : 0 ≤ |a - b| := abs_nonneg _
    have hz : |a - b| = 0 := by omega
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  · rintro rfl
    simpa using hη

private def equalPairCount {I : Type*} [DecidableEq I] (s : Finset I) (g : I → ℤ) : ℕ :=
  ∑ i ∈ s, ∑ j ∈ s, if g i = g j then 1 else 0

private theorem near_count {I : Type*} [DecidableEq I] (s : Finset I) (g : I → ℤ)
    {η : ℝ} (hη : 0 ≤ η) (hη' : η < 1) :
    nearCollisionMass s (fun i => (g i : ℝ)) (fun _ => 1) η = (equalPairCount s g : ℝ) := by
  unfold nearCollisionMass equalPairCount
  simp [int_near_eq _ _ hη hη', Nat.cast_sum]

private def edgeCount (g : Fin 5 → ℤ) : ℕ :=
  equalPairCount (univ.filter (fun e : Fin 5 × Fin 5 => e.1 ≠ e.2)) (fun e => g e.1 - g e.2)

private theorem collision_witness {η : ℝ} (hη : 0 ≤ η) (hη' : η < 1) :
    degreeTwoResidualMass (fun i => (spectrumA i : ℝ)) (fun _ => 1) η = 8 ∧
    degreeTwoResidualMass (fun i => (spectrumB i : ℝ)) (fun _ => 1) η = 0 := by
  have hformula (g : Fin 5 → ℤ) :
      degreeTwoResidualMass (fun i => (g i : ℝ)) (fun _ => 1) η =
        (edgeCount g : ℝ) - 2 * (∑ i, equalPairCount (univ.erase i) g : ℝ) +
          ∑ i : Fin 5, ((univ.erase i).card : ℝ) := by
    have h := degree_two_residual (fun i => (g i : ℝ)) (fun _ => 1) hη
    dsimp only at h
    simp only [one_mul, one_pow, ← Int.cast_sub, near_count _ _ hη hη'] at h
    simpa only [edgeCount, Finset.sum_const, nsmul_eq_mul, mul_one] using h
  rw [hformula spectrumA, hformula spectrumB]
  have hA : edgeCount spectrumA = 28 := by decide
  have hB : edgeCount spectrumB = 20 := by decide
  have hdA : (∑ i, equalPairCount (univ.erase i) spectrumA) = 20 := by decide
  have hdB : (∑ i, equalPairCount (univ.erase i) spectrumB) = 20 := by decide
  have hcard : (∑ i : Fin 5, (univ.erase i).card) = 20 := by decide
  simp only [← Nat.cast_sum, hA, hB, hdA, hdB, hcard]
  norm_num

private theorem common_stats :
    (∑ i, spectrumA i) = 25 ∧ (∑ i, spectrumB i) = 25 ∧
      (∑ i, spectrumA i ^ 2) = 231 ∧ (∑ i, spectrumB i ^ 2) = 231 ∧
      (∀ i, spectrumA i ∈ Set.Icc 0 13 ∧ spectrumB i ∈ Set.Icc 0 13) ∧
      spectrumA 0 = 0 ∧ spectrumB 0 = 0 ∧ spectrumA 4 = 13 ∧ spectrumB 4 = 13 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, by decide, by decide, by decide, by decide⟩
  intro i
  fin_cases i <;> decide

private theorem both_degree_one {η : ℝ} (hη : 0 ≤ η) (hη' : η < 1) :
    nearCollisionMass univ (fun i => (spectrumA i : ℝ)) (fun _ => 1) η = 5 ∧
    nearCollisionMass univ (fun i => (spectrumB i : ℝ)) (fun _ => 1) η = 5 := by
  have hA : equalPairCount univ spectrumA = 5 := by decide
  have hB : equalPairCount univ spectrumB = 5 := by decide
  rw [near_count _ _ hη hη', near_count _ _ hη hη', hA, hB]
  norm_num

/-- Two five-point spectra have identical band, mean, variance and degree-one
mass on resolutions below one, with distinct degree-two residual masses. -/
theorem exists_equal_first_data_distinct_degree_two :
    let secondMoment := fun g : Fin 5 → ℤ => ∑ i, g i ^ 2
    ∃ a b : Fin 5 → ℤ,
      (∑ i, a i) = 25 ∧ (∑ i, b i) = 25 ∧
      secondMoment a = 231 ∧ secondMoment b = 231 ∧
      (∀ i, a i ∈ Set.Icc 0 13 ∧ b i ∈ Set.Icc 0 13) ∧
      a 0 = 0 ∧ b 0 = 0 ∧ a 4 = 13 ∧ b 4 = 13 ∧
      ∀ η : ℝ, 0 ≤ η → η < 1 →
        nearCollisionMass univ (fun i => (a i : ℝ)) (fun _ => 1) η = 5 ∧
        nearCollisionMass univ (fun i => (b i : ℝ)) (fun _ => 1) η = 5 ∧
        degreeTwoResidualMass (fun i => (a i : ℝ)) (fun _ => 1) η = 8 ∧
        degreeTwoResidualMass (fun i => (b i : ℝ)) (fun _ => 1) η = 0 := by
  obtain ⟨ha, hb, ha2, hb2, hband, ha0, hb0, ha4, hb4⟩ := common_stats
  refine ⟨spectrumA, spectrumB, ha, hb, ha2, hb2, hband, ha0, hb0, ha4, hb4, ?_⟩
  intro η hη hη'
  obtain ⟨hcloseA, hcloseB⟩ := both_degree_one hη hη'
  exact ⟨hcloseA, hcloseB, collision_witness hη hη'⟩

/-- Sufficiency of the common band, first two moments and full degree-one
profile below unit resolution for the disjoint degree-two profile. -/
def degreeOneDeterminesDegreeTwo : Prop :=
  ∀ a b : Fin 5 → ℤ,
    (∑ i, a i) = (∑ i, b i) →
    (∑ i, a i ^ 2) = (∑ i, b i ^ 2) →
    (∀ i, a i ∈ Set.Icc 0 13 ∧ b i ∈ Set.Icc 0 13) →
    a 0 = 0 → b 0 = 0 → a 4 = 13 → b 4 = 13 →
    (∀ η : ℝ, 0 ≤ η → η < 1 →
      nearCollisionMass univ (fun i => (a i : ℝ)) (fun _ => 1) η =
        nearCollisionMass univ (fun i => (b i : ℝ)) (fun _ => 1) η) →
    ∀ η : ℝ, 0 ≤ η → η < 1 →
      degreeTwoResidualMass (fun i => (a i : ℝ)) (fun _ => 1) η =
        degreeTwoResidualMass (fun i => (b i : ℝ)) (fun _ => 1) η

/-- Identical degree-one profiles and moments allow different disjoint
degree-two profiles. -/
theorem degree_one_does_not_determine_degree_two : ¬ degreeOneDeterminesDegreeTwo := by
  intro determines
  obtain ⟨a, b, ha, hb, ha2, hb2, hband, ha0, hb0, ha4, hb4, mass⟩ :=
    exists_equal_first_data_distinct_degree_two
  have hfirst (η : ℝ) (hη : 0 ≤ η) (hη' : η < 1) := by
    obtain ⟨hleft, hright, _⟩ := mass η hη hη'
    exact hleft.trans hright.symm
  have h := determines a b (ha.trans hb.symm) (ha2.trans hb2.symm)
    hband ha0 hb0 ha4 hb4 hfirst 0 le_rfl zero_lt_one
  obtain ⟨_, _, hleft, hright⟩ := mass 0 le_rfl zero_lt_one
  rw [hleft, hright] at h
  norm_num at h

end D5.S3.Fourier.Concentration.DegreeTwoMomentWitness

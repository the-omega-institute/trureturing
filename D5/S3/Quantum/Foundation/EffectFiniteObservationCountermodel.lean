/- GID: D5/S3/Quantum/Foundation/EffectFiniteObservationCountermodel
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/EffectFiniteObservationCountermodel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite exact Born tests admit normalized Borel responses with sharp global defect and distance bounds. -/

import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.FiniteDimensional

namespace D5.S3.Quantum.Foundation.EffectFiniteObservationCountermodel

private abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

private def IsEffect {d : ℕ} (E : Mat d) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

private theorem effect_iff_order {d : ℕ} (E : Mat d) :
    IsEffect E ↔ 0 ≤ E ∧ E ≤ 1 := by
  exact and_congr Matrix.nonneg_iff_posSemidef.symm Matrix.le_iff.symm

private abbrev Effect (d : ℕ) := {E : Mat d // IsEffect E}

private def scalar (d : ℕ) (t : ℝ) : Mat d := t • 1

private theorem scalar_diagonal {d : ℕ} (i : Fin d) (t : ℝ) :
    ((scalar d t) i i).re = t := by
  simp [scalar]

private theorem scalar_injective {d : ℕ} (hd : 1 ≤ d) : Function.Injective (scalar d) := by
  intro s t h
  have he := congrArg (fun X : Mat d => (X ⟨0, by omega⟩ ⟨0, by omega⟩).re) h
  simpa only [scalar_diagonal] using he

private theorem scalar_effect {d : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsEffect (scalar d t) := by
  apply (effect_iff_order _).mpr
  refine ⟨smul_nonneg ht0 (zero_le_one : (0 : Mat d) ≤ 1), ?_⟩
  simpa [scalar] using smul_le_smul_of_nonneg_right ht1 (zero_le_one : (0 : Mat d) ≤ 1)

private theorem born_bounds {d : ℕ} {ρ E : Mat d}
    (hρ : ρ.PosSemidef) (htr : Matrix.trace ρ = 1) (hE : IsEffect E) :
    0 ≤ (bornProbability ρ E).re ∧ (bornProbability ρ E).re ≤ 1 := by
  have h0 := (Complex.nonneg_iff.mp (hρ.trace_mul_nonneg hE.1)).1
  have h1 := (Complex.nonneg_iff.mp (hρ.trace_mul_nonneg hE.2)).1
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, htr, Complex.sub_re] at h1
  exact ⟨h0, by dsimp [bornProbability]; norm_num at h1; linarith⟩

private theorem born_scalar {d : ℕ} (ρ : Mat d) (htr : Matrix.trace ρ = 1) (t : ℝ) :
    (bornProbability ρ (scalar d t)).re = t := by
  simp [bornProbability, scalar, Matrix.trace_smul, htr]

private theorem measurable_born {d : ℕ} (ρ : Mat d) : Measurable (fun E : Mat d => (bornProbability ρ E).re) := by
  have hc : Continuous (fun E : Mat d => Matrix.trace (ρ * E)) :=
    (continuous_const.mul continuous_id).matrix_trace
  exact Complex.continuous_re.measurable.comp hc.measurable

/-- A finite set of actual effects misses all sufficiently small positive scalar effects.
No scalarity or full-rank premise is imposed on the tested matrices. -/
private theorem finite_scalar_gap {d : ℕ} (hd : 1 ≤ d) (T : Finset (Effect d)) :
    ∃ a : ℝ, 0 < a ∧ 3 * a < 1 ∧
      ∀ E ∈ T, ∀ t : ℝ, 0 < t → t ≤ 3 * a → scalar d t ≠ E.1 := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨1/4, by norm_num, by norm_num, ?_⟩
      simp
  | @insert E T _hET ih =>
      obtain ⟨a, ha, ha1, hgap⟩ := ih
      by_cases hdiag : 0 < (E.1 i i).re
      · let b := min a ((E.1 i i).re / 4)
        have hb : 0 < b := lt_min ha (by positivity)
        have hba : b ≤ a := min_le_left _ _
        have hbd : b ≤ (E.1 i i).re / 4 := min_le_right _ _
        refine ⟨b, hb, by linarith, ?_⟩
        intro F hF t ht htb heq
        rcases Finset.mem_insert.mp hF with hFE | hFT
        · subst F
          have hdg := congrArg (fun X : Mat d => (X i i).re) heq
          rw [scalar_diagonal] at hdg
          linarith
        · exact hgap F hFT t ht (by linarith) heq
      · refine ⟨a, ha, ha1, ?_⟩
        intro F hF t ht hta heq
        rcases Finset.mem_insert.mp hF with hFE | hFT
        · subst F
          have hdg := congrArg (fun X : Mat d => (X i i).re) heq
          rw [scalar_diagonal] at hdg
          exact hdiag (hdg ▸ ht)
        · exact hgap F hFT t ht hta heq

private def spike (a : ℝ) (n : ℕ) : ℝ := a / ((n : ℝ) + 1)

private theorem spike_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < spike a n := by
  dsimp [spike]
  positivity

private theorem spike_le {a : ℝ} (ha : 0 < a) (n : ℕ) : spike a n ≤ a := by
  dsimp [spike]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

private theorem spike_small {a η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, spike a n < η := by
  obtain ⟨n, hn⟩ := exists_nat_gt (a / η)
  refine ⟨n, ?_⟩
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  have hn' := (div_lt_iff₀ hη).mp hn
  nlinarith

/-- Every finite collection of exact Born readouts admits a normalized Borel
response with maximal binary defect and uniform distance one from every density.
The response is chosen after the finite collection. -/
theorem finite_observation_countermodel
    (d : ℕ) (hd : 1 ≤ d)
    (T : Finset {E : Matrix (Fin d) (Fin d) ℂ // E.PosSemidef ∧ (1 - E).PosSemidef})
    (ρstar : Matrix (Fin d) (Fin d) ℂ)
    (hρstar : ρstar.PosSemidef) (htrstar : Matrix.trace ρstar = 1) :
    ∃ p : Matrix (Fin d) (Fin d) ℂ → ℝ,
      Measurable p ∧
      (∀ E : Matrix (Fin d) (Fin d) ℂ,
        E.PosSemidef ∧ (1 - E).PosSemidef → 0 ≤ p E ∧ p E ≤ 1) ∧
      p 0 = 0 ∧ p 1 = 1 ∧
      (∀ E ∈ T, p E.1 = (Matrix.trace (ρstar * E.1)).re) ∧
      (∀ E F : Matrix (Fin d) (Fin d) ℂ, E.PosSemidef → F.PosSemidef →
        (1 - (E + F)).PosSemidef → |p (E + F) - p E - p F| ≤ 2) ∧
      (∃ E F : Matrix (Fin d) (Fin d) ℂ,
        E ≠ F ∧ E.PosSemidef ∧ F.PosSemidef ∧
        (1 - (E + F)).PosSemidef ∧ |p (E + F) - p E - p F| = 2) ∧
      (∀ ρ : Matrix (Fin d) (Fin d) ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
        (∀ E : Matrix (Fin d) (Fin d) ℂ,
          E.PosSemidef ∧ (1 - E).PosSemidef →
            |p E - (Matrix.trace (ρ * E)).re| ≤ 1) ∧
        ∀ η : ℝ, 0 < η → ∃ E : Matrix (Fin d) (Fin d) ℂ,
          (E.PosSemidef ∧ (1 - E).PosSemidef) ∧
            1 - η < |p E - (Matrix.trace (ρ * E)).re|) := by
  classical
  obtain ⟨a, ha, ha1, hgap⟩ := finite_scalar_gap hd T
  have hinj := scalar_injective hd
  let H : Set (Mat d) := insert (scalar d (2 * a))
    (Set.range (fun n : ℕ => scalar d (spike a n)))
  let p : Mat d → ℝ := fun E =>
    if E ∈ H then 1 else if E = scalar d (3 * a) then 0 else (bornProbability ρstar E).re
  have hHcount : H.Countable := (Set.countable_range _).insert _
  have hHscalar (E : Mat d) (hE : E ∈ H) :
      ∃ t : ℝ, 0 < t ∧ t ≤ 2 * a ∧ E = scalar d t := by
    rcases Set.mem_insert_iff.mp hE with heq | hrange
    · exact ⟨2 * a, by linarith, le_rfl, heq⟩
    · obtain ⟨n, rfl⟩ := hrange
      exact ⟨spike a n, spike_pos ha n, (spike_le ha n).trans (by linarith), rfl⟩
  have hHnot (c : ℝ) (hc : c ≤ 0 ∨ 2 * a < c) : scalar d c ∉ H := by
    intro h
    obtain ⟨t, ht, hta, heq⟩ := hHscalar _ h
    have hct := hinj heq
    rcases hc with hc | hc <;> linarith
  have hzH : (0 : Mat d) ∉ H := by
    simpa only [scalar, zero_smul] using hHnot 0 (Or.inl le_rfl)
  have hoH : (1 : Mat d) ∉ H := by
    simpa only [scalar, one_smul] using hHnot 1 (Or.inr (by linarith))
  have h30 : scalar d (3 * a) ≠ (0 : Mat d) := by
    intro h
    have h' : 3 * a = 0 := hinj (by simpa only [scalar, zero_smul] using h)
    linarith
  have h31 : scalar d (3 * a) ≠ (1 : Mat d) := by
    intro h
    have h' : 3 * a = 1 := hinj (by simpa only [scalar, one_smul] using h)
    linarith
  have hmeas : Measurable p := by
    exact Measurable.ite hHcount.measurableSet measurable_const
      (Measurable.ite (measurableSet_singleton _) measurable_const (measurable_born ρstar))
  have hrange (E : Mat d) (hE : IsEffect E) : 0 ≤ p E ∧ p E ≤ 1 := by
    dsimp only [p]
    split
    · norm_num
    · split
      · norm_num
      · exact born_bounds hρstar htrstar hE
  have hpzero : p 0 = 0 := by
    dsimp only [p]
    rw [ite_eq_right hzH, ite_eq_right (Ne.symm h30)]
    simp [bornProbability]
  have hpone : p 1 = 1 := by
    dsimp only [p]
    rw [ite_eq_right hoH, ite_eq_right (Ne.symm h31)]
    simp [bornProbability, htrstar]
  have hmatch : ∀ E ∈ T, p E.1 = (Matrix.trace (ρstar * E.1)).re := by
    intro E hE
    have hEH : E.1 ∉ H := by
      intro hh
      obtain ⟨t, ht, hta, heq⟩ := hHscalar _ hh
      exact hgap E hE t ht (by linarith) heq.symm
    have hEC : E.1 ≠ scalar d (3 * a) := by
      exact Ne.symm (hgap E hE (3 * a) (by linarith) le_rfl)
    dsimp only [p]
    rw [ite_eq_right hEH, ite_eq_right hEC]
    rfl
  have hpSpike (n : ℕ) : p (scalar d (spike a n)) = 1 := by
    have hmem : scalar d (spike a n) ∈ H :=
      Set.mem_insert_of_mem _ ⟨n, rfl⟩
    dsimp only [p]
    rw [ite_eq_left hmem]
  have hpa : p (scalar d a) = 1 := by
    simpa only [spike, Nat.cast_zero, zero_add, div_one] using hpSpike 0
  have hp2 : p (scalar d (2 * a)) = 1 := by
    have hmem : scalar d (2 * a) ∈ H := Set.mem_insert _ _
    dsimp only [p]
    rw [ite_eq_left hmem]
  have hp3 : p (scalar d (3 * a)) = 0 := by
    dsimp only [p]
    rw [ite_eq_right (hHnot (3 * a) (Or.inr (by linarith))), ite_eq_left rfl]
  have hdefect : ∀ E F : Mat d, E.PosSemidef → F.PosSemidef →
      (1 - (E + F)).PosSemidef → |p (E + F) - p E - p F| ≤ 2 := by
    intro E F hE hF hEF
    have hsum : IsEffect (E + F) := ⟨hE.add hF, hEF⟩
    have hsum1 := ((effect_iff_order _).mp hsum).2
    have hEE : IsEffect E := (effect_iff_order _).mpr
      ⟨hE.nonneg, (le_add_of_nonneg_right hF.nonneg).trans hsum1⟩
    have hFF : IsEffect F := (effect_iff_order _).mpr
      ⟨hF.nonneg, (le_add_of_nonneg_left hE.nonneg).trans hsum1⟩
    have hbE := hrange E hEE
    have hbF := hrange F hFF
    have hbS := hrange (E + F) hsum
    apply abs_le.mpr
    constructor <;> linarith
  have hattain : ∃ E F : Mat d, E ≠ F ∧ E.PosSemidef ∧ F.PosSemidef ∧
      (1 - (E + F)).PosSemidef ∧ |p (E + F) - p E - p F| = 2 := by
    have h1 := scalar_effect (d := d) ha.le (show a ≤ 1 by linarith)
    have h2 := scalar_effect (d := d) (show 0 ≤ 2 * a by linarith)
      (show 2 * a ≤ 1 by linarith)
    have h3 := scalar_effect (d := d) (show 0 ≤ 3 * a by linarith) ha1.le
    have hsum : scalar d a + scalar d (2 * a) = scalar d (3 * a) := by
      change a • (1 : Mat d) + (2 * a) • 1 = (3 * a) • 1
      rw [← add_smul]
      congr 1
      ring
    refine ⟨scalar d a, scalar d (2 * a), ?_, h1.1, h2.1, ?_, ?_⟩
    · intro heq
      have h := hinj heq
      linarith
    · rw [hsum]
      exact h3.2
    · rw [hsum, hp3, hpa, hp2]
      norm_num
  have hdist : ∀ ρ : Mat d, ρ.PosSemidef → Matrix.trace ρ = 1 →
      (∀ E : Mat d, IsEffect E → |p E - (Matrix.trace (ρ * E)).re| ≤ 1) ∧
      ∀ η : ℝ, 0 < η → ∃ E : Mat d,
        IsEffect E ∧ 1 - η < |p E - (Matrix.trace (ρ * E)).re| := by
    intro ρ hρ htr
    constructor
    · intro E hE
      have hbE := hrange E hE
      have hbρ := born_bounds hρ htr hE
      change |p E - (bornProbability ρ E).re| ≤ 1
      apply abs_le.mpr
      constructor <;> linarith
    · intro η hη
      obtain ⟨n, hn⟩ := spike_small (a := a) hη
      refine ⟨scalar d (spike a n), scalar_effect (spike_pos ha n).le
        ((spike_le ha n).trans (by linarith)), ?_⟩
      change 1 - η < |p (scalar d (spike a n)) - (bornProbability ρ (scalar d (spike a n))).re|
      rw [hpSpike, born_scalar ρ htr]
      have hsp1 : spike a n ≤ 1 := (spike_le ha n).trans (by linarith)
      rw [abs_of_nonneg (by linarith)]
      linarith
  exact ⟨p, hmeas, hrange, hpzero, hpone, hmatch, hdefect, hattain, hdist⟩

end D5.S3.Quantum.Foundation.EffectFiniteObservationCountermodel

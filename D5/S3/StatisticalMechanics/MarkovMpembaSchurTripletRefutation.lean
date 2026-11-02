/- GID: D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation.claim; result=D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation.result; claim=D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation.claim
   digest: Four reversible levels refute the static Schur-reduced Mpemba triplet test. -/

import D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation

/-!
# Static Schur-reduced Mpemba triplets

The frozen four-level witness of `MarkovMpembaTripletRefutation` also fails condition (3) in
every triplet obtained by statically eliminating the remaining level, while its slow mode shows
the Mpemba effect. This refutes the static Schur-reduced form of the triplet implication.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.MarkovMpembaSchurTripletRefutation

open D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation
  (generator DetailedBalance TripletCondition IsSlowMode MpembaEffect weights f rates energy small)

/-- Static Schur elimination of the state `s`: the off-diagonal entries of the Schur complement
`M_TT - M_Ts M_ss⁻¹ M_sT` of the rate matrix `M = generator a`, so that the reduced rate from `j`
to `i` is `a i j + a i s * a s j / d_s` with `d_s` the total rate leaving `s`. -/
noncomputable def schurRates {N : ℕ} (a : Fin N → Fin N → ℝ) (s : Fin N) :
    Fin N → Fin N → ℝ :=
  fun i j => generator a i j - generator a i s * generator a s j / generator a s s

/-- The static Schur-reduced triplet implication for four levels: if every original triplet and
every triplet of the three-level system obtained by statically eliminating the remaining state
fails condition (3), then no simple slowest mode shows the Mpemba effect. -/
def claim : Prop :=
  ∀ (E : Fin 4 → ℝ) (βb : ℝ) (a : Fin 4 → Fin 4 → ℝ),
    StrictMono E → 0 < βb → (∀ i j, i ≠ j → 0 < a i j) →
    DetailedBalance E βb a →
    (∀ i j k : Fin 4, i < j → j < k → ¬ TripletCondition E βb a i j k) →
    (∀ s i j k : Fin 4, i < j → j < k → s ≠ i → s ≠ j → s ≠ k →
      ¬ TripletCondition E βb (schurRates a s) i j k) →
    ∀ lam ℓ, IsSlowMode (generator a) lam ℓ → ¬ MpembaEffect E βb ℓ

set_option maxHeartbeats 1000000 in
-- Each reduced margin is an exact rational inequality at r = 16⁻⁶⁴.
private theorem schur_margins :
    ∀ s i j k : Fin 4, i < j → j < k → s ≠ i → s ≠ j → s ≠ k →
    schurRates (rates small) s i k *
        (1 + (weights small j / weights small i) * (weights small k / weights small j) / 2) -
      schurRates (rates small) s j k * (1 + (weights small k / weights small j) / 2) ≤
      schurRates (rates small) s i j * (1 - weights small j / weights small i) ∧
    schurRates (rates small) s i k * (weights small j / weights small i) ≤
      schurRates (rates small) s j k := by
  intro s i j k hij hjk hsi hsj hsk
  change i.val < j.val at hij
  change j.val < k.val at hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first | omega | (dsimp only at hij hjk <;> omega) | (simp at hij hjk <;> omega) | skip
  all_goals fin_cases s <;>
    first | exact absurd rfl hsi | exact absurd rfl hsj | exact absurd rfl hsk | skip
  all_goals
    simp only [schurRates, MarkovMpembaTripletRefutation.generator.eq_1, Fin.sum_univ_four]
    norm_num [MarkovMpembaTripletRefutation.rates.eq_1, MarkovMpembaTripletRefutation.weights.eq_1,
      MarkovMpembaTripletRefutation.mean.eq_1, MarkovMpembaTripletRefutation.small.eq_1,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.reduceFinMk, Fin.ofNat, Fin.succ,
      Fin.mk.injEq]

private theorem no_schur_triplets :
    ∀ s i j k : Fin 4, i < j → j < k → s ≠ i → s ≠ j → s ≠ k →
    ¬ TripletCondition energy 1 (schurRates (rates small) s) i j k := by
  intro s i j k hij hjk hsi hsj hsk
  obtain ⟨hfirst, hsecond⟩ := schur_margins s i j k hij hjk hsi hsj hsk
  simp only [MarkovMpembaTripletRefutation.TripletCondition.eq_1,
    MarkovMpembaTripletRefutation.bath_ratio]
  rintro (⟨_, h⟩ | ⟨_, h⟩) <;> linarith

theorem result : ¬ claim := by
  intro h
  exact (h energy 1 (rates small) MarkovMpembaTripletRefutation.increasing_energy (by norm_num)
    (MarkovMpembaTripletRefutation.rates_positive small
      MarkovMpembaTripletRefutation.small_bounds.1 MarkovMpembaTripletRefutation.small_bounds.2)
    MarkovMpembaTripletRefutation.reversible MarkovMpembaTripletRefutation.no_triplets
    no_schur_triplets (-1) (f small) MarkovMpembaTripletRefutation.slow_mode)
    MarkovMpembaTripletRefutation.effect

end D5.S3.StatisticalMechanics.MarkovMpembaSchurTripletRefutation

/- GID: D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Flat-plus-spike states have uniformly nonvanishing characteristic-three ambiguity. -/

import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The characteristic-three flat-plus-spike ambiguity profile

For a finite field `K` of characteristic three and any nontrivial complex additive
character, use `D a b f x = ψ (b * (x - a)) * f (x - a)` (the `X_a Z_b` convention).
The vector is the phase-zero specialization of Zhu–Wang, arXiv:2608.11850v1,
equation (62), whose stated characteristic-two domain is extended here only for
normalization and ambiguity. No projector-Gram spectral identity is assumed or
proved. In particular this module does not settle issue #13556's Rayleigh bound
for the family `q = 3^r`, `r ≥ 1`.
-/

namespace D5.S3.Quantum.Measurement.CharacteristicThreeSpikeAmbiguity

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

local notation "q" => (Fintype.card K : ℝ)
local notation "s" => Real.sqrt q
local notation "N" => (2 * q + 2 * s : ℝ)

/-- The unnormalized vector `sqrt(q) (|+⟩ + |0⟩)`. -/
private def rawSpike (x : K) : ℂ := 1 + if x = 0 then (s : ℂ) else 0

/-- The unit vector `( |+⟩ + |0⟩ ) / sqrt(2 + 2 / sqrt(q))`, written
with a common denominator to avoid divisions by `sqrt(q)` in finite sums. -/
def spikeState (K : Type*) [Field K] [Fintype K] [DecidableEq K] (x : K) : ℂ :=
  (1 + if x = 0 then (Real.sqrt (Fintype.card K : ℝ) : ℂ) else 0) /
    (Real.sqrt (2 * (Fintype.card K : ℝ) + 2 * Real.sqrt (Fintype.card K : ℝ)) : ℂ)

/-- The ambiguity coefficient `⟨f, X_a Z_b f⟩`, with translation before modulation
in the operator word and conjugation in the first argument of the pairing. -/
def ambiguity (ψ : AddChar K ℂ) (f : K → ℂ) (a b : K) : ℂ :=
  ∑ x, star (f x) * ψ (b * (x - a)) * f (x - a)

omit [DecidableEq K] in
private theorem card_pos : 0 < q := by exact_mod_cast Fintype.card_pos

omit [DecidableEq K] in
private theorem scale_sq : s ^ 2 = q := Real.sq_sqrt (le_of_lt card_pos)

omit [DecidableEq K] in
private theorem mass_pos : 0 < N := by
  have := card_pos (K := K)
  have := Real.sqrt_nonneg q
  positivity

private theorem raw_mass : ∑ x : K, Complex.normSq (rawSpike x) = N := by
  have he : ∀ x : K, Complex.normSq (rawSpike x) =
      1 + if x = 0 then q + 2 * s else 0 := by
    intro x
    by_cases hx : x = 0
    · simp [rawSpike, hx, Complex.normSq_apply]
      nlinarith [scale_sq (K := K)]
    · simp [rawSpike, hx]
  simp_rw [he, Finset.sum_add_distrib]
  simp
  ring

/-- Normalization is proved from the coordinates, without any character hypothesis. -/
theorem spikeState_normalized : ∑ x : K, Complex.normSq (spikeState K x) = 1 := by
  have hN : N ≠ 0 := ne_of_gt mass_pos
  have he : ∀ x : K, Complex.normSq (spikeState K x) = Complex.normSq (rawSpike x) / N := by
    intro x
    rw [spikeState, show (1 + if x = 0 then (s : ℂ) else 0) = rawSpike x from rfl,
      map_div₀, Complex.normSq_ofReal, ← sq, Real.sq_sqrt (le_of_lt mass_pos)]
  simp_rw [he]
  rw [← Finset.sum_div, raw_mass, div_self hN]

private theorem raw_ambiguity (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (a b : K) :
    ambiguity ψ rawSpike a b =
      (if b = 0 then (q : ℂ) else 0) + (if a = 0 then (q : ℂ) else 0) +
        (s : ℂ) * (1 + ψ (-b * a)) := by
  have hs : (s : ℂ) ^ 2 = (q : ℂ) := by exact_mod_cast (scale_sq (K := K))
  have he : ∀ x : K, star (rawSpike x) * ψ (b * (x - a)) * rawSpike (x - a) =
      ψ (b * (x - a)) + (if x = 0 then (s : ℂ) * ψ (-b * a) else 0) +
        (if x = a then (s : ℂ) else 0) +
        (if x = 0 then (if a = 0 then (q : ℂ) else 0) else 0) := by
    intro x
    by_cases hx : x = 0 <;> by_cases ha : a = 0 <;> by_cases hxa : x = a
    all_goals simp_all [rawSpike, sub_eq_zero, star_add]
    all_goals first | ring1 | linear_combination hs
  have hsum : ∑ x : K, ψ (b * (x - a)) = if b = 0 then (q : ℂ) else 0 := by
    calc
      _ = ∑ x : K, ψ (b * x) :=
        Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
      _ = _ := by simpa [mul_comm] using AddChar.sum_mulShift b (AddChar.IsPrimitive.of_ne_one hψ)
  unfold ambiguity
  simp_rw [he, Finset.sum_add_distrib]
  rw [hsum]
  simp
  ring

/-- The exact flat-plus-spike ambiguity formula in the finite-field convention. -/
theorem spikeState_ambiguity (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (a b : K) :
    ambiguity ψ (spikeState K) a b =
      ((if b = 0 then (q : ℂ) else 0) + (if a = 0 then (q : ℂ) else 0) +
        (s : ℂ) * (1 + ψ (-b * a))) / (N : ℂ) := by
  have hden : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    exact_mod_cast (by nlinarith [Real.sq_sqrt (le_of_lt (mass_pos (K := K)))] :
      Real.sqrt N * Real.sqrt N = N)
  have he : ∀ x : K, star (spikeState K x) * ψ (b * (x - a)) * spikeState K (x - a) =
      (star (rawSpike x) * ψ (b * (x - a)) * rawSpike (x - a)) / (N : ℂ) := by
    intro x
    change star (rawSpike x / (Real.sqrt N : ℂ)) * ψ (b * (x - a)) *
      (rawSpike (x - a) / (Real.sqrt N : ℂ)) = _
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    rw [div_mul_eq_mul_div, div_mul_div_comm, hden]
  unfold ambiguity
  simp_rw [he]
  rw [← Finset.sum_div, ← ambiguity, raw_ambiguity ψ hψ]

/-- The cubic-root obstruction to cancellation: unlike a sign, a cubic root
cannot cancel the positive phase in `1 + z`. -/
private theorem cubic_root_bound (z : ℂ) (hz : z ^ 3 = 1) :
    1 ≤ Complex.normSq (1 + z) := by
  have hn : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_eq_one_of_pow_eq_one hz (by decide)]
    norm_num
  by_cases h1 : z = 1
  · norm_num [h1]
  · have hfac : (z - 1) * (z ^ 2 + z + 1) = 0 := by
      calc
        _ = z ^ 3 - 1 := by ring
        _ = 0 := by rw [hz]; ring
    have hquad := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr h1)
    have he : 1 + z = -(z ^ 2) := by linear_combination hquad
    rw [he, Complex.normSq_neg, map_pow, hn]
    norm_num

variable [CharP K 3]

omit [Fintype K] [DecidableEq K] in
private theorem character_cube (ψ : AddChar K ℂ) (x : K) : ψ x ^ 3 = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
    AddChar.map_zero_eq_one]

/-- Every nonidentity ambiguity intensity has the explicit lower bound
`1 / (4 (sqrt(q) + 1)^2)`. This covers extension fields, not cyclic `ZMod q`. -/
theorem spikeState_intensity_lower_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    1 / (4 * (s + 1) ^ 2) ≤ Complex.normSq (ambiguity ψ (spikeState K) a b) := by
  have hs : 0 < s := Real.sqrt_pos.2 card_pos
  have hN : 0 < N := mass_pos
  have hden : 0 < 4 * (s + 1) ^ 2 := by positivity
  have hscale : q / N ^ 2 = 1 / (4 * (s + 1) ^ 2) := by
    have hmass : N = 2 * s * (s + 1) := by nlinarith [scale_sq (K := K)]
    rw [hmass]
    nth_rw 1 [← scale_sq (K := K)]
    field_simp
    ring
  have hnum : q ≤ Complex.normSq
      ((if b = 0 then (q : ℂ) else 0) + (if a = 0 then (q : ℂ) else 0) +
        (s : ℂ) * (1 + ψ (-b * a))) := by
    by_cases ha : a = 0
    · have hb : b ≠ 0 := hab.resolve_left (not_ne_iff.mpr ha)
      simp [ha, hb, Complex.normSq_apply]
      nlinarith [scale_sq (K := K), card_pos (K := K)]
    · by_cases hb : b = 0
      · simp [ha, hb, Complex.normSq_apply]
        nlinarith [scale_sq (K := K), card_pos (K := K)]
      · simp only [if_neg ha, if_neg hb, zero_add, Complex.normSq_mul,
          Complex.normSq_ofReal]
        have hc := cubic_root_bound (ψ (-b * a)) (character_cube ψ (-b * a))
        nlinarith [scale_sq (K := K)]
  rw [spikeState_ambiguity ψ hψ, map_div₀]
  have hn : Complex.normSq (N : ℂ) = N ^ 2 := by
    rw [Complex.normSq_ofReal, sq]
  rw [hn, ← hscale]
  exact div_le_div_of_nonneg_right hnum (sq_nonneg N)

/-- The ambiguity-side SIC normalization has the dimension-independent lower
bound `1/8` for the proved unit vector. The Gram/Rayleigh interpretation still
requires a separate proof. -/
theorem spikeState_uniform_ambiguity_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    (∑ x : K, Complex.normSq (spikeState K x) = 1) ∧
      (1 / 8 : ℝ) ≤ (q + 1) * Complex.normSq (ambiguity ψ (spikeState K) a b) := by
  refine ⟨spikeState_normalized, ?_⟩
  have hden : 0 < 4 * (s + 1) ^ 2 := by positivity
  have hl := spikeState_intensity_lower_bound ψ hψ a b hab
  have hratio : (1 / 8 : ℝ) ≤ (q + 1) / (4 * (s + 1) ^ 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith [scale_sq (K := K), sq_nonneg (s - 1)]
  calc
    _ ≤ (q + 1) / (4 * (s + 1) ^ 2) := hratio
    _ = (q + 1) * (1 / (4 * (s + 1) ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

#print axioms spikeState_normalized
#print axioms spikeState_ambiguity
#print axioms spikeState_intensity_lower_bound
#print axioms spikeState_uniform_ambiguity_bound

end

end D5.S3.Quantum.Measurement.CharacteristicThreeSpikeAmbiguity

/- GID: D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FiveModeMixedCoordinates
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Visible occupancies and the hidden log cross-ratio give a global Fisher chart. -/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

namespace D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates

open Real

noncomputable section

/-- Strictly positive laws on the five admissible words `000, 100, 010, 001, 101`. -/
def openSimplex : Set (Fin 5 → ℝ) := {p | (∀ s, 0 < p s) ∧ ∑ s, p s = 1}

/-- Occupancies of the first site, the last site and the middle site. -/
def visible (p : Fin 5 → ℝ) : ℝ × ℝ × ℝ := (p 1 + p 4, p 3 + p 4, p 2)

/-- The interior of the square pyramid `X + Z ≤ 1`, `Y + Z ≤ 1`, `X, Y, Z ≥ 0`. -/
def openPyramid : Set (ℝ × ℝ × ℝ) :=
  {v | 0 < v.1 ∧ 0 < v.2.1 ∧ 0 < v.2.2 ∧ v.1 + v.2.2 < 1 ∧ v.2.1 + v.2.2 < 1}

/-- The hidden coordinate: the log cross-ratio of the four base corners. -/
def hiddenChi (p : Fin 5 → ℝ) : ℝ := log (p 0) + log (p 4) - log (p 1) - log (p 3)

/-- The base-loop direction `(1, -1, 0, -1, 1)`. -/
def hiddenDirection : Fin 5 → ℝ := ![1, -1, 0, -1, 1]

/-- The Fisher inner product at `p`. -/
def fisher (p u v : Fin 5 → ℝ) : ℝ := ∑ s, u s * v s / p s

/-- The hidden coordinate equals `c` exactly when the base cross product carries `exp c`. -/
private theorem hiddenChi_eq_iff {p : Fin 5 → ℝ} (hp : ∀ s, 0 < p s) (c : ℝ) :
    hiddenChi p = c ↔ p 0 * p 4 = exp c * (p 1 * p 3) := by
  have h0 := hp 0; have h1 := hp 1; have h3 := hp 3; have h4 := hp 4
  have hchi : hiddenChi p = log (p 0 * p 4) - log (p 1 * p 3) := by
    unfold hiddenChi
    rw [log_mul h0.ne' h4.ne', log_mul h1.ne' h3.ne']
    ring
  rw [hchi, sub_eq_iff_eq_add, ← log_exp c, ← log_mul (exp_pos c).ne' (by positivity),
    log_exp]
  exact ⟨fun h => log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) h, fun h => by rw [h]⟩

/-- A law on the open simplex is determined by its visible point and its joint mass. -/
private theorem eq_of_visible {p : Fin 5 → ℝ} (hp : p ∈ openSimplex) :
    p = ![1 - (visible p).1 - (visible p).2.1 - (visible p).2.2 + p 4,
      (visible p).1 - p 4, (visible p).2.2, (visible p).2.1 - p 4, p 4] := by
  obtain ⟨_, hsum⟩ := hp
  rw [Fin.sum_univ_five] at hsum
  funext s
  fin_cases s <;> simp [visible]; linarith

/-- Mixed coordinates of the five-mode simplex: the visible occupancies land in the open
pyramid; over every interior visible point each value of the hidden log cross-ratio is
attained by exactly one positive law; along every direction the derivative of the hidden
coordinate is the Fisher pairing with the base loop, which is tangent and invisible. -/
theorem mixed_coordinates_global_chart :
    (∀ p ∈ openSimplex, visible p ∈ openPyramid) ∧
      (∀ v ∈ openPyramid, ∀ c : ℝ,
        ∃! p : Fin 5 → ℝ, p ∈ openSimplex ∧ visible p = v ∧ hiddenChi p = c) ∧
      (∀ p : Fin 5 → ℝ, (∀ s, 0 < p s) → ∀ u : Fin 5 → ℝ,
        HasDerivAt (fun t : ℝ => hiddenChi (p + t • u)) (fisher p hiddenDirection u) 0) ∧
      ∑ s, hiddenDirection s = 0 ∧ visible hiddenDirection = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨hp, hsum⟩
    rw [Fin.sum_univ_five] at hsum
    have := hp 0; have := hp 1; have := hp 2; have := hp 3; have := hp 4
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [visible] <;> linarith
  · rintro ⟨x, y, z⟩ ⟨hx, hy, hz, hxz, hyz⟩ c
    set r : ℝ := 1 - x - y - z with hr
    set a : ℝ := exp c with ha
    have hapos : 0 < a := exp_pos c
    let h : ℝ → ℝ := fun k => (r + k) * k - a * ((x - k) * (y - k))
    -- Existence by the intermediate value theorem on the open fiber.
    set lo : ℝ := max 0 (-r) with hlo
    set hi : ℝ := min x y with hhi
    have hlo0 : 0 ≤ lo := le_max_left _ _
    have hlor : -r ≤ lo := le_max_right _ _
    have hhix : hi ≤ x := min_le_left _ _
    have hhiy : hi ≤ y := min_le_right _ _
    have hhipos : 0 < hi := lt_min hx hy
    have hrhi : 0 < r + hi := by
      rcases min_choice x y with hm | hm <;> rw [hhi, hm] <;> linarith
    have hlohi : lo < hi := by
      rcases max_choice 0 (-r) with hm | hm <;> rw [hlo, hm] <;> linarith
    have hhlo : h lo < 0 := by
      rcases max_choice 0 (-r) with hm | hm
      · have hl : lo = 0 := by rw [hlo, hm]
        simp only [h, hl, add_zero, mul_zero, sub_zero, zero_sub, neg_lt_zero]
        positivity
      · have hl : lo = -r := by rw [hlo, hm]
        have h1 : 0 < x + r := by rw [hr]; linarith
        have h2 : 0 < y + r := by rw [hr]; linarith
        simp only [h, hl, add_neg_cancel, zero_mul, zero_sub, sub_neg_eq_add, neg_lt_zero]
        positivity
    have hhhi : 0 < h hi := by
      have hzero : (x - hi) * (y - hi) = 0 := by
        rcases min_choice x y with hm | hm
        · rw [hhi, hm, sub_self, zero_mul]
        · rw [hhi, hm, sub_self, mul_zero]
      simp only [h, hzero, mul_zero, sub_zero]
      positivity
    have hcont : ContinuousOn h (Set.Icc lo hi) := by
      apply Continuous.continuousOn
      simp only [h]
      fun_prop
    obtain ⟨k, ⟨hk1, hk2⟩, hk⟩ :=
      intermediate_value_Ioo hlohi.le hcont (show (0 : ℝ) ∈ Set.Ioo (h lo) (h hi) from
        ⟨hhlo, hhhi⟩)
    have hk0 : 0 < k := lt_of_le_of_lt hlo0 hk1
    have hrk : 0 < r + k := by linarith
    have hxk : 0 < x - k := by linarith
    have hyk : 0 < y - k := by linarith
    have hpos : ∀ q : Fin 5 → ℝ, q ∈ openSimplex → visible q = (x, y, z) →
        hiddenChi q = c →
          h (q 4) = 0 ∧ 0 < q 4 ∧ 0 < r + q 4 ∧ 0 < x - q 4 ∧ 0 < y - q 4 := by
      intro q hq hvis hchi
      have hqpos := hq.1
      have hsum := hq.2
      rw [Fin.sum_univ_five] at hsum
      simp only [visible, Prod.mk.injEq] at hvis
      obtain ⟨hv1, hv2, hv3⟩ := hvis
      have e0 : q 0 = r + q 4 := by rw [hr]; linarith
      have e1 : q 1 = x - q 4 := by linarith
      have e3 : q 3 = y - q 4 := by linarith
      have hprod := (hiddenChi_eq_iff hqpos c).mp hchi
      refine ⟨?_, hqpos 4, e0 ▸ hqpos 0, e1 ▸ hqpos 1, e3 ▸ hqpos 3⟩
      simp only [h]
      rw [← e0, ← e1, ← e3, hprod, ← ha]
      ring
    refine ⟨![r + k, x - k, z, y - k, k], ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro s
      fin_cases s <;> simp <;> linarith
    · rw [Fin.sum_univ_five]; simp; rw [hr]; ring
    · simp [visible]
    · rw [hiddenChi_eq_iff (fun s => by fin_cases s <;> simp <;> linarith)]
      change (r + k) * k = exp c * ((x - k) * (y - k))
      have hk' : (r + k) * k - a * ((x - k) * (y - k)) = 0 := hk
      rw [← ha]
      linarith
    · rintro q ⟨hq, hvis, hchi⟩
      obtain ⟨hq4, hq0, hqr, hqx, hqy⟩ := hpos q hq hvis hchi
      have hk' : h k = 0 := hk
      -- Uniqueness: `h` is strictly increasing on the open fiber.
      have hdiff : h (q 4) - h k =
          (q 4 - k) * ((r + q 4) + k + a * ((x - q 4) + (y - k))) := by
        simp only [h]; ring
      have hM : 0 < (r + q 4) + k + a * ((x - q 4) + (y - k)) := by positivity
      have hq4k : q 4 = k := by
        rw [hq4, hk', sub_zero] at hdiff
        have := mul_eq_zero.mp hdiff.symm
        rcases this with h1 | h1
        · linarith
        · linarith
      rw [eq_of_visible hq, hvis, hq4k]
  · intro p hp u
    have hfun : (fun t : ℝ => hiddenChi (p + t • u)) = fun t =>
        log (p 0 + t * u 0) + log (p 4 + t * u 4) - log (p 1 + t * u 1) -
          log (p 3 + t * u 3) := by
      funext t
      simp [hiddenChi]
    have hlin : ∀ s : Fin 5, HasDerivAt (fun t : ℝ => log (p s + t * u s))
        (u s / p s) 0 := by
      intro s
      have hin : HasDerivAt (fun t : ℝ => p s + t * u s) (u s) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (u s)).const_add (p s)
      simpa using hin.log (by simpa using (hp s).ne')
    have hval : fisher p hiddenDirection u = u 0 / p 0 + u 4 / p 4 - u 1 / p 1 - u 3 / p 3 := by
      have d0 : hiddenDirection 0 = 1 := rfl
      have d1 : hiddenDirection 1 = -1 := rfl
      have d2 : hiddenDirection 2 = 0 := rfl
      have d3 : hiddenDirection 3 = -1 := rfl
      have d4 : hiddenDirection 4 = 1 := rfl
      simp only [fisher, Fin.sum_univ_five, d0, d1, d2, d3, d4]
      ring
    rw [hfun, hval]
    exact (((hlin 0).add (hlin 4)).sub (hlin 1)).sub (hlin 3)
  · simp [hiddenDirection, Fin.sum_univ_five]
  · simp [visible, hiddenDirection]

end

#print axioms mixed_coordinates_global_chart

end D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates

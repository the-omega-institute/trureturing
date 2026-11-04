/- GID: D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.claim; result=D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.result; claim=D5/S3/Quantum/Walks/OpenQuantumWalkGamblerHittingTimeRefutation.claim
   digest: A complex reset pair separates states invisible to the proposed mean hitting time. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy

/-! The stopped-word expectation for the complex reset counterexample to Remark 5.3. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation

open scoped BigOperators ComplexOrder Matrix ENNReal

/-- Time-ordered branch operator; `true` is a right step and the last step is leftmost. -/
def wordOperator (l r : Matrix (Fin 2) (Fin 2) ℂ) (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (w.map (fun b => if b then r else l)).reverse.prod

/-- Position after the first `t` letters, using integer positions to retain left steps. -/
def position (k : ℕ) (w : List Bool) (t : ℕ) : ℤ :=
  (k : ℤ) + ((w.take t).map (fun b => if b then (1 : ℤ) else -1)).sum

/-- The path is interior before its final step and reaches a boundary on that step. -/
def firstAbsorbs (m k : ℕ) (w : List Bool) : Prop :=
  (∀ t, t < w.length → 0 < position k w t ∧ position k w t < (m : ℤ)) ∧
    (position k w w.length = 0 ∨ position k w w.length = (m : ℤ))

/-- Sum of unnormalized branch probabilities over all words first absorbed at time `n`. -/
def absorbedMass (l r : Matrix (Fin 2) (Fin 2) ℂ) (m k : ℕ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) : ℝ := by
  classical
  exact (((List.replicate n [false, true]).sections).map (fun w =>
    if firstAbsorbs m k w then
      (Matrix.trace (wordOperator l r w * ρ * (wordOperator l r w)ᴴ)).re else 0)).sum

/-- Extended nonnegative expectation of the first absorption time. -/
def meanHittingTime (l r : Matrix (Fin 2) (Fin 2) ℂ) (m k : ℕ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ≥0∞ :=
  ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (absorbedMass l r m k ρ n)

/-- The Jacq–Lardizabal mean-hitting-time conjecture for complex two-dimensional OQWs. -/
def claim : Prop :=
  ∀ l r : Matrix (Fin 2) (Fin 2) ℂ, lᴴ * l + rᴴ * r = 1 →
    ∀ m : ℕ, 3 ≤ m → ∃ h j : ℕ → ℕ → ℝ,
      (∀ k, 1 ≤ k → k ≤ m - 1 → j m k = -j m (m - k)) ∧
      ∀ k, 1 ≤ k → k ≤ m - 1 → ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
        D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity ρ →
        meanHittingTime l r m k ρ ≠ ⊤ ∧
        (meanHittingTime l r m k ρ).toReal =
          1 + h m (m - k) * (ρ 0 0).re + h m k * (ρ 1 1).re + j m k * (ρ 0 1).re

private lemma word_operator_append (l r : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : List Bool) :
    wordOperator l r (a ++ b) = wordOperator l r b * wordOperator l r a := by
  change ((a ++ b).map (fun b => if b then r else l)).reverse.prod = _
  simp only [List.map_append, List.reverse_append, List.prod_append]
  rfl

private lemma stopped_word_zero (l r : Matrix (Fin 2) (Fin 2) ℂ)
    (hz : l * r = 0) (w : List Bool) (hn : 3 ≤ w.length)
    (hw : firstAbsorbs 3 1 w) : wordOperator l r w = 0 := by
  cases w with
  | nil => simp at hn
  | cons a w =>
    cases w with
    | nil => simp at hn
    | cons b w =>
      have hlen : 2 < (a :: b :: w).length := by
        simp only [List.length_cons] at hn ⊢
        omega
      have ha := (hw.1 1 (by omega)).1
      have hb := (hw.1 2 hlen).2
      cases a <;> cases b
      · change (0 : ℤ) < 0 at ha
        omega
      · change (0 : ℤ) < 0 at ha
        omega
      · have he : wordOperator l r ([true, false] ++ w) =
            wordOperator l r w * wordOperator l r [true, false] :=
          word_operator_append l r [true, false] w
        change wordOperator l r ([true, false] ++ w) = 0
        rw [he]
        have hp : wordOperator l r [true, false] = l * r := by
          change l * (r * 1) = l * r
          rw [mul_one]
        rw [hp, hz, mul_zero]
      · change (3 : ℤ) < 3 at hb
        omega

private lemma absorbed_mass_tail (l r ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hz : l * r = 0) (n : ℕ) (hn : 3 ≤ n) : absorbedMass l r 3 1 ρ n = 0 := by
  classical
  change (List.map _ (List.sections (List.replicate n [false, true]))).sum = 0
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  split_ifs with hs
  · have hlen : w.length = n := by
      simpa only [List.length_replicate] using List.mem_sections_length hw
    rw [stopped_word_zero l r hz w (by omega) hs]
    simp
  · rfl

private lemma absorbed_mass_one (l r ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    absorbedMass l r 3 1 ρ 1 = (Matrix.trace (l * ρ * lᴴ)).re := by
  classical
  have hl : firstAbsorbs 3 1 [false] := by
    constructor
    · intro t ht
      have ht0 : t = 0 := by change t < 1 at ht; omega
      subst t
      change (0 : ℤ) < 1 ∧ 1 < 3
      omega
    · exact Or.inl rfl
  have hr : ¬ firstAbsorbs 3 1 [true] := by
    intro h
    have he := h.2
    change (2 : ℤ) = 0 ∨ 2 = 3 at he
    omega
  change (if firstAbsorbs 3 1 [false] then _ else 0) +
    ((if firstAbsorbs 3 1 [true] then _ else 0) + 0) = _
  rw [ite_eq_left hl, ite_eq_right hr]
  have hop : wordOperator l r [false] = l := by
    change l * 1 = l
    exact mul_one l
  rw [hop]
  simp

private lemma absorbed_mass_two (l r ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    absorbedMass l r 3 1 ρ 2 = (Matrix.trace ((r * r) * ρ * (r * r)ᴴ)).re := by
  classical
  have hbad (b : Bool) : ¬ firstAbsorbs 3 1 [false, b] := by
    intro h
    have he := (h.1 1 (by change 1 < 2; omega)).1
    change (0 : ℤ) < 0 at he
    omega
  have hrl : ¬ firstAbsorbs 3 1 [true, false] := by
    intro h
    have he := h.2
    change (1 : ℤ) = 0 ∨ 1 = 3 at he
    omega
  have hrr : firstAbsorbs 3 1 [true, true] := by
    constructor
    · intro t ht
      change t < 2 at ht
      interval_cases t
      · change (0 : ℤ) < 1 ∧ 1 < 3
        omega
      · change (0 : ℤ) < 2 ∧ 2 < 3
        omega
    · exact Or.inr rfl
  change (if firstAbsorbs 3 1 [false, false] then _ else 0) +
    ((if firstAbsorbs 3 1 [true, false] then _ else 0) +
    ((if firstAbsorbs 3 1 [false, true] then _ else 0) +
    ((if firstAbsorbs 3 1 [true, true] then _ else 0) + 0))) = _
  rw [ite_eq_right (hbad false), ite_eq_right hrl, ite_eq_right (hbad true), ite_eq_left hrr]
  have hop : wordOperator l r [true, true] = r * r := by
    change r * (r * 1) = r * r
    rw [mul_one]
  rw [hop]
  simp

private lemma mean_two_step (l r ρ : Matrix (Fin 2) (Fin 2) ℂ) (hz : l * r = 0) :
    meanHittingTime l r 3 1 ρ = ENNReal.ofReal (Matrix.trace (l * ρ * lᴴ)).re +
      2 * ENNReal.ofReal (Matrix.trace ((r * r) * ρ * (r * r)ᴴ)).re := by
  change (∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (absorbedMass l r 3 1 ρ n)) = _
  rw [tsum_eq_sum (s := Finset.range 3)]
  · simp [Finset.sum_range_succ, absorbed_mass_one, absorbed_mass_two]
  · intro n hn
    have hge : 3 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    rw [absorbed_mass_tail l r ρ hz n hge]
    simp

/-- The complex reset pair refutes the conjectured dependence on three real matrix entries. -/
theorem result : ¬ claim := by
  classical
  let u : Fin 2 → ℂ := ![1, Complex.I]
  let v : Fin 2 → ℂ := ![1, -Complex.I]
  let l : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • Matrix.vecMulVec v (star u)
  let r : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • Matrix.vecMulVec v (star v)
  let ρ : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • Matrix.vecMulVec u (star u)
  let σ : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • Matrix.vecMulVec v (star v)
  have hnorm : lᴴ * l + rᴴ * r = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [l, r, u, v, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec,
        Matrix.conjTranspose_apply, Complex.ext_iff]
  have hzero : l * r = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [l, r, u, v, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec,
        Complex.ext_iff]
  have hρ : D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity ρ := by
    constructor
    · exact (Matrix.posSemidef_vecMulVec_self_star u).smul
        (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1 / 2)
    · norm_num [ρ, u, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.vecMulVec]
  have hσ : D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity σ := by
    constructor
    · exact (Matrix.posSemidef_vecMulVec_self_star v).smul
        (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1 / 2)
    · norm_num [σ, v, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.vecMulVec]
  have hentries : (ρ 0 0).re = (σ 0 0).re ∧ (ρ 1 1).re = (σ 1 1).re ∧
      (ρ 0 1).re = (σ 0 1).re := by
    norm_num [ρ, σ, u, v, Matrix.vecMulVec]
  have htimes : meanHittingTime l r 3 1 ρ = 1 ∧ meanHittingTime l r 3 1 σ = 2 := by
    rw [mean_two_step l r ρ hzero, mean_two_step l r σ hzero]
    norm_num [l, r, ρ, σ, u, v, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.vecMulVec, Matrix.conjTranspose_apply, Complex.ext_iff]
  intro hc
  obtain ⟨h, j, _, he⟩ := hc l r hnorm 3 (by omega)
  have hp := (he 1 (by omega) (by omega) ρ hρ).2
  have hm := (he 1 (by omega) (by omega) σ hσ).2
  rw [htimes.1] at hp
  rw [htimes.2] at hm
  rw [hentries.1, hentries.2.1, hentries.2.2] at hp
  norm_num at hp hm
  linarith

end D5.S3.Quantum.Walks.OpenQuantumWalkGamblerHittingTimeRefutation

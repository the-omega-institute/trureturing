/- GID: D5/S1/Words/Patterns/Separable/EndpointJointLaw
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/EndpointJointLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual alternating endpoint cycles have a coupled removal-count and terminal-type law. -/

import D5.S1.Words.Patterns.Separable.ActualCycleLaw

/-! The actual alternating-cycle law observed through low removals and terminal type. -/

namespace D5.S1.Words.Patterns.Separable.EndpointJointLaw

open D5.S1.Words.Patterns.Separable.ActualCycles
open D5.S1.Words.Patterns.Separable.ActualCycleLaw
open D5.S1.Words.Patterns.Separable.OccupiedComparison
open scoped BigOperators ENNReal

/-- Count the low-value right suffixes actually removed along the alternating cycle.
As in `EndpointHistory.word`, precisely a true (skew) discard advances the low-value
boundary; the false (direct) terminal emits finite endpoint values. -/
def lowRemovalCount : {sign : Bool} → UnboundedCycle sign → ℕ
  | _, .terminal _ _ => 0
  | sign, .discard _ _ tail => (if sign then 1 else 0) + lowRemovalCount tail

/-- A direct terminal cut emits finite values in the endpoint limit. -/
def finiteTerminal : {sign : Bool} → UnboundedCycle sign → Bool
  | sign, .terminal _ _ => !sign
  | _, .discard _ _ tail => finiteTerminal tail

/-- The joint observation retains both the count and the terminal type. -/
def observation (c : MarkedCycle) : ℕ × Bool :=
  (lowRemovalCount c.2, finiteTerminal c.2)

/-- Push forward the actual marked-cycle law, without an independence assumption. -/
noncomputable def endpointPMF : PMF (ℕ × Bool) := cyclePMF.map observation

private def fixedObservation : Bool → ℕ → ℕ × Bool
  | sign, 0 => (0, !sign)
  | sign, k + 1 =>
      ((if sign then 1 else 0) + (fixedObservation (!sign) k).1,
        (fixedObservation (!sign) k).2)

private theorem fixedObservation_even (r : ℕ) :
    fixedObservation false (2*r) = (r, true) ∧
    fixedObservation true (2*r) = (r, false) := by
  induction r with
  | zero => simp [fixedObservation]
  | succ r ih =>
      have h : 2 * (r + 1) = (2*r + 1) + 1 := by omega
      constructor <;> rw [h] <;>
        simp [fixedObservation, ih.1, ih.2, Nat.add_comm]

private theorem fixedObservation_odd (r : ℕ) :
    fixedObservation false (2*r+1) = (r, false) ∧
    fixedObservation true (2*r+1) = (r+1, true) := by
  constructor <;>
    simp [fixedObservation, (fixedObservation_even r).1,
      (fixedObservation_even r).2, Nat.add_comm]

private theorem fixedObservation_zero_true (sign : Bool) (k : ℕ) :
    fixedObservation sign k = (0, true) ↔ sign = false ∧ k = 0 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = 2*n ∨ k = 2*n+1 := ⟨k/2, by omega⟩
  rcases hn with hn | hn
  · subst k
    cases sign <;>
      simp [(fixedObservation_even n).1, (fixedObservation_even n).2] <;> omega
  · subst k
    cases sign <;>
      simp [(fixedObservation_odd n).1, (fixedObservation_odd n).2] <;> omega

private theorem fixedObservation_succ_true (sign : Bool) (k r : ℕ) :
    fixedObservation sign k = (r+1, true) ↔
      (sign = true ∧ k = 2*r+1) ∨
      (sign = false ∧ k = 2*r+2) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = 2*n ∨ k = 2*n+1 := ⟨k/2, by omega⟩
  rcases hn with hn | hn
  · subst k
    cases sign <;>
      simp [(fixedObservation_even n).1, (fixedObservation_even n).2] <;> omega
  · subst k
    cases sign <;>
      simp [(fixedObservation_odd n).1, (fixedObservation_odd n).2] <;> omega

private theorem fixedObservation_false (sign : Bool) (k r : ℕ) :
    fixedObservation sign k = (r, false) ↔
      (sign = true ∧ k = 2*r) ∨
      (sign = false ∧ k = 2*r+1) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = 2*n ∨ k = 2*n+1 := ⟨k/2, by omega⟩
  rcases hn with hn | hn
  · subst k
    cases sign <;>
      simp [(fixedObservation_even n).1, (fixedObservation_even n).2] <;> omega
  · subst k
    cases sign <;>
      simp [(fixedObservation_odd n).1, (fixedObservation_odd n).2] <;> omega

private theorem observation_decode {sign k} (c : Fixed sign k) :
    observation ⟨sign, c.decode⟩ = fixedObservation sign k := by
  induction k generalizing sign with
  | zero => rfl
  | succ k ih =>
    rcases c with ⟨removal, tail⟩
    have h := ih tail
    exact congrArg (fun x : ℕ × Bool => ((if sign then 1 else 0) + x.1, x.2)) h

private theorem mass_by_steps (v : ℕ × Bool) :
    endpointPMF v = ∑' sign : Bool, ∑' k : ℕ,
      if v = fixedObservation sign k then ENNReal.ofReal (ceiling * b ^ k) else 0 := by
  classical
  rw [endpointPMF, PMF.map_apply, ENNReal.tsum_sigma']
  apply tsum_congr
  intro sign
  rw [← (enumeration sign).symm.tsum_eq]
  simp only [enumeration, Equiv.coe_fn_symm_mk]
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro k
  simp only [observation_decode]
  split_ifs with h
  · change (∑' c : Fixed sign k, ENNReal.ofReal (rho ^ c.decode.size)) = _
    simp only [Fixed.decode_size]
    exact actual_countable_cycle_law.2.2.2.1 sign k
  · simp

private theorem endpoint_zero_true : endpointPMF (0, true) = ENNReal.ofReal ceiling := by
  classical
  rw [mass_by_steps]
  have condition (sign : Bool) (k : ℕ) :
      ((0, true) = fixedObservation sign k) ↔ sign = false ∧ k = 0 :=
    eq_comm.trans (fixedObservation_zero_true sign k)
  simp_rw [condition]
  simp [tsum_fintype, add_comm]

private theorem endpoint_succ_true (r : ℕ) :
    endpointPMF (r+1, true) =
      ENNReal.ofReal (ceiling * b ^ (2*r+2)) +
      ENNReal.ofReal (ceiling * b ^ (2*r+1)) := by
  classical
  rw [mass_by_steps]
  have condition (sign : Bool) (k : ℕ) :
      ((r+1, true) = fixedObservation sign k) ↔
        (sign = true ∧ k = 2*r+1) ∨ (sign = false ∧ k = 2*r+2) :=
    eq_comm.trans (fixedObservation_succ_true sign k r)
  simp_rw [condition]
  simp [tsum_fintype, add_comm]

private theorem endpoint_false (r : ℕ) :
    endpointPMF (r, false) =
      ENNReal.ofReal (ceiling * b ^ (2*r+1)) +
      ENNReal.ofReal (ceiling * b ^ (2*r)) := by
  classical
  rw [mass_by_steps]
  have condition (sign : Bool) (k : ℕ) :
      ((r, false) = fixedObservation sign k) ↔
        (sign = true ∧ k = 2*r) ∨ (sign = false ∧ k = 2*r+1) :=
    eq_comm.trans (fixedObservation_false sign k r)
  simp_rw [condition]
  simp [tsum_fintype, add_comm]

private theorem parameter_values : 0 ≤ b ∧ 0 ≤ ceiling ∧
    ceiling = 1 - 1 / Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hlo : 1 < Real.sqrt (2 : ℝ) := by nlinarith
  have hhi : Real.sqrt (2 : ℝ) < 2 := by nlinarith
  refine ⟨by dsimp [b]; linarith, by dsimp [ceiling, a, b]; linarith, ?_⟩
  dsimp [ceiling, a, b]
  field_simp
  nlinarith

/-- The actual endpoint limit has the complete coupled count/type distribution. -/
theorem whole_endpoint_joint_law (r : ℕ) :
    let t : ℝ := Real.sqrt 2 - 1
    let a : ℝ := 1 - 1 / Real.sqrt 2
    endpointPMF (0, true) = ENNReal.ofReal a ∧
    endpointPMF (0, false) = ENNReal.ofReal (a * (1+t)) ∧
    (1 ≤ r →
      endpointPMF (r, true) = ENNReal.ofReal (a*t*(1+t)*t^(2*r-2)) ∧
      endpointPMF (r, false) = ENNReal.ofReal (t*(a*t*(1+t)*t^(2*r-2)))) := by
  change endpointPMF (0,true) = ENNReal.ofReal (1-1/Real.sqrt 2) ∧ _
  rw [← parameter_values.2.2]
  change endpointPMF (0,true) = ENNReal.ofReal ceiling ∧
    endpointPMF (0,false) = ENNReal.ofReal (ceiling*(1+b)) ∧
    (1 ≤ r → endpointPMF (r,true) = ENNReal.ofReal (ceiling*b*(1+b)*b^(2*r-2)) ∧
      endpointPMF (r,false) = ENNReal.ofReal (b*(ceiling*b*(1+b)*b^(2*r-2))))
  refine ⟨endpoint_zero_true, ?_, ?_⟩
  · rw [endpoint_false]
    rw [← ENNReal.ofReal_add (mul_nonneg parameter_values.2.1
      (pow_nonneg parameter_values.1 _)) (mul_nonneg parameter_values.2.1
      (pow_nonneg parameter_values.1 _))]
    congr 1
    ring
  · intro hr
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    have exp : 2*(s+1)-2 = 2*s := by omega
    rw [exp]
    constructor
    · rw [endpoint_succ_true]
      rw [← ENNReal.ofReal_add (mul_nonneg parameter_values.2.1
        (pow_nonneg parameter_values.1 _)) (mul_nonneg parameter_values.2.1
        (pow_nonneg parameter_values.1 _))]
      congr 1
      simp only [pow_add]
      ring
    · rw [endpoint_false]
      rw [← ENNReal.ofReal_add (mul_nonneg parameter_values.2.1
        (pow_nonneg parameter_values.1 _)) (mul_nonneg parameter_values.2.1
        (pow_nonneg parameter_values.1 _))]
      congr 1
      have e2 : 2*(s+1) = 2*s+2 := by omega
      rw [e2]
      simp only [pow_add]
      ring

end D5.S1.Words.Patterns.Separable.EndpointJointLaw

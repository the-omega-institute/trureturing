/- GID: D5/S1/Words/Mechanical/SilverSlopeAbelianPellArithmetic
   generality: I
   mirror-B: none(waiver:open-problem-stage-a)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Pell errors, approximation gaps, and convergent-period realisations. -/
/-
Judgement form:
  silverPell_error_formula:
    proof_shape: content
    escape_witness: ∀ k, (P (k + 1) : Real)*silverSlope - P k = (-1 : Real)^k *
      silverSlope^(k+1)
    Non-binding step: The arbitrary-index identity is created by recurrence induction. Mathlib’s
      continued-fraction determinant/error theorems require an unproved recurrence/stream
      identification; no normalization-only bypass was found.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d)
  silverPell_determinant:
    proof_shape: content
    escape_witness: ∀ k, (P (k + 2) : Int)*P k - (P (k + 1) : Int)^2 = (-1 :
      Int)^(k+1)
    Non-binding step: The alternating determinant identity is produced by induction, without an
      existing identified continued-fraction representation.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d)
  silver_best_approximation:
    proof_shape: content
    escape_witness: unimodular_opposite_error_bound: for all q,p,s,r,m,z : Int and alpha,d,e :
      Real, q>0 ∧ s>0 ∧ 0<m ∧ m<q ∧ q*r-p*s=1 ∧ d>0 ∧ e>0 ∧ q*alpha-p=d ∧ s*alpha-r=-e implies e
      ≤ |m*alpha-z|
    Non-binding step: That same-delivery integer-coordinate exclusion is a live dependency. After
      inlining, it and the Pell identities supply content absent from pinned prerequisites.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d)
  silver_gap_approximation:
    proof_shape: content
    escape_witness: unimodular_gap_error_bound: under 0<s<q, q≤m<2*q+s, m≠q, m≠2*q, m≠q+s,
      determinant 1, d>0, 2*d≤e, and opposite errors d,-e, d+e ≤ |m*alpha-z|
    Non-binding step: The uniform exclusion of the exceptional integer coordinates remains live
      after same-delivery inlining.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d)
  silver_phase_mass:
    proof_shape: content
    escape_witness: ∀ k, ((P (k + 2) : Real)+silverSlope*P (k + 1))*silverSlope^(k+1)=1
    Non-binding step: The all-index invariant is established by recurrence induction; it is not
      just one finite algebraic check.
    Direct frozen dependencies: D5/S1/Recurrence/PellCompanionGcd
      (sha256:d586071be3d8ab650d0c5cfee5c27ece8fc00cb40f5971172495b2950e89d33d)
admission_basis: escape-witness
Escape-audit registration is paused under CLAUDE.md §3.9.
-/
import D5.S1.Words.Mechanical.SilverSlopeAbelianPeriodDefs
import D5.S1.Words.Mechanical.UnimodularApproximationBound
namespace D5.S1.Words.Mechanical
open D5.S1.Recurrence.PellCompanionGcd
open D5.S1.Words.Complexity
theorem silverPell_error_formula (k : Nat) :
    (P (k + 1) : Real) * silverSlope - P k =
      (-1 : Real) ^ k * silverSlope ^ (k + 1) := by
  have silverSlope_quadratic : silverSlope ^ 2 + 2 * silverSlope = 1 := by
    dsimp [silverSlope]
    have h : (Real.sqrt (2 : Real)) ^ 2 = 2 := by norm_num
    nlinarith
  have silverSlope_cubic : silverSlope ^ 3 = 5 * silverSlope - 2 := by
    have hsq : silverSlope ^ 2 = 1 - 2 * silverSlope := by
      nlinarith [silverSlope_quadratic]
    calc
      silverSlope ^ 3 = silverSlope * silverSlope ^ 2 := by ring
      _ = silverSlope * (1 - 2 * silverSlope) := by rw [hsq]
      _ = 5 * silverSlope - 2 := by ring_nf; rw [hsq]; ring
  have silverPell_error_recurrence (k : Nat) :
      (P (k + 3) : Real) * silverSlope - P (k + 2) =
        silverSlope ^ 2 * ((P (k + 1) : Real) * silverSlope - P k) := by
    have hq : (P (k + 2) : Real) =
        2 * (P (k + 1) : Real) + P k := by
      exact_mod_cast (show P (k + 2) = 2 * P (k + 1) + P k from rfl)
    rw [show P (k + 3) = 2 * P (k + 2) + P (k + 1) by rfl]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [hq]
    ring_nf
    have hsq : silverSlope ^ 2 = 1 - 2 * silverSlope := by
      nlinarith [silverSlope_quadratic]
    rw [silverSlope_cubic, hsq]
    ring
  induction k using Nat.strong_induction_on with
  | h k ih =>
      cases k with
      | zero => norm_num [P, Nat.add_assoc]
      | succ k =>
          cases k with
          | zero =>
              norm_num [P, Nat.add_assoc]
              nlinarith [silverSlope_quadratic]
          | succ k =>
              have hik := ih k (by omega)
              have hrec :
                  (P (k + 1 + 1 + 1) : Real) * silverSlope - P (k + 1 + 1) =
                    silverSlope ^ 2 * ((P (k + 1) : Real) * silverSlope - P k) := by
                simpa [Nat.add_assoc] using silverPell_error_recurrence k
              calc
                (P (k + 1 + 1 + 1) : Real) * silverSlope - P (k + 1 + 1) =
                    silverSlope ^ 2 * ((P (k + 1) : Real) * silverSlope - P k) := hrec
                _ = silverSlope ^ 2 * ((-1 : Real) ^ k * silverSlope ^ (k + 1)) := by rw [hik]
                _ = (-1 : Real) ^ (k + 1 + 1) * silverSlope ^ (k + 1 + 1 + 1) := by
                  rw [show k + 1 + 1 + 1 = (k + 1) + 2 by omega, pow_add, pow_add]
                  norm_num
                  ring
#print axioms silverPell_error_formula
theorem silverPell_determinant (k : Nat) :
    (P (k + 2) : Int) * P k - (P (k + 1) : Int) ^ 2 =
      (-1 : Int) ^ (k + 1) := by
  induction k with
  | zero => norm_num [P, Nat.add_assoc]
  | succ k ih =>
      have hr : (P (k + 2) : Int) =
          2 * (P (k + 1) : Int) + P k := by
        exact_mod_cast (show P (k + 2) = 2 * P (k + 1) + P k from rfl)
      have hn : (P (k + 3) : Int) =
          2 * (P (k + 2) : Int) + P (k + 1) := by
        exact_mod_cast (show P (k + 3) =
          2 * P (k + 2) + P (k + 1) from rfl)
      change (P (k + 3) : Int) * P (k + 1) -
        (P (k + 2) : Int) ^ 2 = (-1 : Int) ^ (k + 2)
      calc
        (P (k + 3) : Int) * P (k + 1) - (P (k + 2) : Int) ^ 2 =
            -((P (k + 2) : Int) * P k - (P (k + 1) : Int) ^ 2) := by
          rw [hn, hr]
          ring
        _ = -((-1 : Int) ^ (k + 1)) := by rw [ih]
        _ = (-1 : Int) ^ (k + 2) := by rw [pow_succ]; ring
#print axioms silverPell_determinant
theorem silver_best_approximation (k m : Nat) (hm : 0 < m)
    (hmq : m < P (k + 2)) (z : Int) :
    silverSlope ^ (k + 1) ≤ |(m : Real) * silverSlope - z| := by
  have silverSlope_pos : 0 < silverSlope := by
    dsimp [silverSlope]
    have hs : (Real.sqrt (2 : Real)) ^ 2 = 2 := by norm_num
    have hp : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  have silver_power_pos (k : Nat) : 0 < silverSlope ^ (k + 1) := by
    exact pow_pos silverSlope_pos (k + 1)
  have hq : (0 : Int) < P (k + 2) := by exact_mod_cast (by have hs := (pell_companion_step (k + 1)).1; obtain ⟨j, hj⟩ := companion_odd (k + 1); omega : 0 < P (k + 1 + 1))
  have hs : (0 : Int) < P (k + 1) := by exact_mod_cast (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : 0 < P (k + 1))
  have hmI : (0 : Int) < m := by exact_mod_cast hm
  have hmqI : (m : Int) < P (k + 2) := by exact_mod_cast hmq
  have hdet := silverPell_determinant k
  have herrorq := silverPell_error_formula (k + 1)
  have herrors := silverPell_error_formula k
  by_cases hk : Odd k
  · have hk1 : Even (k + 1) := hk.add_odd odd_one
    rw [hk1.neg_one_pow] at hdet herrorq
    rw [hk.neg_one_pow] at herrors
    simpa [Nat.add_assoc, mul_one, one_mul] using
      unimodular_opposite_error_bound (P (k + 2)) (P (k + 1))
        (P (k + 1)) (P k) m z silverSlope
        (silverSlope ^ (k + 2)) (silverSlope ^ (k + 1))
        hq hs hmI hmqI (by simpa [pow_two] using hdet)
        (silver_power_pos (k + 1)) (silver_power_pos k)
        (by simpa [Nat.add_assoc] using herrorq)
        (by simpa using herrors)
  · have hkeven : Even k := Nat.not_odd_iff_even.mp hk
    have hk1 : Odd (k + 1) := hkeven.add_odd odd_one
    rw [hk1.neg_one_pow] at hdet herrorq
    rw [hkeven.neg_one_pow] at herrors
    have hdet' : (P (k + 2) : Int) * (-(P k : Int)) -
        (-(P (k + 1) : Int)) * (P (k + 1) : Int) = 1 := by
      nlinarith [hdet]
    have heq : (P (k + 2) : Real) * (-silverSlope) - (-(P (k + 1) : Int) : Real) =
        silverSlope ^ (k + 2) := by
      simp only [Int.cast_neg, Int.cast_natCast]
      simp only [Nat.add_assoc, show k + 1 + 1 = k + 2 by omega] at herrorq
      nlinarith [herrorq]
    have hes : (P (k + 1) : Real) * (-silverSlope) - (-(P k : Int) : Real) =
        -silverSlope ^ (k + 1) := by
      simp only [Int.cast_neg, Int.cast_natCast]
      nlinarith [herrors]
    have hbound := unimodular_opposite_error_bound (P (k + 2)) (-(P (k + 1) : Int))
      (P (k + 1)) (-(P k : Int)) m (-z) (-silverSlope)
      (silverSlope ^ (k + 2)) (silverSlope ^ (k + 1))
      hq hs hmI hmqI hdet' (silver_power_pos (k + 1)) (silver_power_pos k)
      (by simpa only [Int.cast_neg, Int.cast_natCast] using heq)
      (by simpa only [Int.cast_neg, Int.cast_natCast] using hes)
    have he : (m : Real) * (-silverSlope) - ((-z : Int) : Real) =
        -((m : Real) * silverSlope - z) := by push_cast; ring
    simpa only [Int.cast_natCast, he, abs_neg] using hbound
#print axioms silver_best_approximation
theorem silver_gap_approximation (k m : Nat)
    (hm : P (k + 2) ≤ m) (hmq : m < P (k + 3))
    (hne1 : m ≠ P (k + 2)) (hne2 : m ≠ 2 * P (k + 2))
    (hnes : m ≠ P (k + 2) + P (k + 1)) (z : Int) :
    silverSlope ^ (k + 2) + silverSlope ^ (k + 1) ≤
      |(m : Real) * silverSlope - z| := by
  have silverSlope_lt_half : silverSlope < (1 / 2 : Real) := by
    dsimp [silverSlope]
    have hp : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
    have hs : (Real.sqrt (2 : Real)) ^ 2 = 2 := by norm_num
    have hp : 0 ≤ Real.sqrt (2 : Real) := Real.sqrt_nonneg _
    nlinarith
  have silverSlope_pos : 0 < silverSlope := by
    dsimp [silverSlope]
    have hs : (Real.sqrt (2 : Real)) ^ 2 = 2 := by norm_num
    have hp : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  have silver_power_pos (k : Nat) : 0 < silverSlope ^ (k + 1) := by
    exact pow_pos silverSlope_pos (k + 1)
  have hq : (0 : Int) < P (k + 2) := by exact_mod_cast (by have hs := (pell_companion_step (k + 1)).1; obtain ⟨j, hj⟩ := companion_odd (k + 1); omega : 0 < P (k + 1 + 1))
  have hs : (0 : Int) < P (k + 1) := by exact_mod_cast (by have hs := (pell_companion_step k).1; obtain ⟨j, hj⟩ := companion_odd k; omega : 0 < P (k + 1))
  have hsq : (P (k + 1) : Int) < P (k + 2) := by
    exact_mod_cast (show P (k + 1) < P (k + 2) by
      simpa [Nat.add_assoc] using (by have hs := (pell_companion_step (k + 1)).1; obtain ⟨j, hj⟩ := companion_odd (k + 1); omega : P (k + 1) < P (k + 1 + 1)))
  have hmI : (P (k + 2) : Int) ≤ m := by exact_mod_cast hm
  have hmqI : (m : Int) < 2 * P (k + 2) + P (k + 1) := by
    have hr : P (k + 3) = 2 * P (k + 2) + P (k + 1) := rfl
    rw [hr] at hmq
    exact_mod_cast hmq
  have hne1I : (m : Int) ≠ P (k + 2) := by exact_mod_cast hne1
  have hne2I : (m : Int) ≠ 2 * P (k + 2) := by exact_mod_cast hne2
  have hnesI : (m : Int) ≠ P (k + 2) + P (k + 1) := by exact_mod_cast hnes
  have hed : 2 * silverSlope ^ (k + 2) ≤ silverSlope ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    nlinarith [silverSlope_lt_half, silver_power_pos k]
  have hdet := silverPell_determinant k
  have herrorq := silverPell_error_formula (k + 1)
  have herrors := silverPell_error_formula k
  by_cases hk : Odd k
  · have hk1 : Even (k + 1) := hk.add_odd odd_one
    rw [hk1.neg_one_pow] at hdet herrorq
    rw [hk.neg_one_pow] at herrors
    simpa [Nat.add_assoc, mul_one, one_mul] using
      unimodular_gap_error_bound (P (k + 2)) (P (k + 1))
        (P (k + 1)) (P k) m z silverSlope
        (silverSlope ^ (k + 2)) (silverSlope ^ (k + 1))
        hq hs hsq hmI hmqI hne1I hne2I hnesI (by simpa [pow_two] using hdet)
        (silver_power_pos (k + 1)) hed
        (by simpa [Nat.add_assoc] using herrorq) (by simpa using herrors)
  · have hkeven : Even k := Nat.not_odd_iff_even.mp hk
    have hk1 : Odd (k + 1) := hkeven.add_odd odd_one
    rw [hk1.neg_one_pow] at hdet herrorq
    rw [hkeven.neg_one_pow] at herrors
    have hdet' : (P (k + 2) : Int) * (-(P k : Int)) -
        (-(P (k + 1) : Int)) * (P (k + 1) : Int) = 1 := by nlinarith [hdet]
    have heq : (P (k + 2) : Real) * (-silverSlope) - (-(P (k + 1) : Int) : Real) =
        silverSlope ^ (k + 2) := by
      simp only [Int.cast_neg, Int.cast_natCast]
      simp only [Nat.add_assoc, show k + 1 + 1 = k + 2 by omega] at herrorq
      nlinarith [herrorq]
    have hes : (P (k + 1) : Real) * (-silverSlope) - (-(P k : Int) : Real) =
        -silverSlope ^ (k + 1) := by
      simp only [Int.cast_neg, Int.cast_natCast]
      nlinarith [herrors]
    have hbound := unimodular_gap_error_bound (P (k + 2)) (-(P (k + 1) : Int))
      (P (k + 1)) (-(P k : Int)) m (-z) (-silverSlope)
      (silverSlope ^ (k + 2)) (silverSlope ^ (k + 1))
      hq hs hsq hmI hmqI hne1I hne2I hnesI hdet' (silver_power_pos (k + 1)) hed
      (by simpa only [Int.cast_neg, Int.cast_natCast] using heq)
      (by simpa only [Int.cast_neg, Int.cast_natCast] using hes)
    have he : (m : Real) * (-silverSlope) - ((-z : Int) : Real) =
        -((m : Real) * silverSlope - z) := by push_cast; ring
    simpa only [Int.cast_natCast, he, abs_neg] using hbound
#print axioms silver_gap_approximation
theorem silver_phase_mass (k : Nat) :
    ((P (k + 2) : Real) + silverSlope * P (k + 1)) *
      silverSlope ^ (k + 1) = 1 := by
  have silverSlope_quadratic : silverSlope ^ 2 + 2 * silverSlope = 1 := by
    dsimp [silverSlope]
    have h : (Real.sqrt (2 : Real)) ^ 2 = 2 := by norm_num
    nlinarith
  induction k with
  | zero =>
      norm_num [P]
      nlinarith [silverSlope_quadratic]
  | succ k ih =>
      have hrec : (P (k + 3) : Real) =
          2 * P (k + 2) + P (k + 1) := by
        exact_mod_cast (show P (k + 3) =
          2 * P (k + 2) + P (k + 1) from rfl)
      rw [show k + 1 + 1 = k + 2 by omega, hrec,
        show k + 2 = (k + 1) + 1 by omega, pow_succ]
      calc
        (2 * (P (k + 2) : Real) + P (k + 1) + silverSlope * P (k + 2)) *
            (silverSlope ^ (k + 1) * silverSlope) =
          ((P (k + 2) : Real) + silverSlope * P (k + 1)) * silverSlope ^ (k + 1) := by
            have h := silverSlope_quadratic
            linear_combination (P (k + 2) : Real) * silverSlope ^ (k + 1) * h
        _ = 1 := ih
#print axioms silver_phase_mass
end D5.S1.Words.Mechanical

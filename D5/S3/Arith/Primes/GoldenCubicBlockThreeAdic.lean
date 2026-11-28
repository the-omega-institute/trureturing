/- GID: D5/S3/Arith/Primes/GoldenCubicBlockThreeAdic
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockThreeAdic
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact three-adic depths and finite transients for the native cubic Lucas block orbit. -/

import D5.S1.Scale.GoldenCubicBlockCongruences

set_option autoImplicit false

/-! An exact transient toward one at every three-adic precision. -/

namespace D5.S3.Arith.Primes.GoldenCubicBlockThreeAdic

open D5.S1.Scale

/-- The native cubic Lucas block, with its level-zero block included. -/
def cubicBlock (i : ℕ) : ℤ := goldenLucas (3^i)^2+3

private theorem lucas_step (i : ℕ) :
    goldenLucas (3^(i+1)) = goldenLucas (3^i)*cubicBlock i := by
  by_cases hi : 1 ≤ i
  · exact (golden_cubic_lucas_block i hi).2.2.2.2.2
  · have he : i = 0 := by omega
    subst i
    open D5.S0.Carrier in norm_num [cubicBlock, goldenLucas, trace, phi, pow_succ]

/-- At three, the relevant fixed residue is one, not three. -/
theorem cubicBlock_three_fixed_point_step (i : ℕ) :
    cubicBlock (i+1)-1 = (cubicBlock i-1)*((cubicBlock i-1)^2-3) := by
  have hr := lucas_step i
  unfold cubicBlock at hr ⊢
  rw [hr]
  ring

private theorem val3_unit_mul_pow (n : ℕ) (u : ℤ) (hu : ¬(3:ℤ) ∣ u) :
    padicValInt 3 ((3:ℤ)^n*u) = n := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hu0 : u ≠ 0 := by intro h; exact hu (h ▸ dvd_zero _)
  rw [padicValInt.mul (by positivity) hu0, padicValInt.eq_zero_of_not_dvd hu, add_zero]
  change padicValInt 3 (↑((3:ℕ)^n) : ℤ) = n
  rw [padicValInt.of_nat, padicValNat.prime_pow]

private theorem cube_block_three_unit (i : ℕ) :
    ∃ u : ℤ, cubicBlock i-1 = (3:ℤ)^(i+1)*u ∧ ¬(3:ℤ) ∣ u := by
  induction i with
  | zero =>
    refine ⟨1, ?_, by decide⟩
    open D5.S0.Carrier in norm_num [cubicBlock, goldenLucas, trace, phi]
  | succ i ih =>
    obtain ⟨u, hu, hu3⟩ := ih
    let v : ℤ := 3*((3:ℤ)^i*u)^2-1
    have hv : ¬(3:ℤ) ∣ v := by
      intro hd
      have hd' := Int.emod_eq_zero_of_dvd hd
      dsimp [v] at hd'
      omega
    refine ⟨u*v, ?_, ?_⟩
    · rw [cubicBlock_three_fixed_point_step, hu]
      simp only [pow_succ]
      dsimp only [v]
      ring
    · have : Prime (3:ℤ) := by norm_num; decide
      exact fun h => (this.dvd_mul.mp h).elim hu3 hv

/-- Each iteration gains exactly one three-adic digit relative to one. -/
theorem cubicBlock_three_depth (i : ℕ) : padicValInt 3 (cubicBlock i-1) = i+1 := by
  obtain ⟨u, hu, hu3⟩ := cube_block_three_unit i
  rw [hu, val3_unit_mul_pow _ _ hu3]

private theorem cube_block_three_lag_unit (n m : ℕ) (hmn : m < n) :
    ∃ u : ℤ, cubicBlock n-cubicBlock m = (3:ℤ)^(m+1)*u ∧ ¬(3:ℤ) ∣ u := by
  obtain ⟨v, hv, _⟩ := cube_block_three_unit n
  obtain ⟨w, hw, hw3⟩ := cube_block_three_unit m
  have hd : n+1 = (m+1)+(n-m) := by omega
  have h3 : (3:ℤ) ∣ (3:ℤ)^(n-m)*v := by
    have hdvd : (3:ℤ) ∣ (3:ℤ)^(n-m) := dvd_pow_self _ (by omega)
    exact dvd_mul_of_dvd_left hdvd _
  refine ⟨(3:ℤ)^(n-m)*v-w, ?_, ?_⟩
  · calc
      cubicBlock n-cubicBlock m = (cubicBlock n-1)-(cubicBlock m-1) := by ring
      _ = _ := by rw [hv, hw, hd, pow_add]; ring
  · intro h
    apply hw3
    have hd' := dvd_sub h3 h
    rwa [sub_sub_cancel] at hd'

/-- Two different levels agree to the depth of the earlier level, but
not one digit further. Unlike the odd-divisor clock, depth depends on
when the earlier observation was made rather than on the lag. -/
theorem cubicBlock_three_lag (n m : ℕ) (hmn : m < n) :
    padicValInt 3 (cubicBlock n-cubicBlock m) = m+1 := by
  obtain ⟨u, hu, hu3⟩ := cube_block_three_lag_unit n m hmn
  rw [hu, val3_unit_mul_pow _ _ hu3]

private theorem unit_pow_dvd_iff (u : ℤ) (hu : ¬(3:ℤ) ∣ u) (a d : ℕ) :
    (3:ℤ)^a ∣ (3:ℤ)^d*u ↔ a ≤ d := by
  have hu0 : u ≠ 0 := by intro h; exact hu (h ▸ dvd_zero _)
  have hn : (3:ℤ)^d*u ≠ 0 := mul_ne_zero (by positivity) hu0
  change (((3:ℕ):ℤ)^a ∣ _) ↔ _
  rw [padicValInt_dvd_iff_of_ne_one (p := 3) (by decide), or_iff_right hn,
    val3_unit_mul_pow _ _ hu]

/-- A block has reached the fixed residue at precision a exactly when
its level has acquired a digits. -/
theorem cubicBlock_three_fixed_iff (n a : ℕ) :
    cubicBlock n ≡ 1 [ZMOD (3:ℤ)^a] ↔ a ≤ n+1 := by
  obtain ⟨u, hu, hu3⟩ := cube_block_three_unit n
  rw [Int.modEq_iff_dvd, show 1-cubicBlock n = -(cubicBlock n-1) by ring, Int.dvd_neg,
    hu, unit_pow_dvd_iff _ hu3]

/-- At every precision, a pair of different levels collides exactly
when the earlier level has reached the fixed residue. -/
theorem cubicBlock_three_collision_iff (n m a : ℕ) (hmn : m < n) :
    cubicBlock n ≡ cubicBlock m [ZMOD (3:ℤ)^a] ↔ a ≤ m+1 := by
  obtain ⟨u, hu, hu3⟩ := cube_block_three_lag_unit n m hmn
  rw [Int.modEq_iff_dvd, show cubicBlock m-cubicBlock n = -(cubicBlock n-cubicBlock m) by ring,
    Int.dvd_neg, hu, unit_pow_dvd_iff _ hu3]

/-- The first a-1 levels are different transient residues; all remaining
levels are the same fixed residue one. Holds also for a=0 and a=1. -/
theorem cubicBlock_three_transient (a : ℕ) :
    (∀ n, a-1 ≤ n → cubicBlock n ≡ 1 [ZMOD (3:ℤ)^a]) ∧
    (∀ n, n < a-1 → ¬ (cubicBlock n ≡ 1 [ZMOD (3:ℤ)^a])) ∧
    (∀ n m, m < n → m < a-1 → ¬(cubicBlock n ≡ cubicBlock m [ZMOD (3:ℤ)^a])) := by
  refine ⟨fun n ha => (cubicBlock_three_fixed_iff n a).mpr (by omega), ?_, ?_⟩
  · intro n hn
    exact (cubicBlock_three_fixed_iff n a).not.mpr (by omega)
  · intro n m hmn hm
    exact (cubicBlock_three_collision_iff n m a hmn).not.mpr (by omega)

/-- The finite image is indexed by `min n (a-1)`: different indices below
the first fixed reading never collide, and every later reading is that one. -/
theorem cubicBlock_three_clamped_phase (n m a : ℕ) :
    cubicBlock n ≡ cubicBlock m [ZMOD (3:ℤ)^a] ↔ min n (a-1) = min m (a-1) := by
  have forward (x y : ℕ) (h : y < x) :
      cubicBlock x ≡ cubicBlock y [ZMOD (3:ℤ)^a] ↔ min x (a-1) = min y (a-1) := by
    rw [cubicBlock_three_collision_iff x y a h]
    omega
  rcases lt_trichotomy m n with h | h | h
  · exact forward n m h
  · subst m
    exact ⟨fun _ => rfl, fun _ => Int.ModEq.refl _⟩
  · exact ⟨fun he => ((forward m n h).mp he.symm).symm,
      fun he => ((forward m n h).mpr he.symm).symm⟩

/-- A positive lag preserves every reading, including level zero, only at the
trivial precisions. Higher precisions have a transient rather than a cycle. -/
theorem cubicBlock_three_no_initial_period (lag a : ℕ) (hlag : 0 < lag) :
    (∀ n, cubicBlock (n+lag) ≡ cubicBlock n [ZMOD (3:ℤ)^a]) ↔ a ≤ 1 := by
  constructor
  · intro h
    have hc := h 0
    rw [Nat.zero_add, cubicBlock_three_collision_iff lag 0 a hlag] at hc
    exact hc
  · intro ha n
    rw [cubicBlock_three_collision_iff (n+lag) n a (by omega)]
    omega

end D5.S3.Arith.Primes.GoldenCubicBlockThreeAdic

/- GID: D5/S3/Combinatorics/Circle/DyadicResetSource
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/DyadicResetSource
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Physical repeated one-bit sources have dyadic positive steps and a maximal reset. -/
module
public import D5.S3.Combinatorics.Circle.ThreeRowSource
public import D5.S3.Combinatorics.Circle.TwoOppositeLargeExchange
public import D5.S3.Combinatorics.Transportation.DyadicAllocation

/-! Physical scaling and the exact half-modulus strip for one-bit periods. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.DyadicResetSource
open SourceWidth ExpandingSourcePath MixedSuffixEnergy ThreeRowSource
open scoped BigOperators

def unit (m r : ℕ) : ℕ := (2 ^ (m * r) - 1) / (2 ^ m - 1)
def top (m : ℕ) : ℕ := 2 ^ (m - 2)
def height (m : ℕ) : ℕ := 2 * top m - 1
/-- The residue determines a value; the original physical index is retained. -/
def value (m : ℕ) (a : ℕ) : ℤ :=
  if a = m - 1 then -(height m : ℤ) else (2 : ℤ) ^ a

private theorem power_facts (m : ℕ) (hm : 3 ≤ m) :
    2 ≤ top m ∧ (2 : ℤ) ^ m = 4 * top m ∧
    (height m : ℤ) = 2 * top m - 1 := by
  have he : m = (m - 2) + 2 := by omega
  have htop : 2 ≤ top m := by
    dsimp [top]
    exact (by norm_num : (2 : ℕ) ^ 1 = 2) ▸
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ m - 2)
  refine ⟨htop, ?_, ?_⟩
  · conv_lhs => rw [he, pow_add]
    simp [top]; ring
  · dsimp [height]
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl

/-- The repeated source theorem is reused at its original owner. The resulting
formula holds at every physical label, also when the numerical period is proper. -/
theorem source_values (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r)
    (i : Fin (m * r)) :
    actualSource (m * r) (unit m r) i = (unit m r : ℤ) * value m (i.val % m) := by
  have hm0 : 0 < m := by omega
  have hu : multiplier m r = unit m r := by
    simpa [unit, Nat.mul_comm] using multiplier_quotient m r hm0
  have hp := multiplier_positive m r hr
  rw [hu] at hp
  have hden : 1 < 2 ^ m - 1 := by
    have h := Nat.one_lt_two_pow (by omega : m - 1 ≠ 0)
    have he : m = (m - 1) + 1 := by omega
    rw [he, pow_succ]
    omega
  have hmod : unit m r < 2 ^ (r * m) - 1 := by
    have hi := multiplier_identity m r
    rw [hu] at hi
    have hnat : unit m r * (2 ^ m - 1) = 2 ^ (r * m) - 1 := by
      have h1 : 1 ≤ (2 : ℕ) ^ m := Nat.one_le_two_pow
      have h2 : 1 ≤ (2 : ℕ) ^ (r * m) := Nat.one_le_two_pow
      unfold modulus at hi
      exact_mod_cast hi
    nlinarith
  have hrep := repeated_source m r 1 hm0 hr
    (i.cast (Nat.mul_comm m r))
  simp only [mul_one, hu, Nat.mod_eq_of_lt hmod] at hrep
  have hbase : actualSource m 1 ⟨i.val % m, Nat.mod_lt _ hm0⟩ =
      value m (i.val % m) := by
    obtain ⟨hB, hpow, hM⟩ := power_facts m hm
    obtain ⟨hN, hodd⟩ := TwoRunSource.modulus_positive_odd m hm0
    have ha : i.val % m < m := Nat.mod_lt _ hm0
    have hhalf : modulus m / 2 = height m := by
      unfold modulus
      rw [hpow, hM]
      omega
    unfold actualSource value
    simp only [mul_one]
    apply centered_unique hN hodd (centered_bounds hN hodd _)
    · split_ifs with h
      · rw [hhalf]; constructor <;> omega
      · have hle : (2 : ℤ) ^ (i.val % m) ≤ top m := by
          have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
            (show i.val % m ≤ m - 2 by omega)
          simpa [top] using this
        rw [hhalf]
        have hp0 : 0 < (2 : ℤ) ^ (i.val % m) := by positivity
        constructor <;> omega
    · rw [centered_mod]
      split_ifs with h
      · have he : (2 : ℤ) ^ (m - 1) = 2 * top m := by
          have he : m - 1 = m - 2 + 1 := by omega
          rw [he, pow_succ]; simp [top]
        rw [h, he]
        have hv : -(height m : ℤ) = 2 * top m - modulus m := by
          unfold modulus
          rw [hM, hpow]
          ring
        rw [hv, Int.sub_emod_right]
      · rfl
  simpa only [Fin.cast_val, Nat.mul_comm] using hrep.trans
    (congrArg (fun z : ℤ => (unit m r : ℤ) * z) hbase)

/-- The native capacity has exactly the same attainable scaled heights as the
integer interval from zero to the reset magnitude. -/
theorem capacity_bounds (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r) :
    0 < unit m r ∧
    (height m : ℤ) * unit m r ≤ half (m * r) ∧
    half (m * r) < ((height m : ℤ) + 1) * unit m r ∧
    modulus (m * r) = (4 * (top m : ℤ) - 1) * unit m r := by
  have hm0 : 0 < m := by omega
  have hu : multiplier m r = unit m r := by
    simpa [unit, Nat.mul_comm] using multiplier_quotient m r hm0
  have hp := multiplier_positive m r hr
  rw [hu] at hp
  have hi := multiplier_identity m r
  obtain ⟨hB, hpow, hM⟩ := power_facts m hm
  rw [hu] at hi
  have hmod : modulus (m * r) = (4 * (top m : ℤ) - 1) * unit m r := by
    simpa [modulus, hpow, Nat.mul_comm, mul_comm] using hi.symm
  have hdiv := Int.emod_add_mul_ediv (modulus (m * r)) 2
  have hrem := Int.emod_nonneg (modulus (m * r)) (by norm_num : (2 : ℤ) ≠ 0)
  have hrem' := Int.emod_lt_of_pos (modulus (m * r)) (by norm_num : (0 : ℤ) < 2)
  have hpz : (1 : ℤ) ≤ unit m r := by exact_mod_cast hp
  refine ⟨by omega, ?_, ?_, hmod⟩
  all_goals unfold half; rw [hmod] at hdiv; rw [hM]; nlinarith

/-- Exact LARGE classification, in terms of the original physical residue. -/
theorem large_iff (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r) (i : Fin (m * r)) :
    Large (m * r) (unit m r) i ↔ m - 2 ≤ i.val % m := by
  obtain ⟨hB, hpow, hM⟩ := power_facts m hm
  obtain ⟨hd, _, _, hmod⟩ := capacity_bounds m r hm hr
  have hk : 3 ≤ m * r := by nlinarith
  obtain ⟨_, hN, _, _, _⟩ := capacity_facts (m * r) hk
  have hQ : 4 * quarter (m * r) =
      (4 * (top m : ℤ) - 1) * unit m r + 1 := by omega
  have ha : i.val % m < m := Nat.mod_lt _ (by omega)
  rw [Large, source_values m r hm hr]
  by_cases hz : i.val % m = m - 1
  · simp only [value, hz, ite_true, abs_mul, abs_neg]
    rw [abs_of_pos (by exact_mod_cast hd : (0 : ℤ) < unit m r),
      abs_of_nonneg (by positivity : (0 : ℤ) ≤ height m)]
    constructor
    · omega
    · intro _; rw [hM]; nlinarith
  · simp only [value, hz, ite_false, abs_mul]
    rw [abs_of_pos (by exact_mod_cast hd : (0 : ℤ) < unit m r),
      abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (i.val % m))]
    by_cases ht : i.val % m = m - 2
    · rw [ht]
      have htop : (2 : ℤ) ^ (m - 2) = top m := by simp [top]
      rw [htop]
      constructor
      · omega
      · intro _; have hz : (1 : ℤ) ≤ unit m r := by exact_mod_cast hd; nlinarith
    · have hsmall : (2 : ℤ) ^ (i.val % m) * 2 ≤ top m := by
        have he : i.val % m + 1 ≤ m - 2 := by omega
        have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) he
        simpa [pow_succ, top] using hp
      have hunit : (1 : ℤ) ≤ unit m r := by exact_mod_cast hd
      constructor
      · intro h; nlinarith
      · omega

end D5.S3.Combinatorics.Circle.DyadicResetSource

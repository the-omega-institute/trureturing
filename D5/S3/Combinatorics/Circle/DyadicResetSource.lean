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
    obtain ⟨_, _, _, hN, hodd⟩ := source_geometry hm
    have ha : i.val % m < m := Nat.mod_lt _ hm0
    have hhalf : modulus m / 2 = height m := by
      unfold modulus
      rw [hpow, hM]
      omega
    unfold actualSource value
    simp only [Nat.cast_one, mul_one]
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
          rw [he, pow_succ]; simp [top, mul_comm]
        rw [h, he]
        have hv : -(height m : ℤ) = 2 * top m - modulus m := by
          unfold modulus
          rw [hM, hpow]
          ring
        rw [hv, Int.sub_emod_right]
      · rfl
  simpa only [actualSource, Fin.val_cast, Nat.mul_comm] using hrep.trans
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
  all_goals unfold half; rw [hmod, hM]; rw [hmod] at hdiv hrem hrem'; nlinarith

/-- Exact LARGE classification, in terms of the original physical residue. -/
theorem large_iff (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r) (i : Fin (m * r)) :
    Large (m * r) (unit m r) i ↔ m - 2 ≤ i.val % m := by
  obtain ⟨hB, hpow, hM⟩ := power_facts m hm
  obtain ⟨hd, _, _, hmod⟩ := capacity_bounds m r hm hr
  have hk : 3 ≤ m * r := by nlinarith
  obtain ⟨_, hN, _, _, _⟩ := source_geometry hk
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
      · intro _
        have hdz : (1 : ℤ) ≤ unit m r := by exact_mod_cast hd
        nlinarith
    · have hsmall : (2 : ℤ) ^ (i.val % m) * 2 ≤ top m := by
        have he : i.val % m + 1 ≤ m - 2 := by omega
        have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) he
        simpa [pow_succ, top] using hp
      have hunit : (1 : ℤ) ≤ unit m r := by exact_mod_cast hd
      constructor
      · intro h; nlinarith
      · omega

/-- The scaled word still has all original physical labels. -/
def scaled (m r : ℕ) (i : Fin (m * r)) : ℤ := value m (i.val % m)

theorem scaled_mass (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r)
    (W : List (Fin (m * r))) :
    mass (actualSource (m * r) (unit m r)) W =
      (unit m r : ℤ) * mass (scaled m r) W := by
  have h := scaled_sum (scaled m r) (actualSource (m * r) (unit m r))
    id (unit m r) W (fun i _ => source_values m r hm hr i)
  simpa [mass] using h

/-- Native legality is equivalent to the exact integral reset strip. The
forward implication uses divisibility of every attainable prefix height. -/
theorem legal_iff (m r : ℕ) (hm : 3 ≤ m) (hr : 1 ≤ r)
    (W : List (Fin (m * r))) :
    TwoOppositeLargeExchange.Legal (m * r) (unit m r) W ↔
      W.Nodup ∧ InStrip (scaled m r) (height m) 0 W := by
  obtain ⟨hd, hlo, hhi, _⟩ := capacity_bounds m r hm hr
  have hdz : (0 : ℤ) < unit m r := by exact_mod_cast hd
  constructor
  · intro hW
    refine ⟨hW.1, strip_of_all_prefixes W ?_⟩
    intro n
    have h := hW.2 n
    change 0 ≤ mass (actualSource (m * r) (unit m r)) (W.take n) ∧
      mass (actualSource (m * r) (unit m r)) (W.take n) ≤ half (m * r) at h
    rw [scaled_mass m r hm hr] at h
    have hp0 : 0 ≤ mass (scaled m r) (W.take n) := by nlinarith [h.1]
    have hp1 : mass (scaled m r) (W.take n) ≤ height m := by
      by_contra hn
      have hn' : (height m : ℤ) + 1 ≤ mass (scaled m r) (W.take n) := by omega
      nlinarith [h.2]
    simpa using And.intro hp0 hp1
  · rintro ⟨hn, hs⟩
    apply TwoOppositeLargeExchange.legal_of_strip hn
    have h := scale_strip (scaled m r) (actualSource (m * r) (unit m r))
      id (unit m r) (height m) (half (m * r)) 0 (le_of_lt hdz)
      (by nlinarith : (unit m r : ℤ) * height m ≤ half (m * r)) W
      (fun i _ => source_values m r hm hr i) hs
    simpa using h

/-- Exactly r distinct physical occurrences have each residue. -/
theorem residue_card (m r a : ℕ) (hm : 0 < m) (ha : a < m) :
    (Finset.univ.filter (fun i : Fin (m * r) => i.val % m = a)).card = r := by
  classical
  let θ : Fin r × Fin m ≃ Fin (m * r) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm r m))
  have hθ (j : Fin r) (b : Fin m) : (θ (j, b)).val % m = b.val := by
    simp [θ, finProdFinEquiv, finCongr, Nat.add_mod, Nat.mod_eq_of_lt b.isLt]
  let f : Fin r → Fin (m * r) := fun j => θ (j, ⟨a, ha⟩)
  have hinj : Function.Injective f := by
    intro j k h
    have := θ.injective h
    exact congrArg Prod.fst this
  have he : Finset.univ.filter (fun i : Fin (m * r) => i.val % m = a) =
      Finset.univ.image f := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      rcases hsplit : θ.symm i with ⟨j, b⟩
      have hback : θ (j, b) = i := by
        simpa only [hsplit] using θ.apply_symm_apply i
      have hb : b = ⟨a, ha⟩ := Fin.ext (by rw [← hθ j b, hback]; exact hi)
      exact ⟨j, by simpa [f, hb] using hback⟩
    · rintro ⟨j, rfl⟩
      exact hθ j ⟨a, ha⟩
  rw [he, Finset.card_image_of_injective _ hinj]
  simp

end D5.S3.Combinatorics.Circle.DyadicResetSource

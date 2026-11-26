/- GID: D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.claim; result=D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.result; claim=D5/S3/Arith/Abundancy/ZelinskyOmegaRatioDensity.claim
   digest: Every fixed prime-factor restriction has positive lower Euler density. -/

import D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
admission_basis: open-problem-resolution; preregistration #31808; Refuted.
The source is Zelinsky's Conjecture 1 in section 7 of Integers 21, A76.
The Euler predicate and its count are reused without an oddness restriction.

Direct frozen dependencies:
* StrongPseudoperfectEulerDensity.EulerForm, eulerCount, eulerCount_pos,
  largeSquares, largeSquares_card and reciprocal_square_sum_le_two.
* ModFourChebyshev.primeCount and prime_count_lower.

Definitions and live consumers:
* OR: definition; family_mem, family_count, orCount, claim.
* orCount: definition; family_count, or_count_le_euler, or_count_lower, claim,
  relative_density_pos, result.
* claim: definition; result.
Per-declaration proof_shape and live consumers (conservative classification):
* euler_prime_square: bind-only; euler_subset.
* primeSquares: definition; euler_subset, primeSquares_card, euler_envelope.
* euler_subset: bind-only; euler_envelope.
* primeSquares_card: bind-only; euler_envelope.
* small_argument: bind-only; small_term, euler_count_upper.
* small_term: bind-only; euler_envelope.
* euler_envelope: bind-only; euler_count_upper.
* euler_count_upper: bind-only; relative_density_pos.
* family_mem: bind-only; family_count.
* family_count: bind-only; or_count_lower.
* or_count_le_euler: bind-only; result.
* or_count_lower: bind-only; relative_density_pos.
* relative_density_pos: bind-only; result.
* result: bind-only; designated external open-problem refutation.
No independent escape-witness qualification is claimed.
Real thresholds x >= 0 count the same integers as X = floor(x); at a natural
threshold X the analytic estimate uses its real cast. All three counts are
explicitly eventually positive in result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity

open StrongPseudoperfectEulerDensity
open D5.S3.PrimeGaps.ModFourChebyshev
attribute [local instance] Classical.propDecidable

private lemma euler_prime_square {n : ℕ} (hn : EulerForm n) :
    ∃ q s : ℕ, q.Prime ∧ 0 < s ∧ n = q * s ^ 2 := by
  obtain ⟨q, a, m, hq, hq4, ha4, hm, hcop, rfl⟩ := hn
  let j := (a - 1) / 2
  have ha : a = 1 + 2 * j := by dsimp [j]; omega
  refine ⟨q, q ^ j * m, hq, mul_pos (pow_pos hq.pos j) hm, ?_⟩
  rw [ha, pow_add, mul_pow, ← pow_mul]
  simp only [pow_one]
  rw [Nat.mul_comm j 2]
  ring

private def primeSquares (X T : ℕ) : Finset ℕ :=
  (Icc 1 T).biUnion fun s => (Nat.primesLE (X / s ^ 2)).image (fun q => q * s ^ 2)

private lemma euler_subset (X T : ℕ) :
    (Icc 1 X).filter EulerForm ⊆ primeSquares X T ∪ largeSquares X T := by
  intro n hn
  obtain ⟨hnI, hn⟩ := mem_filter.mp hn
  obtain ⟨q, s, hq, hs, rfl⟩ := euler_prime_square hn
  have hqX := (mem_Icc.mp hnI).2
  have hsX : s ≤ X := by
    have hss := Nat.le_self_pow (by decide : 2 ≠ 0) s
    nlinarith [hq.pos]
  have hdiv : q ≤ X / s ^ 2 :=
    (Nat.le_div_iff_mul_le (pow_pos hs 2)).mpr hqX
  by_cases hsT : s ≤ T
  · apply mem_union_left
    apply mem_biUnion.mpr
    exact ⟨s, mem_Icc.mpr ⟨hs, hsT⟩,
      mem_image.mpr ⟨q, Nat.mem_primesLE.mpr ⟨hdiv, hq⟩, rfl⟩⟩
  · apply mem_union_right
    apply mem_biUnion.mpr
    exact ⟨s, mem_Icc.mpr ⟨by omega, hsX⟩,
      mem_image.mpr ⟨q, mem_Icc.mpr ⟨hq.pos, hdiv⟩, rfl⟩⟩

private lemma primeSquares_card (X T : ℕ) :
    (primeSquares X T).card ≤ ∑ s ∈ Icc 1 T, Nat.primeCounting (X / s ^ 2) := by
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro s hs
  exact card_image_le.trans_eq (Nat.primesLE_card_eq_primeCounting _)

private lemma small_argument {x : ℝ} (hx : 0 < x) {s : ℕ} (hs : 0 < s)
    (hsx : (s : ℝ) ≤ x ^ (1 / 4 : ℝ)) :
    x ^ (1 / 2 : ℝ) ≤ x / (s : ℝ) ^ 2 := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : (s : ℝ) ^ 2 ≤ x ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (x ^ (1 / 4 : ℝ)) ^ 2 := by gcongr
      _ = _ := by rw [← rpow_mul_natCast hx.le]; norm_num
  apply (le_div_iff₀ (pow_pos hs0 2)).mpr
  calc
    _ ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) := by gcongr
    _ = x := by rw [← rpow_add hx]; norm_num

private lemma small_term {x : ℝ} (hx : 1 < x) {s : ℕ} (hs : 0 < s)
    (hsx : (s : ℝ) ≤ x ^ (1 / 4 : ℝ))
    (hp : (Nat.primeCounting ⌊x / (s : ℝ) ^ 2⌋₊ : ℝ) ≤
      (log 4 + 1) * (x / (s : ℝ) ^ 2) / log (x / (s : ℝ) ^ 2)) :
    (Nat.primeCounting ⌊x / (s : ℝ) ^ 2⌋₊ : ℝ) ≤
      (2 * (log 4 + 1) * (x / log x)) * (1 / (s : ℝ) ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hy := small_argument hx0 hs hsx
  have hlog : log x / 2 ≤ log (x / (s : ℝ) ^ 2) := by
    have hl := log_le_log (rpow_pos_of_pos hx0 (1 / 2 : ℝ)) hy
    rw [log_rpow hx0] at hl
    linarith
  have hlogx : 0 < log x := log_pos hx
  have hc : 0 < log 4 + 1 := by positivity
  calc
    _ ≤ (log 4 + 1) * (x / (s : ℝ) ^ 2) / log (x / (s : ℝ) ^ 2) := hp
    _ ≤ (log 4 + 1) * (x / (s : ℝ) ^ 2) / (log x / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlog
    _ = _ := by field_simp

private lemma euler_envelope {X T : ℕ} (hX : 1 < X)
    (hT : (T : ℝ) ≤ (X : ℝ) ^ (1 / 4 : ℝ))
    (hp : ∀ s ∈ Icc 1 T,
      (Nat.primeCounting ⌊(X : ℝ) / (s : ℝ) ^ 2⌋₊ : ℝ) ≤
        (log 4 + 1) * ((X : ℝ) / (s : ℝ) ^ 2) /
          log ((X : ℝ) / (s : ℝ) ^ 2)) :
    (eulerCount X : ℝ) ≤
      4 * (log 4 + 1) * ((X : ℝ) / log X) + 2 * (X : ℝ) / (T + 1) := by
  have hx : (1 : ℝ) < X := by exact_mod_cast hX
  have hsmall : ((primeSquares X T).card : ℝ) ≤
      4 * (log 4 + 1) * ((X : ℝ) / log X) := by
    calc
      _ ≤ ∑ s ∈ Icc 1 T, (Nat.primeCounting (X / s ^ 2) : ℝ) := by
        exact_mod_cast primeSquares_card X T
      _ ≤ ∑ s ∈ Icc 1 T,
          (2 * (log 4 + 1) * ((X : ℝ) / log X)) * (1 / (s : ℝ) ^ 2) := by
        apply sum_le_sum
        intro s hs
        have hsx : (s : ℝ) ≤ (X : ℝ) ^ (1 / 4 : ℝ) :=
          (show (s : ℝ) ≤ T by exact_mod_cast (mem_Icc.mp hs).2).trans hT
        have ht := small_term hx (mem_Icc.mp hs).1 hsx (hp s hs)
        simpa only [← Nat.cast_pow, Nat.floor_div_eq_div] using ht
      _ = (2 * (log 4 + 1) * ((X : ℝ) / log X)) *
          (∑ s ∈ Icc 1 T, 1 / (s : ℝ) ^ 2) := by rw [mul_sum]
      _ ≤ (2 * (log 4 + 1) * ((X : ℝ) / log X)) * 2 := by
        apply mul_le_mul_of_nonneg_left (reciprocal_square_sum_le_two T)
        positivity
      _ = _ := by ring
  have hc := (card_le_card (euler_subset X T)).trans (card_union_le _ _)
  have hreal : (eulerCount X : ℝ) ≤
      ((primeSquares X T).card : ℝ) + (largeSquares X T).card := by
    exact_mod_cast hc
  linarith [largeSquares_card X T]

/-- Euler forms have counting order at most X / log X. -/
theorem euler_count_upper :
    ∃ C > (0 : ℝ), ∀ᶠ X : ℕ in atTop,
      (eulerCount X : ℝ) ≤ C * ((X : ℝ) / log X) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  refine ⟨4 * (log 4 + 1) + 2, by positivity, ?_⟩
  have hn : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hhalf : Tendsto (fun X : ℕ => (X : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hn
  have hlog : Tendsto (fun X : ℕ => log (X : ℝ) / (X : ℝ) ^ (1 / 4 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero.comp hn
  filter_upwards [eventually_ge_atTop (2 : ℕ), hhalf.eventually_ge_atTop A,
    hlog.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with X hX hXA hlogX
  let u : ℝ := (X : ℝ) ^ (1 / 4 : ℝ)
  let T : ℕ := ⌊u⌋₊
  have hx : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hx0 : (0 : ℝ) < X := zero_lt_one.trans hx
  have hu : 0 < u := rpow_pos_of_pos hx0 _
  have hT : (T : ℝ) ≤ u := Nat.floor_le hu.le
  have huT : u < (T : ℝ) + 1 := Nat.lt_floor_add_one u
  have hen := euler_envelope (show 1 < X by omega) hT (by
    intro s hs
    have hsx : (s : ℝ) ≤ (X : ℝ) ^ (1 / 4 : ℝ) :=
      (show (s : ℝ) ≤ T by exact_mod_cast (mem_Icc.mp hs).2).trans hT
    exact hA _ (hXA.trans (small_argument hx0 (mem_Icc.mp hs).1 hsx)))
  have hlogpos : 0 < log (X : ℝ) := log_pos hx
  have hlogu : log (X : ℝ) ≤ u := by
    have ht := (div_lt_iff₀ hu).mp hlogX
    simpa using ht.le
  have htail : 2 * (X : ℝ) / (T + 1) ≤ 2 * ((X : ℝ) / log X) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hx0.le hlogpos (hlogu.trans huT.le)) (by norm_num)
  calc
    _ ≤ 4 * (log 4 + 1) * ((X : ℝ) / log X) + 2 * (X : ℝ) / (T + 1) := hen
    _ ≤ 4 * (log 4 + 1) * ((X : ℝ) / log X) + 2 * ((X : ℝ) / log X) :=
      add_le_add_right htail _
    _ = _ := by ring


/-- Zelinsky's prime-factor restriction, with real slope and intercept. -/
def OR (α β : ℝ) (n : ℕ) : Prop :=
  α * (ArithmeticFunction.cardDistinctFactors n : ℝ) + β ≤
    (ArithmeticFunction.cardFactors n : ℝ)

/-- Positive Euler-form integers satisfying the restriction, counted once each. -/
def orCount (α β : ℝ) (X : ℕ) : ℕ :=
  ((Icc 1 X).filter (fun n => EulerForm n ∧ OR α β n)).card

/-- Conjecture 1, including both clauses of substantially stronger. -/
def claim : Prop :=
  ∀ α₁ α₂ β₁ β₂ : ℝ, 2 < α₂ → α₂ < α₁ →
    (∀ n, EulerForm n → OR α₁ β₁ n → OR α₂ β₂ n) ∧
      Tendsto (fun X : ℕ => (orCount α₁ β₁ X : ℝ) / orCount α₂ β₂ X)
        atTop (𝓝 0)

private lemma family_mem (α β : ℝ) (h q : ℕ) (hh : 0 < h)
    (hbound : 2 * α + β ≤ (1 + 2 * h : ℕ))
    (hq : q.Prime) (hq4 : q % 4 = 1) :
    EulerForm (3 ^ (2 * h) * q) ∧ OR α β (3 ^ (2 * h) * q) := by
  have hq3 : q ≠ 3 := by intro he; subst q; norm_num at hq4
  have hcop : Nat.Coprime q 3 := (Nat.coprime_primes hq (by decide)).mpr hq3
  have hpow : Nat.Coprime (3 ^ (2 * h)) q := hcop.symm.pow_left _
  constructor
  · refine ⟨q, 1, 3 ^ h, hq, hq4, by norm_num, by positivity,
      hcop.pow_right h, ?_⟩
    simp only [pow_one, ← pow_mul]
    rw [Nat.mul_comm h 2, mul_comm q]
  · unfold OR
    rw [ArithmeticFunction.cardFactors_mul (by positivity) hq.ne_zero,
      ArithmeticFunction.cardFactors_pow,
      ArithmeticFunction.cardFactors_apply_prime (by decide : Nat.Prime 3),
      ArithmeticFunction.cardFactors_apply_prime hq,
      ArithmeticFunction.cardDistinctFactors_mul hpow,
      ArithmeticFunction.cardDistinctFactors_apply_prime_pow
        (by decide : Nat.Prime 3) (by omega),
      ArithmeticFunction.cardDistinctFactors_apply_prime hq]
    push_cast at hbound ⊢
    nlinarith

private lemma family_count (α β : ℝ) (h : ℕ) (hh : 0 < h)
    (hbound : 2 * α + β ≤ (1 + 2 * h : ℕ)) (X : ℕ) :
    primeCount ((X : ℝ) / (3 ^ (2 * h) : ℕ)) ≤ orCount α β X := by
  let M := 3 ^ (2 * h)
  let S := (Ioc 0 ⌊(X : ℝ) / M⌋₊).filter (fun q : ℕ => q.Prime ∧ q % 4 = 1)
  have hM : 0 < M := by dsimp [M]; positivity
  have himage : S.image (fun q => M * q) ⊆
      (Icc 1 X).filter (fun n => EulerForm n ∧ OR α β n) := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hn
    obtain ⟨hqI, hprime, hmod⟩ := mem_filter.mp hq
    have hle : (q : ℝ) ≤ (X : ℝ) / M :=
      (show (q : ℝ) ≤ ⌊(X : ℝ) / M⌋₊ by
        exact_mod_cast (mem_Ioc.mp hqI).2).trans (Nat.floor_le (by positivity))
    have hprod : M * q ≤ X := by
      have := (le_div_iff₀ (by exact_mod_cast hM : (0 : ℝ) < M)).mp hle
      exact_mod_cast (by simpa [mul_comm] using this : (M : ℝ) * q ≤ X)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith [hprime.pos], hprod⟩,
      family_mem α β h q hh hbound hprime hmod⟩
  have hinj : Function.Injective (fun q : ℕ => M * q) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hM hab
  calc
    primeCount ((X : ℝ) / (3 ^ (2 * h) : ℕ)) = S.card := rfl
    _ = (S.image (fun q => M * q)).card := (card_image_of_injective S hinj).symm
    _ ≤ orCount α β X := card_le_card himage

private lemma or_count_le_euler (α β : ℝ) (X : ℕ) :
    orCount α β X ≤ eulerCount X := by
  apply card_le_card
  intro n hn
  obtain ⟨hnI, hnE, hnOR⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hnI, hnE⟩

private lemma or_count_lower (α β : ℝ) :
    ∃ d > (0 : ℝ), ∀ᶠ X : ℕ in atTop,
      d * ((X : ℝ) / log X) ≤ orCount α β X := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * α + β)
  let h := k + 1
  have hh : 0 < h := by dsimp [h]; omega
  have hbound : 2 * α + β ≤ (1 + 2 * h : ℕ) := by
    have hk' : (k : ℝ) ≤ (1 + 2 * h : ℕ) := by dsimp [h]; push_cast; linarith
    exact hk.le.trans hk'
  let M : ℕ := 3 ^ (2 * h)
  have hM : 0 < M := by dsimp [M]; positivity
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  refine ⟨exp (-50) / M, by positivity, ?_⟩
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually_ge_atTop ((M : ℝ) * exp 50)] with X hX
  have hy : exp 50 ≤ (X : ℝ) / M := (le_div_iff₀ hMR).mpr (by nlinarith)
  have hy1 : 1 < (X : ℝ) / M :=
    lt_of_lt_of_le (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 50)) hy
  have hx : 0 < (X : ℝ) := by nlinarith [exp_pos (50 : ℝ)]
  have hyX : (X : ℝ) / M ≤ X := (div_le_self hx.le hM1)
  have hlogy : 0 < log ((X : ℝ) / M) := log_pos hy1
  have hlog : 0 < log (X : ℝ) := log_pos (hy1.trans_le hyX)
  have hlogs : log ((X : ℝ) / M) ≤ log X := log_le_log (by positivity) hyX
  calc
    exp (-50) / M * ((X : ℝ) / log X) =
        (exp (-50) * ((X : ℝ) / M)) / log X := by ring
    _ ≤ (exp (-50) * ((X : ℝ) / M)) / log ((X : ℝ) / M) :=
      div_le_div_of_nonneg_left (by positivity) hlogy hlogs
    _ ≤ (primeCount ((X : ℝ) / M) : ℝ) := prime_count_lower hy
    _ ≤ orCount α β X := by exact_mod_cast family_count α β h hh hbound X

/-- Every fixed restriction occupies a positive lower proportion of Euler forms. -/
theorem relative_density_pos (α β : ℝ) :
    ∃ c > (0 : ℝ), ∀ᶠ X : ℕ in atTop,
      c * (eulerCount X : ℝ) ≤ orCount α β X := by
  obtain ⟨C, hC, hupper⟩ := euler_count_upper
  obtain ⟨d, hd, hlower⟩ := or_count_lower α β
  refine ⟨d / C, div_pos hd hC, ?_⟩
  filter_upwards [hupper, hlower] with X hu hl
  calc
    d / C * (eulerCount X : ℝ) ≤ d / C * (C * ((X : ℝ) / log X)) :=
      mul_le_mul_of_nonneg_left hu (div_pos hd hC).le
    _ = d * ((X : ℝ) / log X) := by field_simp
    _ ≤ orCount α β X := hl

/-- The density clause fails even for the nested restrictions (4,0) and (3,0). -/
theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨c, hc, hnum⟩ := relative_density_pos 4 0
  obtain ⟨d, hd, hden⟩ := relative_density_pos 3 0
  have hpositive : ∀ᶠ X : ℕ in atTop,
      0 < (eulerCount X : ℝ) ∧ 0 < (orCount 3 0 X : ℝ) ∧
        0 < (orCount 4 0 X : ℝ) := by
    filter_upwards [eventually_ge_atTop (5 : ℕ), hnum, hden] with X hX hn hdX
    have he : (0 : ℝ) < eulerCount X := by exact_mod_cast eulerCount_pos X hX
    exact ⟨he, (mul_pos hd he).trans_le hdX, (mul_pos hc he).trans_le hn⟩
  have hratio : ∀ᶠ X : ℕ in atTop,
      c ≤ (orCount 4 0 X : ℝ) / orCount 3 0 X := by
    filter_upwards [hnum, hpositive] with X hn hp
    apply (le_div_iff₀ hp.2.1).mpr
    exact (mul_le_mul_of_nonneg_left
      (by exact_mod_cast or_count_le_euler 3 0 X) hc.le).trans hn
  have ht := (hclaim 4 3 0 0 (by norm_num) (by norm_num)).2
  have hzero : c ≤ 0 := ge_of_tendsto ht hratio
  exact (not_le_of_gt hc) hzero

end D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity

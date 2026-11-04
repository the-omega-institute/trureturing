/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianExpPiRounding
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Concrete exponential pi enclosure for the signed Gaussian certificate. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianExpRounding

/-! Range-split ordinary Taylor proofs for the original exp(-2*pi) input.
Split 2*pi = 6 + q + delta, with q a fixed 40-place truncation and
0 < delta < 10^-40. The three rational enclosures are checked by norm_num;
the exponential bounds follow from the analytic Taylor/geometric theorem.
No interval oracle or unproved floating-point estimate is used.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
noncomputable section
open Finset
namespace RHFiniteGaussian.AnalyticEndpoints

private theorem exp_neg_nat_mul_rat_bounds (y : ℚ)
    (hy0 : (0 : ℝ) ≤ (y : ℝ)) (hy1 : (y : ℝ) < 1) (N m : ℕ) :
    ((1 / expUpperQ y N ^ m : ℚ) : ℝ) ≤ Real.exp (-((m : ℝ) * (y : ℝ))) ∧
      Real.exp (-((m : ℝ) * (y : ℝ))) ≤ ((1 / expPrefixQ y N ^ m : ℚ) : ℝ) := by
  have ht := exp_taylor_geometric_bounds hy0 hy1 N
  have h1 : (1 : ℝ) ≤ expPrefix (y : ℝ) N := by
    have h := Finset.single_le_sum (s := range (N + 1))
      (f := fun n : ℕ => (y : ℝ) ^ n / (n.factorial : ℝ))
      (fun n _ => div_nonneg (pow_nonneg hy0 n) (Nat.cast_nonneg _))
      (show 0 ∈ range (N + 1) by simp)
    simpa [expPrefix] using h
  have hp : 0 < expPrefix (y : ℝ) N := zero_lt_one.trans_le h1
  have hlo : expPrefix (y : ℝ) N ^ m ≤ Real.exp (y : ℝ) ^ m :=
    pow_le_pow_left₀ hp.le ht.1 m
  have hup : Real.exp (y : ℝ) ^ m ≤ expUpper (y : ℝ) N ^ m :=
    pow_le_pow_left₀ (Real.exp_pos (y : ℝ)).le ht.2 m
  have hid : Real.exp (-((m : ℝ) * (y : ℝ))) = 1 / Real.exp (y : ℝ) ^ m := by
    rw [Real.exp_neg, Real.exp_nat_mul, one_div]
  rw [hid]
  constructor
  · simpa using one_div_le_one_div_of_le (pow_pos (Real.exp_pos (y : ℝ)) m) hup
  · simpa using one_div_le_one_div_of_le (pow_pos hp m) hlo

private def sixLo : ℚ := 247875217666635842304516743081666789150647958553394505087862400627619422829399018237472040158266781800924444480371905142113196287641356712374147554216457247583092048388184260454638951362072198338176226985686782211270865148110856789651248686213041063955695091 / (10 : ℚ) ^ 260
private def sixHi : ℚ := 247875217666635842304516743081666789150647958553394505087862400627619422829399018237472040158266781800924444480371905142113196287641356712374147554216457247583092048388184260454638951362072198338176226985686782211270865148110856789651248686213041063955695092 / (10 : ℚ) ^ 260
private def qLo : ℚ := 75338016816973137923535914225322925784896814693844424425920052109882577269295884352872472060151676578867354374218508856190069079093275389379061962004526510291257729684491782529763448604761944351186840059293718416079878577015010037667722457647335579086349452443 / (10 : ℚ) ^ 260
private def qHi : ℚ := 75338016816973137923535914225322925784896814693844424425920052109882577269295884352872472060151676578867354374218508856190069079093275389379061962004526510291257729684491782529763448604761944351186840059293718416079878577015010037667722457647335579086349452444 / (10 : ℚ) ^ 260
private def deltaLo : ℚ := 99999999999999999999999999999999999999996120124978835805011081538436718742758200349660185830845898969486290920508814947753513276020026887500156196468284226655369413883437159870990042350392116732979545370977291858691115904202241390475840198603783560589861642369 / (10 : ℚ) ^ 260
private def deltaHi : ℚ := 99999999999999999999999999999999999999996120124978835805011081538436718742758200349660185830845898969486290920508814947753513276020026887500156196468284226655369413883437159870990042350392116732979545370977291858691115904202241390475840198603783560609861642370 / (10 : ℚ) ^ 260
private def q40 : ℚ := 2831853071795864769252867665590057683943 / (10 : ℚ) ^ 40
private def deltaLowerQ : ℚ := 2 * piLower250 - 6 - q40
private def deltaUpperQ : ℚ := 2 * piUpper250 - 6 - q40

def expNegTwoPiLower250 : ℚ := 18674427317079888144302129348270303934228050024753171993815386383179351229157280739064849054653622898410344084049043643424188957887979450097201417959166938250365754450375918496699130163775358800743962135770093125871535681287106538596134680176555195 / (10 : ℚ) ^ 250
def expNegTwoPiUpper250 : ℚ := 18674427317079888144302129348270303934228050024753171993815386383179351229157280739064849054653622898410344084049043643424188957887979450097201417959166938250365754450375918496699130163775358800743962135770093125871535681287106538596134680176555204 / (10 : ℚ) ^ 250

set_option exponentiation.threshold 1024 in
private theorem six_arithmetic :
    sixLo ≤ 1 / expUpperQ (3 / 4) 240 ^ 8 ∧
      1 / expPrefixQ (3 / 4) 240 ^ 8 ≤ sixHi := by
  norm_num [sixLo, sixHi, expUpperQ, expPrefixQ, Finset.sum_range_succ]

set_option exponentiation.threshold 1024 in
private theorem q_arithmetic :
    qLo ≤ 1 / expUpperQ q40 160 ∧ 1 / expPrefixQ q40 160 ≤ qHi := by
  norm_num [qLo, qHi, q40, expUpperQ, expPrefixQ, Finset.sum_range_succ]

set_option exponentiation.threshold 1024 in
private theorem delta_arithmetic :
    deltaLo ≤ 1 / expUpperQ deltaUpperQ 6 ∧
      1 / expPrefixQ deltaLowerQ 6 ≤ deltaHi := by
  norm_num [deltaLo, deltaHi, deltaUpperQ, deltaLowerQ, piLower250, piUpper250,
    q40, expUpperQ, expPrefixQ, Finset.sum_range_succ]

private theorem six_bounds :
    (sixLo : ℝ) ≤ Real.exp (-6) ∧ Real.exp (-6) ≤ (sixHi : ℝ) := by
  have h := exp_neg_nat_mul_rat_bounds (3 / 4) (by norm_num) (by norm_num) 240 8
  have hl : (sixLo : ℝ) ≤ ((1 / expUpperQ (3 / 4) 240 ^ 8 : ℚ) : ℝ) := by
    exact_mod_cast six_arithmetic.1
  have hu : ((1 / expPrefixQ (3 / 4) 240 ^ 8 : ℚ) : ℝ) ≤ (sixHi : ℝ) := by
    exact_mod_cast six_arithmetic.2
  constructor
  · convert hl.trans h.1 using 1; norm_num
  · convert h.2.trans hu using 1; norm_num

private theorem q_bounds :
    (qLo : ℝ) ≤ Real.exp (-(q40 : ℝ)) ∧ Real.exp (-(q40 : ℝ)) ≤ (qHi : ℝ) := by
  have h := exp_neg_nat_mul_rat_bounds q40 (by norm_num [q40]) (by norm_num [q40]) 160 1
  have hl : (qLo : ℝ) ≤ ((1 / expUpperQ q40 160 : ℚ) : ℝ) := by
    exact_mod_cast q_arithmetic.1
  have hu : ((1 / expPrefixQ q40 160 : ℚ) : ℝ) ≤ (qHi : ℝ) := by
    exact_mod_cast q_arithmetic.2
  constructor
  · exact hl.trans (by simpa using h.1)
  · have hu0 : Real.exp (-(q40 : ℝ)) ≤ ((1 / expPrefixQ q40 160 : ℚ) : ℝ) := by
      simpa using h.2
    exact hu0.trans hu

private theorem delta_bounds :
    (deltaLo : ℝ) ≤ Real.exp (-(2 * Real.pi - 6 - (q40 : ℝ))) ∧
      Real.exp (-(2 * Real.pi - 6 - (q40 : ℝ))) ≤ (deltaHi : ℝ) := by
  have h0 : (0 : ℝ) ≤ (deltaLowerQ : ℝ) := by
    norm_num [deltaLowerQ, piLower250, q40]
  have h1 : (deltaLowerQ : ℝ) < 1 := by
    norm_num [deltaLowerQ, piLower250, q40]
  have h2 : (0 : ℝ) ≤ (deltaUpperQ : ℝ) := by
    norm_num [deltaUpperQ, piUpper250, q40]
  have h3 : (deltaUpperQ : ℝ) < 1 := by
    norm_num [deltaUpperQ, piUpper250, q40]
  have hlo := exp_neg_nat_mul_rat_bounds deltaLowerQ h0 h1 6 1
  have hhi := exp_neg_nat_mul_rat_bounds deltaUpperQ h2 h3 6 1
  have hl : (deltaLo : ℝ) ≤ ((1 / expUpperQ deltaUpperQ 6 : ℚ) : ℝ) := by
    exact_mod_cast delta_arithmetic.1
  have hu : ((1 / expPrefixQ deltaLowerQ 6 : ℚ) : ℝ) ≤ (deltaHi : ℝ) := by
    exact_mod_cast delta_arithmetic.2
  have hdlo : (deltaLowerQ : ℝ) ≤ 2 * Real.pi - 6 - (q40 : ℝ) := by
    simp only [deltaLowerQ, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
    linarith [pi_250_bounds.1]
  have hdhi : 2 * Real.pi - 6 - (q40 : ℝ) ≤ (deltaUpperQ : ℝ) := by
    simp only [deltaUpperQ, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
    linarith [pi_250_bounds.2]
  constructor
  · exact (hl.trans (by simpa using hhi.1)).trans (Real.exp_le_exp.mpr (neg_le_neg hdhi))
  · have hu0 : Real.exp (-(deltaLowerQ : ℝ)) ≤
        ((1 / expPrefixQ deltaLowerQ 6 : ℚ) : ℝ) := by
      simpa using hlo.2
    exact (Real.exp_le_exp.mpr (neg_le_neg hdlo)).trans (hu0.trans hu)

set_option exponentiation.threshold 1024 in
private theorem final_arithmetic :
    expNegTwoPiLower250 ≤ sixLo * qLo * deltaLo ∧
      sixHi * qHi * deltaHi ≤ expNegTwoPiUpper250 := by
  norm_num [expNegTwoPiLower250, expNegTwoPiUpper250, sixLo, sixHi,
    qLo, qHi, deltaLo, deltaHi]

set_option exponentiation.threshold 1024 in
/-- The original signed-V certificate's actual outward-rounded exp(-2*pi) box. -/
theorem exp_neg_two_pi_250_bounds :
    (expNegTwoPiLower250 : ℝ) ≤ Real.exp (-(2 * Real.pi)) ∧
      Real.exp (-(2 * Real.pi)) ≤ (expNegTwoPiUpper250 : ℝ) := by
  have hb0 : (0 : ℝ) ≤ (qLo : ℝ) := by norm_num [qLo]
  have hc0 : (0 : ℝ) ≤ (deltaLo : ℝ) := by norm_num [deltaLo]
  have hau : (0 : ℝ) ≤ (sixHi : ℝ) := by norm_num [sixHi]
  have hbu : (0 : ℝ) ≤ (qHi : ℝ) := by norm_num [qHi]
  have hlow : (sixLo : ℝ) * (qLo : ℝ) * (deltaLo : ℝ) ≤
      Real.exp (-6) * Real.exp (-(q40 : ℝ)) *
        Real.exp (-(2 * Real.pi - 6 - (q40 : ℝ))) := by
    exact mul_le_mul (mul_le_mul six_bounds.1 q_bounds.1 hb0
      (Real.exp_pos (-6)).le) delta_bounds.1 hc0
      (mul_nonneg (Real.exp_pos (-6)).le (Real.exp_pos _).le)
  have hupp : Real.exp (-6) * Real.exp (-(q40 : ℝ)) *
      Real.exp (-(2 * Real.pi - 6 - (q40 : ℝ))) ≤
        (sixHi : ℝ) * (qHi : ℝ) * (deltaHi : ℝ) := by
    exact mul_le_mul (mul_le_mul six_bounds.2 q_bounds.2 (Real.exp_pos _).le hau)
      delta_bounds.2 (Real.exp_pos _).le (mul_nonneg hau hbu)
  have hid : Real.exp (-6) * Real.exp (-(q40 : ℝ)) *
      Real.exp (-(2 * Real.pi - 6 - (q40 : ℝ))) = Real.exp (-(2 * Real.pi)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hid] at hlow hupp
  have hl : (expNegTwoPiLower250 : ℝ) ≤ (sixLo : ℝ) * (qLo : ℝ) * (deltaLo : ℝ) := by
    exact_mod_cast final_arithmetic.1
  have hu : (sixHi : ℝ) * (qHi : ℝ) * (deltaHi : ℝ) ≤ (expNegTwoPiUpper250 : ℝ) := by
    exact_mod_cast final_arithmetic.2
  exact ⟨hl.trans hlow, hupp.trans hu⟩

/-- Original normalization input, rounded outward in units of 10^-250. -/
def sqrt2Lower250 : ℚ := 14142135623730950488016887242096980785696718753769480731766797379907324784621070388503875343276415727350138462309122970249248360558507372126441214970999358314132226659275055927557999505011527820605714701095599716059702745345968620147285174186408891986 / (10 : ℚ) ^ 250
def sqrt2Upper250 : ℚ := 14142135623730950488016887242096980785696718753769480731766797379907324784621070388503875343276415727350138462309122970249248360558507372126441214970999358314132226659275055927557999505011527820605714701095599716059702745345968620147285174186408891987 / (10 : ℚ) ^ 250

set_option exponentiation.threshold 1024 in
/-- Integer squares certify the sqrt(2) box used in N0 squared. -/
theorem sqrt_two_square_comparisons :
    0 ≤ sqrt2Lower250 ∧ 0 ≤ sqrt2Upper250 ∧
      sqrt2Lower250 ^ 2 ≤ 2 ∧ 2 ≤ sqrt2Upper250 ^ 2 := by
  norm_num [sqrt2Lower250, sqrt2Upper250]

theorem sqrt_two_250_bounds :
    (sqrt2Lower250 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (sqrt2Upper250 : ℝ) := by
  have hl : (sqrt2Lower250 : ℝ) ^ 2 ≤ 2 := by
    exact_mod_cast sqrt_two_square_comparisons.2.2.1
  have hu : (2 : ℝ) ≤ (sqrt2Upper250 : ℝ) ^ 2 := by
    exact_mod_cast sqrt_two_square_comparisons.2.2.2
  have hpos : (0 : ℝ) ≤ (sqrt2Upper250 : ℝ) := by
    exact_mod_cast sqrt_two_square_comparisons.2.1
  exact ⟨Real.le_sqrt_of_sq_le hl, Real.sqrt_le_iff.mpr ⟨hpos, hu⟩⟩

end RHFiniteGaussian.AnalyticEndpoints

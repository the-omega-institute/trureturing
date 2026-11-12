/- GID: D5/S3/Combinatorics/SpectralGraph/PairTailCutoffComparison
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairTailCutoffComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact floor-square versus old large-tail cutoff, with actual graph consumer. -/
import D5.S3.Combinatorics.SpectralGraph.PairTailCandidates

/-! Sources: four-prime-large-tail and four-prime-tail-reduction,
PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02. The earlier
large-tail conclusion is reused through the stronger full quadratic
cutoff. This does not replace the separate source statement identifying
the ordered second restricted eigenvalue, or the original reported
control/determinant evidence. No tail scan or integrality sufficiency
is asserted. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.PairTailCutoffComparison
open PairTailCandidates IdealIntersectionSupport IdealIntersectionObstructions
open PairedIdealIntersectionLift

def oldCutoff (a b : ℤ) : ℤ :=
  let M := (a+1)*(b+1)
  24*(M+a)^3*(3*M+a)

/-- The complete original factor-greater-than-128 improvement, with
floor division retained and no ordering assumption between a and b. -/
theorem cutoff_comparison (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    128*cutoff a b < oldCutoff a b := by
  let d := (a+1)*b
  let M := (a+1)*(b+1)
  let U := d^2/4
  let B := U+a*(d-1)+a^2*b
  have hd : 0 < d := by dsimp [d]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hdM : d < M := by dsimp [d,M]; nlinarith
  have haM : a < M := by dsimp [M]; nlinarith
  have hsq : 0 ≤ d^2 := sq_nonneg d
  have hU0 : 0 ≤ U := by dsimp [U]; omega
  have hU4 : 4*U ≤ d^2 := by dsimp [U]; omega
  have hdm : 0 ≤ d-1 := by omega
  have hB0 : 0 ≤ B := add_nonneg (add_nonneg hU0 (mul_nonneg ha.le hdm))
    (mul_nonneg (sq_nonneg a) hb.le)
  have hab : a^2*b ≤ a*d := by dsimp [d]; nlinarith
  have hB4 : 4*B ≤ d^2+8*a*d := by dsimp [B]; nlinarith
  have hmul := mul_le_mul hU4 hB4 (by positivity : 0 ≤ 4*B) hsq
  have hQ : 16*cutoff a b ≤ d^4+8*a*d^3 := by
    change 16*(U*B) ≤ _
    nlinarith [hmul]
  have hd4 : d^4 < M^4 := by exact pow_lt_pow_left₀ hdM (by omega) (by norm_num)
  have hd3 : d^3 < M^3 := by exact pow_lt_pow_left₀ hdM (by omega) (by norm_num)
  have hmix : a*d^3 < M^4 := by
    have hprod := mul_lt_mul_of_pos_right haM (by positivity : 0 < d^3)
    have hprod' := mul_lt_mul_of_pos_left hd3 hM
    nlinarith
  have hQ8 : 128*cutoff a b < 72*M^4 := by nlinarith
  have hpow : M^3 < (M+a)^3 := by
    exact pow_lt_pow_left₀ (by omega : M < M+a) (by omega) (by norm_num)
  have hR : 72*M^4 < oldCutoff a b := by
    have hm1 := mul_lt_mul_of_pos_right hpow (by positivity : 0 < 3*M)
    have hm2 := mul_lt_mul_of_pos_left (by omega : 3*M < 3*M+a)
      (by positivity : 0 < (M+a)^3)
    change 72*M^4 < 24*(M+a)^3*(3*M+a)
    nlinarith
  exact hQ8.trans hR

/-- The two full source numerical cutoffs, with exact floor arithmetic. -/
theorem cutoff_five : cutoff 5 5=111375 ∧ oldCutoff 5 5=186913752 := by
  norm_num [cutoff,oldCutoff]

/-- The earlier uniform large-tail obstruction follows on every actual
graph from the stronger cutoff, without any ordering of a and b. -/
theorem actual_large_tail (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hc : oldCutoff (a : ℤ) b < c) :
    ¬ActualLaplacianIntegral (modulus p (pairExponents a b c)) := by
  have hcut := cutoff_comparison (a : ℤ) b (by positivity) (by positivity)
  have hR0 : 0 < oldCutoff (a : ℤ) b := by unfold oldCutoff; positivity
  have hc0 : 0 < c := by exact_mod_cast (hR0.trans hc)
  intro H
  have hQ := actual_le_cutoff p hp hinj a b c ha hb hc0 H
  have hQ0 : 0 ≤ cutoff (a : ℤ) b := le_trans (by positivity : (0 : ℤ) ≤ c) hQ
  omega

end D5.S3.Combinatorics.SpectralGraph.PairTailCutoffComparison

/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4TailCharge
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete infinite tail charge convergence and an explicit quadratic energy bound. -/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Complete infinite tail charge convergence and an explicit quadratic energy bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FiniteGaussianCap4
open Filter
open scoped BigOperators Topology

def ratio (x : ℝ) : ℝ :=
  ((x + 9 / 4) * (x + 1 / 2)) / ((x + 11 / 4) * (x + 1))

/-- Squared even-mode central Mellin weights, normalized by w_0=1. -/
def weight : ℕ → ℝ
  | 0 => 1
  | n + 1 => weight n * ratio n

/-- Exactly the candidate's complete-complement energy, before its charge. -/
def tailH (x : ℝ) : ℝ := ((2 * x + 9 / 4) ^ 2 - 440) / 10 - 3 / 4

private def tailFactor (x : ℝ) : ℝ := (1 + (x + 9 / 4) / 2) / tailH x
private def potential (k : ℕ) : ℝ := weight k * tailFactor k

/-- The SAME rational Sbar and rho as the designated certificate. -/
def sbar : ℝ := 1028725771676171625 / 157438844598004744192
def rho : ℝ := 157438844598004744192 / 1028725771676171625

private theorem ratio_pos (x : ℝ) (hx : 0 ≤ x) : 0 < ratio x := by
  unfold ratio
  positivity

private theorem weight_pos (k : ℕ) : 0 < weight k := by
  induction k with
  | zero => norm_num [weight]
  | succ k ih =>
      change 0 < weight k * ratio k
      exact mul_pos ih (ratio_pos k (Nat.cast_nonneg k))

private theorem tailH_pos (x : ℝ) (hx : 16 ≤ x) : 0 < tailH x := by
  have hbase : (137 / 4 : ℝ) ≤ 2 * x + 9 / 4 := by linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 137 / 4) hbase 2
  unfold tailH
  nlinarith

/- The shifted cubic is strictly positive for x>=16. This identity replaces
both asymptotic weight estimates and the decreasing-integral comparison. -/
private theorem scalar_telescoping (x : ℝ) (hx : 16 ≤ x) :
    1 / tailH x + ratio x * tailFactor (x + 1) ≤ tailFactor x := by
  have hH := tailH_pos x hx
  have hH1 := tailH_pos (x + 1) (by linarith)
  have h0 : 0 < x + 11 / 4 := by linarith
  have h1 : 0 < x + 1 := by linarith
  have h4 : 0 < 4 * x + 11 := by linarith
  have hdelta : 0 ≤ x - 16 := by linarith
  have hid :
      tailFactor x - 1 / tailH x - ratio x * tailFactor (x + 1) =
        (13056 * (x - 16) ^ 3 + 1145920 * (x - 16) ^ 2 +
          27734596 * (x - 16) + 203852865) /
          (2560 * (x + 1) * (4 * x + 11) * tailH x * tailH (x + 1)) := by
    unfold tailFactor ratio
    field_simp [hH.ne', hH1.ne', h0.ne', h1.ne', h4.ne']
    <;> dsimp [tailH]
    <;> ring
  have hnonneg : 0 ≤
      tailFactor x - 1 / tailH x - ratio x * tailFactor (x + 1) := by
    rw [hid]
    have hx0 : 0 ≤ x := by linarith
    positivity
  linarith

private theorem potential_nonneg (k : ℕ) (hk : 16 ≤ k) : 0 ≤ potential k := by
  have hx : (16 : ℝ) ≤ k := by exact_mod_cast hk
  have hH := tailH_pos k hx
  have hk0 := Nat.cast_nonneg (α := ℝ) k
  unfold potential tailFactor
  exact mul_nonneg (weight_pos k).le (by positivity)

private theorem potential_step (k : ℕ) (hk : 16 ≤ k) :
    weight k / tailH k + potential (k + 1) ≤ potential k := by
  have hx : (16 : ℝ) ≤ k := by exact_mod_cast hk
  have h := mul_le_mul_of_nonneg_left (scalar_telescoping k hx) (weight_pos k).le
  change weight k / tailH k +
    (weight k * ratio k) * tailFactor ((k + 1 : ℕ) : ℝ) ≤
      weight k * tailFactor k
  rw [Nat.cast_add, Nat.cast_one]
  calc
    _ = weight k * (1 / tailH k + ratio k * tailFactor ((k : ℝ) + 1)) := by ring
    _ ≤ _ := h

private theorem potential_sixteen : potential 16 = sbar := by
  norm_num [potential, tailFactor, tailH, weight, ratio, sbar]

/-- The uncancelled endpoint is retained for every finite prefix. -/
private theorem prefix_with_remainder (m : ℕ) :
    (∑ n ∈ Finset.range m, weight (16 + n) / tailH (16 + n : ℕ)) +
      potential (16 + m) ≤ sbar := by
  induction m with
  | zero => simp [potential_sixteen]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hs := potential_step (16 + m) (by omega)
      have he : 16 + (m + 1) = (16 + m) + 1 := by omega
      rw [he]
      linarith

private def reciprocalTail (n : ℕ) : ℝ :=
  weight (16 + n) / tailH (16 + n : ℕ)

private theorem reciprocalTail_nonneg (n : ℕ) : 0 ≤ reciprocalTail n := by
  have hn : (16 : ℝ) ≤ (16 + n : ℕ) := by
    exact_mod_cast (show 16 ≤ 16 + n by omega)
  exact div_nonneg (weight_pos (16 + n)).le (tailH_pos _ hn).le

private theorem reciprocalTail_prefix_le (m : ℕ) :
    (∑ n ∈ Finset.range m, reciprocalTail n) ≤ sbar := by
  have h := prefix_with_remainder m
  have hp := potential_nonneg (16 + m) (by omega)
  change (∑ n ∈ Finset.range m, weight (16 + n) / tailH (16 + n : ℕ)) ≤ sbar
  linarith

/-- A real infinite series theorem: every term k>=16 is included. -/
theorem complete_tail_reciprocal_bound :
    Summable (fun n : ℕ => weight (16 + n) / tailH (16 + n : ℕ)) ∧
      (∑' n : ℕ, weight (16 + n) / tailH (16 + n : ℕ)) ≤ sbar := by
  exact ⟨summable_of_sum_range_le reciprocalTail_nonneg reciprocalTail_prefix_le,
    Real.tsum_le_of_sum_range_le reciprocalTail_nonneg reciprocalTail_prefix_le⟩

private def chargeTerm (u : ℕ → ℝ) (n : ℕ) : ℝ := weight (16 + n) * u n
private def energyTerm (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  tailH (16 + n : ℕ) * weight (16 + n) * u n ^ 2

private theorem energyTerm_nonneg (u : ℕ → ℝ) (n : ℕ) : 0 ≤ energyTerm u n := by
  have hn : (16 : ℝ) ≤ (16 + n : ℕ) := by
    exact_mod_cast (show 16 ≤ 16 + n by omega)
  exact mul_nonneg
    (mul_nonneg (tailH_pos _ hn).le (weight_pos (16 + n)).le) (sq_nonneg _)

private theorem chargeTerm_sq (u : ℕ → ℝ) (n : ℕ) :
    chargeTerm u n ^ 2 = reciprocalTail n * energyTerm u n := by
  have hn : (16 : ℝ) ≤ (16 + n : ℕ) := by
    exact_mod_cast (show 16 ≤ 16 + n by omega)
  have hH := tailH_pos _ hn
  unfold chargeTerm reciprocalTail energyTerm
  field_simp [hH.ne']
  <;> ring

/- The newly proved bound is consumed here by the mass-tail estimate. The only
hypothesis is a genuine summable energy series. Charge convergence is proved,
not assumed. No physical expansion or mass-zero theorem is hidden in it. -/
theorem complete_tail_charge_bound (u : ℕ → ℝ)
    (hE : Summable (fun n : ℕ =>
      tailH (16 + n : ℕ) * weight (16 + n) * u n ^ 2)) :
    Summable (fun n : ℕ => weight (16 + n) * u n) ∧
      rho * (∑' n : ℕ, weight (16 + n) * u n) ^ 2 ≤
        ∑' n : ℕ, tailH (16 + n : ℕ) * weight (16 + n) * u n ^ 2 := by
  have hq : Summable reciprocalTail := complete_tail_reciprocal_bound.1
  have he : Summable (energyTerm u) := hE
  have hc : Summable (chargeTerm u) := by
    apply (hq.add he).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs]
    have hsq : |chargeTerm u n| ^ 2 ≤ reciprocalTail n * energyTerm u n := by
      rw [sq_abs, chargeTerm_sq]
    have h := two_mul_le_add_of_sq_le_mul
      (reciprocalTail_nonneg n) (energyTerm_nonneg u n) hsq
    have hn := add_nonneg (reciprocalTail_nonneg n) (energyTerm_nonneg u n)
    linarith
  have hfinite (m : ℕ) :
      (∑ n ∈ Finset.range m, chargeTerm u n) ^ 2 ≤
        sbar * ∑ n ∈ Finset.range m, energyTerm u n := by
    calc
      _ ≤ (∑ n ∈ Finset.range m, reciprocalTail n) *
          ∑ n ∈ Finset.range m, energyTerm u n := by
        exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range m)
          (fun n _ => reciprocalTail_nonneg n) (fun n _ => energyTerm_nonneg u n)
          (fun n _ => (chargeTerm_sq u n).le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (reciprocalTail_prefix_le m)
        (Finset.sum_nonneg (fun n _ => energyTerm_nonneg u n))
  have hfull : (∑' n : ℕ, chargeTerm u n) ^ 2 ≤
      sbar * ∑' n : ℕ, energyTerm u n :=
    le_of_tendsto_of_tendsto' (hc.hasSum.tendsto_sum_nat.pow 2)
      (tendsto_const_nhds.mul he.hasSum.tendsto_sum_nat) hfinite
  have hr : 0 ≤ rho := by norm_num [rho]
  have hrs : rho * sbar = 1 := by norm_num [rho, sbar]
  refine ⟨hc, ?_⟩
  change rho * (∑' n : ℕ, chargeTerm u n) ^ 2 ≤ ∑' n : ℕ, energyTerm u n
  calc
    _ ≤ rho * (sbar * ∑' n : ℕ, energyTerm u n) :=
      mul_le_mul_of_nonneg_left hfull hr
    _ = _ := by rw [← mul_assoc, hrs, one_mul]

end FiniteGaussianCap4

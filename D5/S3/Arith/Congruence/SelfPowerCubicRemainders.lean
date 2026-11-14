/- GID: D5/S3/Arith/Congruence/SelfPowerCubicRemainders
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/SelfPowerCubicRemainders
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Six cubic branches for the least remainder of the exact self-power quotient. -/
import D5.S3.Arith.Congruence.SelfPowerQuotient

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators
namespace D5.S3.Arith.Congruence.SelfPowerCubicRemainders
open SelfPowerQuotient

/-- Twice the six prescribed remainders, with integer polynomial arithmetic. -/
def twiceR (n : ℕ) : ℤ :=
  let z : ℤ := n
  match n % 6 with
  | 0 => z^3 + z^2 - z
  | 1 => z^3 - 2*z^2 + 2*z - 1
  | 2 => z^3 + 3*z^2 - z - 2
  | 3 => z^3 - 2*z^2 + 1
  | 4 => z^3 + z^2 + z - 2
  | _ => z^3 - 1

private def geom (j : ℕ) (y : ℤ) : ℤ := ∑ i ∈ Finset.range j, y^i

private theorem geom_add (j k : ℕ) (y : ℤ) :
    geom (j+k) y = geom j y + y^j * geom k y := by
  simp [geom, Finset.sum_range_add, pow_add, Finset.mul_sum]

private theorem tail_add (j k : ℕ) (y : ℤ) :
    tail (j+k) y = tail j y + y^j * tail k y + (k : ℤ) * geom j y := by
  induction k with
  | zero => simp [tail]
  | succ k ih =>
    have hr (m : ℕ) : tail (m+1) y = tail m y + geom m y := by
      simp [tail, geom, Finset.sum_range_succ]
    rw [Nat.add_succ, hr, ih, hr, geom_add]
    push_cast
    ring

private theorem block (m : ℕ) (y : ℤ) :
    (y^3+1) ∣ tail (m+6) y - tail m y - 3*(1+y+y^2) := by
  rw [Nat.add_comm m 6, tail_add]
  refine ⟨tail 3 y + (y^3-1)*tail m y + (m : ℤ)*(1+y+y^2), ?_⟩
  norm_num [tail, geom, Finset.sum_range_succ]
  ring

/-- Uniform six-block descent of the integer weighted geometric sum. -/
theorem tail_blocks (h t : ℕ) (y : ℤ) :
    (y^3+1) ∣ tail (6*h+t) y - (3*(h : ℤ)*(1+y+y^2)+tail t y) := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hb := block (6*h+t) y
    have hi := dvd_add hb ih
    convert hi using 1 <;> push_cast <;> ring_nf

/-- Integral forms of the source's six polynomials at `n=6h+c`. -/
private def representative (h c : ℕ) : ℤ :=
  let z : ℤ := h
  match c with
  | 0 => 108*z^3 + 18*z^2 - 3*z
  | 1 => 108*z^3 + 18*z^2 + 3*z
  | 2 => 108*z^3 + 162*z^2 + 69*z + 8
  | 3 => 108*z^3 + 126*z^2 + 45*z + 5
  | 4 => 108*z^3 + 234*z^2 + 171*z + 41
  | _ => 108*z^3 + 270*z^2 + 225*z + 62

private theorem representative_congruence (h c : ℕ) (hc : c < 6) :
    ((6*h+c : ℕ) : ℤ)^3-1 ∣ a (6*h+c) - representative h c := by
  have hp : (-1 : ℤ)^(6*h+c) = (-1 : ℤ)^c := by
    rw [pow_add, pow_mul]
    norm_num
  have hi : 6*h+(c+1) = (6*h+c)+1 := by omega
  obtain ⟨w, hw⟩ := tail_blocks h (c+1) (-((6*h+c : ℕ) : ℤ))
  rw [hi] at hw
  rw [quotient_tail, hp]
  interval_cases c
  · refine ⟨w-1, ?_⟩
    norm_num [representative, tail, Finset.sum_range_succ] at hw ⊢
    linear_combination -hw
  · refine ⟨-w, ?_⟩
    norm_num [representative, tail, Finset.sum_range_succ] at hw ⊢
    linear_combination hw
  · refine ⟨w-1, ?_⟩
    norm_num [representative, tail, Finset.sum_range_succ] at hw ⊢
    linear_combination -hw
  · refine ⟨-w, ?_⟩
    norm_num [representative, tail, Finset.sum_range_succ] at hw ⊢
    linear_combination hw
  · refine ⟨w, ?_⟩
    norm_num [representative, tail, Finset.sum_range_succ] at hw ⊢
    linear_combination -hw
  · refine ⟨-w+6*(h : ℤ)+3, ?_⟩
    norm_num [representative, tail, Finset.sum_range_succ] at hw ⊢
    linear_combination hw

private theorem representative_bounds (h c : ℕ) (hc : c < 6) (hn : 2 < 6*h+c) :
    0 ≤ representative h c ∧ representative h c < ((6*h+c : ℕ) : ℤ)^3-1 := by
  have h0 : (0 : ℤ) ≤ h := by positivity
  have hsq := sq_nonneg (h : ℤ)
  have hcube := mul_nonneg hsq h0
  interval_cases c <;> norm_num [representative] at hn ⊢
  all_goals push_cast
  all_goals try (constructor <;> nlinarith)

/-- The complete XIV claim, including exact quotient integrality. -/
def claim : Prop := ∀ n : ℕ, 2 < n →
  ((n : ℤ)+1)^2 * a n = numerator n ∧
  2 * (a n % ((n : ℤ)^3-1)) = twiceR n

/-- All six least-nonnegative remainder branches hold on the printed domain. -/
theorem result : claim := by
  intro n hn
  refine ⟨exact_quotient n, ?_⟩
  let h := n / 6
  let c := n % 6
  have hc : c < 6 := Nat.mod_lt n (by norm_num)
  have he : n = 6*h+c := by dsimp [h,c]; omega
  have hb := representative_bounds h c hc (by omega)
  have hd := representative_congruence h c hc
  have hm : a n % ((n : ℤ)^3-1) = representative h c := by
    have hmod : a (6*h+c) % (((6*h+c : ℕ) : ℤ)^3-1) =
        representative h c % (((6*h+c : ℕ) : ℤ)^3-1) := by
      apply Int.modEq_iff_dvd.mpr
      simpa only [neg_sub] using dvd_neg.mpr hd
    rw [Int.emod_eq_of_lt hb.1 hb.2] at hmod
    simpa only [← he] using hmod
  rw [hm]
  have hres : n % 6 = c := rfl
  unfold twiceR
  rw [hres, he]
  interval_cases c <;> norm_num [representative] <;> push_cast <;> ring

#print axioms tail_blocks
#print axioms result
end D5.S3.Arith.Congruence.SelfPowerCubicRemainders

/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Private chain, schedule and charge preparation for the ordered-cone joint lift. -/
import D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
private theorem list_map_cons_sum {α : Type*} (f : α → ℤ) (x : α) (l : List α) :
    ((x :: l).map f).sum = f x + (l.map f).sum := by
  rfl

private theorem int_half_two_mul (p : ℤ) : (2 * p) / 2 = p := by
  exact Int.mul_ediv_cancel_left p (by norm_num)

private theorem fresh_prefix_sum_bridge {α : Type*} (f : α → ℤ)
    (P Q : List α) (fresh : α) (base freshVal A : ℤ)
    (hP : (P.map f).sum = base) (hfresh : f fresh = freshVal) :
    (P.map f).sum - A + ((fresh :: Q).map f).sum =
      base - A + freshVal + (Q.map f).sum := by
  rw [hP, list_map_cons_sum, hfresh]
  exact (add_assoc _ _ _).symm

private theorem fresh_prefix_bounds {α : Type*} (f : α → ℤ)
    (P Q : List α) (fresh : α) (base freshVal A C : ℤ)
    (hP : (P.map f).sum = base) (hfresh : f fresh = freshVal)
    (hbound : 0 ≤ base - A + freshVal + (Q.map f).sum ∧
      base - A + freshVal + (Q.map f).sum ≤ C) :
    0 ≤ (P.map f).sum - A + ((fresh :: Q).map f).sum ∧
      (P.map f).sum - A + ((fresh :: Q).map f).sum ≤ C := by
  rw [fresh_prefix_sum_bridge f P Q fresh base freshVal A hP hfresh]
  exact hbound

private theorem fresh_prefix_bounds_sub {α : Type*} (f : α → ℤ)
    (P Q : List α) (fresh : α) (base freshVal A B C : ℤ)
    (hP : (P.map f).sum = base) (hfresh : f fresh = freshVal)
    (hbound : 0 ≤ base - A + freshVal + (Q.map f).sum - B ∧
      base - A + freshVal + (Q.map f).sum - B ≤ C) :
    0 ≤ (P.map f).sum - A + ((fresh :: Q).map f).sum - B ∧
      (P.map f).sum - A + ((fresh :: Q).map f).sum - B ≤ C := by
  have hEq := fresh_prefix_sum_bridge f P Q fresh base freshVal A hP hfresh
  rw [hEq]
  exact hbound

private theorem add_bound_of_eq {D K X C : ℤ} (hD : D ≤ X) (hX : X + K = C) :
    D + K ≤ C := by omega

private theorem ordered_schedule {α : Type*} (f : α → ℤ) (labels P Q T : List α)
    (alpha beta gamma : α) (Ha Hb Hg C : ℤ)
    (hperm : (P ++ alpha :: Q ++ beta :: T ++ [gamma]).Perm labels)
    (halpha : f alpha = -Ha) (hbeta : f beta = -Hb) (hgamma : f gamma = -Hg)
    (hHa : 0 ≤ Ha) (hHb : 0 ≤ Hb) (hHg : 0 ≤ Hg ∧ Hg ≤ C)
    (hPpos : ∀ i ∈ P, 0 ≤ f i) (hQpos : ∀ i ∈ Q, 0 ≤ f i)
    (hTpos : ∀ i ∈ T, 0 ≤ f i)
    (hPmass : 0 ≤ (P.map f).sum ∧ (P.map f).sum ≤ C)
    (hAlpha : 0 ≤ (P.map f).sum - Ha ∧ (P.map f).sum - Ha ≤ C)
    (hQend : 0 ≤ (P.map f).sum - Ha + (Q.map f).sum ∧
      (P.map f).sum - Ha + (Q.map f).sum ≤ C)
    (hBeta : 0 ≤ (P.map f).sum - Ha + (Q.map f).sum - Hb ∧
      (P.map f).sum - Ha + (Q.map f).sum - Hb ≤ C)
    (htotal : (labels.map f).sum = 0) :
    InStrip f C 0 (P ++ alpha :: Q ++ beta :: T ++ [gamma]) := by
  exact ThreeNegativeEqualOuterSourceBridge.physical_schedule f labels P Q T
    alpha beta gamma Ha Hb Hg C hperm halpha hbeta hgamma hHa hHb hHg
    hPpos hQpos hTpos ⟨by omega, hPmass.2⟩ ⟨by omega, hQend.2⟩ htotal

private theorem floor_tail_bound (x d rem v : ℤ)
    (h : x = rem + d * v) (hrem : rem < d) : x - d ≤ d * v := by
  omega

private theorem mul_le_mul_left_int {a b c : ℤ} (h : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  exact mul_le_mul_of_nonneg_left h hc

private theorem beta_block_bound (r p t : ℤ) (hrp : r + 1 ≤ p) (ht0 : 0 ≤ t)
    (hp1 : 1 ≤ p) : 1 + t + t * r ≤ p * (t + 1) := by
  have hmul : t * (r + 1) ≤ t * p :=
    mul_le_mul_left_int hrp ht0
  calc
    1 + t + t * r = 1 + t * (r + 1) := by ring
    _ ≤ 1 + t * p := by omega
    _ = 1 + p * t := by rw [mul_comm t p]
    _ ≤ p + p * t := by omega
    _ = p * (t + 1) := by ring

private theorem one_le_of_add_one_le {r p : ℤ} (hr : 0 ≤ r) (h : r + 1 ≤ p) :
    1 ≤ p := by
  omega

private theorem floor_tail_bound_mul (L u B rem v : ℤ)
    (h : L - u = rem + B * v) (hrem : rem < B) :
    L - u - B ≤ B * v := by
  have h' := floor_tail_bound (x := L - u) (d := B) (rem := rem) (v := v) h hrem
  exact h'

private theorem core_from_floor (L u B rem v p r s t : ℤ)
    (h : L - u = rem + B * v) (hrem : rem < B)
    (hLB : p * (t + 1) - r * (s + 1) ≤ L - u - B) :
    0 ≤ v * B + r * (s + 1) - p * (t + 1) := by
  have hfloor := floor_tail_bound_mul L u B rem v h hrem
  linarith only [hLB, hfloor]

private theorem new_margin_bounds (q s r t N : ℤ) (hq : 1 ≤ q)
    (hsr : 0 ≤ s - r - 1) (hr : 4 ≤ r) (hs : 4 ≤ s)
    (htq : t = q * s) (hN : N = r * s * t - 1) :
    0 ≤ 2 * (1 + q * (s - r - 1)) - 1 ∧
      2 * (1 + q * (s - r - 1)) - 1 ≤ N := by
  have hq0 : 0 ≤ q := by omega
  have hqs0 : 0 ≤ q * s := mul_nonneg hq0 (by omega)
  have h2 : 2 ≤ r * s := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right h2 hqs0
  rw [htq] at hN
  constructor
  · nlinarith
  · nlinarith [hmul]

private theorem cone_length_old (a b c : ℕ) (ha : 2 ≤ a) (hab : a < b)
    (hbc : b ≤ c) : 3 ≤ a + b + c := by
  omega

private theorem cone_length_new (a b c : ℕ) (ha : 2 ≤ a) (hab : a < b)
    (hbc : b ≤ c) : 3 ≤ a + b + c + 1 := by
  omega

private theorem split_sum_zero {α : Type*} (f : α → ℤ)
    (P Q T : List α) (alpha beta gamma : α)
    (x y Ha Hb Hg : ℤ)
    (hP : (P.map f).sum = x) (hT : (T.map f).sum = y)
    (hα : f alpha = -Ha) (hβ : f beta = -Hb) (hγ : f gamma = -Hg)
    (hzero : ((P ++ alpha :: Q ++ beta :: T ++ [gamma]).map f).sum = 0) :
    x + (-Ha + (Q.map f).sum) + (-Hb + y) + -Hg = 0 := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, add_zero, hP, hT, hα, hβ, hγ] at hzero
  linarith only [hzero]

private theorem old_beta_bounds (x Ha qsum Hb y Hg C : ℤ)
    (hsum : x + (-Ha + qsum) + (-Hb + y) + -Hg = 0)
    (hdelta0 : 0 ≤ Hg - y) (hdeltaC : Hg - y ≤ C) :
    0 ≤ x - Ha + qsum - Hb ∧ x - Ha + qsum - Hb ≤ C := by
  have hrel : x - Ha + qsum - Hb = Hg - y := by
    linarith only [hsum]
  rw [hrel]
  exact ⟨hdelta0, hdeltaC⟩

private theorem nat_cast_nonneg_mul (u : ℤ) (m : ℕ) (hu : 0 ≤ u) :
    0 ≤ u * (m : ℤ) := by
  have hm : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (Nat.zero_le m)
  exact mul_nonneg hu hm

private theorem doubled_source_zero_cast (n t : ℕ) (u : ℤ) (hn : 3 ≤ n)
    (ht : (t : ℤ) = u) :
    ((List.range n).map
      (fun i => centered (modulus n) ((2 : ℤ) ^ i * (2 * u)))).sum = 0 := by
  have hz := ThreeNegativeEqualOuterSourceBridge.source_zero n (2 * t) hn
  have htu : ((2 * t : ℕ) : ℤ) = (2 : ℤ) * u := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ht]
  rw [htu] at hz
  exact hz

end D5.S3.Combinatorics.Circle.ThreeNegativeOrderedConeJointLift

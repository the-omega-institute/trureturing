/- GID: D5/S3/Observer/DynamicProgramming/WeightedSoftDescent
   generality: G
   mirror-B: D5/B/S3/Observer/DynamicProgramming/WeightedSoftDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted fiber comparison bounds both soft recurrences at every finite horizon. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-!
# Weighted soft dynamic-programming descent

The same stochastic microscopic kernel, real costs, quotient map and unnormalized
coarse weight matrix are used in the support, one-step and horizon estimates.
No nonempty state space or sign condition on costs is required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace D5.S3.Observer.DynamicProgramming.WeightedSoftDescent

def partition {I : Type*} [Fintype I] (a : I → ℝ) (τ : ℝ) (v : I → ℝ) : ℝ :=
  ∑ i, a i * Real.exp (-v i / τ)

def rowSoft {I : Type*} [Fintype I] (a : I → ℝ) (τ : ℝ) (v : I → ℝ) : ℝ :=
  -τ * Real.log (partition a τ v)

def soft {I : Type*} [Fintype I] (K : I → I → ℝ) (τ : ℝ) (v : I → ℝ) : I → ℝ :=
  fun i => rowSoft (K i) τ v

def micro {X : Type*} [Fintype X] (R c : X → X → ℝ) (τ : ℝ) (v : X → ℝ) : X → ℝ :=
  fun x => -τ * Real.log (∑ y, R x y * Real.exp (-(c x y + v y) / τ))

def weight {X : Type*} (R c : X → X → ℝ) (τ : ℝ) : X → X → ℝ :=
  fun x y => R x y * Real.exp (-c x y / τ)

def kernel {X Y : Type*} [Fintype X] (q : X → Y) (R c : X → X → ℝ) (τ : ℝ)
    (x : X) (j : Y) : ℝ := by
  classical
  exact ∑ y ∈ Finset.univ.filter (fun y => q y = j), weight R c τ x y

def microValue {X : Type*} [Fintype X] (R c : X → X → ℝ) (τ : ℝ)
    (terminal : X → ℝ) : ℕ → X → ℝ
  | 0 => terminal
  | n+1 => micro R c τ (microValue R c τ terminal n)

def coarseValue {Y : Type*} [Fintype Y] (K : Y → Y → ℝ) (τ : ℝ)
    (g : Y → ℝ) : ℕ → Y → ℝ
  | 0 => g
  | n+1 => soft K τ (coarseValue K τ g n)

theorem partition_pos {I : Type*} [Fintype I] (a : I → ℝ) (τ : ℝ) (v : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hp : ∃ i, 0 < a i) : 0 < partition a τ v := by
  classical
  obtain ⟨i, hi⟩ := hp
  exact (mul_pos hi (Real.exp_pos _)).trans_le
    (Finset.single_le_sum (fun j _ => mul_nonneg (ha j) (Real.exp_nonneg _))
      (Finset.mem_univ i))

theorem log_sandwich (τ δ A B : ℝ) (ht : 0 < τ) (ha : 0 < A) (hb : 0 < B)
    (hl : Real.exp (-δ / τ) * B ≤ A) (hu : A ≤ Real.exp (δ / τ) * B) :
    |(-τ * Real.log A) - (-τ * Real.log B)| ≤ δ := by
  have l := Real.log_le_log (mul_pos (Real.exp_pos _) hb) hl
  have u := Real.log_le_log ha hu
  rw [Real.log_mul (Real.exp_ne_zero _) hb.ne', Real.log_exp] at l u
  have hcancel : τ * (δ / τ) = δ := by field_simp [ht.ne']
  have hcancel' : τ * (-δ / τ) = -δ := by field_simp [ht.ne']
  have lm := mul_le_mul_of_nonneg_left l ht.le
  have um := mul_le_mul_of_nonneg_left u ht.le
  rw [mul_add, hcancel'] at lm
  rw [mul_add, hcancel] at um
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem partition_compare {I : Type*} [Fintype I]
    (a b : I → ℝ) (τ δ : ℝ) (v : I → ℝ)
    (h : ∀ i, Real.exp (-δ / τ) * b i ≤ a i ∧ a i ≤ Real.exp (δ / τ) * b i) :
    Real.exp (-δ / τ) * partition b τ v ≤ partition a τ v ∧
      partition a τ v ≤ Real.exp (δ / τ) * partition b τ v := by
  unfold partition
  simp only [Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro i _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (h i).1 (Real.exp_nonneg _)
  · apply Finset.sum_le_sum
    intro i _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (h i).2 (Real.exp_nonneg _)

theorem row_nonexp {I : Type*} [Fintype I] (a : I → ℝ) (τ A : ℝ)
    (ht : 0 < τ) (ha : ∀ i, 0 ≤ a i) (hp : ∃ i, 0 < a i)
    (v w : I → ℝ) (hvw : ∀ i, |v i - w i| ≤ A) :
    |rowSoft a τ v - rowSoft a τ w| ≤ A := by
  have he (i : I) : Real.exp (-A / τ) * Real.exp (-w i / τ) ≤ Real.exp (-v i / τ) ∧
      Real.exp (-v i / τ) ≤ Real.exp (A / τ) * Real.exp (-w i / τ) := by
    rw [← Real.exp_add, ← Real.exp_add]
    constructor <;> apply Real.exp_le_exp.mpr
    · rw [← add_div]; apply (div_le_div_iff_of_pos_right ht).2
      have := (abs_le.mp (hvw i)).2
      linarith
    · rw [← add_div]; apply (div_le_div_iff_of_pos_right ht).2
      have := (abs_le.mp (hvw i)).1
      linarith
  have hs : Real.exp (-A / τ) * partition a τ w ≤ partition a τ v ∧
      partition a τ v ≤ Real.exp (A / τ) * partition a τ w := by
    unfold partition
    simp only [Finset.mul_sum]
    constructor
    · apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_le_mul_of_nonneg_left (he i).1 (ha i)]
    · apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_le_mul_of_nonneg_left (he i).2 (ha i)]
  exact log_sandwich τ A _ _ ht (partition_pos a τ v ha hp)
    (partition_pos a τ w ha hp) hs.1 hs.2

theorem soft_nonexp {I : Type*} [Fintype I] (K : I → I → ℝ) (τ : ℝ)
    (ht : 0 < τ) (hn : ∀ i j, 0 ≤ K i j) (hp : ∀ i, ∃ j, 0 < K i j)
    (v w : I → ℝ) : ‖soft K τ v - soft K τ w‖ ≤ ‖v-w‖ := by
  rw [← dist_eq_norm]
  apply (dist_pi_le_iff (norm_nonneg (v-w))).2
  intro i
  simp only [soft, Real.dist_eq]
  apply row_nonexp (K i) τ ‖v-w‖ ht (hn i) (hp i) v w
  intro j
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (v-w) j

theorem micro_argument {X : Type*} [Fintype X] (R c : X → X → ℝ) (τ : ℝ)
    (v : X → ℝ) (x : X) :
    (∑ y, R x y * Real.exp (-(c x y + v y) / τ)) = partition (weight R c τ x) τ v := by
  unfold partition weight
  apply Finset.sum_congr rfl
  intro y _
  rw [show -(c x y + v y) / τ = -c x y / τ + -v y / τ by ring,
    Real.exp_add]
  ring

theorem micro_eq_soft {X : Type*} [Fintype X] (R c : X → X → ℝ) (τ : ℝ)
    (v : X → ℝ) : micro R c τ v = soft (weight R c τ) τ v := by
  funext x
  unfold micro soft rowSoft
  rw [micro_argument]

theorem weight_rows {X : Type*} [Fintype X] (R c : X → X → ℝ) (τ : ℝ)
    (hn : ∀ x y, 0 ≤ R x y) (hs : ∀ x, ∑ y, R x y = 1) :
    (∀ x y, 0 ≤ weight R c τ x y) ∧ (∀ x, ∃ y, 0 < weight R c τ x y) := by
  constructor
  · intro x y; exact mul_nonneg (hn x y) (Real.exp_nonneg _)
  · intro x
    have hr : ∃ y, 0 < R x y := by
      by_contra! h
      have hz : ∑ y, R x y = 0 := Finset.sum_eq_zero (fun y _ => le_antisymm (h y) (hn x y))
      linarith [hs x]
    obtain ⟨y, hy⟩ := hr
    exact ⟨y, mul_pos hy (Real.exp_pos _)⟩

theorem fiber_partition {X Y : Type*} [Fintype X] [Fintype Y]
    (q : X → Y) (R c : X → X → ℝ) (τ : ℝ) (v : Y → ℝ) (x : X) :
    partition (weight R c τ x) τ (v ∘ q) = partition (kernel q R c τ x) τ v := by
  classical
  unfold partition
  rw [← Finset.sum_fiberwise Finset.univ q
    (fun y => weight R c τ x y * Real.exp (-(v ∘ q) y / τ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [kernel, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [Function.comp_apply]
  rw [(Finset.mem_filter.mp hy).2]

theorem kernel_zero_iff {X Y : Type*} [Fintype X]
    (q : X → Y) (R c : X → X → ℝ) (τ : ℝ) (hn : ∀ x y, 0 ≤ R x y)
    (x : X) (j : Y) : kernel q R c τ x j = 0 ↔ ∀ y, q y = j → R x y = 0 := by
  classical
  constructor
  · intro hz y hy
    have hm : y ∈ Finset.univ.filter (fun z => q z = j) := by simp [hy]
    have hle := Finset.single_le_sum
      (s := Finset.univ.filter (fun z => q z = j))
      (f := weight R c τ x)
      (fun z _ => mul_nonneg (hn x z) (Real.exp_nonneg _)) hm
    change R x y * Real.exp (-c x y / τ) ≤ kernel q R c τ x j at hle
    rw [hz] at hle
    have he := Real.exp_pos (-c x y / τ)
    nlinarith [hn x y]
  · intro hz
    unfold kernel
    apply Finset.sum_eq_zero
    intro y hy
    simp [weight, hz y (Finset.mem_filter.mp hy).2]

theorem support_match {X Y : Type*} [Fintype X]
    (q : X → Y) (R c : X → X → ℝ) (τ δ : ℝ) (K : Y → Y → ℝ)
    (hn : ∀ x y, 0 ≤ R x y) (hk : ∀ i j, 0 ≤ K i j)
    (hcmp : ∀ x j, Real.exp (-δ / τ) * K (q x) j ≤ kernel q R c τ x j ∧
      kernel q R c τ x j ≤ Real.exp (δ / τ) * K (q x) j) :
    ∀ x j, kernel q R c τ x j = 0 ↔ K (q x) j = 0 := by
  intro x j
  have hkn : 0 ≤ kernel q R c τ x j :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (hn x y) (Real.exp_nonneg _))
  constructor
  · intro hz
    have h := (hcmp x j).1
    rw [hz] at h
    have hz' : Real.exp (-δ / τ) * K (q x) j = 0 :=
      le_antisymm h (mul_nonneg (Real.exp_nonneg _) (hk _ _))
    exact (mul_eq_zero.mp hz').resolve_left (Real.exp_ne_zero _)
  · intro hz
    have h := (hcmp x j).2
    rw [hz, mul_zero] at h
    exact le_antisymm h hkn

theorem one_step {X Y : Type*} [Fintype X] [Fintype Y]
    (q : X → Y) (R c : X → X → ℝ) (τ δ : ℝ) (K : Y → Y → ℝ)
    (ht : 0 < τ) (hn : ∀ x y, 0 ≤ R x y) (hs : ∀ x, ∑ y, R x y = 1)
    (hk : ∀ i j, 0 ≤ K i j) (hp : ∀ i, ∃ j, 0 < K i j)
    (hcmp : ∀ x j, Real.exp (-δ / τ) * K (q x) j ≤ kernel q R c τ x j ∧
      kernel q R c τ x j ≤ Real.exp (δ / τ) * K (q x) j)
    (v : Y → ℝ) (x : X) : |micro R c τ (v ∘ q) x - soft K τ v (q x)| ≤ δ := by
  have wr := weight_rows R c τ hn hs
  have hpos := partition_pos (weight R c τ x) τ (v ∘ q) (wr.1 x) (wr.2 x)
  rw [fiber_partition q R c τ v x] at hpos
  have hc := partition_compare (kernel q R c τ x) (K (q x)) τ δ v (hcmp x)
  rw [micro_eq_soft]
  change |(-τ * Real.log (partition (weight R c τ x) τ (v ∘ q))) -
    (-τ * Real.log (partition (K (q x)) τ v))| ≤ δ
  rw [fiber_partition q R c τ v x]
  exact log_sandwich τ δ _ _ ht hpos (partition_pos _ τ v (hk _) (hp _)) hc.1 hc.2

theorem value_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (q : X → Y) (R c : X → X → ℝ) (τ δ : ℝ) (K : Y → Y → ℝ)
    (ht : 0 < τ) (hd : 0 ≤ δ) (hn : ∀ x y, 0 ≤ R x y)
    (hs : ∀ x, ∑ y, R x y = 1) (hk : ∀ i j, 0 ≤ K i j)
    (hp : ∀ i, ∃ j, 0 < K i j)
    (hcmp : ∀ x j, Real.exp (-δ / τ) * K (q x) j ≤ kernel q R c τ x j ∧
      kernel q R c τ x j ≤ Real.exp (δ / τ) * K (q x) j)
    (g : Y → ℝ) (n : ℕ) :
    ‖microValue R c τ (g ∘ q) n - (coarseValue K τ g n ∘ q)‖ ≤ (n : ℝ) * δ := by
  have wr := weight_rows R c τ hn hs
  have point : ∀ n : ℕ, ∀ x,
      |microValue R c τ (g ∘ q) n x - coarseValue K τ g n (q x)| ≤ (n : ℝ) * δ := by
    intro n
    induction n with
    | zero => intro x; simp [microValue, coarseValue, Function.comp_apply]
    | succ n ih =>
      intro x
      have hnon := row_nonexp (weight R c τ x) τ ((n : ℝ) * δ) ht (wr.1 x) (wr.2 x)
        (microValue R c τ (g ∘ q) n) (coarseValue K τ g n ∘ q) ih
      have hstep := one_step q R c τ δ K ht hn hs hk hp hcmp (coarseValue K τ g n) x
      change |soft (weight R c τ) τ (microValue R c τ (g ∘ q) n) x -
        soft (weight R c τ) τ (coarseValue K τ g n ∘ q) x| ≤ (n : ℝ) * δ at hnon
      rw [← micro_eq_soft, ← micro_eq_soft] at hnon
      change |micro R c τ (microValue R c τ (g ∘ q) n) x -
        soft K τ (coarseValue K τ g n) (q x)| ≤ (↑(n+1) : ℝ) * δ
      calc
        _ ≤ |micro R c τ (microValue R c τ (g ∘ q) n) x -
              micro R c τ (coarseValue K τ g n ∘ q) x| +
            |micro R c τ (coarseValue K τ g n ∘ q) x -
              soft K τ (coarseValue K τ g n) (q x)| := abs_sub_le _ _ _
        _ ≤ (n : ℝ) * δ + δ := add_le_add hnon hstep
        _ = _ := by push_cast; ring
  rw [← dist_eq_norm]
  apply (dist_pi_le_iff (mul_nonneg (Nat.cast_nonneg _) hd)).2
  intro x
  simpa only [Real.dist_eq, Function.comp_apply] using point n x

theorem original194 {X Y : Type*} [Fintype X] [Fintype Y]
    (q : X → Y) (surjective : Function.Surjective q)
    (R c : X → X → ℝ) (τ δ : ℝ) (K : Y → Y → ℝ)
    (ht : 0 < τ) (hd : 0 ≤ δ) (hn : ∀ x y, 0 ≤ R x y)
    (hs : ∀ x, ∑ y, R x y = 1) (hk : ∀ i j, 0 ≤ K i j)
    (hp : ∀ i, ∃ j, 0 < K i j)
    (hcmp : ∀ x j, Real.exp (-δ / τ) * K (q x) j ≤ kernel q R c τ x j ∧
      kernel q R c τ x j ≤ Real.exp (δ / τ) * K (q x) j) :
    ∀ (g : Y → ℝ) (H t : ℕ), t ≤ H →
      ‖microValue R c τ (g ∘ q) (H-t) - (coarseValue K τ g (H-t) ∘ q)‖ ≤
        ((H-t : ℕ) : ℝ) * δ := by
  intro g H t _
  exact value_bound q R c τ δ K ht hd hn hs hk hp hcmp g (H-t)

theorem full_certificate {X Y : Type*} [Fintype X] [Fintype Y]
    (q : X → Y) (surjective : Function.Surjective q)
    (R c : X → X → ℝ) (τ δ : ℝ) (K : Y → Y → ℝ)
    (ht : 0 < τ) (hd : 0 ≤ δ) (hn : ∀ x y, 0 ≤ R x y)
    (hs : ∀ x, ∑ y, R x y = 1) (hk : ∀ i j, 0 ≤ K i j)
    (hp : ∀ i, ∃ j, 0 < K i j)
    (hcmp : ∀ x j, Real.exp (-δ / τ) * K (q x) j ≤ kernel q R c τ x j ∧
      kernel q R c τ x j ≤ Real.exp (δ / τ) * K (q x) j) :
    (∀ (v : X → ℝ) x, 0 < ∑ y, R x y * Real.exp (-(c x y + v y) / τ)) ∧
    (∀ (v : Y → ℝ) i, 0 < partition (K i) τ v) ∧
    (∀ x j, (kernel q R c τ x j = 0 ↔ K (q x) j = 0) ∧
      (kernel q R c τ x j = 0 ↔ ∀ y, q y = j → R x y = 0)) ∧
    (∀ v w : X → ℝ, ‖micro R c τ v - micro R c τ w‖ ≤ ‖v-w‖) ∧
    (∀ v w : Y → ℝ, ‖soft K τ v - soft K τ w‖ ≤ ‖v-w‖) ∧
    (∀ (v : Y → ℝ) x, |micro R c τ (v ∘ q) x - soft K τ v (q x)| ≤ δ) ∧
    (∀ (g : Y → ℝ) (H : ℕ),
      let V := fun t => microValue R c τ (g ∘ q) (H-t)
      let B := fun t => coarseValue K τ g (H-t)
      V H = g ∘ q ∧ B H = g ∧
      (∀ t, t < H → V t = micro R c τ (V (t+1)) ∧ B t = soft K τ (B (t+1))) ∧
      (∀ t, t ≤ H → ‖V t - (B t ∘ q)‖ ≤ ((H-t : ℕ) : ℝ) * δ)) := by
  have wr := weight_rows R c τ hn hs
  refine ⟨?_, ?_, ?_, ?_, soft_nonexp K τ ht hk hp, ?_, ?_⟩
  · intro v x
    rw [micro_argument]
    exact partition_pos _ τ v (wr.1 x) (wr.2 x)
  · intro v i
    exact partition_pos _ τ v (hk i) (hp i)
  · intro x j
    exact ⟨support_match q R c τ δ K hn hk hcmp x j, kernel_zero_iff q R c τ hn x j⟩
  · intro v w
    rw [micro_eq_soft, micro_eq_soft]
    exact soft_nonexp _ τ ht wr.1 wr.2 v w
  · exact one_step q R c τ δ K ht hn hs hk hp hcmp
  · intro g H
    dsimp only
    refine ⟨by simp [microValue], by simp [coarseValue], ?_, ?_⟩
    · intro t htH
      have he : H-t = (H-(t+1))+1 := by omega
      rw [he]
      exact ⟨rfl, rfl⟩
    · exact original194 q surjective R c τ δ K ht hd hn hs hk hp hcmp g H


#print axioms partition_pos
#print axioms log_sandwich
#print axioms partition_compare
#print axioms row_nonexp
#print axioms soft_nonexp
#print axioms micro_argument
#print axioms micro_eq_soft
#print axioms weight_rows
#print axioms fiber_partition
#print axioms kernel_zero_iff
#print axioms support_match
#print axioms one_step
#print axioms value_bound
#print axioms original194
#print axioms full_certificate

end D5.S3.Observer.DynamicProgramming.WeightedSoftDescent

/- GID: D5/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/TriangularFirstSplitRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Discounted values and finite first-split candidates on the reduced triangular graph. -/

import D5.S3.Arith.FibonacciAtomic.TriangularPathNormalization
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.ConditionallyCompleteLattice.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.TriangularFirstSplitRecurrence

open scoped BigOperators
open TriangularPathNormalization

/-- An infinite legal triangular path from an arbitrary residual state. -/
structure Path (e r : ℕ) where
  state : ℕ → State
  action : ℕ → Action
  start : state 0 = ⟨r, e⟩
  legal : ∀ d, Legal e (state d) (action d)
  step : ∀ d, state (d + 1) = successor (state d) (action d)

/-- The residual orbit when no positive block of labels leaves. -/
def rho (e r j : ℕ) : ℕ := (fun a : ℕ => 2 * a % e)^[j] r

/-- Indices before the first repeated residual, including the first visit to zero. -/
def J (e r : ℕ) : Finset ℕ :=
  (Finset.range e).filter fun j => ∀ i ∈ Finset.range j, rho e r i ≠ rho e r j

/-- The cost of the path which never makes a positive split. -/
noncomputable def U (e r : ℕ) : ℝ := ∑' j : ℕ, (rho e r j : ℝ) / 2 ^ j

/-- The affine value of the no-split path at a real anchor price. -/
noncomputable def K (x : ℝ) (e r : ℕ) : ℝ := U e r - x * r / e

/-- Cost minus price times anchor mass, for an arbitrary starting state. -/
noncomputable def pathValue {e r : ℕ} (x : ℝ) (γ : Path e r) : ℝ :=
  (∑' d : ℕ, ((γ.state d).r : ℝ) / 2 ^ d) -
    x * (∑' d : ℕ, (anchorDigit (γ.action d) : ℝ) / 2 ^ (d + 1))

/-- The infimum over all infinite legal paths from the specified state. -/
noncomputable def W (x : ℝ) (e r : ℕ) : ℝ :=
  sInf (Set.range fun γ : Path e r => pathValue x γ)

/-- The finite set of legal positive first-split positions and sizes. -/
def splitChoices (e r : ℕ) : Finset (ℕ × ℕ) :=
  ((J e r).product (Finset.range e)).filter fun p =>
    2 * rho e r p.1 < e ∧ 1 ≤ p.2 ∧ p.2 ≤ 2 * rho e r p.1

/-- Discounted improvements relative to never splitting, with zero retained. -/
noncomputable def corrections (x : ℝ) (e r : ℕ) : Finset ℝ :=
  {0} ∪ (splitChoices e r).image fun p =>
    ((rho e r p.1 : ℝ) + W x (e - p.2) (2 * rho e r p.1 - p.2) / 2 -
      K x e (rho e r p.1)) / 2 ^ p.1

/-- The forced common digit, or the legal zero digit without removing labels. -/
def noSplitAction (e a : ℕ) : Action := if e ≤ 2 * a then .one else .zero 0

/-- The actual infinite no-split path, retaining zero residual self-loops. -/
def noSplit (e r : ℕ) (hr : r < e) : Path e r := by
  have bounds (j : ℕ) : rho e r j < e := by
    cases j with
    | zero => exact hr
    | succ j =>
      rw [rho, Function.iterate_succ_apply']
      exact Nat.mod_lt _ (by omega)
  refine ⟨fun j => ⟨rho e r j, e⟩,
    fun j => noSplitAction e (rho e r j), rfl, ?_, ?_⟩
  · intro j
    change 0 < e ∧ rho e r j < e ∧ e ≤ e ∧ _
    refine ⟨by omega, bounds j, le_rfl, ?_⟩
    unfold noSplitAction
    split_ifs with h
    · exact h
    · change 2 * rho e r j < e ∧ 0 ≤ 2 * rho e r j
      exact ⟨by omega, Nat.zero_le _⟩
  · intro j
    rw [rho, Function.iterate_succ_apply']
    change State.mk (2 * rho e r j % e) e = _
    unfold noSplitAction
    split_ifs with h
    · simp only [successor]
      congr 1
      exact Nat.mod_eq_sub_mod h |>.trans (Nat.mod_eq_of_lt (by have := bounds j; omega))
    · simp only [successor, Nat.sub_zero]
      congr 1
      exact Nat.mod_eq_of_lt (by omega)

/-- The remaining path, using the current retained label count as its bound. -/
def suffix {e r : ℕ} (γ : Path e r) (n : ℕ) :
    Path (γ.state n).e (γ.state n).r := by
  have retained : Antitone (fun d => (γ.state d).e) := by
    apply antitone_nat_of_succ_le
    intro d
    rw [γ.step d]
    cases γ.action d <;> simp [successor]
  refine ⟨fun d => γ.state (n + d), fun d => γ.action (n + d), by simp, ?_, ?_⟩
  · intro d
    exact ⟨(γ.legal _).1, (γ.legal _).2.1,
      retained (Nat.le_add_right n d), (γ.legal _).2.2.2⟩
  · intro d
    simpa only [Nat.add_assoc] using γ.step (n + d)

/-- Follow the no-split orbit to j, split off h labels, and use the supplied tail. -/
def splitPath (e r : ℕ) (hr : r < e) (j h : ℕ)
    (hj : 2 * rho e r j < e) (hh : h ≤ 2 * rho e r j)
    (δ : Path (e - h) (2 * rho e r j - h)) : Path e r := by
  let γ := noSplit e r hr
  refine ⟨fun d => if d ≤ j then γ.state d else δ.state (d - j - 1),
    fun d => if d < j then γ.action d else if d = j then .zero h
      else δ.action (d - j - 1), ?_, ?_, ?_⟩
  · simp [γ]
    rfl
  · intro d
    by_cases hd : d < j
    · simpa only [if_pos hd, if_pos hd.le] using γ.legal d
    · by_cases heq : d = j
      · subst d
        simp only [if_neg (lt_irrefl j), if_pos le_rfl]
        change 0 < e ∧ rho e r j < e ∧ e ≤ e ∧ _
        exact ⟨by omega, (γ.legal j).2.1, le_rfl, hj, hh⟩
      · have hle : ¬d ≤ j := by omega
        simp only [if_neg hd, if_neg heq, if_neg hle]
        exact ⟨(δ.legal _).1, (δ.legal _).2.1,
          ((δ.legal _).2.2.1).trans (Nat.sub_le _ _), (δ.legal _).2.2.2⟩
  · intro d
    by_cases hd : d < j
    · simpa only [if_pos hd, if_pos hd.le, if_pos (show d + 1 ≤ j by omega)]
        using γ.step d
    · by_cases heq : d = j
      · subst d
        simp only [if_neg (lt_irrefl j), if_pos le_rfl,
          if_neg (show ¬j + 1 ≤ j by omega),
          show j + 1 - j - 1 = 0 by omega]
        exact δ.start
      · have hle : ¬d ≤ j := by omega
        simp only [if_neg hd, if_neg heq, if_neg hle,
          if_neg (show ¬d + 1 ≤ j by omega),
          show d + 1 - j - 1 = (d - j - 1) + 1 by omega]
        exact δ.step _

/-- Zero residuals have zero value. Every positive residual satisfies the finite
first-split recurrence, and the infimum over all legal paths is attained. -/
theorem result (m : ℕ) (_hm : 2 ≤ m) (x : ℝ) (e : ℕ)
    (he : 1 ≤ e ∧ e ≤ m) (r : ℕ) (hr : r < e) :
    W x e 0 = 0 ∧
    (0 < r → W x e r = K x e r +
      (corrections x e r).min' (by
        classical
        exact ⟨0, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩)) ∧
    (∃ γ : Path e r, pathValue x γ = W x e r) := by
  classical
  have bounded_sum (f : ℕ → ℝ) (B : ℝ) (hf : ∀ n, |f n| ≤ B) :
      Summable (fun n => f n / (2 : ℝ) ^ n) := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left B)
    intro n
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ n),
      div_pow, one_pow, mul_one_div]
    exact div_le_div_of_nonneg_right (hf n) (by positivity)
  have orbit_lt (e r : ℕ) (hr : r < e) (j : ℕ) : rho e r j < e := by
    cases j with
    | zero => exact hr
    | succ j =>
      rw [rho, Function.iterate_succ_apply']
      exact Nat.mod_lt _ (by omega)
  have orbit_add (e r i j : ℕ) : rho e r (i + j) = rho e (rho e r i) j := by
    unfold rho
    rw [← Function.iterate_add_apply, Nat.add_comm]
  have orbit_step (e r j : ℕ) : rho e r (j + 1) = 2 * rho e r j % e := by
    exact Function.iterate_succ_apply' (fun a : ℕ => 2 * a % e) j r
  have first_index (e r : ℕ) (hr : r < e) (n : ℕ) :
      ∃ j ∈ J e r, j ≤ n ∧ rho e r j = rho e r n := by
    have witness : ∃ i, rho e r i = rho e r n := ⟨n, rfl⟩
    let j := Nat.find witness
    have hj : rho e r j = rho e r n := Nat.find_spec witness
    have jle : j ≤ n := Nat.find_min' witness rfl
    have distinct : ∀ i < j, ∀ k < j + 1, i < k → rho e r i ≠ rho e r k := by
      intro i hi k hk hik eq
      have hshift : rho e r (i + (j - k)) = rho e r j := by
        rw [orbit_add, eq, ← orbit_add]
        congr 1
        omega
      have hminimal : ¬rho e r (i + (j - k)) = rho e r n :=
        Nat.find_min witness (by omega)
      exact hminimal (hshift.trans hj)
    have je : j < e := by
      by_contra! h
      obtain ⟨i, hi, k, hk, hik, heq⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to
          (s := Finset.range (j + 1)) (t := Finset.range e) (f := rho e r)
          (by simpa using (show e < j + 1 by omega))
          (fun a _ => Finset.mem_range.mpr (orbit_lt e r hr a))
      simp only [Finset.mem_range] at hi hk
      rcases lt_or_gt_of_ne hik with hik | hik
      · exact distinct i (by omega) k hk hik heq
      · exact distinct k (by omega) i hi hik heq.symm
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr je, ?_⟩, jle, hj⟩
    intro i hi
    exact distinct i (Finset.mem_range.mp hi) j (by omega) (Finset.mem_range.mp hi)
  have orbit_sum (e r : ℕ) (hr : r < e) :
      Summable (fun j => (rho e r j : ℝ) / (2 : ℝ) ^ j) :=
    bounded_sum _ e (fun j => by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast (orbit_lt e r hr j).le)
  have no_split_mass (e r : ℕ) (hr : r < e) :
      (∑' j : ℕ, (anchorDigit ((noSplit e r hr).action j) : ℝ) / (2 : ℝ) ^ (j + 1)) =
        (r : ℝ) / e := by
    have sb := Real.summable_ofDigitsTerm
      (digits := fun j => anchorDigit ((noSplit e r hr).action j))
    have digits : (fun j => (anchorDigit ((noSplit e r hr).action j) : ℝ) /
        (2 : ℝ) ^ (j + 1)) =
        (fun j => ((rho e r j : ℝ) / (2 : ℝ) ^ j -
          (rho e r (j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) / e) := by
      funext j
      have hb := orbit_lt e r hr j
      have he : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
      change (anchorDigit (noSplitAction e (rho e r j)) : ℝ) / (2 : ℝ) ^ (j + 1) = _
      rw [orbit_step]
      unfold noSplitAction
      split_ifs with h
      · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega),
          Nat.cast_sub h]
        simp only [anchorDigit, Fin.val_one, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
        rw [pow_succ]
        field_simp
        ring
      · rw [Nat.mod_eq_of_lt (by omega)]
        simp only [anchorDigit, Fin.val_zero, Nat.cast_zero, Nat.cast_mul, Nat.cast_ofNat,
          zero_div, pow_succ]
        field_simp
        ring
    rw [digits, tsum_div_const, (orbit_sum e r hr).tsum_sub
      ((summable_nat_add_iff 1).mpr (orbit_sum e r hr))]
    have hs := (orbit_sum e r hr).tsum_eq_zero_add
    have h0 : rho e r 0 = r := rfl
    rw [h0, pow_zero, div_one] at hs
    rw [show (∑' j : ℕ, (rho e r j : ℝ) / (2 : ℝ) ^ j) -
      (∑' j : ℕ, (rho e r (j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) = r by linarith only [hs]]
  have no_split_value (x : ℝ) (e r : ℕ) (hr : r < e) :
      pathValue x (noSplit e r hr) = K x e r := by
    unfold pathValue K U
    rw [no_split_mass]
    congr 1
    ring
  have path_sum {e r : ℕ} (γ : Path e r) :
      Summable (fun d => ((γ.state d).r : ℝ) / (2 : ℝ) ^ d) :=
    bounded_sum _ e (fun d => by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast ((γ.legal d).2.1.le.trans (γ.legal d).2.2.1))
  let tariff (x : ℝ) {e r : ℕ} (γ : Path e r) (d : ℕ) : ℝ :=
    ((γ.state d).r : ℝ) - x * (anchorDigit (γ.action d) : ℝ) / 2
  have digit_sum {e r : ℕ} (γ : Path e r) :
      Summable (fun d => (anchorDigit (γ.action d) : ℝ) / (2 : ℝ) ^ (d + 1)) := by
    convert Real.summable_ofDigitsTerm (digits := fun d => anchorDigit (γ.action d)) using 1
    ext d
    simp only [Real.ofDigitsTerm, Nat.cast_ofNat, div_eq_mul_inv]
  have tariff_sum {e r : ℕ} (x : ℝ) (γ : Path e r) :
      Summable (fun d => tariff x γ d / (2 : ℝ) ^ d) := by
    apply ((path_sum γ).sub ((digit_sum γ).mul_left x)).congr
    intro d
    dsimp [tariff]
    rw [pow_succ]
    ring
  have series {e r : ℕ} (x : ℝ) (γ : Path e r) :
      pathValue x γ = ∑' d : ℕ, tariff x γ d / (2 : ℝ) ^ d := by
    unfold pathValue
    rw [← (digit_sum γ).tsum_mul_left, ← (path_sum γ).tsum_sub ((digit_sum γ).mul_left x)]
    apply tsum_congr
    intro d
    dsimp [tariff]
    rw [pow_succ]
    ring
  have prefix_value {e r : ℕ} (x : ℝ) (γ : Path e r) (n : ℕ) :
      pathValue x γ = (∑ d ∈ Finset.range n, tariff x γ d / (2 : ℝ) ^ d) +
        pathValue x (suffix γ n) / (2 : ℝ) ^ n := by
    rw [series, series]
    have H := (tariff_sum x γ).sum_add_tsum_nat_add n
    rw [← H]
    congr 1
    rw [← tsum_div_const]
    apply tsum_congr
    intro d
    change tariff x γ (d + n) / (2 : ℝ) ^ (d + n) =
      (tariff x γ (n + d) / (2 : ℝ) ^ d) / (2 : ℝ) ^ n
    rw [Nat.add_comm d n, pow_add]
    ring
  have no_split_suffix (x : ℝ) (e r n : ℕ) (hr : r < e) :
      pathValue x (suffix (noSplit e r hr) n) = K x e (rho e r n) := by
    rw [← no_split_value x e (rho e r n) (orbit_lt e r hr n), series, series]
    apply tsum_congr
    intro d
    dsimp only [tariff, suffix, noSplit]
    rw [orbit_add]
  have one_step {e r : ℕ} (x : ℝ) (γ : Path e r) (n : ℕ) :
      pathValue x (suffix γ n) = tariff x γ n + pathValue x (suffix γ (n + 1)) / 2 := by
    rw [series, series]
    rw [(tariff_sum x (suffix γ n)).tsum_eq_zero_add]
    simp only [pow_zero, div_one]
    change tariff x γ (n + 0) + (∑' d : ℕ, tariff x γ (n + (d + 1)) / (2 : ℝ) ^ (d + 1)) = _
    simp only [Nat.add_zero]
    congr 1
    rw [← tsum_div_const]
    apply tsum_congr
    intro d
    change tariff x γ (n + (d + 1)) / (2 : ℝ) ^ (d + 1) =
      (tariff x γ (n + 1 + d) / (2 : ℝ) ^ d) / 2
    rw [show n + (d + 1) = n + 1 + d by omega, pow_succ]
    ring
  have quiet_action {e r : ℕ} (γ : Path e r) (d : ℕ)
      (hq : ∀ h, γ.action d = .zero h → h = 0) :
      γ.action d = noSplitAction (γ.state d).e (γ.state d).r := by
    have hl := (γ.legal d).2.2.2
    cases ha : γ.action d with
    | one =>
      simp only [ha] at hl
      simp [noSplitAction, hl]
    | zero h =>
      have hz := hq h ha
      subst h
      simp only [ha] at hl
      simp [noSplitAction, show ¬(γ.state d).e ≤ 2 * (γ.state d).r by omega]
  have quiet_prefix {e r : ℕ} (γ : Path e r) (hr : r < e) (n : ℕ)
      (hq : ∀ d < n, ∀ h, γ.action d = .zero h → h = 0) :
      (∀ d ≤ n, γ.state d = (noSplit e r hr).state d) ∧
      (∀ d < n, γ.action d = (noSplit e r hr).action d) := by
    have states : ∀ d ≤ n, γ.state d = (noSplit e r hr).state d := by
      intro d hd
      induction d with
      | zero => exact γ.start
      | succ d ih =>
        have heq := ih (by omega)
        have ha := quiet_action γ d (hq d (by omega))
        rw [heq] at ha
        rw [γ.step d, heq, ha]
        exact ((noSplit e r hr).step d).symm
    refine ⟨states, ?_⟩
    intro d hd
    have ha := quiet_action γ d (hq d hd)
    rw [states d hd.le] at ha
    exact ha
  have split_identity {e r : ℕ} (x : ℝ) (γ : Path e r) (hr : r < e) (j h : ℕ)
      (hq : ∀ d < j, ∀ k, γ.action d = .zero k → k = 0)
      (ha : γ.action j = .zero h) :
      pathValue x γ = K x e r +
        ((rho e r j : ℝ) + pathValue x (suffix γ (j + 1)) / 2 -
          K x e (rho e r j)) / (2 : ℝ) ^ j := by
    obtain ⟨hs, hac⟩ := quiet_prefix γ hr j hq
    have ps := prefix_value x γ j
    have pn := prefix_value x (noSplit e r hr) j
    rw [no_split_value, no_split_suffix] at pn
    have sums : (∑ d ∈ Finset.range j, tariff x γ d / (2 : ℝ) ^ d) =
        ∑ d ∈ Finset.range j, tariff x (noSplit e r hr) d / (2 : ℝ) ^ d := by
      apply Finset.sum_congr rfl
      intro d hd
      dsimp only [tariff]
      rw [hs d (Finset.mem_range.mp hd).le, hac d (Finset.mem_range.mp hd)]
    rw [sums] at ps
    have os := one_step x γ j
    have tj : tariff x γ j = rho e r j := by
      dsimp only [tariff]
      rw [hs j le_rfl, ha]
      simp [anchorDigit, noSplit]
    rw [tj] at os
    rw [os] at ps
    linear_combination ps - pn
  have never_split {e r : ℕ} (x : ℝ) (γ : Path e r) (hr : r < e)
      (hq : ∀ d h, γ.action d = .zero h → h = 0) : pathValue x γ = K x e r := by
    rw [← no_split_value x e r hr, series, series]
    apply tsum_congr
    intro d
    obtain ⟨hs, ha⟩ := quiet_prefix γ hr (d + 1) (fun k _ => hq k)
    dsimp only [tariff]
    rw [hs d (by omega), ha d (by omega)]
  have discount (j n : ℕ) (hjn : j ≤ n) (z : ℝ) :
      min 0 (z / (2 : ℝ) ^ j) ≤ z / (2 : ℝ) ^ n := by
    by_cases hz : 0 ≤ z
    · exact (min_le_left _ _).trans (by positivity)
    · have hn : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hjn
      have H : -z / (2 : ℝ) ^ n ≤ -z / (2 : ℝ) ^ j :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) hn
      have H' : z / (2 : ℝ) ^ j ≤ z / (2 : ℝ) ^ n := by
        simp only [neg_div] at H
        linarith only [H]
      exact (min_le_right _ _).trans H'
  have core (x : ℝ) : ∀ e r : ℕ, r < e →
      (∀ γ : Path e r, W x e r ≤ pathValue x γ) ∧
      (∃ γ : Path e r, pathValue x γ = W x e r) ∧
      W x e r = K x e r + sInf (corrections x e r : Set ℝ) := by
    intro e
    induction e using Nat.strong_induction_on with
    | h e ih =>
      intro r hr
      have nonempty : (corrections x e r).Nonempty :=
        ⟨0, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
      let c := sInf (corrections x e r : Set ℝ)
      have cmem : c ∈ corrections x e r := nonempty.csInf_mem
      have c_le : ∀ z ∈ corrections x e r, c ≤ z :=
        fun z hz => csInf_le (Finset.bddBelow _) hz
      have c0 : c ≤ 0 := c_le 0 (Finset.mem_union_left _ (Finset.mem_singleton_self _))
      have child (j h : ℕ) (hj : 2 * rho e r j < e) (h0 : 0 < h)
          (hh : h ≤ 2 * rho e r j) :
          (∀ δ : Path (e - h) (2 * rho e r j - h),
            W x (e - h) (2 * rho e r j - h) ≤ pathValue x δ) ∧
          (∃ δ : Path (e - h) (2 * rho e r j - h),
            pathValue x δ = W x (e - h) (2 * rho e r j - h)) := by
        exact ⟨(ih (e - h) (by omega) _ (by omega)).1,
          (ih (e - h) (by omega) _ (by omega)).2.1⟩
      have lower (γ : Path e r) : K x e r + c ≤ pathValue x γ := by
        by_cases hp : ∃ j h, 0 < h ∧ γ.action j = .zero h
        · let j := Nat.find hp
          obtain ⟨h, h0, ha⟩ := Nat.find_spec hp
          have hq : ∀ d < j, ∀ k, γ.action d = .zero k → k = 0 := by
            intro d hd k hk
            by_contra hk0
            exact Nat.find_min hp hd ⟨k, by omega, hk⟩
          have hs := (quiet_prefix γ hr j hq).1 j le_rfl
          have hl := (γ.legal j).2.2.2
          rw [ha, hs] at hl
          change 2 * rho e r j < e ∧ h ≤ 2 * rho e r j at hl
          have next : γ.state (j + 1) = ⟨2 * rho e r j - h, e - h⟩ := by
            rw [γ.step j, hs, ha]
            rfl
          have tail_bound : W x (e - h) (2 * rho e r j - h) ≤
              pathValue x (suffix γ (j + 1)) := by
            have ht := (ih (γ.state (j + 1)).e (by rw [next]; dsimp; omega)
              (γ.state (j + 1)).r (γ.legal (j + 1)).2.1).1 (suffix γ (j + 1))
            simpa only [next] using ht
          obtain ⟨i, hi, hij, heq⟩ := first_index e r hr j
          have choice : (i, h) ∈ splitChoices e r := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr ⟨hi, Finset.mem_range.mpr (by omega)⟩,
              by rw [heq]; exact ⟨hl.1, h0, hl.2⟩⟩
          let z : ℝ := (rho e r j : ℝ) + W x (e - h) (2 * rho e r j - h) / 2 -
            K x e (rho e r j)
          have cz : c ≤ z / (2 : ℝ) ^ i := by
            apply c_le
            apply Finset.mem_union_right
            exact Finset.mem_image.mpr ⟨(i, h), choice, by dsimp [z]; rw [heq]⟩
          have cj : c ≤ z / (2 : ℝ) ^ j :=
            (le_min c0 cz).trans (discount i j hij z)
          rw [split_identity x γ hr j h hq ha]
          apply add_le_add le_rfl
          exact cj.trans (div_le_div_of_nonneg_right
            (by dsimp [z]; linarith only [tail_bound]) (by positivity))
        · have hq : ∀ d h, γ.action d = .zero h → h = 0 := by
            intro d h ha
            by_contra hh
            exact hp ⟨d, h, by omega, ha⟩
          rw [never_split x γ hr hq]
          linarith only [c0]
      have attained : ∃ γ : Path e r, pathValue x γ = K x e r + c := by
        simp only [corrections, Finset.mem_union, Finset.mem_singleton] at cmem
        rcases cmem with hc | hc
        · exact ⟨noSplit e r hr, by rw [no_split_value, hc, add_zero]⟩
        · obtain ⟨⟨j, h⟩, choice, hc⟩ := Finset.mem_image.mp hc
          have H := Finset.mem_filter.mp choice
          have hj := H.2.1
          have h0 : 0 < h := H.2.2.1
          have hh := H.2.2.2
          obtain ⟨δ, hδ⟩ := (child j h hj h0 hh).2
          let γ := splitPath e r hr j h hj hh δ
          have ha : γ.action j = .zero h := by simp [γ, splitPath]
          have hq : ∀ d < j, ∀ k, γ.action d = .zero k → k = 0 := by
            intro d hd k hk
            change (if d < j then (noSplit e r hr).action d else _) = .zero k at hk
            rw [if_pos hd] at hk
            change noSplitAction e (rho e r d) = .zero k at hk
            unfold noSplitAction at hk
            split_ifs at hk
            exact (Action.zero.inj hk).symm
          have tail_eq : pathValue x (suffix γ (j + 1)) = pathValue x δ := by
            unfold pathValue
            congr 1
            · apply tsum_congr
              intro d
              simp [γ, splitPath, suffix, show ¬j + 1 + d ≤ j by omega,
                show j + 1 + d - j - 1 = d by omega]
            · congr 1
              apply tsum_congr
              intro d
              simp [γ, splitPath, suffix, show ¬j + 1 + d < j by omega,
                show ¬j + 1 + d = j by omega,
                show j + 1 + d - j - 1 = d by omega]
          refine ⟨γ, ?_⟩
          rw [split_identity x γ hr j h hq ha, tail_eq, hδ]
          exact congrArg (K x e r + ·) hc
      obtain ⟨γ, hγ⟩ := attained
      have eqW : W x e r = K x e r + c :=
        (show IsLeast (Set.range fun δ : Path e r => pathValue x δ) (K x e r + c) from
          ⟨⟨γ, hγ⟩, by rintro _ ⟨δ, rfl⟩; exact lower δ⟩).csInf_eq
      refine ⟨?_, ⟨γ, hγ.trans eqW.symm⟩, eqW⟩
      intro δ
      rw [eqW]
      exact lower δ
  have rho_zero (e j : ℕ) : rho e 0 j = 0 :=
    Function.iterate_fixed (by simp : (fun a : ℕ => 2 * a % e) 0 = 0) j
  have choices_zero (e : ℕ) : splitChoices e 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have H := (Finset.mem_filter.mp hp).2
    rw [rho_zero] at H
    omega
  have value_zero (x : ℝ) (e : ℕ) (he : 0 < e) : W x e 0 = 0 := by
    rw [(core x e 0 he).2.2]
    simp [K, U, rho_zero, corrections, choices_zero]
  refine ⟨value_zero x e (by omega), ?_, (core x e r hr).2.1⟩
  intro _
  rw [(core x e r hr).2.2]
  congr 1
  exact (show (corrections x e r).Nonempty from
    ⟨0, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩).csInf_eq_min'

end D5.S3.Arith.FibonacciAtomic.TriangularFirstSplitRecurrence

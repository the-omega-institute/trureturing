/- GID: D5/S3/FiniteGroups/BajnokBeattyOddWrapSingleCrossing
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyOddWrapSingleCrossing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite normalized binomial recurrences determine the unique sign transition. -/

import D5.S3.FiniteGroups.BajnokBeattyBoundaryReturnDefect
import D5.S3.FiniteGroups.BajnokBeattyInitialOddWrapSign
import D5.S3.FiniteGroups.BajnokBeattyOddWrapLateSign
import Mathlib.Tactic

/-! A finite three-column binomial recurrence proves the unique sign
threshold on the complete original odd-wrap quotient family. The existing
choose_two_step_rat supplier is exposed and consumed without reproving it.
Late positive samples give cofinality, so no limit theorem is required. -/

set_option autoImplicit false

noncomputable section
namespace D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open NearSquareLatticeRigidity BajnokBeattyFirstReturnDefect
open BajnokBeattyOddWrapReturnCounts BajnokBeattyBoundaryReturnDefect
open BajnokBeattyOddWrapLateSign BajnokBeattyInitialOddWrapSign

/-- The factor 10 is the exact ratio of the two lambda gaps for the
three odd - wrap columns.  This is an algebraic identity, not a TP premise. -/
private theorem normalized_step (a q x y : ℚ) (ha : 0 < a) (hq : 10 * a < q)
    (hx : 0 < x) (hy : 0 < y) :
    let x' := x * q / (q - a)
    let y' := y * q / (q - 10 * a)
    0 < x'-x ∧ y / x < y'/x' ∧
      (2 * x'-1 - y') - (2 * x - 1 - y) = (x'-x) * (2 - 10 * (y'/x')) := by
  dsimp only
  have hqa : 0 < q - a := by linarith
  have hq10 : 0 < q - 10 * a := by linarith
  have hq0 : 0 < q := by linarith
  have hdx : x * q / (q - a) - x = x * a / (q - a) := by
    field_simp [ne_of_gt hqa]
    ring
  have hdy : y * q / (q - 10 * a) - y = y * (10 * a) / (q - 10 * a) := by
    field_simp [ne_of_gt hq10]
    ring
  have hr : (y * q / (q - 10 * a)) / (x * q / (q - a)) =
      (y / x) * ((q - a) / (q - 10 * a)) := by
    field_simp [ne_of_gt hx, ne_of_gt hq0, ne_of_gt hqa, ne_of_gt hq10]
  have hfactor : 1 < (q - a) / (q - 10 * a) := by
    apply (lt_div_iff₀ hq10).mpr
    linarith
  have hratio : y / x < (y * q / (q - 10 * a)) / (x * q / (q - a)) := by
    rw [hr]
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left hfactor (div_pos hy hx)
  have hslope : y * q / (q - 10 * a) - y =
      10 * ((y * q / (q - 10 * a)) / (x * q / (q - a))) * (x * q / (q - a) - x) := by
    rw [hdy, hdx, hr]
    field_simp [ne_of_gt hx, ne_of_gt hqa, ne_of_gt hq10]
  refine ⟨?_, hratio, ?_⟩
  · rw [hdx]
    exact div_pos (mul_pos hx ha) hqa
  · nlinarith only [hslope]

/-- Increasing step slopes and cofinal positive values imply that a
nonnegative value is followed only by strictly positive values. -/
theorem finite_sign_persistence (d w s : ℕ → ℚ)
    (hw : ∀ n, 0 < w n) (hs : StrictMono s)
    (hstep : ∀ n, d (n + 1) - d n = w n * (2 - s n))
    (hcofinal : ∀ n, ∃ c, n < c ∧ 0 < d c)
    {a b : ℕ} (hab : a < b) (ha : 0 ≤ d a) : 0 < d b := by
  by_cases hsb : s b < 2
  · have hinc (n : ℕ) (hn : n < b) : d n < d (n + 1) := by
      have hsn := hs hn
      have hc : 0 < 2 - s n := by linarith only [hsn, hsb]
      have hh := mul_pos (hw n) hc
      rw [← hstep n] at hh
      linarith only [hh]
    have hwalk : ∀ r : ℕ, a + r < b → d a < d (a + r + 1) := by
      intro r
      induction r with
      | zero =>
        intro hr
        simpa only [Nat.add_zero] using hinc a hr
      | succ r ih =>
        intro hr
        have hprev := ih (by omega)
        have hnext := hinc (a + r + 1) (by omega)
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hprev.trans hnext
    have hh := hwalk (b - a - 1) (by omega)
    rw [show a + (b - a - 1) + 1 = b by omega] at hh
    linarith only [hh, ha]
  · have hsb' : 2 ≤ s b := le_of_not_gt hsb
    have hdec (n : ℕ) (hn : b ≤ n) : d (n + 1) ≤ d n := by
      have hsn := hs.monotone hn
      have hc : 2 - s n ≤ 0 := by linarith only [hsn, hsb']
      have hh := mul_nonpos_of_nonneg_of_nonpos (hw n).le hc
      rw [← hstep n] at hh
      linarith only [hh]
    have hwalk : ∀ r : ℕ, d (b + r) ≤ d b := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
        have hh := hdec (b + r) (by omega)
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hh.trans ih
    obtain ⟨c, hbc, hc⟩ := hcofinal b
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hbc.le
    have hh := hwalk r
    linarith only [hh, hc]

/-- A fully finite single - crossing consequence of the normalized
three - column recurrence.  Cofinal positivity will come from the already
proved actual late cone, on the unbounded subsequence of actual t - values. -/
private theorem recurrence_sign_persistence (x y q : ℕ → ℚ) (a : ℚ)
    (ha : 0 < a) (hq : ∀ n, 10 * a < q n)
    (hx : ∀ n, 0 < x n) (hy : ∀ n, 0 < y n)
    (hrecx : ∀ n, x (n + 1) = x n * q n / (q n - a))
    (hrecy : ∀ n, y (n + 1) = y n * q n / (q n - 10 * a))
    (hcofinal : ∀ n, ∃ c, n < c ∧ 0 < 2 * x c - 1 - y c)
    {i j : ℕ} (hij : i < j) (hi : 0 ≤ 2 * x i - 1 - y i) :
    0 < 2 * x j - 1 - y j := by
  have hlocal (n : ℕ) :
      0 < x (n + 1) - x n ∧ y n / x n < y (n + 1) / x (n + 1) ∧
      (2 * x (n + 1) - 1 - y (n + 1)) - (2 * x n - 1 - y n) =
        (x (n + 1) - x n) * (2 - 10 * (y (n + 1) / x (n + 1))) := by
    have hh := normalized_step a (q n) (x n) (y n) ha (hq n) (hx n) (hy n)
    rwa [← hrecx n, ← hrecy n] at hh
  let d : ℕ → ℚ := fun n => 2 * x n - 1 - y n
  let w : ℕ → ℚ := fun n => x (n + 1) - x n
  let r : ℕ → ℚ := fun n => y n / x n
  let s : ℕ → ℚ := fun n => 10 * r (n + 1)
  have hr : StrictMono r := strictMono_nat_of_lt_succ (fun n => (hlocal n).2.1)
  have hs : StrictMono s := by
    intro u v huv
    exact mul_lt_mul_of_pos_left (hr (Nat.add_lt_add_right huv 1)) (by norm_num)
  exact finite_sign_persistence d w s (fun n => (hlocal n).1) hs
    (fun n => (hlocal n).2.2) hcofinal hij hi


/-- Return counts for the two complete original integer - plane quotients. -/
def original_return_pair (p t : ℤ) : ℕ × ℕ :=
  let m : ℤ := 6 * t - 1
  let v119 : Plane := ![p * (m - 1) / 2, p * (m + 1) / 2]
  let v219 : Plane := ![p * (m - 9) / 2, -(p * (m + 9) / 2)]
  let v133 : Plane := ![p * (m - 3) / 2, p * (m + 3) / 2]
  let v233 : Plane := ![p * (m - 3) / 2, -(p * (m + 3) / 2)]
  let K19 := Submodule.span ℤ (Set.range ![v119, v219])
  let K33 := Submodule.span ℤ (Set.range ![v133, v233])
  let F19 : Plane →+ (Plane ⧸ K19) := K19.mkQ.toAddMonoidHom
  let F33 : Plane →+ (Plane ⧸ K33) := K33.mkQ.toAddMonoidHom
  let L : ℕ := (p * m).toNat
  (W F19 L, W F33 L)

private theorem first_threshold_of_persistence (a b : ℕ → ℕ)
    (hinitial : b 2 < a 2)
    (heventual : ∃ t, 2 ≤ t ∧ a t ≤ b t)
    (hpersist : ∀ t u, 2 ≤ t → t < u → a t ≤ b t → a u < b u) :
    ∃ T : ℕ, 2 < T ∧
      (∀ t, 2 ≤ t → t < T → b t < a t) ∧
      a T ≤ b T ∧ (∀ u, T < u → a u < b u) := by
  classical
  let P : ℕ → Prop := fun t => 2 ≤ t ∧ a t ≤ b t
  have hex : ∃ t, P t := heventual
  let T := Nat.find hex
  have hT : 2 ≤ T ∧ a T ≤ b T := Nat.find_spec hex
  have hTne : T ≠ 2 := by
    intro h
    have hh := hT.2
    rw [h] at hh
    omega
  have hTgt : 2 < T := by omega
  refine ⟨T, hTgt, ?_, hT.2, ?_⟩
  · intro t ht hlt
    by_contra h
    have hle : a t ≤ b t := by omega
    have hh : T ≤ t := Nat.find_min' hex ⟨ht, hle⟩
    omega
  · intro u hu
    exact hpersist T u hT.1 hu hT.2

private def P (u : ℕ) : ℕ := 2 * u + 1
private def row (u r : ℕ) : ℕ := 9 * u + 4 + r
def K (m j : ℕ) : ℚ := Nat.choose (2 * m + 1) (m - j)
def S (m : ℕ) : ℚ := ((m : ℚ) + 1) * ((m : ℚ) + 2)
def lam (j : ℕ) : ℚ := (j : ℚ) * ((j : ℚ) + 1)
private def alpha (u : ℕ) : ℚ := 2 * (P u : ℚ)^2
private def Q (u r : ℕ) : ℚ := S (row u r) - lam u
private def X (u r : ℕ) : ℚ := K (row u r) (3 * u + 1) / K (row u r) u
private def Y (u r : ℕ) : ℚ := K (row u r) (9 * u + 4) / K (row u r) u

theorem K_pos (m j : ℕ) : 0 < K m j := by
  dsimp [K]
  exact_mod_cast (Nat.choose_pos (show m - j ≤ 2 * m + 1 by omega))

theorem denom_pos (m j : ℕ) (hj : j ≤ m) : 0 < S m - lam j := by
  have hjQ : (j : ℚ) ≤ (m : ℚ) := by exact_mod_cast hj
  have he : S m - lam j = ((m : ℚ) + 1 - j) * ((m : ℚ) + j + 2) := by
    dsimp [S, lam]
    ring
  rw [he]
  exact mul_pos (by linarith) (by positivity)

private theorem K_cross (m j : ℕ) (hj : j ≤ m) :
    K (m + 1) j * (S m - lam j) = K m j * ((2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 3)) := by
  have hh := choose_two_step_rat (2 * m + 1) (m - j) (by omega)
  rw [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega,
    show m - j + 1 = (m + 1) - j by omega] at hh
  rw [Nat.cast_sub hj] at hh
  push_cast at hh
  dsimp [K, S, lam]
  nlinarith only [hh]

private theorem K_step (m j : ℕ) (hj : j ≤ m) :
    K (m + 1) j = K m j * ((2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 3)) / (S m - lam j) := by
  exact (eq_div_iff (ne_of_gt (denom_pos m j hj))).mpr (K_cross m j hj)

theorem ratio_step (m j1 j2 : ℕ) (hj1 : j1 ≤ m) (hj2 : j2 ≤ m) :
    K (m + 1) j2 / K (m + 1) j1 =
      (K m j2 / K m j1) * ((S m - lam j1) / (S m - lam j2)) := by
  rw [K_step m j1 hj1, K_step m j2 hj2]
  have hc : 0 < (2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 3) := by positivity
  field_simp [ne_of_gt (K_pos m j1), ne_of_gt hc,
    ne_of_gt (denom_pos m j1 hj1), ne_of_gt (denom_pos m j2 hj2)]

private theorem gap2 (u : ℕ) : lam (3 * u + 1) - lam u = alpha u := by
  dsimp [lam, alpha, P]
  push_cast
  ring

private theorem gap3 (u : ℕ) : lam (9 * u + 4) - lam u = 10 * alpha u := by
  dsimp [lam, alpha, P]
  push_cast
  ring

private theorem denom2 (u r : ℕ) :
    Q u r - alpha u = S (row u r) - lam (3 * u + 1) := by
  dsimp [Q]
  linarith only [gap2 u]

private theorem denom3 (u r : ℕ) :
    Q u r - 10 * alpha u = S (row u r) - lam (9 * u + 4) := by
  dsimp [Q]
  linarith only [gap3 u]

private theorem normalization_bridge (u : ℕ) :
    0 < alpha u ∧ (∀ r, 10 * alpha u < Q u r) ∧
      (∀ r, 0 < X u r) ∧ (∀ r, 0 < Y u r) ∧
      (∀ r, X u (r + 1) = X u r * Q u r / (Q u r - alpha u)) ∧
      (∀ r, Y u (r + 1) = Y u r * Q u r / (Q u r - 10 * alpha u)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [alpha, P]
    positivity
  · intro r
    have hh := denom_pos (row u r) (9 * u + 4) (by dsimp [row]; omega)
    rw [← denom3 u r] at hh
    linarith only [hh]
  · intro r
    exact div_pos (K_pos _ _) (K_pos _ _)
  · intro r
    exact div_pos (K_pos _ _) (K_pos _ _)
  · intro r
    change K (row u (r + 1)) (3 * u + 1) / K (row u (r + 1)) u =
      (K (row u r) (3 * u + 1) / K (row u r) u) * Q u r / (Q u r - alpha u)
    rw [show row u (r + 1) = row u r + 1 by dsimp [row]; omega]
    rw [ratio_step (row u r) u (3 * u + 1)
      (by dsimp [row]; omega) (by dsimp [row]; omega)]
    rw [denom2 u r]
    dsimp [Q]
    ring
  · intro r
    change K (row u (r + 1)) (9 * u + 4) / K (row u (r + 1)) u =
      (K (row u r) (9 * u + 4) / K (row u r) u) * Q u r / (Q u r - 10 * alpha u)
    rw [show row u (r + 1) = row u r + 1 by dsimp [row]; omega]
    rw [ratio_step (row u r) u (9 * u + 4)
      (by dsimp [row]; omega) (by dsimp [row]; omega)]
    rw [denom3 u r]
    dsimp [Q]
    ring


private theorem sampled_return_gap (u t : ℕ) (hu : 1 ≤ u) (ht : 2 ≤ t) :
    let p : ℕ := P u
    let r : ℕ := p * (3 * t - 5)
    let m : ℕ := row u r
    ((original_return_pair (p : ℤ) (t : ℤ)).2 : ℚ)-
        ((original_return_pair (p : ℤ) (t : ℤ)).1 : ℚ) =
      2 * K m u * (2 * X u r - 1 - Y u r) := by
  let p : ℕ := P u
  let r : ℕ := p * (3 * t - 5)
  let m : ℕ := row u r
  let N : ℕ := p * (6 * t - 1)
  have hp3 : 3 ≤ (p : ℤ) := by dsimp [p, P]; omega
  have hpo : Odd (p : ℤ) := ⟨(u : ℤ), by simp [p, P]⟩
  have htZ : 2 ≤ (t : ℤ) := by exact_mod_cast ht
  have hrowN : 2 * m + 1 = N := by
    dsimp [m, row, r, N, p, P]
    rw [show 6 * t - 1 = 2 * (3 * t - 5) + 9 by omega]
    ring
  have hm1 : m = u + p * (3 * t - 1) := by
    dsimp [m, row, r, p, P]
    rw [show 3 * t - 1 = (3 * t - 5) + 4 by omega]
    ring
  have hm2 : m = (3 * u + 1) + p * (3 * t - 2) := by
    dsimp [m, row, r, p, P]
    rw [show 3 * t - 2 = (3 * t - 5) + 3 by omega]
    ring
  have hm3 : m = (9 * u + 4) + p * (3 * t - 5) := by rfl
  have hi1 : m - u = p * (3 * t - 1) := by omega
  have hi2 : m - (3 * u + 1) = p * (3 * t - 2) := by omega
  have hi3 : m - (9 * u + 4) = p * (3 * t - 5) := by omega
  have hsum0 : p * (3 * t) + p * (3 * t - 1) = N := by
    dsimp [N]
    rw [← Nat.mul_add, show 3 * t + (3 * t - 1) = 6 * t - 1 by omega]
  have hsum1 : p * (3 * t + 1) + p * (3 * t - 2) = N := by
    dsimp [N]
    rw [← Nat.mul_add, show (3 * t + 1) + (3 * t - 2) = 6 * t - 1 by omega]
  have hsum4 : p * (3 * t + 4) + p * (3 * t - 5) = N := by
    dsimp [N]
    rw [← Nat.mul_add, show (3 * t + 4) + (3 * t - 5) = 6 * t - 1 by omega]
  have hsym0 : Nat.choose N (p * (3 * t)) = Nat.choose N (p * (3 * t - 1)) := by
    have hh := Nat.choose_symm (show p * (3 * t) ≤ N by omega)
    rw [show N - p * (3 * t) = p * (3 * t - 1) by omega] at hh
    exact hh.symm
  have hsym1 : Nat.choose N (p * (3 * t + 1)) = Nat.choose N (p * (3 * t - 2)) := by
    have hh := Nat.choose_symm (show p * (3 * t + 1) ≤ N by omega)
    rw [show N - p * (3 * t + 1) = p * (3 * t - 2) by omega] at hh
    exact hh.symm
  have hsym4 : Nat.choose N (p * (3 * t + 4)) = Nat.choose N (p * (3 * t - 5)) := by
    have hh := Nat.choose_symm (show p * (3 * t + 4) ≤ N by omega)
    rw [show N - p * (3 * t + 4) = p * (3 * t - 5) by omega] at hh
    exact hh.symm
  have hc := actual_odd_wrap_counts (p : ℤ) (t : ℤ) hp3 hpo htZ
  have hhalf1 : (p : ℤ) * ((6 * (t : ℤ) - 1) + 1) / 2 = (p : ℤ) * (3 * (t : ℤ)) := by
    have hh : (p : ℤ) * ((6 * (t : ℤ) - 1) + 1) = 2 * ((p : ℤ) * (3 * (t : ℤ))) := by ring
    omega
  have hhalf3 : (p : ℤ) * ((6 * (t : ℤ) - 1) + 3) / 2 = (p : ℤ) * (3 * (t : ℤ) + 1) := by
    have hh : (p : ℤ) * ((6 * (t : ℤ) - 1) + 3) = 2 * ((p : ℤ) * (3 * (t : ℤ) + 1)) := by ring
    omega
  have hhalf9 : (p : ℤ) * ((6 * (t : ℤ) - 1) + 9) / 2 = (p : ℤ) * (3 * (t : ℤ) + 4) := by
    have hh : (p : ℤ) * ((6 * (t : ℤ) - 1) + 9) = 2 * ((p : ℤ) * (3 * (t : ℤ) + 4)) := by ring
    omega
  have hNcast : ((p : ℤ) * (6 * (t : ℤ) - 1)).toNat = N := by
    have hh : (p : ℤ) * (6 * (t : ℤ) - 1) = (N : ℤ) := by
      simp only [N, Nat.cast_mul, Nat.cast_sub (show 1 ≤ 6 * t by omega),
        Nat.cast_ofNat, Nat.cast_one]
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hH0 : ((p : ℤ) * (3 * (t : ℤ))).toNat = p * (3 * t) := by
    have hh : (p : ℤ) * (3 * (t : ℤ)) = ((p * (3 * t) : ℕ) : ℤ) := by push_cast <;> ring
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hH1 : ((p : ℤ) * (3 * (t : ℤ) + 1)).toNat = p * (3 * t + 1) := by
    have hh : (p : ℤ) * (3 * (t : ℤ) + 1) = ((p * (3 * t + 1) : ℕ) : ℤ) := by push_cast <;> ring
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hH4 : ((p : ℤ) * (3 * (t : ℤ) + 4)).toNat = p * (3 * t + 4) := by
    have hh : (p : ℤ) * (3 * (t : ℤ) + 4) = ((p * (3 * t + 4) : ℕ) : ℤ) := by push_cast <;> ring
    exact (congrArg Int.toNat hh).trans (Int.toNat_natCast _)
  have hpair1 : (original_return_pair (p : ℤ) (t : ℤ)).1 =
      2 * (Nat.choose N (p * (3 * t)) + Nat.choose N (p * (3 * t + 4))) := by
    calc
      (original_return_pair (p : ℤ) (t : ℤ)).1 =
          2*(Nat.choose ((p : ℤ)*(6*(t : ℤ)-1)).toNat
              ((p : ℤ)*((6*(t : ℤ)-1)+1)/2).toNat +
            Nat.choose ((p : ℤ)*(6*(t : ℤ)-1)).toNat
              ((p : ℤ)*((6*(t : ℤ)-1)+9)/2).toNat) := hc.1
      _ = _ := by rw [hhalf1, hhalf9, hNcast, hH0, hH4]
  have hpair2 : (original_return_pair (p : ℤ) (t : ℤ)).2 =
      4 * Nat.choose N (p * (3 * t + 1)) := by
    calc
      (original_return_pair (p : ℤ) (t : ℤ)).2 =
          4*Nat.choose ((p : ℤ)*(6*(t : ℤ)-1)).toNat
            ((p : ℤ)*((6*(t : ℤ)-1)+3)/2).toNat := hc.2
      _ = _ := by rw [hhalf3, hNcast, hH1]
  have hpair1K : ((original_return_pair (p : ℤ) (t : ℤ)).1 : ℚ) =
      2 * (K m u + K m (9 * u + 4)) := by
    have hh : ((original_return_pair (p : ℤ) (t : ℤ)).1 : ℚ) =
        2 * ((Nat.choose N (p * (3 * t)) : ℚ) + Nat.choose N (p * (3 * t + 4))) := by
      exact_mod_cast hpair1
    rw [hsym0, hsym4] at hh
    dsimp [K]
    rw [hrowN, hi1, hi3]
    exact hh
  have hpair2K : ((original_return_pair (p : ℤ) (t : ℤ)).2 : ℚ) =
      4 * K m (3 * u + 1) := by
    have hh : ((original_return_pair (p : ℤ) (t : ℤ)).2 : ℚ) =
        4 * (Nat.choose N (p * (3 * t + 1)) : ℚ) := by exact_mod_cast hpair2
    rw [hsym1] at hh
    dsimp [K]
    rw [hrowN, hi2]
    exact hh
  change ((original_return_pair (p : ℤ) (t : ℤ)).2 : ℚ)-
      ((original_return_pair (p : ℤ) (t : ℤ)).1 : ℚ) =
    2 * K m u * (2 * X u r - 1 - Y u r)
  rw [hpair1K, hpair2K]
  change 4 * K m (3 * u + 1) - 2 * (K m u + K m (9 * u + 4)) =
    2 * K m u * (2 * (K m (3 * u + 1) / K m u) - 1 - K m (9 * u + 4) / K m u)
  field_simp [ne_of_gt (K_pos m u)] <;> ring

private theorem sampled_positive (u t : ℕ) (hu : 1 ≤ u) (ht : 2 ≤ t)
    (hcone : 9 * (P u : ℤ) + 1 < 6 * (t : ℤ)) :
    0 < 2 * X u (P u * (3 * t - 5)) - 1 - Y u (P u * (3 * t - 5)) := by
  have hp3 : 3 ≤ (P u : ℤ) := by dsimp [P]; omega
  have hpo : Odd (P u : ℤ) := ⟨(u : ℤ), by simp [P]⟩
  have htZ : 2 ≤ (t : ℤ) := by exact_mod_cast ht
  have hw := actual_late_odd_wrap_sign (P u : ℤ) (t : ℤ) hp3 hpo htZ hcone
  change (original_return_pair (P u : ℤ) (t : ℤ)).1 <
    (original_return_pair (P u : ℤ) (t : ℤ)).2 at hw
  have hwQ : ((original_return_pair (P u : ℤ) (t : ℤ)).1 : ℚ) <
      ((original_return_pair (P u : ℤ) (t : ℤ)).2 : ℚ) := by exact_mod_cast hw
  have hgap := sampled_return_gap u t hu ht
  dsimp only at hgap
  have hfactor : 0 < 2 * K (row u (P u * (3 * t - 5))) u :=
    mul_pos (by norm_num) (K_pos _ _)
  have hmul : (2 * K (row u (P u * (3 * t - 5))) u) * 0 <
      (2 * K (row u (P u * (3 * t - 5))) u)*
        (2 * X u (P u * (3 * t - 5)) - 1 - Y u (P u * (3 * t - 5))) := by
    rw [mul_zero, ← hgap]
    linarith only [hwQ]
  exact (mul_lt_mul_iff_right₀ hfactor).mp hmul

private theorem cofinal_positive (u : ℕ) (hu : 1 ≤ u) :
    ∀ n : ℕ, ∃ r : ℕ, n < r ∧ 0 < 2 * X u r - 1 - Y u r := by
  intro n
  let t : ℕ := n + 2 * P u + 2
  have hp : 3 ≤ P u := by dsimp [P]; omega
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hcone : 9 * (P u : ℤ) + 1 < 6 * (t : ℤ) := by
    dsimp [t]
    push_cast
    omega
  refine ⟨P u * (3 * t - 5), ?_, sampled_positive u t hu ht hcone⟩
  have hcoef : n + 1 ≤ 3 * t - 5 := by dsimp [t]; omega
  have hm := Nat.mul_le_mul_right (3 * t - 5) (show 1 ≤ P u by omega)
  simp only [one_mul] at hm
  omega

private theorem sampled_actual_persistence (u s t : ℕ) (hu : 1 ≤ u)
    (hs : 2 ≤ s) (hst : s < t)
    (hbefore : (original_return_pair (P u : ℤ) (s : ℤ)).1 ≤
      (original_return_pair (P u : ℤ) (s : ℤ)).2) :
    (original_return_pair (P u : ℤ) (t : ℤ)).1 <
      (original_return_pair (P u : ℤ) (t : ℤ)).2 := by
  have ht : 2 ≤ t := by omega
  let rs : ℕ := P u * (3 * s - 5)
  let rt : ℕ := P u * (3 * t - 5)
  have hfactorS : 0 < 2 * K (row u rs) u := mul_pos (by norm_num) (K_pos _ _)
  have hfactorT : 0 < 2 * K (row u rt) u := mul_pos (by norm_num) (K_pos _ _)
  have hgapS := sampled_return_gap u s hu hs
  have hgapT := sampled_return_gap u t hu ht
  dsimp only at hgapS hgapT
  have hbeforeQ : ((original_return_pair (P u : ℤ) (s : ℤ)).1 : ℚ) ≤
      ((original_return_pair (P u : ℤ) (s : ℤ)).2 : ℚ) := by exact_mod_cast hbefore
  have hnonneg : 0 ≤ 2 * X u rs - 1 - Y u rs := by
    have hh : (2 * K (row u rs) u) * 0 ≤
        (2 * K (row u rs) u) * (2 * X u rs - 1 - Y u rs) := by
      rw [mul_zero, ← hgapS]
      linarith only [hbeforeQ]
    exact (mul_le_mul_iff_right₀ hfactorS).mp hh
  have horder : rs < rt := by
    exact Nat.mul_lt_mul_of_pos_left (show 3 * s - 5 < 3 * t - 5 by omega)
      (show 0 < P u by dsimp [P]; omega)
  obtain ⟨ha,hQ,hX,hY,hrecX,hrecY⟩ := normalization_bridge u
  have hpositive := recurrence_sign_persistence (X u) (Y u) (Q u) (alpha u)
    ha hQ hX hY hrecX hrecY (cofinal_positive u hu) horder hnonneg
  have hh := mul_pos hfactorT hpositive
  rw [← hgapT] at hh
  have hafterQ : ((original_return_pair (P u : ℤ) (t : ℤ)).1 : ℚ) <
      ((original_return_pair (P u : ℤ) (t : ℤ)).2 : ℚ) := by linarith only [hh]
  exact_mod_cast hafterQ


/-- For every admissible odd p, the original quotient return counts have
exactly one threshold from strictly negative to strictly positive defect.
The value at the threshold may be zero; existence of a zero is not asserted. -/
theorem actual_odd_wrap_single_crossing (p : ℤ) (hp3 : 3 ≤ p) (hpo : Odd p) :
    ∃! T : ℕ, 2 < T ∧
      (∀ t : ℕ, 2 ≤ t → t < T →
        (original_return_pair p t).2 < (original_return_pair p t).1) ∧
      (original_return_pair p T).1 ≤ (original_return_pair p T).2 ∧
      (∀ t : ℕ, T < t →
        (original_return_pair p t).1 < (original_return_pair p t).2) := by
  obtain ⟨k,hk⟩ := hpo
  have hkpos : 0 ≤ k := by omega
  let u : ℕ := k.toNat
  have huZ : (u : ℤ) = k := Int.toNat_of_nonneg hkpos
  have hu : 1 ≤ u := by omega
  have hp : (P u : ℤ) = p := by dsimp [P]; push_cast; omega
  have hinitial : (original_return_pair p 2).2 < (original_return_pair p 2).1 := by
    have hh := actual_initial_odd_wrap_sign p hp3 ⟨k,hk⟩
    simpa [original_return_pair, mul_comm] using hh
  have heventual : ∃ t : ℕ, 2 ≤ t ∧
      (original_return_pair p t).1 ≤ (original_return_pair p t).2 := by
    let t : ℕ := 2 * P u + 2
    have ht : 2 ≤ t := by dsimp [t]; omega
    have htcone : 9 * p + 1 < 6 * (t : ℤ) := by
      rw [← hp]
      dsimp [t]
      push_cast
      omega
    have hh := actual_late_odd_wrap_sign p (t : ℤ) hp3 ⟨k,hk⟩ (by exact_mod_cast ht) htcone
    have hh' : (original_return_pair p t).1 < (original_return_pair p t).2 := hh
    exact ⟨t,ht,hh'.le⟩
  have hpersist (t v : ℕ) (ht : 2 ≤ t) (htv : t < v)
      (h : (original_return_pair p t).1 ≤ (original_return_pair p t).2) :
      (original_return_pair p v).1 < (original_return_pair p v).2 := by
    rw [← hp] at h ⊢
    exact sampled_actual_persistence u t v hu ht htv h
  obtain ⟨T,hT,hbefore,hat,hafter⟩ := first_threshold_of_persistence
    (fun t => (original_return_pair p t).1)
    (fun t => (original_return_pair p t).2) hinitial heventual hpersist
  refine ⟨T,⟨hT,hbefore,hat,hafter⟩,?_⟩
  intro U hU
  rcases hU with ⟨hU,hUb,hUa,hUf⟩
  apply Nat.le_antisymm
  · by_contra h
    have hh := hUb T (by omega) (by omega)
    omega
  · by_contra h
    have hh := hbefore U (by omega) (by omega)
    omega

end D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing

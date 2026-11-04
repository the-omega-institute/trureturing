/- GID: D5/S3/Combinatorics/Circle/ExpandingSourcePath
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ExpandingSourcePath
   mirror-E: none(waiver:audit-open-22063)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq, mathlib/module/Mathlib.Order.Prod.Lex.Basic]
   utility: none
   digest: Actual even expanding physical paths force prefix bounds and an exponential energy gap. -/
module
public import D5.S3.Combinatorics.Circle.SourceWidth
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Prod.Lex.Basic

/-! Native expanding-path source candidate for canonical integration.
The mathematical input is source-proof.txt, SHA256
8d99323356724050173e678e93a8c4316466ba56efcaf4190e40e723fa223d72.
The final native theorem is consumed by MixedSuffixEnergy. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
namespace D5.S3.Combinatorics.Circle.ExpandingSourcePath
open SourceWidth
open scoped BigOperators

def quarter (k : ℕ) : ℤ := (2 : ℤ) ^ (k - 2)
def half (k : ℕ) : ℤ := modulus k / 2
def Large (k t : ℕ) (p : Fin k) : Prop := quarter k ≤ |actualSource k t p|

instance (k t : ℕ) (p : Fin k) : Decidable (Large k t p) :=
  inferInstanceAs (Decidable (quarter k ≤ |actualSource k t p|))

/-- Orientation changes arithmetic signs, never physical labels. -/
def orient (negative : Bool) (z : ℤ) : ℤ := if negative then -z else z

@[simp] theorem orient_abs (negative : Bool) (z : ℤ) :
    |orient negative z| = |z| := by cases negative <;> simp [orient]

@[simp] theorem orient_natAbs (negative : Bool) (z : ℤ) :
    (orient negative z).natAbs = z.natAbs := by cases negative <;> simp [orient]

/-- The complete physical k-cycle, including a wrap at k-1. -/
def phase {k : ℕ} (hk : 0 < k) (p : Fin k) (j : ℕ) : Fin k :=
  ⟨(p.val + j) % k, Nat.mod_lt _ hk⟩

def path {k : ℕ} (hk : 0 < k) (p : Fin k) (m : ℕ) : List (Fin k) :=
  (List.range m).map (phase hk p)

@[simp] theorem phase_zero {k : ℕ} (hk : 0 < k) (p : Fin k) :
    phase hk p 0 = p := by
  apply Fin.ext
  simp [phase, Nat.mod_eq_of_lt p.isLt]

@[simp] theorem path_length {k : ℕ} (hk : 0 < k) (p : Fin k) (m : ℕ) :
    (path hk p m).length = m := by simp [path]

theorem source_geometry {k : ℕ} (hk : 3 ≤ k) :
    2 ≤ quarter k ∧ modulus k = 4 * quarter k - 1 ∧
      half k = 2 * quarter k - 1 ∧ 0 < modulus k ∧ modulus k % 2 = 1 := by
  have hp : 2 ≤ quarter k := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (show 1 ≤ k - 2 by omega)
    simpa [quarter] using h
  have hn : modulus k = 4 * quarter k - 1 := by
    unfold modulus quarter
    conv_lhs => rw [show k = (k - 2) + 2 by omega, pow_add]
    ring
  refine ⟨hp, hn, ?_, by omega, ?_⟩
  · unfold half; rw [hn]; omega
  · rw [hn]; omega

theorem doubleStep_neg {N z : ℤ} (hN : 0 ≤ N) :
    doubleStep N (-z) = -doubleStep N z := by
  unfold doubleStep
  split_ifs <;> omega

/-- This proof uses centered_full_period at the seam, not a numerical-period quotient. -/
theorem phase_step {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (p : Fin k) (j : ℕ) :
    actualSource k t (phase (by omega) p (j + 1)) =
      doubleStep (modulus k) (actualSource k t (phase (by omega) p j)) := by
  obtain ⟨_, _, _, hN, ho⟩ := source_geometry hk
  let next : Fin k → Fin k := fun q => ⟨(q.val + 1) % k, Nat.mod_lt _ (by omega)⟩
  have hnext (q : Fin k) : actualSource k t (next q) =
      centered (modulus k) ((2 : ℤ) ^ (q.val + 1) * t) := by
    by_cases hq : q.val + 1 < k
    · simp [next, actualSource, Nat.mod_eq_of_lt hq]
    · have he : q.val + 1 = k := by omega
      rw [he, centered_full_period]
      simp [next, he, actualSource]
  have he : phase (by omega) p (j + 1) = next (phase (by omega) p j) := by
    apply Fin.ext
    change (p.val + (j + 1)) % k = ((p.val + j) % k + 1) % k
    rw [Nat.mod_add_mod, Nat.add_assoc]
  rw [he, hnext]
  have hp : (2 : ℤ) ^ ((phase (by omega) p j).val + 1) * t =
      2 * ((2 : ℤ) ^ (phase (by omega) p j).val * t) := by rw [pow_succ]; ring
  rw [hp, centered_double hN ho]
  rfl

private theorem two_pow_linear (j : ℕ) : j + 1 ≤ (2 : ℕ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; nlinarith

private theorem three_pow_strict (j : ℕ) : j + 2 < (3 : ℕ) ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih => rw [pow_succ]; nlinarith

/-- A consumed helper: all scalar premises are proved from actualSource below. -/
private theorem expanding_profile
    (Q N : ℤ) (hQ : 2 ≤ Q) (hN : N = 4 * Q - 1)
    (w : ℕ → ℤ) (m : ℕ) (hm : 2 ≤ m) (heven : m % 2 = 0)
    (hb : ∀ j, -(2 * Q - 1) ≤ w j ∧ w j ≤ 2 * Q - 1)
    (hs : ∀ j < m, w (j + 1) = doubleStep N (w j))
    (hL : ∀ j < m, Q ≤ |w j|) (hd : 0 < 3 * w 0 - N) :
    (0 < w m ∧ Q ≤ |w m|) ∧
    (∀ j ≤ m, 3 * w j = (if j % 2 = 0 then N else -N) +
      (2 : ℤ) ^ j * (3 * w 0 - N)) ∧
    (∀ j ≤ m, 0 ≤ (((List.range j).map w).sum) ∧
      (((List.range j).map w).sum) ≤ w m) ∧
    (|w m| - |w (m - 2)| = (2 : ℤ) ^ (m - 2) * (3 * w 0 - N)) ∧
    ((m : ℤ) - 1 ≤ |w m| - |w (m - 2)|) ∧
    (((List.range m).map (fun j => (3 : ℕ) ^ (w j).natAbs)).sum <
      (3 : ℕ) ^ (w m).natAbs) := by
  let d := 3 * w 0 - N
  have hN0 : 0 < N := by omega
  have hd0 : 0 < d := hd
  have hform : ∀ j ≤ m,
      (if j % 2 = 0 then 0 < w j else w j < 0) ∧
      3 * w j = (if j % 2 = 0 then N else -N) + (2 : ℤ) ^ j * d := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [Nat.zero_mod, ite_true, pow_zero, one_mul]
      dsimp [d] at *
      omega
    | succ j ih =>
      intro hj
      have hjm : j < m := by omega
      obtain ⟨hsgn, heq⟩ := ih (by omega)
      have hlarge := hL j hjm
      obtain ⟨hlo, hhi⟩ := hb j
      have hstep := hs j hjm
      by_cases he : j % 2 = 0
      · have he' : (j + 1) % 2 ≠ 0 := by omega
        simp only [he, ite_true] at hsgn heq
        have ha : |w j| = w j := abs_of_pos hsgn
        have ht : N < 4 * w j := by rw [ha] at hlarge; omega
        rw [doubleStep, if_pos ht] at hstep
        simp only [Nat.succ_eq_add_one, he', ite_false, pow_succ]
        constructor <;> nlinarith
      · have he' : (j + 1) % 2 = 0 := by omega
        simp only [he, ite_false] at hsgn heq
        have ha : |w j| = -w j := abs_of_neg hsgn
        have ht : 4 * w j < -N := by rw [ha] at hlarge; omega
        have ht' : ¬ N < 4 * w j := by omega
        rw [doubleStep, if_neg ht', if_pos ht] at hstep
        simp only [Nat.succ_eq_add_one, he', ite_true, pow_succ]
        constructor <;> nlinarith
  have hmform := hform m (le_refl _)
  have hwm : 0 < w m := by simpa [heven] using hmform.1
  have hr : 3 * w m = N + (2 : ℤ) ^ m * d := by simpa [heven] using hmform.2
  have hm2 : (m - 2) % 2 = 0 := by omega
  have hMform := hform (m - 2) (by omega)
  have hwM : 0 < w (m - 2) := by simpa [hm2] using hMform.1
  have hM : 3 * w (m - 2) = N + (2 : ℤ) ^ (m - 2) * d := by
    simpa [hm2] using hMform.2
  have hp4 : (2 : ℤ) ^ m = 4 * (2 : ℤ) ^ (m - 2) := by
    conv_lhs => rw [show m = (m - 2) + 2 by omega, pow_add]
    ring
  have hgap : |w m| - |w (m - 2)| = (2 : ℤ) ^ (m - 2) * d := by
    rw [abs_of_pos hwm, abs_of_pos hwM]
    have hr' := hr
    rw [hp4] at hr'
    nlinarith [hr', hM]
  have hgaplo : (m : ℤ) - 1 ≤ |w m| - |w (m - 2)| := by
    have ht : (m - 2 : ℕ) + 1 ≤ (2 : ℕ) ^ (m - 2) := two_pow_linear (m - 2)
    have ht' : (m : ℤ) - 1 ≤ (2 : ℤ) ^ (m - 2) := by
      have hc : ((m - 2 : ℕ) : ℤ) + 1 ≤ (2 : ℤ) ^ (m - 2) := by exact_mod_cast ht
      have he : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
      omega
    rw [hgap]
    have hd1 : 1 ≤ d := by omega
    calc
      (m : ℤ) - 1 ≤ (2 : ℤ) ^ (m - 2) := ht'
      _ ≤ (2 : ℤ) ^ (m - 2) * d := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1
          (pow_nonneg (by norm_num : (0 : ℤ) ≤ 2) (m - 2))
  have hmax : ∀ j < m, |w j| ≤ |w (m - 2)| := by
    intro j hj
    obtain ⟨hsgn, heq⟩ := hform j (by omega)
    by_cases he : j % 2 = 0
    · have hj2 : j ≤ m - 2 := by omega
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hj2
      have hmul := mul_le_mul_of_nonneg_right hp (le_of_lt hd0)
      simp only [he, ite_true] at hsgn heq
      rw [abs_of_pos hsgn, abs_of_pos hwM]
      nlinarith
    · simp only [he, ite_false] at hsgn heq
      rw [abs_of_neg hsgn, abs_of_pos hwM]
      have hp : 0 < (2 : ℤ) ^ j := pow_pos (by norm_num) _
      have hp' : 0 < (2 : ℤ) ^ (m - 2) := pow_pos (by norm_num) _
      nlinarith [mul_pos hp hd0, mul_pos hp' hd0]
  have hlargeEnd : Q ≤ |w m| := by
    have h0 := hL 0 (by omega)
    have hx := hmax 0 (by omega)
    omega
  have hprefix_eq : ∀ j ≤ m,
      3 * (((List.range j).map w).sum) =
        (if j % 2 = 0 then 0 else N) + ((2 : ℤ) ^ j - 1) * d := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hf := (hform j (by omega)).2
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton, pow_succ]
      by_cases he : j % 2 = 0
      · have he' : (j + 1) % 2 ≠ 0 := by omega
        simp only [he, he', ite_true, ite_false] at hi hf ⊢
        nlinarith
      · have he' : (j + 1) % 2 = 0 := by omega
        simp only [he, he', ite_true, ite_false] at hi hf ⊢
        nlinarith
  have hprefix : ∀ j ≤ m, 0 ≤ (((List.range j).map w).sum) ∧
      (((List.range j).map w).sum) ≤ w m := by
    intro j hj
    have heq := hprefix_eq j hj
    have hp : 1 ≤ (2 : ℤ) ^ j := one_le_pow₀ (by norm_num)
    have hpm := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hj
    have hmul := mul_le_mul_of_nonneg_right hpm (le_of_lt hd0)
    have hprod : 0 ≤ ((2 : ℤ) ^ j - 1) * d :=
      mul_nonneg (by omega) (le_of_lt hd0)
    split_ifs at heq <;> constructor <;>
      nlinarith only [heq, hprod, hmul, hr, hN0, hd0]
  have hsum : (((List.range m).map (fun j => (3 : ℕ) ^ (w j).natAbs)).sum) ≤
      m * (3 : ℕ) ^ (w (m - 2)).natAbs := by
    have ht := List.sum_le_length_nsmul
      ((List.range m).map (fun j => (3 : ℕ) ^ (w j).natAbs))
      ((3 : ℕ) ^ (w (m - 2)).natAbs) (by
        intro z hz
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
        have ha : (w j).natAbs ≤ (w (m - 2)).natAbs := by
          have hh := hmax j (List.mem_range.mp hj)
          exact_mod_cast (show ((w j).natAbs : ℤ) ≤ ((w (m - 2)).natAbs : ℤ) by
            simpa only [Int.natCast_natAbs] using hh)
        exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 3) ha)
    simpa [nsmul_eq_mul] using ht
  have hgapNat : (w (m - 2)).natAbs + (m - 1) ≤ (w m).natAbs := by
    have hc : ((w (m - 2)).natAbs : ℤ) + ((m - 1 : ℕ) : ℤ) ≤
        ((w m).natAbs : ℤ) := by
      simp only [Int.natCast_natAbs]
      have he : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
      omega
    exact_mod_cast hc
  have hthree : m < (3 : ℕ) ^ (m - 1) := by
    have h := three_pow_strict (m - 2)
    simpa only [show m - 2 + 2 = m by omega, show m - 2 + 1 = m - 1 by omega] using h
  have henergy : (((List.range m).map (fun j => (3 : ℕ) ^ (w j).natAbs)).sum) <
      (3 : ℕ) ^ (w m).natAbs := by
    calc
      _ ≤ m * (3 : ℕ) ^ (w (m - 2)).natAbs := hsum
      _ < (3 : ℕ) ^ (m - 1) * (3 : ℕ) ^ (w (m - 2)).natAbs :=
        Nat.mul_lt_mul_of_pos_right hthree (pow_pos (by decide) _)
      _ = (3 : ℕ) ^ ((w (m - 2)).natAbs + (m - 1)) := by rw [pow_add]; ring
      _ ≤ (3 : ℕ) ^ (w m).natAbs := pow_le_pow_right₀ (by decide) hgapNat
  exact ⟨⟨hwm, hlargeEnd⟩, fun j hj => (hform j hj).2, hprefix, hgap, hgaplo, henergy⟩

/-- Native even expanding path estimates. No prefix, energy, or endpoint-LARGE
conclusion is supplied as a hypothesis. m%2=0, m>=2 is the exact even-length scope. -/
theorem expanding_path_estimates
    {k : ℕ} (hk : 3 ≤ k) (t : ℕ) (p : Fin k) (m : ℕ)
    (hm : 2 ≤ m) (heven : m % 2 = 0) (negative : Bool)
    (hL : ∀ j < m, Large k t (phase (by omega) p j))
    (hd : 0 < 3 * orient negative (actualSource k t p) - modulus k) :
    let x := phase (by omega) p m
    let d := 3 * orient negative (actualSource k t p) - modulus k
    0 < orient negative (actualSource k t x) ∧ Large k t x ∧
    (∀ n : ℕ,
      0 ≤ orient negative ((((path (by omega) p m).take n).map (actualSource k t)).sum) ∧
      orient negative ((((path (by omega) p m).take n).map (actualSource k t)).sum) ≤
        orient negative (actualSource k t x)) ∧
    (|actualSource k t x| - |actualSource k t (phase (by omega) p (m - 2))| =
      (2 : ℤ) ^ (m - 2) * d) ∧
    ((m : ℤ) - 1 ≤ |actualSource k t x| -
      |actualSource k t (phase (by omega) p (m - 2))|) ∧
    (((path (by omega) p m).map (fun q => (3 : ℕ) ^ (actualSource k t q).natAbs)).sum <
      (3 : ℕ) ^ (actualSource k t x).natAbs) := by
  dsimp only
  obtain ⟨hQ, hN, hC, hN0, hodd⟩ := source_geometry hk
  let w := fun j => orient negative (actualSource k t (phase (by omega) p j))
  have hb : ∀ j, -(2 * quarter k - 1) ≤ w j ∧ w j ≤ 2 * quarter k - 1 := by
    intro j
    have hb := centered_bounds hN0 hodd ((2 : ℤ) ^ (phase (by omega) p j).val * t)
    change -half k ≤ actualSource k t (phase (by omega) p j) ∧
      actualSource k t (phase (by omega) p j) ≤ half k at hb
    rw [hC] at hb
    cases negative <;> dsimp [w, orient] <;> omega
  have hs : ∀ j < m, w (j + 1) = doubleStep (modulus k) (w j) := by
    intro j _
    have h := phase_step hk t p j
    cases negative
    · simpa [w, orient] using h
    · simpa [w, orient, doubleStep_neg (le_of_lt hN0)] using congrArg Neg.neg h
  have hl : ∀ j < m, quarter k ≤ |w j| := by
    intro j hj
    simpa [w, Large] using hL j hj
  have hd' : 0 < 3 * w 0 - modulus k := by simpa [w] using hd
  obtain ⟨hend, _, hpre, hgap, hgaplo, henergy⟩ :=
    expanding_profile (quarter k) (modulus k) hQ hN w m hm heven hb hs hl hd'
  refine ⟨hend.1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Large, w] using hend.2
  · intro n
    have h := hpre (min n m) (Nat.min_le_right _ _)
    have htake : (path (by omega) p m).take n =
        (List.range (min n m)).map (phase (by omega) p) := by
      unfold path
      rw [← List.map_take, List.take_range]
    have heq : orient negative ((((path (by omega) p m).take n).map (actualSource k t)).sum) =
        (((List.range (min n m)).map w).sum) := by
      rw [htake]
      cases negative <;>
        simp [List.map_map, Function.comp_def, w, orient, sum_neg_map]
    rw [heq]
    exact h
  · simpa [w] using hgap
  · simpa [w] using hgaplo
  · simpa [path, List.map_map, Function.comp_def, w] using henergy

end D5.S3.Combinatorics.Circle.ExpandingSourcePath

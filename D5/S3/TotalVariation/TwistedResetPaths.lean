/- GID: D5/S3/TotalVariation/TwistedResetPaths
   generality: G
   mirror-B: D5/B/S3/TotalVariation/TwistedResetPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact complete-prefix marginals, positive mass, and support of twisted reset paths. -/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators
namespace D5.S3.TotalVariation.TwistedResetPaths
/-- Absolute sign and the length of the current run of ones. -/
abbrev State (k : ℕ) := Bool × Fin k
/-- The finite geometric right eigenvector, with reciprocal eigenvalue parameter `p`. -/
noncomputable def suffixWeight (k : ℕ) (p : ℝ) (j : Fin k) : ℝ :=
  ∑ a ∈ Finset.range (k - j.val), p ^ (a + 1)
/-- Reset flips the sign and returns the suffix to zero; increment preserves the sign.
At the Parry parameter this is the lifted transition kernel. -/
noncomputable def kernel (k : ℕ) (p : ℝ) : Matrix (State k) (State k) ℝ :=
  fun s t => if t.1 = !s.1 ∧ t.2.val = 0 then p / suffixWeight k p s.2
    else if t.1 = s.1 ∧ t.2.val = s.2.val + 1 then
      p * suffixWeight k p t.2 / suffixWeight k p s.2 else 0

/-- Complement the absolute sign, leaving the suffix unchanged. -/
def flip {k : ℕ} (s : State k) : State k := (!s.1, s.2)

/-- A nonzero twisted return of length `L` must start below suffix `L`.
The high-suffix induction excludes every reset, which would otherwise be needed to flip the sign. -/
theorem twisted_power_support (k : ℕ) (p : ℝ) (L : ℕ) (s : State k)
    (h : (kernel k p ^ L) s (flip s) ≠ 0) : s.2.val < L := by
  classical
  have high : ∀ (m : ℕ) (s t : State k), m ≤ t.2.val →
      (kernel k p ^ m) s t ≠ 0 → t.1 = s.1 ∧ t.2.val = s.2.val + m := by
    intro m
    induction m with
    | zero =>
      intro s t _ hn
      have heq : s = t := by
        by_contra hst
        simp [hst] at hn
      subst t
      simp
    | succ m ih =>
      intro s t ht hn
      rw [pow_succ, Matrix.mul_apply] at hn
      obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
      have hpow : (kernel k p ^ m) s u ≠ 0 := (mul_ne_zero_iff.mp hu).1
      have hedge : kernel k p u t ≠ 0 := (mul_ne_zero_iff.mp hu).2
      have ht0 : t.2.val ≠ 0 := by omega
      have hstep : t.1 = u.1 ∧ t.2.val = u.2.val + 1 := by
        by_contra hbad
        simp [kernel, ht0, hbad] at hedge
      have huHigh : m ≤ u.2.val := by omega
      obtain ⟨hsign, hindex⟩ := ih s u huHigh hpow
      exact ⟨hstep.1.trans hsign, by omega⟩
  by_contra hcut
  have hh := high L s (flip s) (by simpa [flip] using Nat.le_of_not_gt hcut) h
  have hsign : (!s.1) = s.1 := hh.1
  cases s.1 <;> simp_all

/-- Product of all transition weights, including the transition out of the given start. -/
noncomputable def pathWeight (k : ℕ) (p : ℝ) :
    (n : ℕ) → State k → (Fin n → State k) → ℝ
  | 0, _, _ => 1
  | n + 1, s, v => kernel k p s (v 0) * pathWeight k p n (v 0) (fun i => v i.succ)

/-- Endpoint after the specified number of transitions. -/
def endpoint {k : ℕ} : (n : ℕ) → State k → (Fin n → State k) → State k
  | 0, s, _ => s
  | n + 1, _, v => endpoint n (v 0) (fun i => v i.succ)

/-- Sum over all closing continuations of a fixed complete prefix.
The initial state has no stationary factor. -/
noncomputable def twistedPrefixMass (k : ℕ) (p : ℝ) (n G : ℕ)
    (s : State k) (v : Fin n → State k) : ℝ :=
  ∑ w : Fin G → State k,
    if endpoint G (endpoint n s v) w = flip s then
      pathWeight k p n s v * pathWeight k p G (endpoint n s v) w else 0

/-- Summing every closing continuation leaves the exact matrix-power bridge factor. -/
theorem twisted_prefix_marginal (k : ℕ) (p : ℝ) (n G : ℕ)
    (s : State k) (v : Fin n → State k) :
    twistedPrefixMass k p n G s v =
      pathWeight k p n s v * (kernel k p ^ G) (endpoint n s v) (flip s) := by
  classical
  have bridge : ∀ (m : ℕ) (x y : State k),
      (∑ w : Fin m → State k, if endpoint m x w = y then pathWeight k p m x w else 0) =
        (kernel k p ^ m) x y := by
    intro m
    induction m with
    | zero =>
      intro x y
      simp [endpoint, pathWeight, Matrix.one_apply]
      rfl
    | succ m ih =>
      intro x y
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m + 1) => State k)]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk,
        pathWeight, endpoint, Fin.cons_zero, Fin.cons_succ]
      rw [pow_succ', Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro z _
      rw [← ih z y, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp
  unfold twistedPrefixMass
  rw [← bridge G (endpoint n s v) (flip s), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> simp

/-- Every complete-prefix marginal vanishes outside the actual twisted-loop support. -/
theorem twisted_prefix_support (k : ℕ) (p : ℝ) (hp : 0 ≤ p) (n G : ℕ)
    (s : State k) (v : Fin n → State k) (hcut : n + G ≤ s.2.val) :
    twistedPrefixMass k p n G s v = 0 := by
  classical
  have hh (j : Fin k) : 0 ≤ suffixWeight k p j :=
    Finset.sum_nonneg fun a _ => pow_nonneg hp _
  have hQ (x y : State k) : 0 ≤ kernel k p x y := by
    unfold kernel
    split_ifs
    · exact div_nonneg hp (hh _)
    · exact div_nonneg (mul_nonneg hp (hh _)) (hh _)
    · exact le_rfl
  have hw : ∀ (m : ℕ) (x : State k) (w : Fin m → State k),
      0 ≤ pathWeight k p m x w ∧
      pathWeight k p m x w ≤ (kernel k p ^ m) x (endpoint m x w) := by
    intro m
    induction m with
    | zero => intro x w; simp [pathWeight, endpoint]
    | succ m ih =>
      intro x w
      obtain ⟨hw0, hwle⟩ := ih (w 0) (fun i => w i.succ)
      constructor
      · exact mul_nonneg (hQ _ _) hw0
      · calc
          pathWeight k p (m + 1) x w ≤
              kernel k p x (w 0) * (kernel k p ^ m) (w 0)
                (endpoint m (w 0) (fun i => w i.succ)) :=
            mul_le_mul_of_nonneg_left hwle (hQ _ _)
          _ ≤ (kernel k p ^ (m + 1)) x (endpoint (m + 1) x w) := by
            rw [pow_succ', Matrix.mul_apply]
            exact Finset.single_le_sum
              (fun z _ => mul_nonneg (hQ x z)
                (Matrix.pow_apply_nonneg hQ m z (endpoint (m + 1) x w)))
              (Finset.mem_univ (w 0))
  rw [twisted_prefix_marginal]
  have hzero : (kernel k p ^ (n + G)) s (flip s) = 0 := by
    by_contra hn
    exact (Nat.not_lt_of_ge hcut) (twisted_power_support k p (n + G) s hn)
  apply le_antisymm
  · calc
      pathWeight k p n s v * (kernel k p ^ G) (endpoint n s v) (flip s) ≤
          (kernel k p ^ n) s (endpoint n s v) *
            (kernel k p ^ G) (endpoint n s v) (flip s) :=
        mul_le_mul_of_nonneg_right (hw n s v).2 (Matrix.pow_apply_nonneg hQ _ _ _)
      _ ≤ (kernel k p ^ (n + G)) s (flip s) := by
        rw [pow_add, Matrix.mul_apply]
        exact Finset.single_le_sum
          (fun z _ => mul_nonneg (Matrix.pow_apply_nonneg hQ n s z)
            (Matrix.pow_apply_nonneg hQ G z (flip s))) (Finset.mem_univ (endpoint n s v))
      _ = 0 := hzero
  · exact mul_nonneg (hw n s v).1 (Matrix.pow_apply_nonneg hQ _ _ _)

/-- Total unnormalized mass of complement-twisted loops. -/
noncomputable def loopMass (k : ℕ) (p : ℝ) (L : ℕ) : ℝ :=
  ∑ s : State k, (kernel k p ^ L) s (flip s)

/-- The full prefix marginal has the same total mass as the twisted loop law. -/
theorem twisted_prefix_total_mass (k : ℕ) (p : ℝ) (n G : ℕ) :
    (∑ s : State k, ∑ v : Fin n → State k, twistedPrefixMass k p n G s v) =
      loopMass k p (n + G) := by
  classical
  have extend : ∀ (m : ℕ) (x y : State k),
      (∑ v : Fin m → State k, pathWeight k p m x v *
        (kernel k p ^ G) (endpoint m x v) y) = (kernel k p ^ (m + G)) x y := by
    intro m
    induction m with
    | zero => intro x y; simp [pathWeight, endpoint]
    | succ m ih =>
      intro x y
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (m + 1) => State k)]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, pathWeight, endpoint,
        Fin.cons_zero, Fin.cons_succ, mul_assoc]
      simp_rw [← Finset.mul_sum, ih]
      rw [show m + 1 + G = (m + G) + 1 by omega, pow_succ', Matrix.mul_apply]
  unfold loopMass
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [twisted_prefix_marginal]
  exact extend n s (flip s)

/-- Reset-only odd loops and one-increment even loops give positive mass
for every length at least two. -/
theorem loop_mass_pos (k : ℕ) (hk : 2 ≤ k) (p : ℝ) (hp : 0 < p)
    (L : ℕ) (hL : 2 ≤ L) : 0 < loopMass k p L := by
  classical
  let z : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, by omega⟩
  have hh (j : Fin k) : 0 < suffixWeight k p j := by
    unfold suffixWeight
    apply lt_of_lt_of_le (show 0 < p ^ (0 + 1) by simpa using hp)
    exact Finset.single_le_sum (fun a _ => pow_nonneg hp.le (a + 1))
      (Finset.mem_range.mpr (by have := j.isLt; omega))
  have hQ (x y : State k) : 0 ≤ kernel k p x y := by
    unfold kernel
    split_ifs
    · exact (div_pos hp (hh _)).le
    · exact (div_pos (mul_pos hp (hh _)) (hh _)).le
    · exact le_rfl
  have hreset (s : State k) : 0 < kernel k p s (!s.1, z) := by
    simpa [kernel, z] using div_pos hp (hh s.2)
  have hjoin (a b : ℕ) (x y t : State k)
      (ha : 0 < (kernel k p ^ a) x y) (hb : 0 < (kernel k p ^ b) y t) :
      0 < (kernel k p ^ (a + b)) x t := by
    rw [pow_add, Matrix.mul_apply]
    exact lt_of_lt_of_le (mul_pos ha hb) (Finset.single_le_sum
      (fun u _ => mul_nonneg (Matrix.pow_apply_nonneg hQ a x u)
        (Matrix.pow_apply_nonneg hQ b u t)) (Finset.mem_univ y))
  have htwo (a : Bool) : 0 < (kernel k p ^ 2) (a, z) (a, z) := by
    have h := hjoin 1 1 (a,z) (!a,z) (a,z)
      (by simpa using hreset (a,z)) (by simpa using hreset (!a,z))
    exact h
  have hodd : ∀ (m : ℕ) (s : State k),
      0 < (kernel k p ^ (2 * m + 1)) s (!s.1, z) := by
    intro m
    induction m with
    | zero => intro s; simpa using hreset s
    | succ m ih =>
      intro s
      have h := hjoin (2 * m + 1) 2 s (!s.1,z) (!s.1,z) (ih s) (htwo (!s.1))
      convert h using 1
      congr 2
  have hentry : 0 < (kernel k p ^ L) (false,z) (true,z) := by
    obtain ⟨m, hEven | hOdd⟩ := Nat.even_or_odd' L
    · have hm : 0 < m := by omega
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      have hinc : 0 < kernel k p (false,z) (false,o) := by
        simpa [kernel, z, o] using div_pos (mul_pos hp (hh o)) (hh z)
      have h := hjoin 1 (2*t+1) (false,z) (false,o) (true,z)
        (by simpa using hinc) (by simpa using hodd t (false,o))
      have he : L = 1 + (2 * t + 1) := by omega
      rw [he]
      exact h
    · simpa [hOdd] using hodd m (false,z)
  unfold loopMass
  exact lt_of_lt_of_le hentry (Finset.single_le_sum
    (fun s _ => Matrix.pow_apply_nonneg hQ L s (flip s)) (Finset.mem_univ (false,z)))

#print axioms twisted_power_support
#print axioms twisted_prefix_marginal
#print axioms twisted_prefix_support
#print axioms twisted_prefix_total_mass
#print axioms loop_mass_pos
end D5.S3.TotalVariation.TwistedResetPaths

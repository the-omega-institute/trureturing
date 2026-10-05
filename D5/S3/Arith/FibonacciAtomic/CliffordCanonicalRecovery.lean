/- GID: D5/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CliffordCanonicalRecovery
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp modular, carry, and complete digit recovery from Clifford leaves. -/

import D5.S3.Arith.FibonacciAtomic.CliffordLeafOrbit
import D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
import Mathlib.Order.SuccPred.Archimedean

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CliffordCanonicalRecovery

open CliffordLeafOrbit (Q E X Factors)
open GenealogicalFiberTransport (Source substitution composition)
open GraftAffineClosure (atomicBlock residue step quantity)

/-- Standard low representatives of the actual canonical composition. -/
def low (d j : ℕ) : ℕ × ℕ := ((atomicBlock j).1 % d, (atomicBlock j).2 % d)

/-- The integer carry of the next Fibonacci composition step. -/
def carry (d j : ℕ) : ℕ := ((low d j).1 + (low d j).2) / d

/-- The next-step carry vector, reduced modulo the output modulus. -/
def K (d e j : ℕ) : ZMod e × ZMod e := (0, carry d j)

/-- The current high representatives, reduced modulo the output modulus. -/
def H (d e j : ℕ) : ZMod e × ZMod e :=
  ((atomicBlock j).1 / d, (atomicBlock j).2 / d)

/-- The complete low and high target from one and the same source. -/
def L (d e j : ℕ) : (ℕ × ℕ) × (ZMod e × ZMod e) := (low d j, H d e j)

/-- All sharp recovery classifications on the full infinite canonical source orbit. -/
theorem result :
    (∀ D : ℕ, 1 ≤ D → (Factors (fun j => residue D (atomicBlock j)) ↔ D ∣ 4)) ∧
    (∀ d e : ℕ, 1 ≤ d → 2 ≤ e → (Factors (K d e) ↔ d ∣ 4)) ∧
    (∀ d : ℕ, 1 ≤ d → Factors (K d 1) ∧ ∀ j, K d 1 j = 0) ∧
    (∀ e : ℕ, 1 ≤ e → Factors (K 1 e) ∧ ∀ j, low 1 j = 0 ∧ carry 1 j = 0 ∧ K 1 e j = 0) ∧
    (∀ d e : ℕ, 1 ≤ d → 1 ≤ e → (Factors (L d e) ↔ d * e ∣ 4)) ∧
    (∀ d e : ℕ, 1 ≤ d → 1 ≤ e → d ∣ 4 → (Factors (H d e) ↔ d * e ∣ 4)) := by
  classical
  have criterion := CliffordLeafOrbit.result.2.2.2.1
  have block_succ (j : ℕ) : atomicBlock (j + 1) = step (atomicBlock j) :=
    Function.iterate_succ_apply' step j (1, 0)
  have block_six (j : ℕ) : atomicBlock (j + 6) =
      (5 * (atomicBlock j).1 + 8 * (atomicBlock j).2,
        8 * (atomicBlock j).1 + 13 * (atomicBlock j).2) := by
    rw [atomicBlock, show j + 6 = 6 + j by omega, Function.iterate_add_apply]
    apply Prod.ext
    · rw [GlobalGcdSampling.iterate_first 6 (by decide)]
      norm_num [atomicBlock]
    · rw [GlobalGcdSampling.iterate_second]
      norm_num [atomicBlock]
  have modular (D : ℕ) : Factors (fun j => residue D (atomicBlock j)) ↔ D ∣ 4 := by
    rw [criterion]
    constructor
    · intro h
      have h0 := congrArg Prod.fst (h 0)
      have h1 := congrArg Prod.snd (h 1)
      norm_num [atomicBlock, Function.iterate_succ_apply', step, residue] at h0 h1
      have h4 : (4 : ZMod D) = 0 := by linear_combination h0
      exact (ZMod.natCast_eq_zero_iff 4 D).mp h4
    · intro hd j
      have h4 : (4 : ZMod D) = 0 := (ZMod.natCast_eq_zero_iff 4 D).mpr hd
      rw [block_six]
      apply Prod.ext <;> simp only [residue, Nat.cast_add, Nat.cast_mul]
      · linear_combination ((atomicBlock j).1 : ZMod D) * h4 +
          (2 * ((atomicBlock j).2 : ZMod D)) * h4
      · linear_combination (2 * ((atomicBlock j).1 : ZMod D)) * h4 +
          (3 * ((atomicBlock j).2 : ZMod D)) * h4
  have low_period (d : ℕ) (hd : d ∣ 4) (j : ℕ) : low d (j + 6) = low d j := by
    have h := (criterion _ _).mp ((modular d).mpr hd) j
    apply Prod.ext
    · exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (congrArg Prod.fst h)
    · exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (congrArg Prod.snd h)
  have bounded_zero (a : ℕ → ℤ) (b : ℤ) (hb : 0 ≤ b)
      (ha : ∀ j, -b ≤ a j ∧ a j ≤ b)
      (hr : ∀ j, a (j + 2) = a (j + 1) + a j) : ∀ j, a j = 0 := by
    let p : ℕ → ℤ := fun j => a j * a (j + 1)
    have growth (j : ℕ) : p (j + 1) = p j + a (j + 1) ^ 2 := by
      dsimp [p]
      rw [show j + 1 + 1 = j + 2 by omega, hr]
      ring
    have mono : Monotone p := monotone_nat_of_le_succ fun j => by
      rw [growth]
      nlinarith [sq_nonneg (a (j + 1))]
    have bound : BddAbove (Set.range p) := by
      refine ⟨b ^ 2, ?_⟩
      rintro _ ⟨j, rfl⟩
      nlinarith [(ha j).1, (ha j).2, (ha (j + 1)).1, (ha (j + 1)).2]
    obtain ⟨v, hv⟩ := bound.exists_isGreatest_of_nonempty ⟨p 0, ⟨0, rfl⟩⟩
    obtain ⟨N, rfl⟩ := hv.1
    have tail (j : ℕ) (hj : N ≤ j) : a (j + 1) = 0 := by
      have heq : p (j + 1) = p j := le_antisymm
        ((hv.2 ⟨j + 1, rfl⟩).trans (mono hj)) (mono (by omega))
      rw [growth] at heq
      nlinarith [sq_nonneg (a (j + 1))]
    have back (k : ℕ) : a (N + 1 - k) = 0 ∧ a (N + 2 - k) = 0 := by
      induction k with
      | zero => exact ⟨tail N (by omega), tail (N + 1) (by omega)⟩
      | succ k ih =>
        by_cases hk : k ≤ N
        · have h := hr (N - k)
          rw [show N - k + 1 = N + 1 - k by omega,
            show N - k + 2 = N + 2 - k by omega, ih.1, ih.2] at h
          constructor <;> omega
        · have h := hr 0
          have h0 : a 0 = 0 := by
            have := ih.1
            rwa [show N + 1 - k = 0 by omega] at this
          constructor <;> simpa [show N + 1 - (k + 1) = 0 by omega,
            show N + 2 - (k + 1) = 0 by omega] using h0
    intro j
    by_cases hj : N + 1 ≤ j
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
      exact tail (N + i) (by omega)
    · have h := (back (N + 1 - j)).1
      simpa [show N + 1 - (N + 1 - j) = j by omega] using h
  have carry_class (d e : ℕ) (hd : 1 ≤ d) (he : 2 ≤ e) : Factors (K d e) ↔ d ∣ 4 := by
    rw [criterion]
    constructor
    · intro hk
      have cbound (j : ℕ) : carry d j < 2 := by
        have h1 := Nat.mod_lt (atomicBlock j).1 (by omega : 0 < d)
        have h2 := Nat.mod_lt (atomicBlock j).2 (by omega : 0 < d)
        dsimp [carry, low]
        omega
      have cp (j : ℕ) : carry d (j + 6) = carry d j := by
        have h := congrArg Prod.snd (hk j)
        have h' := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
        rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (cbound _) he),
          Nat.mod_eq_of_lt (lt_of_lt_of_le (cbound _) he)] at h'
        exact h'
      have next (j : ℕ) : (low d (j + 1)).1 = (low d j).2 ∧
          (low d (j + 1)).2 + d * carry d j = (low d j).1 + (low d j).2 := by
        rw [low, block_succ]
        simp only [step]
        constructor
        · rfl
        · dsimp [low, carry]
          rw [Nat.add_mod]
          exact Nat.mod_add_div _ _
      let a : ℕ → ℤ := fun j => ((low d (j + 6)).2 : ℤ) - (low d j).2
      have ar (j : ℕ) : a (j + 2) = a (j + 1) + a j := by
        have h1 := (next (j + 1)).2
        have h2 := (next (j + 6 + 1)).2
        have h3 := (next j).1
        have h4 := (next (j + 6)).1
        rw [show j + 6 + 1 = (j + 1) + 6 by omega, cp] at h2
        dsimp only [a]
        rw [show j + 2 + 6 = j + 6 + 1 + 1 by omega,
          show j + 1 + 6 = j + 6 + 1 by omega]
        zify at h1 h2
        rw [h3] at h1
        rw [h4] at h2
        omega
      have ab (j : ℕ) : -(d : ℤ) ≤ a j ∧ a j ≤ d := by
        have h1 := Nat.mod_lt (atomicBlock j).2 (by omega : 0 < d)
        have h2 := Nat.mod_lt (atomicBlock (j + 6)).2 (by omega : 0 < d)
        dsimp [a, low]
        omega
      have az := bounded_zero a d (by positivity) ab ar
      have h0 := az 0
      have h1 := az 1
      norm_num [a, low, atomicBlock, Function.iterate_succ_apply', step] at h0 h1
      have hd8 : d ∣ 8 := Nat.dvd_of_mod_eq_zero (by omega)
      have hd12 : d ∣ 12 := Nat.dvd_of_mod_eq_zero (by omega)
      have hg := Nat.dvd_gcd hd8 hd12
      norm_num at hg
      exact hg
    · intro hdiv j
      unfold K carry
      rw [low_period d hdiv]
  have digits (d e n m : ℕ) (hd : 1 ≤ d) :
      n % d = m % d ∧ (n / d : ZMod e) = (m / d : ZMod e) ↔
        (n : ZMod (d * e)) = (m : ZMod (d * e)) := by
    rw [ZMod.natCast_eq_natCast_iff', ZMod.natCast_eq_natCast_iff']
    have hnd := Nat.mod_mul_right_mod n d e
    have hmd := Nat.mod_mul_right_mod m d e
    have hne := Nat.mod_mul_right_div_self n d e
    have hme := Nat.mod_mul_right_div_self m d e
    constructor
    · rintro ⟨hl, hh⟩
      apply Nat.ext_div_mod (n := d)
      · omega
      · omega
    · intro h
      constructor
      · omega
      · omega
  have complete (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) :
      Factors (L d e) ↔ d * e ∣ 4 := by
    rw [criterion, ← modular (d * e), criterion]
    have equiv (n m : ℕ) : L d e n = L d e m ↔
        residue (d * e) (atomicBlock n) = residue (d * e) (atomicBlock m) := by
      simp only [L, low, H, residue, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
        exact ⟨(digits d e _ _ hd).mp ⟨h1,h3⟩,
          (digits d e _ _ hd).mp ⟨h2,h4⟩⟩
      · rintro ⟨h1,h2⟩
        have a := (digits d e _ _ hd).mpr h1
        have b := (digits d e _ _ hd).mpr h2
        exact ⟨⟨a.1,b.1⟩,⟨a.2,b.2⟩⟩
    exact forall_congr' fun j => equiv (j + 6) j
  have high (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) (hdiv : d ∣ 4) :
      Factors (H d e) ↔ d * e ∣ 4 := by
    rw [← complete d e hd he, criterion, criterion]
    have equiv (j : ℕ) : H d e (j + 6) = H d e j ↔ L d e (j + 6) = L d e j := by
      simp only [L, Prod.mk.injEq, low_period d hdiv j, true_and]
    exact forall_congr' equiv
  refine ⟨fun D _ => modular D, carry_class, ?_, ?_, complete, high⟩
  · intro d _
    have zero (j : ℕ) : K d 1 j = 0 := by ext <;> exact Subsingleton.elim _ _
    exact ⟨(criterion _ _).mpr (fun j => (zero _).trans (zero _).symm), zero⟩
  · intro e _
    have zero (j : ℕ) : low 1 j = 0 ∧ carry 1 j = 0 ∧ K 1 e j = 0 := by
      simp [low, carry, K]
    exact ⟨(criterion _ _).mpr (fun j => (zero _).2.2.trans (zero _).2.2.symm), zero⟩

end D5.S3.Arith.FibonacciAtomic.CliffordCanonicalRecovery

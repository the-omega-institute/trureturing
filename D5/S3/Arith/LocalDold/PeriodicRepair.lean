/- GID: D5/S3/Arith/LocalDold/PeriodicRepair
   generality: G
   mirror-B: D5/B/S3/Arith/LocalDold/PeriodicRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact transforms and repair divisibilities for zero and half residues. -/
import D5.S3.Arith.LocalDold.BackwardZero
import D5.S1.Dynamics.PeriodicOrbits.CountableRealization
import Mathlib.Data.Nat.GCD.Basic

/-! Exact all-index periodic transforms; no recurrence valuation bridge is assumed. -/

set_option autoImplicit false
namespace D5.S3.Arith.LocalDold.PeriodicRepair
open D5.S3.Arith.LocalDold.BackwardZero
open scoped ArithmeticFunction.Moebius

/-- The zero-residue periodic sample, including its baseline fixed points. -/
def zeroSample (R : ℕ) (C : ℤ) (n : ℕ) : ℤ := 1 + if R ∣ n then C else 0

private theorem mobius_of_sum {u w : ℕ → ℤ}
    (hs : ∀ n, 0 < n → ∑ d ∈ n.divisors, w d = u n)
    {n : ℕ} (hn : 0 < n) : mobiusSum u n = w n := by
  have h := ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := w) (g := u)).mp hs) n hn
  unfold mobiusSum
  rw [← Nat.sum_divisorsAntidiagonal' (f := fun a b => μ a * u b)]
  exact h

/-- The transform has exactly the baseline and the prescribed cycle-length spike.
When R=1 the two contributions combine at the same index. -/
theorem zero_transform {R n : ℕ} (hR : 0 < R) (hn : 0 < n) (C : ℤ) :
    mobiusSum (zeroSample R C) n =
      (if n = 1 then 1 else 0) + (if n = R then C else 0) := by
  apply mobius_of_sum (w := fun d =>
    (if d = 1 then 1 else 0) + (if d = R then C else 0)) ?_ hn
  intro k hk
  simp [zeroSample, Finset.sum_add_distrib, Nat.mem_divisors, hk.ne', hR.ne']

private theorem mobius_scale (u : ℕ → ℤ) (c : ℤ) (n : ℕ) :
    mobiusSum (fun d => c*u d) n = c*mobiusSum u n := by
  unfold mobiusSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Every multiplier is classified, not only one sufficient repair. -/
theorem zero_dold_iff {R : ℕ} (hR : 0 < R) (C c : ℕ) :
    Dold (fun n => (c : ℤ)*zeroSample R (C : ℤ) n) ↔ R ∣ c*C := by
  constructor
  · intro h
    by_cases h1 : R = 1
    · simp [h1]
    · have ht := h R hR
      rw [mobius_scale, zero_transform hR hR, ite_eq_right h1, ite_eq_left rfl, zero_add] at ht
      exact_mod_cast ht
  · intro h n hn
    rw [mobius_scale, zero_transform hR hn]
    by_cases h1 : n = 1
    · simp [h1]
    · by_cases he : n = R
      · subst n
        simpa [h1] using (show (R : ℤ) ∣ (c : ℤ)*(C : ℤ) by exact_mod_cast h)
      · simp [h1,he]

/-- Odd multiples of D select exactly the half-residue of period 2D. -/
def halfSample (D : ℕ) (C : ℤ) (n : ℕ) : ℤ :=
  zeroSample D C n - zeroSample (2*D) C n + 1

private theorem mobius_add (u v : ℕ → ℤ) (n : ℕ) :
    mobiusSum (fun d => u d + v d) n = mobiusSum u n + mobiusSum v n := by
  simp [mobiusSum, mul_add, Finset.sum_add_distrib]

private theorem mobius_sub (u v : ℕ → ℤ) (n : ℕ) :
    mobiusSum (fun d => u d - v d) n = mobiusSum u n - mobiusSum v n := by
  simp [mobiusSum, mul_sub, Finset.sum_sub_distrib]

/-- A half residue has a positive D spike and a negative 2D spike. -/
theorem half_transform {D n : ℕ} (hD : 0 < D) (hn : 0 < n) (C : ℤ) :
    mobiusSum (halfSample D C) n =
      (if n = 1 then 1 else 0) +
        (if n = D then C else 0) - (if n = 2*D then C else 0) := by
  have hc : mobiusSum (fun _ => (1 : ℤ)) n = if n=1 then 1 else 0 := by
    have he : zeroSample 1 0 = fun _ => (1 : ℤ) := by
      funext k
      simp [zeroSample]
    simpa only [he, ite_self, add_zero] using zero_transform (R := 1) (by omega) hn (0 : ℤ)
  unfold halfSample
  rw [mobius_add, mobius_sub, zero_transform hD hn,
    zero_transform (by omega : 0 < 2*D) hn, hc]
  ring

/-- The negative orbit contribution survives every positive multiplier. -/
theorem half_negative {D : ℕ} (hD : 0 < D) {C c : ℕ} (hC : 0 < C) (hc : 0 < c) :
    mobiusSum (fun n => (c : ℤ)*halfSample D (C : ℤ) n) (2*D) < 0 := by
  rw [mobius_scale, half_transform hD (by omega),
    ite_eq_right (by omega : 2*D ≠ 1), ite_eq_right (by omega : 2*D ≠ D), ite_eq_left rfl]
  have hp : (0 : ℤ) < c := by exact_mod_cast hc
  have hp' : (0 : ℤ) < C := by exact_mod_cast hC
  nlinarith

#print axioms zero_transform
#print axioms zero_dold_iff
#print axioms half_transform
#print axioms half_negative
end D5.S3.Arith.LocalDold.PeriodicRepair

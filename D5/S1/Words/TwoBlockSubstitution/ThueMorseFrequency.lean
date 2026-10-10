/- GID: D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency
   generality: I
   mirror-B: D5/B/S1/Words/TwoBlockSubstitution/ThueMorseFrequency
   mirror-E: none(waiver:analytic-proof)
   anchors: []
   utility: none
   digest: The Thue-Morse two-block fixed point has one-letter frequency one half. -/

/-
The statements concern the specific Thue-Morse two-block fixed point, so generality is I.
The frozen block-sum owners supply the pair and triple partitions with R := ℤ.
Direct frozen dependencies (baseline declaration statement_id):
D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.sum_pairs:
  sha256:9b4eec748d00b5e9229115baad1ffc8ba7b173ae920a33099a0f3b491f08d5a6.
D5/S1/Recurrence/Residue/ExponentialSquareWeightTernarySupport.sum_triples:
  sha256:9c892fedc469ebda935e14fd76118dd2346c59b78a162429aaece2655d92a68a.
Admission basis: open-problem-resolution (#14986; Proved).
Escape witness: none. The coefficient energy and signed-block estimate give the frequency limit.
Declaration classifications (consumer -> prerequisite):
kappaTM: proof_shape: bind-only; consumers: fixed_point_density, kappaTM_one, kappaTM_two, kappaTM_zero, sign_kappa, signed_fixed, tmFixed, tmFixed_fixed, tmFixed_step.
tmFixed: proof_shape: bind-only; consumers: claim, result, tmFixed_fixed, tmFixed_step.
kappaTM_zero: proof_shape: bind-only; consumers: tmFixed_fixed.
kappaTM_one: proof_shape: bind-only; consumers: tmFixed_fixed, tmFixed_step.
kappaTM_two: proof_shape: bind-only; consumers: tmFixed_fixed, tmFixed_step.
tmFixed_step: proof_shape: bind-only; consumers: tmFixed_fixed.
tmFixed_fixed: proof_shape: bind-only; consumers: result.
claim: proof_shape: bind-only; consumers: result.
dNat: proof_shape: bind-only; consumers: E, R, Tblock_sum, aligned_functional, aligned_square_bound, coefficient_functional, correlation_succ, d_add, d_combo_period, d_even, d_multi, d_odd, d_period, d_product_period, d_square_period, energy_recurrence.
d_even: proof_shape: bind-only; consumers: coefficient_functional, correlation_succ, energy_recurrence.
d_odd: proof_shape: bind-only; consumers: coefficient_functional, correlation_succ, energy_recurrence.
d_period: proof_shape: content; consumers: d_add, d_multi, d_product_period, d_square_period.
d_add: proof_shape: content; consumers: d_combo_period, d_product_period, energy_recurrence.
sum_blocks: proof_shape: bind-only; consumers: coefficient_functional, prefix_bound.
periodic_sum_shift: proof_shape: bind-only; consumers: correlation_succ, energy_recurrence.
sum_range_zmod: proof_shape: bind-only; consumers: periodic_sum_mul.
periodic_sum_mul: proof_shape: bind-only; consumers: correlation_succ, energy_recurrence.
E: proof_shape: bind-only; consumers: aligned_square_bound, energy_recurrence, energy_succ.
R: proof_shape: bind-only; consumers: correlation_succ, energy_recurrence, energy_succ.
d_product_period: proof_shape: content; consumers: correlation_succ, energy_recurrence.
d_square_period: proof_shape: content; consumers: energy_recurrence.
d_combo_period: proof_shape: content; consumers: correlation_succ.
correlation_succ: proof_shape: content; consumers: energy_succ.
energy_recurrence: proof_shape: content; consumers: energy_succ.
energy_succ: proof_shape: content; consumers: aligned_square_bound.
T: proof_shape: bind-only; consumers: T_one, T_shift, T_two, T_zero, Tblock, Tblock_sum, Tpower_local, Tpower_shift, aligned_block_bound, aligned_block_identity, aligned_functional, aligned_square_bound, coefficient_functional, signed_fixed, signed_mean_tendsto.
T_zero: proof_shape: bind-only; consumers: coefficient_functional.
T_one: proof_shape: bind-only; consumers: coefficient_functional.
T_two: proof_shape: bind-only; consumers: coefficient_functional.
T_shift: proof_shape: bind-only; consumers: Tpower_shift.
Tpower_shift: proof_shape: content; consumers: aligned_block_identity, coefficient_functional.
d_multi: proof_shape: content; consumers: coefficient_functional.
coefficient_functional: proof_shape: content; consumers: Tblock_sum.
Tpower_local: proof_shape: content; consumers: aligned_block_identity.
Tblock: proof_shape: bind-only; consumers: Tblock_sum, aligned_block_identity, aligned_functional.
Tblock_sum: proof_shape: content; consumers: aligned_functional.
sign: proof_shape: bind-only; consumers: bool_density_of_signed_mean, fixed_point_density, sign_abs, sign_kappa, sign_sq, signed_count_identity, signed_fixed.
sign_sq: proof_shape: bind-only; consumers: fixed_point_density.
sign_abs: proof_shape: bind-only; consumers: fixed_point_density.
sign_kappa: proof_shape: bind-only; consumers: signed_fixed.
signed_fixed: proof_shape: bind-only; consumers: fixed_point_density.
aligned_block_identity: proof_shape: content; consumers: aligned_functional.
aligned_functional: proof_shape: content; consumers: aligned_square_bound.
aligned_square_bound: proof_shape: content; consumers: aligned_block_bound.
B: proof_shape: bind-only; consumers: B_ratio_formula, B_ratio_tendsto, aligned_block_bound, signed_mean_tendsto.
aligned_block_bound: proof_shape: content; consumers: signed_mean_tendsto.
prefix_bound: proof_shape: bind-only; consumers: prefix_ratio_bound.
prefix_ratio_bound: proof_shape: bind-only; consumers: signed_mean_tendsto.
B_ratio_formula: proof_shape: bind-only; consumers: B_ratio_tendsto.
B_ratio_tendsto: proof_shape: bind-only; consumers: signed_mean_tendsto.
signed_mean_tendsto: proof_shape: content; consumers: fixed_point_density.
signed_count_identity: proof_shape: bind-only; consumers: bool_density_of_signed_mean.
bool_density_of_signed_mean: proof_shape: bind-only; consumers: fixed_point_density.
fixed_point_density: proof_shape: content; consumers: result.
result: proof_shape: content; consumers: none (settling result).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15019
-/

import D5.S1.Recurrence.Residue.ExponentialSquareWeightTernarySupport
import Mathlib.Data.Nat.Periodic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency

def kappaTM : Bool → Bool → Fin 3 → Bool
  | false, false => ![false, false, true]
  | false, true => ![false, true, false]
  | true, false => ![true, false, true]
  | true, true => ![true, true, false]

def tmFixed : ℕ → Bool
  | 0 => false
  | 1 => false
  | n + 2 =>
    if h : (n + 2) % 3 = 0 then tmFixed (2 * ((n + 2) / 3))
    else kappaTM (tmFixed (2 * ((n + 2) / 3))) (tmFixed (2 * ((n + 2) / 3) + 1))
      ⟨(n + 2) % 3, Nat.mod_lt _ (by decide)⟩
termination_by n => n
decreasing_by all_goals omega

private theorem kappaTM_zero (a b : Bool) : kappaTM a b 0 = a := by cases a <;> cases b <;> rfl
private theorem kappaTM_one (a b : Bool) : kappaTM a b 1 = b := by cases a <;> cases b <;> rfl
private theorem kappaTM_two (a b : Bool) : kappaTM a b 2 = !b := by cases a <;> cases b <;> rfl

private theorem tmFixed_step (n : ℕ) (hn : 2 ≤ n) :
    tmFixed n = if n % 3 = 0 then tmFixed (2 * (n / 3))
      else if n % 3 = 1 then tmFixed (2 * (n / 3) + 1)
      else !(tmFixed (2 * (n / 3) + 1)) := by
  match n with
  | 0 => omega
  | 1 => omega
  | n + 2 =>
    rw [tmFixed]
    split_ifs with h0 h1
    · rfl
    · have hr : (⟨(n + 2) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 1 := Fin.ext h1
      rw [hr, kappaTM_one]
    · have hr : (⟨(n + 2) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 2 := by
        apply Fin.ext
        have := Nat.mod_lt (n + 2) (by decide : 0 < 3)
        dsimp
        omega
      rw [hr, kappaTM_two]

private theorem tmFixed_fixed (n : ℕ) (r : Fin 3) :
    tmFixed (3 * n + r) = kappaTM (tmFixed (2 * n)) (tmFixed (2 * n + 1)) r := by
  fin_cases r
  · change tmFixed (3 * n + 0) = kappaTM (tmFixed (2 * n)) (tmFixed (2 * n + 1)) 0
    rw [kappaTM_zero]
    by_cases hn : n = 0
    · subst n; rfl
    · rw [tmFixed_step _ (by omega)]
      simp
  · change tmFixed (3 * n + 1) = kappaTM (tmFixed (2 * n)) (tmFixed (2 * n + 1)) 1
    rw [kappaTM_one]
    by_cases hn : n = 0
    · subst n; rfl
    · rw [tmFixed_step _ (by omega)]
      simp [Nat.add_div, Nat.add_mod]
  · change tmFixed (3 * n + 2) = kappaTM (tmFixed (2 * n)) (tmFixed (2 * n + 1)) 2
    rw [kappaTM_two, tmFixed_step _ (by omega)]
    simp [Nat.add_div, Nat.add_mod]

def claim : Prop := Filter.Tendsto
    (fun N : ℕ => (((Finset.range N).filter (fun n => tmFixed n = true)).card : ℝ) / N)
    Filter.atTop (nhds (1 / 2))


end D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency

namespace D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency
open Finset

private def dNat : ℕ → ℕ → ℤ
  | 0, _ => 1
  | k + 1, n => if n % 2 = 0 then dNat k (3 * (n / 2))
      else dNat k (3 * (n / 2) + 1) - dNat k (3 * (n / 2) + 2)

private theorem d_even (k j : ℕ) : dNat (k + 1) (2 * j) = dNat k (3 * j) := by
  simp [dNat]

private theorem d_odd (k j : ℕ) :
    dNat (k + 1) (2 * j + 1) = dNat k (3 * j + 1) - dNat k (3 * j + 2) := by
  simp [dNat, Nat.add_div, Nat.add_mod]

private theorem d_period (k : ℕ) : Function.Periodic (dNat k) (2 ^ k) := by
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    have hi : Function.Periodic (dNat k) (3 * 2 ^ k) := by simpa using ih.nat_mul 3
    have hdiv : (n + 2 ^ (k + 1)) / 2 = n / 2 + 2 ^ k := by
      rw [pow_succ]; omega
    have hmod : (n + 2 ^ (k + 1)) % 2 = n % 2 := by
      rw [pow_succ]; omega
    simp only [dNat, hmod, hdiv]
    split
    · convert hi (3 * (n / 2)) using 1
      congr 1
      omega
    · rw [show 3 * (n / 2 + 2 ^ k) + 1 = (3 * (n / 2) + 1) + 3 * 2 ^ k by omega,
          show 3 * (n / 2 + 2 ^ k) + 2 = (3 * (n / 2) + 2) + 3 * 2 ^ k by omega,
          hi, hi]

private theorem d_add (k n : ℕ) : dNat k (n + 2 ^ k) = dNat k n := d_period k n

private theorem sum_blocks {A : Type*} [AddCommMonoid A] (f : ℕ → A) (q m : ℕ) :
    (∑ n ∈ range (q * m), f n) = ∑ j ∈ range q, ∑ i ∈ range m, f (j * m + i) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

private theorem periodic_sum_shift (f : ℕ → ℤ) (m : ℕ)
    (hf : Function.Periodic f m) (t : ℕ) :
    (∑ i ∈ range m, f (i + t)) = ∑ i ∈ range m, f i := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := sum_range_succ' (fun i => f (i + t)) m
    have h' := sum_range_succ (fun i => f (i + t)) m
    have hper : f (m + t) = f t := by simpa [add_comm] using hf t
    simp only [hper] at h'
    have heq : (∑ i ∈ range m, f (i + 1 + t)) = ∑ i ∈ range m, f (i + t) := by
      rw [h] at h'
      simp only [zero_add] at h'
      exact add_right_cancel h'
    simpa [Nat.add_assoc, Nat.add_comm 1 t] using heq.trans ih

private theorem sum_range_zmod (m : ℕ) [NeZero m] (f : ℕ → ℤ) :
    (∑ i ∈ range m, f i) = ∑ x : ZMod m, f x.val := by
  rw [← Fin.sum_univ_eq_sum_range]
  have he : ∀ x : Fin m, (ZMod.finEquiv m x).val = x.val := by
    cases m with
    | zero => exact False.elim (NeZero.ne 0 rfl)
    | succ m => intro x; rfl
  have h := Equiv.sum_comp (ZMod.finEquiv m).toEquiv (fun x : ZMod m => f x.val)
  change (∑ i : Fin m, f (ZMod.finEquiv m i).val) = _ at h
  simpa only [he] using h

private theorem periodic_sum_mul (f : ℕ → ℤ) (m t : ℕ) [NeZero m]
    (hf : Function.Periodic f m) (ht : t.Coprime m) :
    (∑ i ∈ range m, f (t * i)) = ∑ i ∈ range m, f i := by
  rw [sum_range_zmod, sum_range_zmod]
  have he : ∀ x : ZMod m, f (t * x.val) = f ((t * x).val) := by
    intro x
    rw [← hf.map_mod_nat (t * x.val)]
    congr 1
    simp [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod]
  simp_rw [he]
  have h := Equiv.sum_comp (ZMod.unitOfCoprime t ht).mulLeft (fun x : ZMod m => f x.val)
  change (∑ x : ZMod m, f (((ZMod.unitOfCoprime t ht : (ZMod m)ˣ) : ZMod m) * x).val) = _ at h
  simpa only [ZMod.coe_unitOfCoprime] using h

private def E (k : ℕ) : ℤ := ∑ i ∈ range (2 ^ k), (dNat k i) ^ 2
private def R (k : ℕ) : ℤ := ∑ i ∈ range (2 ^ k), dNat k i * dNat k (i + 1)

end D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency

namespace D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency
open Finset

private theorem d_product_period (k t : ℕ) :
    Function.Periodic (fun r => dNat k r * dNat k (r + t)) (2 ^ k) := by
  intro r
  dsimp
  rw [d_period, show r + 2 ^ k + t = (r + t) + 2 ^ k by omega, d_add]

private theorem d_square_period (k : ℕ) :
    Function.Periodic (fun r => (dNat k r) ^ 2) (2 ^ k) := by
  intro r
  dsimp
  rw [d_period]

private theorem d_combo_period (k : ℕ) : Function.Periodic
    (fun r => dNat k r * dNat k (r + 1) - dNat k r * dNat k (r + 2) +
      dNat k (r + 1) * dNat k (r + 3) - dNat k (r + 2) * dNat k (r + 3)) (2 ^ k) := by
  intro r
  dsimp
  simp only [show r + 2 ^ k + 1 = (r + 1) + 2 ^ k by omega,
    show r + 2 ^ k + 2 = (r + 2) + 2 ^ k by omega,
    show r + 2 ^ k + 3 = (r + 3) + 2 ^ k by omega, d_add]

private theorem correlation_succ (k : ℕ) : R (k + 1) = 0 := by
  let : NeZero (2 ^ k) := ⟨by positivity⟩
  have hcop : Nat.Coprime 3 (2 ^ k) := (by decide : Nat.Coprime 3 2).pow_right k
  have h1 := periodic_sum_shift (fun r => dNat k r * dNat k (r + 1)) (2 ^ k)
    (d_product_period k 1) 2
  have h2 := periodic_sum_shift (fun r => dNat k r * dNat k (r + 2)) (2 ^ k)
    (d_product_period k 2) 1
  have hreindex := periodic_sum_mul _ (2 ^ k) 3 (d_combo_period k) hcop
  unfold R
  rw [pow_succ, Nat.mul_comm (2 ^ k) 2, D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.sum_pairs (R := ℤ)]
  simp_rw [d_even, d_odd]
  have hnext (j : ℕ) : dNat (k + 1) (2 * j + 1 + 1) = dNat k (3 * j + 3) := by
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega, d_even]
    congr 1
  simp_rw [hnext]
  calc
    _ = ∑ j ∈ range (2 ^ k),
        (dNat k (3 * j) * dNat k (3 * j + 1) - dNat k (3 * j) * dNat k (3 * j + 2) +
         dNat k (3 * j + 1) * dNat k (3 * j + 3) - dNat k (3 * j + 2) * dNat k (3 * j + 3)) := by
      apply sum_congr rfl; intro j hj; ring
    _ = ∑ r ∈ range (2 ^ k),
        (dNat k r * dNat k (r + 1) - dNat k r * dNat k (r + 2) +
         dNat k (r + 1) * dNat k (r + 3) - dNat k (r + 2) * dNat k (r + 3)) := hreindex
    _ = 0 := by
      simp only [Nat.add_assoc] at h1 h2
      simp only [sum_sub_distrib, sum_add_distrib]
      rw [h1, h2]
      ring

private theorem energy_recurrence (k : ℕ) : E (k + 1) = 3 * E k - 2 * R k := by
  let : NeZero (2 ^ k) := ⟨by positivity⟩
  have hcop : Nat.Coprime 3 (2 ^ k) := (by decide : Nat.Coprime 3 2).pow_right k
  have hp : Function.Periodic
      (fun r => (dNat k r) ^ 2 + (dNat k (r + 1)) ^ 2 + (dNat k (r + 2)) ^ 2 -
        2 * (dNat k (r + 1) * dNat k (r + 2))) (2 ^ k) := by
    intro r
    dsimp
    simp only [show r + 2 ^ k + 1 = (r + 1) + 2 ^ k by omega,
      show r + 2 ^ k + 2 = (r + 2) + 2 ^ k by omega, d_add]
  have hs1 := periodic_sum_shift (fun r => (dNat k r) ^ 2) (2 ^ k) (d_square_period k) 1
  have hs2 := periodic_sum_shift (fun r => (dNat k r) ^ 2) (2 ^ k) (d_square_period k) 2
  have hr := periodic_sum_shift (fun r => dNat k r * dNat k (r + 1)) (2 ^ k)
    (d_product_period k 1) 1
  unfold E
  rw [pow_succ, Nat.mul_comm (2 ^ k) 2, D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.sum_pairs (R := ℤ)]
  simp_rw [d_even, d_odd]
  calc
    _ = ∑ j ∈ range (2 ^ k),
        ((dNat k (3 * j)) ^ 2 + (dNat k (3 * j + 1)) ^ 2 + (dNat k (3 * j + 2)) ^ 2 -
          2 * (dNat k (3 * j + 1) * dNat k (3 * j + 2))) := by
      apply sum_congr rfl; intro j hj; ring
    _ = ∑ r ∈ range (2 ^ k),
        ((dNat k r) ^ 2 + (dNat k (r + 1)) ^ 2 + (dNat k (r + 2)) ^ 2 -
          2 * (dNat k (r + 1) * dNat k (r + 2))) := periodic_sum_mul _ _ _ hp hcop
    _ = _ := by
      simp only [Nat.add_assoc] at hr
      simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum]
      rw [hs1, hs2, hr]
      unfold R
      ring

private theorem energy_succ (k : ℕ) : E (k + 1) = 3 ^ k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    rw [energy_recurrence, ih, correlation_succ, pow_succ]
    ring

end D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency
namespace D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency
open Finset

private def T (v : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n % 3 = 0 then v (2 * (n / 3))
  else if n % 3 = 1 then v (2 * (n / 3) + 1) else -v (2 * (n / 3) + 1)

private theorem T_zero (v : ℕ → ℤ) (j : ℕ) : T v (3 * j) = v (2 * j) := by simp [T]
private theorem T_one (v : ℕ → ℤ) (j : ℕ) : T v (3 * j + 1) = v (2 * j + 1) := by
  simp [T, Nat.add_div, Nat.add_mod]
private theorem T_two (v : ℕ → ℤ) (j : ℕ) : T v (3 * j + 2) = -v (2 * j + 1) := by
  simp [T, Nat.add_div, Nat.add_mod]

private theorem T_shift (v : ℕ → ℤ) (j i : ℕ) :
    T v (3 * j + i) = T (fun n => v (2 * j + n)) i := by
  have hi : i % 3 < 3 := Nat.mod_lt _ (by decide)
  simp [T, Nat.add_div, Nat.add_mod, hi.not_ge, Nat.mul_add, Nat.add_assoc]

private theorem Tpower_shift (k j : ℕ) (v : ℕ → ℤ) (i : ℕ) :
    (T^[k]) v (j * 3 ^ k + i) = (T^[k]) (fun n => v (j * 2 ^ k + n)) i := by
  induction k generalizing j v i with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rw [show j * 3 ^ (k + 1) + i = 3 * (j * 3 ^ k) + i by ring, T_shift]
    apply congrArg (fun w => T w i)
    funext n
    rw [show 2 * (j * 3 ^ k) + n = (2 * j) * 3 ^ k + n by ring, ih]
    apply congrArg (fun w : ℕ → ℤ => T^[k] w n)
    funext r
    congr 1
    ring

private theorem d_multi (k j n : ℕ) : dNat k (j * 2 ^ k + n) = dNat k n := by
  simpa [Nat.add_comm] using (d_period k).nat_mul j n

private theorem coefficient_functional (k : ℕ) (v : ℕ → ℤ) :
    (∑ n ∈ range (3 ^ k), (T^[k]) v n) = ∑ i ∈ range (2 ^ k), dNat k i * v i := by
  induction k generalizing v with
  | zero => simp [dNat]
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    calc
      _ = ∑ j ∈ range 3, ∑ i ∈ range (3 ^ k),
          (T^[k]) (T v) (j * 3 ^ k + i) := by
        rw [pow_succ, Nat.mul_comm (3 ^ k) 3, sum_blocks]
      _ = ∑ j ∈ range 3, ∑ i ∈ range (2 ^ k), dNat k i * T v (j * 2 ^ k + i) := by
        apply sum_congr rfl; intro j hj
        simp_rw [Tpower_shift]
        exact ih _
      _ = ∑ n ∈ range (3 * 2 ^ k), dNat k n * T v n := by
        rw [sum_blocks]
        simp_rw [d_multi]
      _ = ∑ j ∈ range (2 ^ k),
          (dNat k (3 * j) * v (2 * j) +
            (dNat k (3 * j + 1) - dNat k (3 * j + 2)) * v (2 * j + 1)) := by
        rw [D5.S1.Recurrence.Residue.ExponentialSquareWeightTernarySupport.sum_triples (R := ℤ)]
        simp_rw [T_zero, T_one, T_two]
        apply sum_congr rfl; intro j hj; ring
      _ = _ := by
        rw [pow_succ, Nat.mul_comm (2 ^ k) 2, D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.sum_pairs (R := ℤ)]
        simp_rw [d_even, d_odd]

private theorem Tpower_local (k m : ℕ) (v w : ℕ → ℤ)
    (hv : ∀ n < m * 2 ^ k, v n = w n) :
    ∀ i < m * 3 ^ k, (T^[k]) v i = (T^[k]) w i := by
  induction k generalizing m v w with
  | zero => simpa [Function.iterate_succ_apply'] using hv
  | succ k ih =>
    intro i hi
    have hi' : i < 3 * (m * 3 ^ k) := by
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hi
    have hdiv : i / 3 < m * 3 ^ k := by omega
    have hv' : ∀ n < (2 * m) * 2 ^ k, v n = w n := by
      intro n hn
      apply hv n
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hn
    have he := ih (2 * m) v w hv'
    have he0 := he (2 * (i / 3)) (by nlinarith)
    have he1 := he (2 * (i / 3) + 1) (by nlinarith)
    simp only [Function.iterate_succ_apply', T, he0, he1]

private def Tblock (k : ℕ) (v : Fin (2 ^ k) → ℤ) : Fin (3 ^ k) → ℤ :=
  fun i => (T^[k]) (fun n => if h : n < 2 ^ k then v ⟨n, h⟩ else 0) i

private theorem Tblock_sum (k : ℕ) (v : Fin (2 ^ k) → ℤ) :
    (∑ i, Tblock k v i) = ∑ j : Fin (2 ^ k), dNat k j * v j := by
  have h := coefficient_functional k (fun n => if h : n < 2 ^ k then v ⟨n, h⟩ else 0)
  rw [← Fin.sum_univ_eq_sum_range] at h
  simp only [Tblock] at ⊢
  rw [h]
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro j hj
  simp [j.isLt]

end D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency
namespace D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency
open Finset Filter

private def sign (b : Bool) : ℤ := if b then -1 else 1

private theorem sign_sq (b : Bool) : (sign b) ^ 2 = 1 := by cases b <;> norm_num [sign]
private theorem sign_abs (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]

private theorem sign_kappa (a b : Bool) (r : Fin 3) :
    sign (kappaTM a b r) =
      if r.val = 0 then sign a else if r.val = 1 then sign b else -sign b := by
  fin_cases r <;> cases a <;> cases b <;> decide

private theorem signed_fixed (x : ℕ → Bool)
    (hx : ∀ n (r : Fin 3), x (3 * n + r) = kappaTM (x (2 * n)) (x (2 * n + 1)) r) :
    T ((fun n => sign (x n))) = (fun n => sign (x n)) := by
  funext n
  have h := congrArg sign (hx (n / 3) ⟨n%3, Nat.mod_lt _ (by decide)⟩)
  rw [sign_kappa] at h
  simpa only [T, Nat.div_add_mod] using h.symm

private theorem aligned_block_identity (k j : ℕ) (a : ℕ → ℤ) (ha : T a = a)
    (i : Fin (3 ^ k)) :
    a (j * 3 ^ k + i) = Tblock k (fun r : Fin (2 ^ k) => a (j * 2 ^ k + r)) i := by
  calc
    _ = (T^[k]) a (j * 3 ^ k + i) := by rw [Function.iterate_fixed ha k]
    _ = (T^[k]) (fun n => a (j * 2 ^ k + n)) i := Tpower_shift k j a i
    _ = _ := by
      apply Tpower_local k 1 _ _ ?_ i (by simp)
      intro n hn
      have hn' : n < 2 ^ k := by simpa using hn
      simp [hn']

private theorem aligned_functional (k j : ℕ) (a : ℕ → ℤ) (ha : T a = a) :
    (∑ n ∈ range (3 ^ k), a (j * 3 ^ k + n)) =
      ∑ r : Fin (2 ^ k), dNat k r * a (j * 2 ^ k + r) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [aligned_block_identity k j a ha]
  exact Tblock_sum k _

private theorem aligned_square_bound (k j : ℕ) (a : ℕ → ℤ) (ha : T a = a)
    (ha_sq : ∀ n, (a n) ^ 2 = 1) :
    (∑ n ∈ range (3 ^ (k + 1)), a (j * 3 ^ (k + 1) + n)) ^ 2 ≤ (2 : ℤ) ^ (k + 1) * 3 ^ k := by
  rw [aligned_functional _ _ a ha]
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin (2 ^ (k + 1))))
    (fun r => dNat (k + 1) r) (fun r => a (j * 2 ^ (k + 1) + r))
  have he : (∑ r : Fin (2 ^ (k + 1)), (dNat (k + 1) r) ^ 2) = E (k + 1) := by
    exact Fin.sum_univ_eq_sum_range (fun r : ℕ => (dNat (k + 1) r) ^ 2) (2 ^ (k + 1))
  simp only [ha_sq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
  rw [he, energy_succ] at hc
  simpa [mul_comm] using hc

private noncomputable def B (k : ℕ) : ℝ := Real.sqrt ((2 : ℝ) ^ k * 3 ^ (k - 1))

private theorem aligned_block_bound (k j : ℕ) (a : ℕ → ℤ) (ha : T a = a)
    (ha_sq : ∀ n, (a n) ^ 2 = 1) :
    |((∑ n ∈ range (3 ^ (k + 1)), a (j * 3 ^ (k + 1) + n)) : ℝ)| ≤ B (k + 1) := by
  have h := aligned_square_bound k j a ha ha_sq
  have h' : (((∑ n ∈ range (3 ^ (k + 1)), a (j * 3 ^ (k + 1) + n)) : ℝ)) ^ 2 ≤
      (2 : ℝ) ^ (k + 1) * 3 ^ k := by exact_mod_cast h
  simpa [B] using Real.abs_le_sqrt h'

private theorem prefix_bound (a : ℕ → ℤ) (ha_abs : ∀ n, |a n| = 1)
    (m : ℕ) (b : ℝ)
    (hb : ∀ j, |((∑ i ∈ range m, a (j * m + i)) : ℝ)| ≤ b) (q r : ℕ) :
    |((∑ n ∈ range (q * m + r), a n) : ℝ)| ≤ (q : ℝ) * b + r := by
  rw [sum_range_add, sum_blocks]
  have hr : |∑ i ∈ range r, a (q * m + i)| ≤ (r : ℤ) := by
    calc
      _ ≤ ∑ i ∈ range r, |a (q * m + i)| := abs_sum_le_sum_abs _ _
      _ = _ := by simp [ha_abs]
  have hr' : |((∑ i ∈ range r, a (q * m + i)) : ℝ)| ≤ (r : ℝ) := by exact_mod_cast hr
  calc
    _ ≤ |∑ j ∈ range q, ((∑ i ∈ range m, a (j * m + i)) : ℝ)| +
        |((∑ i ∈ range r, a (q * m + i)) : ℝ)| := abs_add_le _ _
    _ ≤ (∑ j ∈ range q, |((∑ i ∈ range m, a (j * m + i)) : ℝ)|) + (r : ℝ) :=
      add_le_add (abs_sum_le_sum_abs _ _) hr'
    _ ≤ (q : ℝ) * b + r := by
      refine add_le_add ?_ le_rfl
      calc
        _ ≤ ∑ j ∈ range q, b := sum_le_sum (fun j _ => hb j)
        _ = _ := by simp

private theorem prefix_ratio_bound (a : ℕ → ℤ) (ha_abs : ∀ n, |a n| = 1)
    (m : ℕ) (hm : 0 < m) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ j, |((∑ i ∈ range m, a (j * m + i)) : ℝ)| ≤ b)
    (N : ℕ) (hN : 0 < N) :
    |((∑ n ∈ range N, a n) : ℝ) / N| ≤ b / m + (m : ℝ) / N := by
  let q := N / m
  let r := N%m
  have hdecomp : q * m + r = N := by simpa [q, r, Nat.mul_comm] using Nat.div_add_mod N m
  have hr : r < m := Nat.mod_lt _ hm
  have hprefix := prefix_bound a ha_abs m b hb q r
  rw [hdecomp] at hprefix
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hqm : (q : ℝ) * m ≤ N := by exact_mod_cast (by omega : q * m ≤ N)
  have hqb : (q : ℝ) * b ≤ (N : ℝ) * (b / m) := by
    calc
      _ = ((q : ℝ) * m) * (b / m) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hqm (div_nonneg hb0 hm'.le)
  have hr' : (r : ℝ) ≤ m := by exact_mod_cast hr.le
  rw [abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).2
  have hid : (b / (m : ℝ) + (m : ℝ) / N) * N = (N : ℝ) * (b / m) + m := by field_simp
  rw [hid]
  exact hprefix.trans (add_le_add hqb hr')

private theorem B_ratio_formula (k : ℕ) : B (k + 1) / (3 : ℝ) ^ (k + 1) =
    Real.sqrt ((2 / 9 : ℝ) * (2 / 3 : ℝ) ^ k) := by
  have hs : (B (k + 1) / (3 : ℝ) ^ (k + 1)) ^ 2 = (2 / 9 : ℝ) * (2 / 3 : ℝ) ^ k := by
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1) * 3 ^ k := by positivity
    simp only [B, Nat.add_sub_cancel, div_pow, Real.sq_sqrt hp]
    rw [pow_succ, pow_succ]
    field_simp
    ring
  have hr : (Real.sqrt ((2 / 9 : ℝ) * (2 / 3 : ℝ) ^ k)) ^ 2 = (2 / 9 : ℝ) * (2 / 3 : ℝ) ^ k :=
    Real.sq_sqrt (by positivity)
  have h0 : 0 ≤ B (k + 1) / (3 : ℝ) ^ (k + 1) := by unfold B; positivity
  have h1 := Real.sqrt_nonneg ((2 / 9 : ℝ) * (2 / 3 : ℝ) ^ k)
  nlinarith

private theorem B_ratio_tendsto : Tendsto (fun k : ℕ => B (k + 1) / (3 : ℝ) ^ (k + 1))
    atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)
  have h' := (h.const_mul (2 / 9 : ℝ)).sqrt
  simpa only [mul_zero, Real.sqrt_zero, ← B_ratio_formula] using h'

end D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency
namespace D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency
open Finset Filter

private theorem signed_mean_tendsto (a : ℕ → ℤ) (ha : T a = a)
    (ha_sq : ∀ n, (a n) ^ 2 = 1) (ha_abs : ∀ n, |a n| = 1) :
    Tendsto (fun N : ℕ => ((∑ n ∈ range N, a n) : ℝ) / N) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro eps heps
  have heps2 : (0 : ℝ) < eps / 2 := by linarith
  obtain ⟨k, hk⟩ := (B_ratio_tendsto.eventually (gt_mem_nhds heps2)).exists
  have htail : Tendsto (fun N : ℕ => (3 : ℝ) ^ (k + 1) / N) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (htail.eventually (gt_mem_nhds heps2))
  refine ⟨max N0 1, ?_⟩
  intro N hN
  have hNpos : 0 < N := by omega
  have ht := hN0 N (le_trans (le_max_left _ _) hN)
  have hbound := prefix_ratio_bound a ha_abs (3 ^ (k + 1)) (by positivity)
    (B (k + 1)) (Real.sqrt_nonneg _) (fun j => aligned_block_bound k j a ha ha_sq) N hNpos
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hbound
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt hbound (by linarith)

private theorem signed_count_identity (x : ℕ → Bool) (N : ℕ) :
    (∑ n ∈ range N, sign (x n)) =
      (N : ℤ) - 2 * (((range N).filter (fun n => x n = true)).card : ℤ) := by
  calc
    _ = ∑ n ∈ range N, (1 - 2 * (if x n = true then 1 else 0) : ℤ) := by
      apply sum_congr rfl
      intro n hn
      cases hx : x n <;> simp [sign]
    _ = _ := by
      rw [sum_sub_distrib, ← mul_sum]
      simp

private theorem bool_density_of_signed_mean (x : ℕ → Bool)
    (hx : Tendsto (fun N : ℕ => ((∑ n ∈ range N, sign (x n)) : ℝ) / N)
      atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (((range N).filter (fun n => x n = true)).card : ℝ) / N)
      atTop (nhds (1 / 2)) := by
  have h : Tendsto (fun N : ℕ => (1 / 2 : ℝ) - (((∑ n ∈ range N, sign (x n)) : ℝ) / N) / 2)
      atTop (nhds (1 / 2)) := by
    simpa using tendsto_const_nhds.sub (hx.div_const 2)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : ((∑ n ∈ range N, sign (x n)) : ℝ) =
      (N : ℝ) - 2 * (((range N).filter (fun n => x n = true)).card : ℝ) := by
    exact_mod_cast signed_count_identity x N
  rw [hid]
  field_simp
  ring

private theorem fixed_point_density (x : ℕ → Bool)
    (hx : ∀ n (r : Fin 3), x (3 * n + r) = kappaTM (x (2 * n)) (x (2 * n + 1)) r) :
    Tendsto (fun N : ℕ => (((range N).filter (fun n => x n = true)).card : ℝ) / N)
      atTop (nhds (1 / 2)) := by
  apply bool_density_of_signed_mean x
  exact signed_mean_tendsto ((fun n => sign (x n))) (signed_fixed x hx)
    (fun n => sign_sq (x n)) (fun n => sign_abs (x n))

theorem result : claim := fixed_point_density tmFixed tmFixed_fixed

end D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency

#print axioms D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency.result

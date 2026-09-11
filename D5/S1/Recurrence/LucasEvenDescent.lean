/- GID: D5/S1/Recurrence/LucasEvenDescent
   generality: G
   mirror-B: D5/B/S1/Recurrence/LucasEvenDescent
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: Lucas doubling descends to zero or half-modulus at odd half-entry indices. -/

import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
The companion matrix defines the two-parameter Lucas sequence at every integer index when
q is a unit. The result addresses Conjecture 5.2 of Fiebig--Mbirika--Spilker,
arXiv:2408.14632v2, under the paper's coprime-modulus convention.
The modular implication needs only a positive even modulus and a unit q, in addition to
the two doubling hypotheses. None of the paper's standing restrictions on the parameters
are needed: nonzero parameters, coprimality of p and q, nondegeneracy, or parity of p.
The local library supplies matrix determinant and integer-power identities, cyclic subgroup
theory, finite orders, and `ZMod.neg_eq_self_iff`; the Lucas identities are derived here.
All declarations are general definitions and proofs; this module has no bounded enumeration,
checker, numeric reduction, or certified instance.
-/

namespace D5.S1.Recurrence.LucasEvenDescent

open Matrix

variable {R : Type*} [CommRing R]

/-- The invertible Lucas companion matrix; its determinant is the unit `q`. -/
def companion (p : R) (q : Rˣ) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![p, -(q : R); 1, 0]
  inv := !![0, 1; -(↑q⁻¹ : R), ↑q⁻¹ * p]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The Lucas sequence at integer indices, reduced in its coefficient ring. -/
def lucasU (p : R) (q : Rˣ) (n : ℤ) : R :=
  (↑(companion p q ^ n) : Matrix (Fin 2) (Fin 2) R) 1 0

private def powerMatrix (p : R) (q : Rˣ) (n : ℤ) : Matrix (Fin 2) (Fin 2) R :=
  ↑(companion p q ^ n)

private theorem power_add (p : R) (q : Rˣ) (a b : ℤ) :
    powerMatrix p q (a + b) = powerMatrix p q a * powerMatrix p q b := by
  simp only [powerMatrix, _root_.zpow_add, Units.val_mul]

private theorem power_shape (p : R) (q : Rˣ) (n : ℤ) :
    powerMatrix p q n =
      !![lucasU p q (n + 1), -(q : R) * lucasU p q n;
         lucasU p q n, lucasU p q (n + 1) - p * lucasU p q n] := by
  have hc : powerMatrix p q n * (companion p q : Matrix (Fin 2) (Fin 2) R) =
      (companion p q : Matrix (Fin 2) (Fin 2) R) * powerMatrix p q n := by
    exact congrArg Units.val (Commute.zpow_self (companion p q) n).eq
  have h01 : -(powerMatrix p q n 1 0 * (q : R)) = powerMatrix p q n 0 1 := by
    simpa [companion, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 1) hc
  have h10 : powerMatrix p q n 1 0 * p + powerMatrix p q n 1 1 =
      powerMatrix p q n 0 0 := by
    simpa [companion, Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 0) hc
  have hone : powerMatrix p q 1 = !![p, -(q : R); 1, 0] := by
    simp [powerMatrix, companion]
  have hs : powerMatrix p q (1 + n) 1 0 = powerMatrix p q n 0 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 0) (power_add p q 1 n)
    rw [hone] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hb : lucasU p q (n + 1) = powerMatrix p q n 0 0 := by
    simpa only [lucasU, powerMatrix, add_comm] using hs
  ext i j
  fin_cases i <;> fin_cases j
  · exact hb.symm
  · change _ = -(q : R) * powerMatrix p q n 1 0
    simpa [mul_comm] using h01.symm
  · rfl
  · change powerMatrix p q n 1 1 = lucasU p q (n + 1) - p * powerMatrix p q n 1 0
    rw [hb]
    linear_combination h10

/-- Initial values and recurrence, including negative indices. -/
theorem lucas_recurrence (p : R) (q : Rˣ) :
    lucasU p q 0 = 0 ∧ lucasU p q 1 = 1 ∧
      ∀ n : ℤ, lucasU p q (n + 2) = p * lucasU p q (n + 1) - ↑q * lucasU p q n := by
  refine ⟨by simp [lucasU], by simp [lucasU, companion], ?_⟩
  intro n
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 0 0)
    (power_add p q n 1)
  rw [power_shape p q (n + 1), power_shape p q n] at h
  simpa [powerMatrix, companion, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, sub_eq_add_neg,
    show n + 1 + 1 = n + 2 by omega] using h

private theorem determinant_identity (p : R) (q : Rˣ) (n : ℤ) :
    lucasU p q (n + 1) ^ 2 - p * lucasU p q n * lucasU p q (n + 1) +
      ↑q * lucasU p q n ^ 2 = (↑(q ^ n) : R) := by
  have hd : Units.map (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) R →* R)
      (companion p q) = q := by
    ext
    simp [companion, Matrix.det_fin_two]
  have h := congrArg Units.val
    (map_zpow (Units.map (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) R →* R))
      (companion p q) n)
  rw [hd] at h
  change (powerMatrix p q n).det = _ at h
  rw [power_shape, Matrix.det_fin_two] at h
  convert h using 1
  simp
  ring

private theorem doubling (p : R) (q : Rˣ) (n : ℤ) :
    lucasU p q (2 * n) = 2 * lucasU p q n * lucasU p q (n + 1) - p * lucasU p q n ^ 2 ∧
    lucasU p q (2 * n + 1) = lucasU p q (n + 1) ^ 2 - ↑q * lucasU p q n ^ 2 := by
  have h := power_add p q n n
  rw [← two_mul, power_shape p q (2 * n), power_shape p q n] at h
  constructor
  · have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 0) h
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hh
    linear_combination hh
  · have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 0 0) h
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hh
    linear_combination hh

/-- The two doubling hypotheses force two-torsion, over any commutative ring. -/
theorem two_mul_lucas_eq_zero (p : R) (q : Rˣ) (n : ℤ)
    (h0 : lucasU p q (2 * n) = 0)
    (h1 : lucasU p q (2 * n + 1) = (↑(q ^ n) : R)) :
    2 * lucasU p q n = 0 := by
  obtain ⟨hd0, hd1⟩ := doubling p q n
  have hdet := determinant_identity p q n
  rw [h0] at hd0
  rw [h1] at hd1
  have h : (2 * lucasU p q n) * (↑(q ^ n) : R) = 0 := by
    linear_combination
      -lucasU p q (n + 1) * hd0 -
      lucasU p q n * hdet + lucasU p q n * hd1
  exact (q ^ n).mul_left_eq_zero.mp h

private theorem addition (p : R) (q : Rˣ) (a b : ℤ) :
    lucasU p q (a + b) = lucasU p q a * lucasU p q (b + 1) +
      (lucasU p q (a + 1) - p * lucasU p q a) * lucasU p q b := by
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 1 0) (power_add p q a b)
  rw [power_shape p q a, power_shape p q b] at h
  simpa [lucasU, powerMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h

private def zeroIndices (p : R) (q : Rˣ) : AddSubgroup ℤ where
  carrier := {n | lucasU p q n = 0}
  zero_mem' := (lucas_recurrence p q).1
  add_mem' := by
    intro a b ha hb
    change lucasU p q (a + b) = 0
    rw [addition, ha, hb]
    ring
  neg_mem' := by
    intro a ha
    change lucasU p q (-a) = 0
    have hd := determinant_identity p q a
    change lucasU p q a = 0 at ha
    simp only [ha, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0),
      sub_zero, add_zero] at hd
    have hu : IsUnit (lucasU p q (a + 1)) :=
      (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (hd ▸ (q ^ a).isUnit)
    have hh := addition p q (-a) a
    rw [neg_add_cancel, (lucas_recurrence p q).1, ha, mul_zero, add_zero] at hh
    exact hu.mul_left_eq_zero.mp hh.symm

private theorem exists_generator (p : R) (q : Rˣ) :
    ∃ g : ℤ, AddSubgroup.zmultiples g = zeroIndices p q :=
  (zeroIndices p q).isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance

/-- The nonnegative generator of the integer zero indices; `entry_point_spec` proves
that it is the least positive zero index over a finite coefficient ring. -/
noncomputable def entryPoint (p : R) (q : Rˣ) : ℕ :=
  (Classical.choose (exists_generator p q)).natAbs

/-- Zero indices are precisely the integer multiples of the entry point. -/
theorem lucas_eq_zero_iff_entry_dvd (p : R) (q : Rˣ) (n : ℤ) :
    lucasU p q n = 0 ↔ (entryPoint p q : ℤ) ∣ n := by
  have hg := Classical.choose_spec (exists_generator p q)
  change n ∈ zeroIndices p q ↔ _
  rw [← hg, Int.mem_zmultiples_iff]
  simp [entryPoint]

/-- Existence and the defining least-positive-index property of the entry point. -/
theorem entry_point_spec [Finite R] (p : R) (q : Rˣ) :
    0 < entryPoint p q ∧ lucasU p q (entryPoint p q) = 0 ∧
      ∀ r : ℕ, 0 < r → lucasU p q r = 0 → entryPoint p q ≤ r := by
  have hz : lucasU p q (orderOf (companion p q)) = 0 := by
    simp [lucasU, pow_orderOf_eq_one]
  have hp := orderOf_pos (companion p q)
  have he : 0 < entryPoint p q := by
    have hd := (lucas_eq_zero_iff_entry_dvd p q _).mp hz
    have hn : entryPoint p q ∣ orderOf (companion p q) := by exact_mod_cast hd
    exact Nat.pos_of_dvd_of_pos hn hp
  refine ⟨he, (lucas_eq_zero_iff_entry_dvd p q _).mpr (dvd_refl _), ?_⟩
  intro r hr hz
  have hd := (lucas_eq_zero_iff_entry_dvd p q _).mp hz
  exact Nat.le_of_dvd hr (by exact_mod_cast hd)

private theorem half_index (e : ℕ) (n : ℤ) (hd : (e : ℤ) ∣ 2 * n)
    (hn : ¬ (e : ℤ) ∣ n) : Even e ∧ ∃ c : ℤ, Odd c ∧ n = c * ((e : ℤ) / 2) := by
  obtain ⟨c, hc⟩ := hd
  have hco : Odd c := by
    rw [← Int.not_even_iff_odd]
    rintro ⟨k, hk⟩
    apply hn
    refine ⟨k, ?_⟩
    have hh : 2 * n = 2 * ((e : ℤ) * k) := by
      rw [hc, hk]
      ring
    omega
  have he : Even (e : ℤ) := by
    have hprod : Even ((e : ℤ) * c) := by rw [← hc]; exact even_two_mul n
    exact (Int.even_mul.mp hprod).resolve_right (Int.not_even_iff_odd.mpr hco)
  refine ⟨by exact_mod_cast he, c, hco, ?_⟩
  have hh := Int.ediv_mul_cancel (even_iff_two_dvd.mp he)
  have heq : 2 * n = 2 * (c * ((e : ℤ) / 2)) := by
    linear_combination hc - c * hh
  omega

private theorem half_modulus_ne_zero (m : ℕ) (hm : 0 < m) (he : Even m) :
    ((m / 2 : ℕ) : ZMod m) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  have hp : 0 < m / 2 := by obtain ⟨k, hk⟩ := he; omega
  have hl : m / 2 < m := Nat.div_lt_self hm (by decide)
  exact fun h => (Nat.le_of_dvd hp h).not_gt hl

/-- A strengthening of Conjecture 5.2 without a parity hypothesis on p:
exactly one alternative holds, with an odd integer multiple of
half the entry point in the nonzero alternative. The index ranges over all integers. -/
theorem lucas_even_descent (m : ℕ) (hm : 0 < m) (hmEven : Even m)
    (p : ZMod m) (q : (ZMod m)ˣ) (n : ℤ)
    (h0 : lucasU p q (2 * n) = 0)
    (h1 : lucasU p q (2 * n + 1) = (↑(q ^ n) : ZMod m)) :
    Xor (lucasU p q n = 0)
      (lucasU p q n = ((m / 2 : ℕ) : ZMod m) ∧ Even (entryPoint p q) ∧
        ∃ c : ℤ, Odd c ∧ n = c * ((entryPoint p q : ℤ) / 2)) := by
  let : NeZero m := ⟨by omega⟩
  have ht := two_mul_lucas_eq_zero p q n h0 h1
  have hh : lucasU p q n = 0 ∨ 2 * (lucasU p q n).val = m := by
    apply (ZMod.neg_eq_self_iff _).mp
    rw [neg_eq_iff_add_eq_zero, ← two_mul]
    exact ht
  have hne := half_modulus_ne_zero m hm hmEven
  rcases hh with hz | hh
  · exact Or.inl ⟨hz, fun h => hne (h.1.symm.trans hz)⟩
  · have hv : lucasU p q n = ((m / 2 : ℕ) : ZMod m) := by
      have hval : (lucasU p q n).val = m / 2 := by omega
      rw [← hval, ZMod.natCast_zmod_val]
    have hn : lucasU p q n ≠ 0 := by rw [hv]; exact hne
    have hi := half_index (entryPoint p q) n
      ((lucas_eq_zero_iff_entry_dvd p q _).mp h0)
      (fun h => hn ((lucas_eq_zero_iff_entry_dvd p q _).mpr h))
    exact Or.inr ⟨⟨hv, hi⟩, hn⟩

/-- Integer parameters with the paper's load-bearing coprimality hypothesis.
The unit lift specifies modular negative powers without dividing integers.
The parity hypothesis on p is retained for fidelity to the cited statement and is not used
by the proof. -/
theorem conjecture_five_two (p q : ℤ) (m : ℕ) (hm : 0 < m)
    (_hp : Even p) (hmEven : Even m) (hqm : Int.gcd q (m : ℤ) = 1) (n : ℤ) :
    let Q := ZMod.unitOfIsCoprime q (Int.isCoprime_iff_gcd_eq_one.mpr hqm)
    lucasU (p : ZMod m) Q (2 * n) = 0 →
    lucasU (p : ZMod m) Q (2 * n + 1) = (↑(Q ^ n) : ZMod m) →
    Xor (lucasU (p : ZMod m) Q n = 0)
      (lucasU (p : ZMod m) Q n = ((m / 2 : ℕ) : ZMod m) ∧
        Even (entryPoint (p : ZMod m) Q) ∧
        ∃ c : ℤ, Odd c ∧ n = c * ((entryPoint (p : ZMod m) Q : ℤ) / 2)) := by
  dsimp only
  exact lucas_even_descent m hm hmEven _ _ _

#print axioms companion
#print axioms lucasU
#print axioms lucas_recurrence
#print axioms two_mul_lucas_eq_zero
#print axioms entryPoint
#print axioms lucas_eq_zero_iff_entry_dvd
#print axioms entry_point_spec
#print axioms lucas_even_descent
#print axioms conjecture_five_two

end D5.S1.Recurrence.LucasEvenDescent

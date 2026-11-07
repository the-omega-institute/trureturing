/- GID: D5/S1/Recurrence/Invariants/HannaA320949ModThree
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaA320949ModThree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Newton reciprocity and contraction prove the OEIS A320949 mod-three conjecture. -/

/-
proof_shape: result: bind-only; consumer: settling result.
proof_shape: all private theorem/lemma declarations: bind-only; consumers: downstream declarations on the result path, as listed by the source proof.
escape_witness: none (external open-problem-resolution admission).
admission_basis: open-problem-resolution (#21890; Proved)
Direct frozen dependencies: PowerSeriesNormalizedContraction.exists_unique_fixed; AbsoluteReciprocalGeometricParity.agree_inv; UnitReversionSquareParity.Agree, agree_pow, agree_mul, and agree_X; ContinuedFractionOddSquare.map_inverse and inverse_one; CompositionalSquareDyadicDenominators.coeff_subst_sum.
The public source definitions term, IsGF, and claim retain their literal preregistered expressions; all auxiliary declarations are private and consumed by result.
Escape audit unfinished: issue #22543; registration is pending CI reading after the Stage-B freeze.
-/

import D5.S1.Recurrence.Residue.ContinuedFractionOddSquare
import D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Basic
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
set_option maxRecDepth 2048
set_option maxHeartbeats 50000

namespace D5.S1.Recurrence.Invariants.HannaA320949ModThree
open Finset Function Polynomial fwdDiff

private noncomputable def newtonCoeff (k m : ℕ) : ℤ :=
  (fwdDiff 1)^[m] (fun j : ℕ => ((j ^ 2).choose k : ℤ)) 0

private theorem finite_newton (f : ℕ → ℤ) (d : ℕ)
    (hd : ∀ m, d < m → (fwdDiff 1)^[m] f 0 = 0) (j : ℕ) :
    f j = ∑ m ∈ range (d + 1), (j.choose m : ℤ) * (fwdDiff 1)^[m] f 0 := by
  have hj := shift_eq_sum_fwdDiff_iter (1 : ℕ) f j 0
  simp only [nsmul_eq_mul, zero_add, mul_one, Nat.cast_id] at hj
  rw [hj]
  by_cases h : j ≤ d
  · apply Finset.sum_subset (Finset.range_mono (by omega))
    intro m hm hnot
    have hmj : j < m := by simp only [mem_range] at hnot; omega
    rw [Nat.choose_eq_zero_of_lt hmj, Int.natCast_zero, zero_mul]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro m hm hnot
    rw [hd m (by simp only [mem_range] at hnot; omega), mul_zero]


private theorem squareChoosePolynomial_eval (k j : ℕ) :
    (Ring.choose (Polynomial.X ^ 2 : ℚ[X]) k).eval (j : ℚ) =
      ((j ^ 2).choose k : ℚ) := by
  have h := Ring.map_choose (Polynomial.evalRingHom (j : ℚ))
    (Polynomial.X ^ 2 : ℚ[X]) k
  simp only [Polynomial.coe_evalRingHom] at h
  simpa only [eval_pow, eval_X, ← Nat.cast_pow, Ring.choose_natCast] using h

private theorem squareChoosePolynomial_degree (k : ℕ) :
    (Ring.choose (Polynomial.X ^ 2 : ℚ[X]) k).natDegree ≤ 2 * k := by
  have h : Ring.choose (Polynomial.X ^ 2 : ℚ[X]) k =
      Polynomial.C (k.factorial : ℚ)⁻¹ *
        (descPochhammer ℚ k).comp (Polynomial.X ^ 2) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective
      (Nat.cast_injective : Function.Injective (fun j : ℕ => (j : ℚ)))).mono
    rintro t ⟨j, rfl⟩
    simp only [Set.mem_ofPred_eq, eval_mul, eval_C, eval_comp, eval_pow, eval_X]
    have hm := Ring.map_choose (Polynomial.evalRingHom (j : ℚ))
      (Polynomial.X ^ 2 : ℚ[X]) k
    simp only [Polynomial.coe_evalRingHom, eval_pow, eval_X] at hm
    rw [hm, Ring.choose_eq_smul, smul_eq_mul,
      Polynomial.descPochhammer_smeval_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval,
      descPochhammer_eval_eq_ascPochhammer]
  rw [h]
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  simp
  omega

private theorem cast_forward_difference (f : ℕ → ℤ) (P : ℚ[X])
    (hf : ∀ j : ℕ, (f j : ℚ) = P.eval (j : ℚ)) (m : ℕ) :
    (((fwdDiff (1 : ℕ))^[m] f 0 : ℤ) : ℚ) =
      (fwdDiff (1 : ℚ))^[m] P.eval 0 := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  push_cast
  apply sum_congr rfl
  intro j hj
  simp only [zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul]
  rw [← hf]
  push_cast
  rfl

private theorem newtonCoeff_high (k m : ℕ) (hm : 2 * k < m) :
    newtonCoeff k m = 0 := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_zero]
  change (((fwdDiff (1 : ℕ))^[m] (fun j : ℕ => ((j ^ 2).choose k : ℤ)) 0 : ℤ) : ℚ) = 0
  rw [cast_forward_difference _ (Ring.choose (Polynomial.X ^ 2 : ℚ[X]) k)
    (fun j => by simpa using (squareChoosePolynomial_eval k j).symm)]
  rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    ((squareChoosePolynomial_degree k).trans_lt hm)]
  rfl

private theorem squareChoose_newton (k j : ℕ) :
    ((j ^ 2).choose k : ℤ) =
      ∑ m ∈ range (2 * k + 1), (j.choose m : ℤ) * newtonCoeff k m := by
  exact finite_newton _ (2 * k) (newtonCoeff_high k) j

private theorem choosePolynomial_eval (m : ℕ) (t : ℚ) :
    (Ring.choose (Polynomial.X : ℚ[X]) m).eval t = Ring.choose t m := by
  simpa only [Polynomial.coe_evalRingHom, eval_X] using
    Ring.map_choose (Polynomial.evalRingHom t) (Polynomial.X : ℚ[X]) m

private theorem squareChoosePolynomial_expansion (k : ℕ) :
    Ring.choose (Polynomial.X ^ 2 : ℚ[X]) k =
      ∑ m ∈ range (2 * k + 1), Polynomial.C (newtonCoeff k m : ℚ) *
        Ring.choose (Polynomial.X : ℚ[X]) m := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective : Function.Injective (fun j : ℕ => (j : ℚ)))).mono
  rintro t ⟨j, rfl⟩
  simp only [Set.mem_setOf_eq, eval_finset_sum, eval_mul, eval_C,
    choosePolynomial_eval, Ring.choose_natCast]
  rw [squareChoosePolynomial_eval]
  have h := congrArg (fun z : ℤ => (z : ℚ)) (squareChoose_newton k j)
  push_cast at h
  simpa only [mul_comm] using h

private theorem newton_expansion_even (k : ℕ) (t : ℤ) :
    ∑ m ∈ range (2 * k + 1), newtonCoeff k m * Ring.choose (-t) m =
      ∑ m ∈ range (2 * k + 1), newtonCoeff k m * Ring.choose t m := by
  apply Int.cast_injective (α := ℚ)
  have hm (u : ℤ) (m : ℕ) : ((Ring.choose u m : ℤ) : ℚ) =
      Ring.choose (u : ℚ) m := Ring.map_choose (Int.castRingHom ℚ) u m
  simp only [Int.cast_sum, Int.cast_mul, hm, Int.cast_neg]
  have h := congrArg (fun p : ℚ[X] => p.eval (t : ℚ)) (squareChoosePolynomial_expansion k)
  have hn := congrArg (fun p : ℚ[X] => p.eval (-(t : ℚ))) (squareChoosePolynomial_expansion k)
  simp only [eval_finset_sum, eval_mul, eval_C, choosePolynomial_eval] at h hn
  have hp : (Ring.choose (Polynomial.X ^ 2 : ℚ[X]) k).eval (-(t : ℚ)) =
      (Ring.choose (Polynomial.X ^ 2 : ℚ[X]) k).eval (t : ℚ) := by
    have hn := Ring.map_choose (Polynomial.evalRingHom (-(t : ℚ)))
      (Polynomial.X ^ 2 : ℚ[X]) k
    have ht := Ring.map_choose (Polynomial.evalRingHom (t : ℚ))
      (Polynomial.X ^ 2 : ℚ[X]) k
    simp only [Polynomial.coe_evalRingHom, eval_pow, eval_X, neg_sq] at hn ht
    exact hn.trans ht.symm
  rw [← hn, ← h]
  exact hp

end D5.S1.Recurrence.Invariants.HannaA320949ModThree

set_option maxHeartbeats 50000
set_option maxRecDepth 2048
namespace D5.S1.Recurrence.Invariants.HannaA320949ModThree
open Finset Function fwdDiff

private theorem negative_choose_nat (j m : ℕ) :
    Ring.choose (-(j : ℤ)) (m + 1) =
      (-1 : ℤ) ^ (m + 1) * Ring.choose ((j : ℤ) + m) (m + 1) := by
  rw [Ring.choose_neg]
  simp only [Int.coe_negOnePow_natCast, Units.smul_def, zsmul_eq_mul]
  congr 2
  omega


private theorem forward_nat_choose_iter (a r k : ℕ) :
    (fwdDiff 1)^[r] (fun j : ℕ => ((j + a).choose (r + k) : ℤ)) 0 =
      (a.choose k : ℤ) := by
  rw [fwdDiff_iter_comp_add (1 : ℕ) (fun j : ℕ => (j.choose (r + k) : ℤ)) a r 0]
  simpa using congrFun (fwdDiff_iter_choose (R := ℤ) k r) a

private theorem forward_nat_choose_high (a r k : ℕ) (hr : k < r) :
    (fwdDiff 1)^[r] (fun j : ℕ => ((j + a).choose k : ℤ)) 0 = 0 := by
  rw [fwdDiff_iter_comp_add (1 : ℕ) (fun j : ℕ => (j.choose k : ℤ)) a r 0]
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_lt hr
  rw [show k + s + 1 = (s + 1) + k by omega, iterate_add_apply]
  have hh := fwdDiff_iter_choose (R := ℤ) 0 k
  simp only [Nat.add_zero, Nat.choose_zero_right, Int.natCast_one] at hh
  rw [hh, iterate_succ_apply, fwdDiff_const]
  simp [fwdDiff_iter_eq_sum_shift]

private theorem negative_choose_difference (m r : ℕ) (hr : r ≤ m + 1) :
    (fwdDiff 1)^[r] (fun j : ℕ => Ring.choose (-(j : ℤ)) (m + 1)) 0 =
      (-1 : ℤ) ^ (m + 1) * (m.choose (m + 1 - r) : ℤ) := by
  have he : (fun j : ℕ => Ring.choose (-(j : ℤ)) (m + 1)) =
      (-1 : ℤ) ^ (m + 1) • (fun j : ℕ => ((j + m).choose (m + 1) : ℤ)) := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, negative_choose_nat, ← Nat.cast_add,
      Ring.choose_natCast]
  rw [he, fwdDiff_iter_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 1
  have h := forward_nat_choose_iter m r (m + 1 - r)
  simpa only [Nat.add_sub_of_le hr] using h

private theorem negative_choose_difference_high (m r : ℕ) (hr : m + 1 < r) :
    (fwdDiff 1)^[r] (fun j : ℕ => Ring.choose (-(j : ℤ)) (m + 1)) 0 = 0 := by
  have he : (fun j : ℕ => Ring.choose (-(j : ℤ)) (m + 1)) =
      (-1 : ℤ) ^ (m + 1) • (fun j : ℕ => ((j + m).choose (m + 1) : ℤ)) := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, negative_choose_nat, ← Nat.cast_add,
      Ring.choose_natCast]
  rw [he, fwdDiff_iter_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul, forward_nat_choose_high m r (m + 1) hr, mul_zero]

private noncomputable def newtonMass (d : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ r ∈ range (d + 1), (fwdDiff 1)^[r] f 0

private theorem negative_choose_mass (d m : ℕ) (hm : m + 1 ≤ d) :
    newtonMass d (fun j : ℕ => Ring.choose (-(j : ℤ)) (m + 1)) =
      (-1 : ℤ) ^ (m + 1) * (2 : ℤ) ^ m := by
  unfold newtonMass
  have hs : ∑ r ∈ range (d + 1),
      (fwdDiff 1)^[r] (fun j : ℕ => Ring.choose (-(j : ℤ)) (m + 1)) 0 =
      ∑ r ∈ range (m + 2),
      (fwdDiff 1)^[r] (fun j : ℕ => Ring.choose (-(j : ℤ)) (m + 1)) 0 := by
    symm
    apply sum_subset (range_mono (by omega))
    intro r hr hnot
    exact negative_choose_difference_high m r (by simp only [mem_range] at hnot; omega)
  rw [hs]
  calc
    _ = ∑ r ∈ range (m + 2),
        (-1 : ℤ) ^ (m + 1) * (m.choose (m + 1 - r) : ℤ) := by
      apply sum_congr rfl
      intro r hr
      exact negative_choose_difference m r (by simp only [mem_range] at hr; omega)
    _ = (-1 : ℤ) ^ (m + 1) * ∑ r ∈ range (m + 2), (m.choose (m + 1 - r) : ℤ) :=
      (mul_sum _ _ _).symm
    _ = (-1 : ℤ) ^ (m + 1) * ∑ r ∈ range (m + 2), (m.choose r : ℤ) := by
      congr 1
      rw [← sum_range_reflect]
      apply sum_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      congr 2 <;> omega
    _ = (-1 : ℤ) ^ (m + 1) * (2 : ℤ) ^ m := by
      rw [show m + 2 = (m + 1) + 1 by omega, sum_range_succ]
      simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m), Int.natCast_zero, add_zero]
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]


private theorem positive_choose_mass (d m : ℕ) (hm : m ≤ d) :
    newtonMass d (fun j : ℕ => (j.choose m : ℤ)) = 1 := by
  simp [newtonMass, fwdDiff_iter_choose_zero, hm]

private theorem newtonMass_sum (d N : ℕ) (c : ℕ → ℤ) (f : ℕ → ℕ → ℤ) :
    newtonMass d (fun j => ∑ m ∈ range N, c m * f m j) =
      ∑ m ∈ range N, c m * newtonMass d (f m) := by
  have he : (fun j => ∑ m ∈ range N, c m * f m j) =
      ∑ m ∈ range N, c m • f m := by
    exact (sum_fn (range N) fun m => c m • f m).symm
  rw [he]
  simp only [newtonMass, fwdDiff_iter_finsetSum, fwdDiff_iter_const_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]

private theorem even_newton_congruence (d : ℕ) (c : ℕ → ℤ)
    (he : ∀ j : ℕ,
      ∑ m ∈ range (d + 1), c m * Ring.choose (-(j : ℤ)) m =
      ∑ m ∈ range (d + 1), c m * (j.choose m : ℤ)) :
    (∑ m ∈ range (d + 1), c m) ≡ c 0 [ZMOD 3] := by
  have hh := congrArg (newtonMass d) (funext he)
  rw [newtonMass_sum, newtonMass_sum] at hh
  have hp (m : ℕ) (hm : m ∈ range (d + 1)) :
      newtonMass d (fun j => (j.choose m : ℤ)) = 1 :=
    positive_choose_mass d m (by simp only [mem_range] at hm; omega)
  have hright : (∑ m ∈ range (d + 1),
      c m * newtonMass d (fun j => (j.choose m : ℤ))) =
      ∑ m ∈ range (d + 1), c m := by
    apply sum_congr rfl
    intro m hm
    rw [hp m hm, mul_one]
  rw [hright] at hh
  have hn (m : ℕ) (hm : m + 1 ≤ d) :
      newtonMass d (fun j : ℕ => Ring.choose (-(j : ℤ)) (m + 1)) =
      (-1 : ℤ) ^ (m + 1) * 2 ^ m := negative_choose_mass d m hm
  have hzero : newtonMass d (fun j : ℕ => Ring.choose (-(j : ℤ)) 0) = 1 := by
    simpa only [Ring.choose_zero_right, Nat.choose_zero_right, Int.natCast_one] using positive_choose_mass d 0 (by omega)
  rw [sum_range_succ'] at hh
  rw [hzero, mul_one] at hh
  have hf : ∀ m ∈ range d,
      newtonMass d (fun j : ℕ => Ring.choose (-(j : ℤ)) (m + 1)) =
      (-1 : ℤ) ^ (m + 1) * 2 ^ m := by
    intro m hm; exact hn m (by simp only [mem_range] at hm; omega)
  have hleft : (∑ m ∈ range d, c (m + 1) *
      newtonMass d (fun j : ℕ => Ring.choose (-(j : ℤ)) (m + 1))) =
      ∑ m ∈ range d, c (m + 1) * ((-1 : ℤ) ^ (m + 1) * 2 ^ m) := by
    apply sum_congr rfl
    intro m hm
    rw [hf m hm]
  rw [hleft] at hh
  have hmod (m : ℕ) : ((-1 : ℤ) ^ (m + 1) * 2 ^ m) ≡ -1 [ZMOD 3] := by
    have hpow := (show (-2 : ℤ) ≡ 1 [ZMOD 3] by decide).pow m
    calc
      (-1 : ℤ) ^ (m + 1) * 2 ^ m = -((-2 : ℤ) ^ m) := by
        rw [pow_succ, show (-2 : ℤ) = -1 * 2 by norm_num, mul_pow]
        ring
      _ ≡ -(1 ^ m) [ZMOD 3] := hpow.neg
      _ = -1 := by simp
  have hs : (∑ m ∈ range d, c (m + 1) * ((-1 : ℤ) ^ (m + 1) * 2 ^ m)) ≡
      -(∑ m ∈ range d, c (m + 1)) [ZMOD 3] := by
    rw [← sum_neg_distrib]
    apply Int.ModEq.sum
    intro m hm
    simpa using (Int.ModEq.refl (c (m + 1))).mul (hmod m)
  rw [sum_range_succ'] at hh
  have heq : 2 * (∑ m ∈ range d, c (m + 1)) ≡ 0 [ZMOD 3] := by
    have h := hs.add (Int.ModEq.refl (c 0))
    rw [hh] at h
    have := h.sub (Int.ModEq.refl (-(∑ m ∈ range d, c (m + 1)) + c 0))
    convert this using 1 <;> ring
  rw [sum_range_succ']
  have hz : (∑ m ∈ range d, c (m + 1)) ≡ 0 [ZMOD 3] := by
    simpa only [show Int.gcd 3 2 = 1 by decide, Nat.cast_one, Int.ediv_one] using Int.ModEq.cancel_left_div_gcd (by decide : (0 : ℤ) < 3)
      (show (2 : ℤ) * (∑ m ∈ range d, c (m + 1)) ≡ 2 * 0 [ZMOD 3] by simpa using heq)
  simpa using hz.add (Int.ModEq.refl (c 0))

end D5.S1.Recurrence.Invariants.HannaA320949ModThree

set_option maxHeartbeats 50000
namespace D5.S1.Recurrence.Invariants.HannaA320949ModThree
open Finset Function

private theorem choose_product (j m r : ℕ) :
    (j + m).choose m * (j + m + r).choose r =
      (m + r).choose r * (j + (m + r)).choose (m + r) := by
  have h := Nat.choose_mul (n := j + m + r) (k := m + r) (s := r) (by omega)
  simp only [Nat.add_sub_cancel] at h
  simpa only [Nat.add_assoc, Nat.mul_comm] using h.symm

private theorem hasSum_choose_product_real (m r : ℕ) :
    HasSum (fun j : ℕ => (j.choose m : ℝ) * ((j + r).choose r : ℝ) *
      (1 / 2 : ℝ) ^ (j + r + 1)) ((m + r).choose r : ℝ) := by
  rw [← hasSum_nat_add_iff' m]
  have hz : ∑ j ∈ range m, (j.choose m : ℝ) * ((j + r).choose r : ℝ) *
      (1 / 2 : ℝ) ^ (j + r + 1) = 0 := by
    apply sum_eq_zero
    intro j hj
    simp [Nat.choose_eq_zero_of_lt (mem_range.mp hj)]
  rw [hz, sub_zero]
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one (m + r)
    (r := (1 / 2 : ℝ)) (by norm_num)).mul_left
      (((m + r).choose r : ℝ) * (1 / 2 : ℝ) ^ (m + r + 1))
  convert hs using 1
  · funext j
    rw [← Nat.cast_mul, choose_product, Nat.cast_mul]
    rw [show j + m + r + 1 = (m + r + 1) + j by omega, pow_add]
    ring
  · norm_num

private theorem hasSum_choose_product_rat (m r : ℕ) :
    HasSum (fun j : ℕ => (j.choose m : ℚ) * ((j + r).choose r : ℚ) *
      (1 / 2 : ℚ) ^ (j + r + 1)) ((m + r).choose r : ℚ) := by
  apply (Rat.isEmbedding_coe_real.isInducing.hasSum_iff
    (g := (Rat.castHom ℝ).toAddMonoidHom) _ _).mp
  change HasSum (fun j : ℕ =>
    (((j.choose m : ℚ) * ((j + r).choose r : ℚ) *
      (1 / 2 : ℚ) ^ (j + r + 1) : ℚ) : ℝ))
      (((m + r).choose r : ℚ) : ℝ)
  push_cast
  exact hasSum_choose_product_real m r

end D5.S1.Recurrence.Invariants.HannaA320949ModThree

set_option maxHeartbeats 50000
set_option maxRecDepth 2048
namespace D5.S1.Recurrence.Invariants.HannaA320949ModThree
open PowerSeries Finset
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
variable {R : Type*} [CommRing R]

private noncomputable def transformedRow (c : ℕ → ℕ → ℤ) (k : ℕ)
    (A : PowerSeries R) : PowerSeries R :=
  ∑ m ∈ range (2 * k + 1), (c k m : R) • (invOfUnit A 1) ^ (m + 1)

private noncomputable def normalizedResidual (c : ℕ → ℕ → ℤ)
    (A : PowerSeries R) : PowerSeries R :=
  mk fun n => ∑ k ∈ range (n + 1), coeff (n - k) (transformedRow c (k + 1) A)

private noncomputable def normalizedStep (c : ℕ → ℕ → ℤ)
    (A : PowerSeries R) : PowerSeries R :=
  1 + X * (A * normalizedResidual c A)

private theorem transformedRow_agree (c : ℕ → ℕ → ℤ) (k : ℕ)
    {d : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1) (h : Agree d A B) :
    Agree d (transformedRow c k A) (transformedRow c k B) := by
  have hi := D5.S1.Recurrence.Invariants.AbsoluteReciprocalGeometricParity.agree_inv hA hB h
  intro n hn
  simp only [transformedRow, map_sum, map_smul]
  apply sum_congr rfl
  intro m hm
  rw [agree_pow hi (m + 1) n hn]

private theorem normalizedResidual_agree (c : ℕ → ℕ → ℤ)
    {d : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1) (h : Agree d A B) :
    Agree d (normalizedResidual c A) (normalizedResidual c B) := by
  intro n hn
  simp only [normalizedResidual, coeff_mk]
  apply sum_congr rfl
  intro k hk
  exact transformedRow_agree c (k + 1) hA hB h (n - k) (by omega)

private theorem normalizedStep_constant (c : ℕ → ℕ → ℤ) (A : PowerSeries R) :
    constantCoeff (normalizedStep c A) = 1 := by
  simp [normalizedStep]

private theorem normalizedStep_agree (c : ℕ → ℕ → ℤ)
    {d : ℕ} {A B : PowerSeries R}
    (hA : constantCoeff A = 1) (hB : constantCoeff B = 1) (h : Agree d A B) :
    Agree (d + 1) (normalizedStep c A) (normalizedStep c B) := by
  have hx := agree_X (agree_mul h (normalizedResidual_agree c hA hB h))
  intro n hn
  simp only [normalizedStep, map_add, hx n hn]

private theorem normalized_exists_unique (c : ℕ → ℕ → ℤ) :
    ∃ A : PowerSeries R, constantCoeff A = 1 ∧ A = normalizedStep c A ∧
      ∀ B, constantCoeff B = 1 → B = normalizedStep c B → B = A := by
  exact D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
    (normalizedStep c) (fun A hA => normalizedStep_constant c A)
      (fun hd hA hB h => normalizedStep_agree c hA hB h)


private theorem invOfUnit_map {S : Type*} [CommRing S] (hom : R →+* S)
    (A : PowerSeries R) (hA : constantCoeff A = 1) :
    PowerSeries.map hom (invOfUnit A 1) = invOfUnit (PowerSeries.map hom A) 1 := by
  exact D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.map_inverse hom A hA

private theorem transformedRow_map {S : Type*} [CommRing S] (hom : R →+* S)
    (c : ℕ → ℕ → ℤ) (k : ℕ) (A : PowerSeries R) (hA : constantCoeff A = 1) :
    PowerSeries.map hom (transformedRow c k A) =
      transformedRow c k (PowerSeries.map hom A) := by
  simp only [transformedRow, PowerSeries.smul_eq_C_mul, map_sum, map_mul, map_pow,
    map_C, map_intCast, invOfUnit_map hom A hA]

private theorem normalizedResidual_map {S : Type*} [CommRing S] (hom : R →+* S)
    (c : ℕ → ℕ → ℤ) (A : PowerSeries R) (hA : constantCoeff A = 1) :
    PowerSeries.map hom (normalizedResidual c A) =
      normalizedResidual c (PowerSeries.map hom A) := by
  ext n
  simp only [coeff_map, normalizedResidual, coeff_mk, map_sum]
  apply sum_congr rfl
  intro k hk
  simpa only [coeff_map] using congrArg (coeff (n - k)) (transformedRow_map hom c (k + 1) A hA)

private theorem normalizedStep_map {S : Type*} [CommRing S] (hom : R →+* S)
    (c : ℕ → ℕ → ℤ) (A : PowerSeries R) (hA : constantCoeff A = 1) :
    PowerSeries.map hom (normalizedStep c A) = normalizedStep c (PowerSeries.map hom A) := by
  simp only [normalizedStep, map_add, map_one, map_mul, map_X,
    normalizedResidual_map hom c A hA]

private theorem transformedRow_one (c : ℕ → ℕ → ℤ) (k : ℕ) :
    transformedRow c k (1 : PowerSeries R) = C (∑ m ∈ range (2 * k + 1), (c k m : R)) := by
  have hi : invOfUnit (1 : PowerSeries R) 1 = 1 := by
    exact D5.S1.Recurrence.Residue.ContinuedFractionOddSquare.inverse_one
  simp only [transformedRow, hi, one_pow, PowerSeries.smul_eq_C_mul, mul_one, map_sum]

private theorem normalizedStep_one (c : ℕ → ℕ → ℤ)
    (hc : ∀ k, 0 < k → ∑ m ∈ range (2 * k + 1), (c k m : R) = 0) :
    normalizedStep c (1 : PowerSeries R) = 1 := by
  have hz : normalizedResidual c (1 : PowerSeries R) = 0 := by
    ext n
    simp only [normalizedResidual, coeff_mk, map_zero]
    apply sum_eq_zero
    intro k hk
    rw [transformedRow_one, hc (k + 1) (by omega), map_zero, map_zero]
  simp [normalizedStep, hz]

end D5.S1.Recurrence.Invariants.HannaA320949ModThree

/-! Binding definitions for Paul D. Hanna, OEIS A320949, revision 12.
The infinite sum is taken coefficient by coefficient in the usual topology on ℚ.
No convergence in the X-adic topology is asserted: each summand has nonzero constant term.
-/

namespace D5.S1.Recurrence.Invariants.HannaA320949ModThree

open PowerSeries

/-- The literal nth summand (1+x)^(n²)/(1+A(x))^(n+1). -/
noncomputable def term (A : PowerSeries ℚ) (j : ℕ) : PowerSeries ℚ :=
  (1 + X : PowerSeries ℚ) ^ (j ^ 2) * ((1 + A) ^ (j + 1))⁻¹

/-- The source equation, with the normalization A(0)=1 in its displayed example. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧
    ∀ k : ℕ, HasSum (fun j : ℕ => coeff k (term A j)) (coeff k (1 : PowerSeries ℚ))

/-- A320949's sole FORMULA conjecture, including existence to prevent vacuity.
Every rational solution's positive-degree coefficient is an integer divisible by three. -/
def claim : Prop :=
  (∃ A : PowerSeries ℚ, IsGF A) ∧
    ∀ A : PowerSeries ℚ, IsGF A →
      ∀ n : ℕ, 0 < n → ∃ z : ℤ, coeff n A = (3 * z : ℤ)

end D5.S1.Recurrence.Invariants.HannaA320949ModThree

set_option maxHeartbeats 50000
namespace D5.S1.Recurrence.Invariants.HannaA320949ModThree
open PowerSeries Finset

private theorem subst_coeff_range (f B : PowerSeries ℚ) (hB : constantCoeff B = 0) (n : ℕ) :
    coeff n (f.subst B) = ∑ r ∈ range (n + 1), coeff r f * coeff n (B ^ r) := by
  exact D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.coeff_subst_sum hB f n


private theorem inverse_power_expansion (a : ℚ) (ha : a ≠ 0)
    (B : PowerSeries ℚ) (hB : constantCoeff B = 0) (n : ℕ) :
    ((C a + B) ^ n)⁻¹ = C (a⁻¹ ^ n) *
      (binomialSeries ℚ (-(n : ℤ))).subst (C a⁻¹ * B) := by
  let T : PowerSeries ℚ := C a⁻¹ * B
  have hT : constantCoeff T = 0 := by simp [T, hB]
  have hs : (binomialSeries ℚ (-(n : ℤ))).subst T * (1 + T) ^ n = 1 := by
    have h := congrArg (substAlgHom (R := ℚ) (.of_constantCoeff_zero hT))
      (binomialSeries_add (A := ℚ) (-(n : ℤ)) (n : ℤ))
    simp only [neg_add_cancel, binomialSeries_zero, map_one, map_mul,
      binomialSeries_nat, map_pow, map_add, substAlgHom_X] at h
    simpa only [coe_substAlgHom] using h.symm
  have hf : C a + B = C a * (1 + T) := by
    dsimp [T]
    rw [mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  have hc : C (a⁻¹ ^ n) * (C a : PowerSeries ℚ) ^ n = 1 := by
    rw [← map_pow, ← map_mul, ← mul_pow, inv_mul_cancel₀ ha, one_pow, map_one]
  symm
  apply (eq_inv_iff_mul_eq_one (by simpa [hB] using pow_ne_zero n ha)).mpr
  change (C (a⁻¹ ^ n) * (binomialSeries ℚ (-(n : ℤ))).subst T) * (C a + B) ^ n = 1
  rw [hf, mul_pow]
  calc
    _ = (C (a⁻¹ ^ n) * (C a : PowerSeries ℚ) ^ n) *
        ((binomialSeries ℚ (-(n : ℤ))).subst T * (1 + T) ^ n) := by ring
    _ = 1 := by rw [hc, hs, one_mul]


private theorem inverse_coefficient_expansion_general (a : ℚ) (ha : a ≠ 0) (B : PowerSeries ℚ)
    (hB : constantCoeff B = 0) (j n : ℕ) :
    coeff n (((C a + B) ^ (j + 1))⁻¹) =
      ∑ r ∈ range (n + 1), (-1 : ℚ) ^ r * ((j + r).choose r : ℚ) *
        a⁻¹ ^ (j + r + 1) * coeff n (B ^ r) := by
  rw [inverse_power_expansion a ha B hB (j + 1), coeff_C_mul,
    subst_coeff_range _ _ (by simp [hB]), mul_sum]
  apply sum_congr rfl
  intro r hr
  have hneg : coeff r (binomialSeries ℚ (-((j + 1 : ℕ) : ℤ))) =
      (-1 : ℚ) ^ r * (Nat.choose (j + 1 + r - 1) r : ℚ) := by
    rw [← rescale_neg_one_invOneSubPow, coeff_rescale]
    simp only [invOneSubPow, coeff_mk]
    rw [show j + 1 + r - 1 = j + r by omega, Nat.choose_symm_add]
  rw [hneg]
  rw [mul_pow, ← map_pow, coeff_C_mul]
  rw [show j + 1 + r - 1 = j + r by omega,
    show j + r + 1 = (j + 1) + r by omega]
  simp only [pow_add, pow_one]
  ring

private theorem inverse_coefficient_expansion (B : PowerSeries ℚ)
    (hB : constantCoeff B = 0) (j n : ℕ) :
    coeff n (((C 2 + B) ^ (j + 1))⁻¹) =
      ∑ r ∈ range (n + 1), (-1 : ℚ) ^ r * ((j + r).choose r : ℚ) *
        (1 / 2 : ℚ) ^ (j + r + 1) * coeff n (B ^ r) := by
  simpa using inverse_coefficient_expansion_general 2 (by norm_num) B hB j n

end D5.S1.Recurrence.Invariants.HannaA320949ModThree
namespace D5.S1.Recurrence.Invariants.HannaA320949ModThree
open PowerSeries Finset

private theorem numerator_coefficient (j k : ℕ) :
    coeff k ((1 + X : PowerSeries ℚ) ^ (j ^ 2)) = ((j ^ 2).choose k : ℚ) := by
  rw [← PowerSeries.binomialSeries_nat (R := ℤ) (A := ℚ) (j ^ 2),
    PowerSeries.binomialSeries_coeff, Ring.choose_natCast]
  simp

private theorem term_coefficient (A : PowerSeries ℚ) (hA : constantCoeff A = 1) (j n : ℕ) :
    coeff n (term A j) =
      ∑ k ∈ range (n + 1), ∑ r ∈ range (n - k + 1),
        ((j ^ 2).choose k : ℚ) * (-1 : ℚ) ^ r * ((j + r).choose r : ℚ) *
          (1 / 2 : ℚ) ^ (j + r + 1) * coeff (n - k) ((A - 1) ^ r) := by
  rw [term, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl
  intro k hk
  rw [numerator_coefficient]
  have hB : constantCoeff (A - 1) = 0 := by simp [hA]
  have he : (1 + A : PowerSeries ℚ) = C 2 + (A - 1) := by
    simp only [map_ofNat]
    ring
  rw [he, inverse_coefficient_expansion (A - 1) hB j (n - k), mul_sum]
  apply sum_congr rfl
  intro r hr
  ring

end D5.S1.Recurrence.Invariants.HannaA320949ModThree
namespace D5.S1.Recurrence.Invariants.HannaA320949ModThree
open Finset
private noncomputable def weightedNewtonCoeff (k r : ℕ) : ℤ :=
  ∑ m ∈ range (2 * k + 1), newtonCoeff k m * ((m + r).choose r : ℤ)

private theorem hasSum_squareChoose_weighted (k r : ℕ) :
    HasSum (fun j : ℕ => ((j ^ 2).choose k : ℚ) * ((j + r).choose r : ℚ) *
      (1 / 2 : ℚ) ^ (j + r + 1)) (weightedNewtonCoeff k r : ℚ) := by
  have hs : HasSum (fun j : ℕ => ∑ m ∈ range (2 * k + 1),
      (newtonCoeff k m : ℚ) * ((j.choose m : ℚ) * ((j + r).choose r : ℚ) *
        (1 / 2 : ℚ) ^ (j + r + 1)))
      (∑ m ∈ range (2 * k + 1),
        (newtonCoeff k m : ℚ) * ((m + r).choose r : ℚ)) := by
    apply hasSum_sum
    intro m hm
    exact (hasSum_choose_product_rat m r).mul_left _
  convert hs using 1
  · funext j
    have h := congrArg (fun z : ℤ => (z : ℚ)) (squareChoose_newton k j)
    push_cast at h
    rw [h, sum_mul, sum_mul]
    apply sum_congr rfl
    intro m hm
    ring
  · simp only [weightedNewtonCoeff, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

end D5.S1.Recurrence.Invariants.HannaA320949ModThree
namespace D5.S1.Recurrence.Invariants.HannaA320949ModThree
open PowerSeries Finset

private theorem transformedRow_coefficient (A : PowerSeries ℚ) (hA : constantCoeff A = 1)
    (k n : ℕ) :
    coeff n (transformedRow newtonCoeff k A) =
      ∑ r ∈ range (n + 1), (-1 : ℚ) ^ r * (weightedNewtonCoeff k r : ℚ) *
        coeff n ((A - 1) ^ r) := by
  have hB : constantCoeff (A - 1) = 0 := by simp [hA]
  have he : A = C 1 + (A - 1) := by
    exact Eq.symm (add_sub_cancel (C 1) A)
  simp only [transformedRow, map_sum, map_smul, smul_eq_mul]
  simp_rw [invOfUnit_eq' A 1 hA, PowerSeries.inv_pow]
  have hex (m : ℕ) : coeff n ((A ^ (m + 1))⁻¹) =
      ∑ r ∈ range (n + 1), (-1 : ℚ) ^ r * ((m + r).choose r : ℚ) *
        coeff n ((A - 1) ^ r) := by
    have hh := inverse_coefficient_expansion_general 1 (by norm_num) (A - 1) hB m n
    have h1 : C (1 : ℚ) + (A - 1) = A := by
      exact PowerSeries.ext fun n => congrArg (⇑(coeff n)) (id (Eq.symm he))
    simpa only [h1, inv_one, one_pow, mul_one] using hh
  simp_rw [hex, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  simp only [weightedNewtonCoeff, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  rw [mul_sum, sum_mul]
  apply sum_congr rfl
  intro m hm
  ring

private noncomputable def transformedSource (A : PowerSeries ℚ) : PowerSeries ℚ :=
  mk fun n => ∑ k ∈ range (n + 1), coeff (n - k) (transformedRow newtonCoeff k A)

private theorem source_hasSum (A : PowerSeries ℚ) (hA : constantCoeff A = 1) (n : ℕ) :
    HasSum (fun j : ℕ => coeff n (term A j)) (coeff n (transformedSource A)) := by
  have hs : HasSum (fun j : ℕ => ∑ k ∈ range (n + 1),
      ∑ r ∈ range (n - k + 1),
        (-1 : ℚ) ^ r *
          (((j ^ 2).choose k : ℚ) * ((j + r).choose r : ℚ) *
            (1 / 2 : ℚ) ^ (j + r + 1)) * coeff (n - k) ((A - 1) ^ r))
      (∑ k ∈ range (n + 1), ∑ r ∈ range (n - k + 1),
        (-1 : ℚ) ^ r * (weightedNewtonCoeff k r : ℚ) *
          coeff (n - k) ((A - 1) ^ r)) := by
    apply hasSum_sum
    intro k hk
    apply hasSum_sum
    intro r hr
    exact ((hasSum_squareChoose_weighted k r).mul_left _).mul_right _
  convert hs using 1
  · funext j
    rw [term_coefficient A hA]
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro r hr
    ring
  · simp only [transformedSource, coeff_mk]
    apply sum_congr rfl
    intro k hk
    exact transformedRow_coefficient A hA k (n - k)

private theorem newtonCoeff_zero_row (m : ℕ) : newtonCoeff 0 m = if m = 0 then 1 else 0 := by
  simpa only [newtonCoeff, Nat.choose_zero_right, Int.natCast_one] using
    (fwdDiff_iter_choose_zero (R := ℤ) 0 m)

private theorem transformedSource_split (A : PowerSeries ℚ) :
    transformedSource A = invOfUnit A 1 + X * normalizedResidual newtonCoeff A := by
  have hr : transformedRow newtonCoeff 0 A = invOfUnit A 1 := by
    simp [transformedRow, newtonCoeff_zero_row]
  ext n
  cases n
  · simp [transformedSource, hr]
  · rename_i n
    simp only [transformedSource, coeff_mk, map_add, coeff_succ_X_mul,
      normalizedResidual]
    rw [sum_range_succ']
    rw [add_comm]
    congr 1
    · simpa using congrArg (coeff (n + 1)) hr
    · apply sum_congr rfl
      intro k hk
      congr 2
      omega

private theorem source_iff_fixed (A : PowerSeries ℚ) (hA : constantCoeff A = 1) :
    IsGF A ↔ A = normalizedStep newtonCoeff A := by
  have hi := invOfUnit_mul A 1 hA
  have hs : IsGF A ↔ transformedSource A = 1 := by
    constructor
    · intro h
      ext n
      exact (source_hasSum A hA n).unique (h.2 n)
    · intro h
      refine ⟨hA, ?_⟩
      intro n
      simpa only [h] using source_hasSum A hA n
  rw [hs, transformedSource_split]
  constructor
  · intro h
    have hh := congrArg (fun F : PowerSeries ℚ => A * F) h
    have hi' : A * invOfUnit A 1 = 1 := mul_invOfUnit A 1 hA
    rw [mul_add, hi', mul_one] at hh
    unfold normalizedStep
    linear_combination -hh
  · intro h
    have hh := congrArg (fun F : PowerSeries ℚ => invOfUnit A 1 * F) h
    unfold normalizedStep at hh
    rw [mul_add, mul_one] at hh
    have hx : invOfUnit A 1 * (X * (A * normalizedResidual newtonCoeff A)) =
        X * normalizedResidual newtonCoeff A := by
      calc
        _ = (invOfUnit A 1 * A) * (X * normalizedResidual newtonCoeff A) := by ring
        _ = _ := by rw [hi, one_mul]
    rw [hi, hx] at hh
    exact hh.symm

private theorem newtonCoeff_mod_three (k : ℕ) (hk : 0 < k) :
    (∑ m ∈ range (2 * k + 1), newtonCoeff k m) ≡ 0 [ZMOD 3] := by
  have he (j : ℕ) := newton_expansion_even k (j : ℤ)
  simp only [Ring.choose_natCast] at he
  have hh := even_newton_congruence (2 * k) (newtonCoeff k) he
  have hz : newtonCoeff k 0 = 0 := by simp [newtonCoeff, Nat.choose_eq_zero_of_lt hk]
  simpa only [hz] using hh

theorem result : claim := by
  obtain ⟨A, hA, hfix, huniq⟩ := normalized_exists_unique (R := ℤ) newtonCoeff
  let AQ := PowerSeries.map (Int.castRingHom ℚ) A
  have hAQ : constantCoeff AQ = 1 := by
    exact Eq.symm (Rat.ext (id (Eq.symm hA)) rfl)
  have hAQfix : AQ = normalizedStep newtonCoeff AQ := by
    simpa only [AQ, normalizedStep_map (Int.castRingHom ℚ) newtonCoeff A hA] using
      congrArg (PowerSeries.map (Int.castRingHom ℚ)) hfix
  have hAQgf : IsGF AQ := (source_iff_fixed AQ hAQ).mpr hAQfix
  have hmodone : normalizedStep newtonCoeff (1 : PowerSeries (ZMod 3)) = 1 := by
    apply normalizedStep_one
    intro k hk
    rw [← Int.cast_sum]
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (newtonCoeff_mod_three k hk)
  have hmodA : PowerSeries.map (Int.castRingHom (ZMod 3)) A = 1 := by
    obtain ⟨F, hF, hFF, hu⟩ := normalized_exists_unique (R := ZMod 3) newtonCoeff
    have hm0 : constantCoeff (PowerSeries.map (Int.castRingHom (ZMod 3)) A) = 1 := by
      change ((constantCoeff A : ℤ) : ZMod 3) = 1
      rw [hA, Int.cast_one]
    have hmf : PowerSeries.map (Int.castRingHom (ZMod 3)) A =
        normalizedStep newtonCoeff (PowerSeries.map (Int.castRingHom (ZMod 3)) A) := by
      simpa only [normalizedStep_map (Int.castRingHom (ZMod 3)) newtonCoeff A hA] using
        congrArg (PowerSeries.map (Int.castRingHom (ZMod 3))) hfix
    exact (hu _ hm0 hmf).trans (hu 1 (by simp) hmodone.symm).symm
  refine ⟨⟨AQ, hAQgf⟩, ?_⟩
  intro B hB n hn
  have heq : B = AQ := by
    obtain ⟨F, hF, hFF, hu⟩ := normalized_exists_unique (R := ℚ) newtonCoeff
    exact (hu B hB.1 ((source_iff_fixed B hB.1).mp hB)).trans
      (hu AQ hAQ hAQfix).symm
  have hz : ((coeff n A : ℤ) : ZMod 3) = 0 := by
    have hh := congrArg (coeff n) hmodA
    change ((coeff n A : ℤ) : ZMod 3) = coeff n (1 : PowerSeries (ZMod 3)) at hh
    simpa only [coeff_one, if_neg (by omega : n ≠ 0)] using hh
  obtain ⟨z, hz⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff n A) 3).mp hz
  refine ⟨z, ?_⟩
  rw [heq]
  change ((coeff n A : ℤ) : ℚ) = ((3 * z : ℤ) : ℚ)
  rw [hz]
  norm_num

end D5.S1.Recurrence.Invariants.HannaA320949ModThree

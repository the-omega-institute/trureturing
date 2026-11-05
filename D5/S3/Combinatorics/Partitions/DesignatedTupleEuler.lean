/- GID: D5/S3/Combinatorics/Partitions/DesignatedTupleEuler
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/DesignatedTupleEuler
   mirror-E: none(waiver:formal-integral-designated-count)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Partition.GenFun, mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Ordered designated partitions and their integral Euler quotient. -/

import D5.S3.Combinatorics.Partitions.ColouredOddOccupation
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

/-! Partitions with one chosen occurrence in every nonempty block of equal
positive parts, and ordered tuples with a prescribed total size. The source is
Section 2 and Definition 2.1 of https://arxiv.org/html/2611.05623v1.
No congruence or sharp divisibility assertion is made here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators PowerSeries.WithPiTopology
namespace D5.S3.Combinatorics.Partitions.DesignatedTupleEuler

/-- An occurrence is indexed from zero within its block of equal parts. -/
abbrev Marks {N : ℕ} (p : Nat.Partition N) :=
  (s : ↥p.parts.toFinset) → Fin (p.parts.count s.1)

/-- The underlying partition is retained independently of its choices of marks. -/
abbrev Designated (N : ℕ) := Σ p : Nat.Partition N, Marks p

instance designatedFintype (N : ℕ) : Fintype (Designated N) := inferInstance

/-- Sizes are nonnegative; a component of size zero is the empty partition. -/
abbrev Tuple (k N : ℕ) :=
  Σ e : ColouredOddOccupation.EnergyAllocation (Fin k) N,
    (i : Fin k) → Designated (e.1 i)

instance tupleFintype (k N : ℕ) : Fintype (Tuple k N) := by
  letI : Fintype (ColouredOddOccupation.EnergyAllocation (Fin k) N) :=
    Fintype.ofEquiv _ (ColouredOddOccupation.energyAllocationEquivAntidiag (Fin k) N).symm
  exact inferInstance

/-- This is the cardinality of actual ordered marked partitions. -/
def count (k N : ℕ) : ℕ := Nat.card (Tuple k N)

/-- Mathlib's weighted partition generating function, over the integers. -/
def markedSeries : PowerSeries ℤ := Nat.Partition.genFun (fun _ m => (m : ℤ))

private theorem card_designated (N : ℕ) :
    (Nat.card (Designated N) : ℤ) = PowerSeries.coeff N markedSeries := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma, Nat.cast_sum]
  simp only [markedSeries, Nat.Partition.coeff_genFun, Finsupp.prod,
    Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
  exact (Finset.prod_coe_sort p.parts.toFinset (fun s => (p.parts.count s : ℤ)))

private def tupleEquivAntidiag (k N : ℕ) :
    Tuple k N ≃ Σ e : ↥((Finset.univ : Finset (Fin k)).finsuppAntidiag N),
      (i : Fin k) → Designated (e.1 i) :=
  Equiv.sigmaCongr (ColouredOddOccupation.energyAllocationEquivAntidiag (Fin k) N)
    (fun _ => Equiv.refl _)

private theorem count_eq_coeff_pow (k N : ℕ) :
    (count k N : ℤ) = PowerSeries.coeff N (markedSeries ^ k) := by
  classical
  unfold count
  rw [Nat.card_congr (tupleEquivAntidiag k N), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  have hp : markedSeries ^ k = ∏ _ : Fin k, markedSeries := by simp
  rw [hp, PowerSeries.coeff_prod]
  simp only [Nat.cast_sum, Fintype.card_pi, Nat.cast_prod]
  rw [← Finset.sum_coe_sort ((Finset.univ : Finset (Fin k)).finsuppAntidiag N)]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [Nat.card_eq_fintype_card] using card_designated (e.1 i)

private def kernel : PowerSeries ℤ :=
  PowerSeries.mk (fun n => if n = 0 then 1 else (n : ℤ))

private theorem local_factor (t : ℕ) (ht : t ≠ 0) :
    (1 : PowerSeries ℤ) + ∑' j : ℕ,
      ((j+1 : ℕ) : ℤ) • PowerSeries.X ^ (t*(j+1)) =
    PowerSeries.expand t ht kernel := by
  ext N
  rw [PowerSeries.coeff_expand]
  simp only [kernel, PowerSeries.coeff_mk]
  rw [map_add,
    (Nat.Partition.summable_genFun_term' (fun _ m => (m : ℤ)) ht).map_tsum _
      (PowerSeries.WithPiTopology.continuous_coeff _ _)]
  simp only [map_smul, PowerSeries.coeff_X_pow, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  by_cases hn : N = 0
  · subst N
    simp [ht]
  · by_cases hd : t ∣ N
    · rw [ite_eq_left hd]
      have hq : 0 < N / t := Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) (Nat.pos_of_ne_zero ht)
      have hmul : t * (N / t - 1 + 1) = N := by
        rw [Nat.sub_add_cancel hq, Nat.mul_div_cancel' hd]
      rw [tsum_eq_single (N / t - 1)]
      · simp [hn, Nat.sub_add_cancel hq, Nat.ne_of_gt hq, Nat.mul_div_cancel' hd]
      · intro j hj
        have hne : N ≠ t * (j+1) := by
          intro heq
          have he : N/t = j+1 := by
            rw [heq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ht)]
          omega
        simp [hne]
    · rw [ite_eq_right hd]
      have hz (j : ℕ) : N ≠ t * (j+1) := fun h => hd ⟨j+1,h⟩
      simp [hn, hz]

private theorem kernel_closed :
    kernel = 1 + PowerSeries.X * PowerSeries.mk (fun n => (n+1 : ℤ)) := by
  ext n
  cases n with
  | zero => simp [kernel]
  | succ n =>
    rw [map_add, show PowerSeries.X * PowerSeries.mk (fun n => (n+1 : ℤ)) =
      PowerSeries.X ^ 1 * PowerSeries.mk (fun n => (n+1 : ℤ)) by rw [pow_one],
      PowerSeries.coeff_X_pow_mul]
    simp [kernel]

private theorem kernel_identity :
    kernel * (1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2) *
      (1 - PowerSeries.X ^ 3) = (1 - PowerSeries.X ^ 6 : PowerSeries ℤ) := by
  have h : PowerSeries.mk (fun n => (n+1 : ℤ)) *
      (1 - PowerSeries.X) ^ 2 = (1 : PowerSeries ℤ) := by
    simpa [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, add_comm] using
      PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℤ 1
  rw [kernel_closed]
  linear_combination (PowerSeries.X * (1 + PowerSeries.X) *
    (1 - PowerSeries.X ^ 3)) * h

/-- The actual integral Euler product at a positive dilation. -/
def euler (m : ℕ+) : PowerSeries ℤ :=
  PowerSeries.expand m.1 m.ne_zero (PowerSeries.pentagonalSeries ℤ)

private theorem continuous_expand (t : ℕ) (ht : t ≠ 0) :
    Continuous (PowerSeries.expand (R := ℤ) t ht) := by
  apply continuous_pi
  intro d
  have hd : d = Finsupp.single () (d ()) := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  have h : Continuous (fun f : PowerSeries ℤ => PowerSeries.coeff (d ())
      (PowerSeries.expand t ht f)) := by
    simp_rw [PowerSeries.coeff_expand]
    split_ifs
    · exact PowerSeries.WithPiTopology.continuous_coeff _ _
    · exact continuous_const
  convert h using 1
  funext f
  change (PowerSeries.expand t ht f) d =
    (PowerSeries.expand t ht f) (Finsupp.single () (d ()))
  rw [← hd]

private theorem hasProd_euler (m : ℕ+) :
    HasProd (fun n : ℕ => (1 - PowerSeries.X ^ (m.1*(n+1)) : PowerSeries ℤ))
      (euler m) := by
  have h := (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℤ).map
    (PowerSeries.expand m.1 m.ne_zero) (continuous_expand m.1 m.ne_zero)
  simpa only [euler, Function.comp_def, map_sub, map_one, map_pow, PowerSeries.expand_X,
    ← pow_mul, mul_comm (m.1)] using h

private theorem euler_constant (m : ℕ+) :
    PowerSeries.constantCoeff (euler m) = 1 := by
  rw [euler, PowerSeries.constantCoeff_expand,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simpa only [show pentagonal (0 : ℤ) = 0 by decide,
    Int.coe_negOnePow, Int.natAbs_zero, pow_zero] using
    PowerSeries.coeff_pentagonalSeries_pentagonal ℤ 0

/-- Division uses the unique inverse with constant term one, entirely over ℤ. -/
def quotient : PowerSeries ℤ := euler 6 *
  PowerSeries.invOfUnit (euler 1 * euler 2 * euler 3) 1

/-- Every degree counts the actual ordered six-tuples, including empty components. -/
theorem count_six_eq_coeff (N : ℕ) :
    (count 6 N : ℤ) = PowerSeries.coeff N (quotient ^ 6) := by
  have hP := Nat.Partition.hasProd_genFun (fun _ m => (m : ℤ))
  have hD := ((hasProd_euler 1).mul (hasProd_euler 2)).mul (hasProd_euler 3)
  have h := hP.mul hD
  have hlocal (n : ℕ) :
      ((1 : PowerSeries ℤ) + ∑' j : ℕ,
        ((j+1 : ℕ) : ℤ) • PowerSeries.X ^ ((n+1)*(j+1))) *
        ((1 - PowerSeries.X ^ (n+1)) * (1 - PowerSeries.X ^ (2*(n+1))) *
          (1 - PowerSeries.X ^ (3*(n+1)))) =
        1 - PowerSeries.X ^ (6*(n+1)) := by
    rw [local_factor (n+1) (by omega)]
    have h := congrArg (PowerSeries.expand (n+1) (by omega)) kernel_identity
    simpa only [map_mul, map_sub, map_one, map_pow, PowerSeries.expand_X,
      ← pow_mul, mul_comm (n+1), mul_assoc] using h
  change HasProd (fun n => _ * _) (markedSeries * (euler 1 * euler 2 * euler 3)) at h
  have h' : HasProd (fun n : ℕ =>
      (1 - PowerSeries.X ^ (6*(n+1)) : PowerSeries ℤ))
      (markedSeries * (euler 1 * euler 2 * euler 3)) := by
    apply h.congr_fun
    intro n
    change (1 - PowerSeries.X ^ (6*(n+1)) : PowerSeries ℤ) =
      ((1 : PowerSeries ℤ) + ∑' j : ℕ,
        ((j+1 : ℕ) : ℤ) • PowerSeries.X ^ ((n+1)*(j+1))) *
        ((1 - PowerSeries.X ^ (1*(n+1))) * (1 - PowerSeries.X ^ (2*(n+1))) *
          (1 - PowerSeries.X ^ (3*(n+1))))
    simpa only [one_mul] using (hlocal n).symm
  have heq : markedSeries * (euler 1 * euler 2 * euler 3) = euler 6 :=
    h'.unique (hasProd_euler 6)
  have hc : PowerSeries.constantCoeff (euler 1 * euler 2 * euler 3) =
      ((1 : ℤˣ) : ℤ) := by simp only [map_mul, euler_constant, one_mul, Units.val_one]
  have hq : markedSeries = quotient := by
    calc
      markedSeries = (markedSeries * (euler 1 * euler 2 * euler 3)) *
          PowerSeries.invOfUnit (euler 1 * euler 2 * euler 3) 1 := by
        rw [mul_assoc, PowerSeries.mul_invOfUnit _ 1 hc, mul_one]
      _ = quotient := by rw [heq]; rfl
  rw [count_eq_coeff_pow, hq]

end D5.S3.Combinatorics.Partitions.DesignatedTupleEuler

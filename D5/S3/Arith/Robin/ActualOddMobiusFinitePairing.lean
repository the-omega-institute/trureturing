/- GID: D5/S3/Arith/Robin/ActualOddMobiusFinitePairing
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ActualOddMobiusFinitePairing
   mirror-E: none(waiver:finite-identity)
   anchors: []
   utility: none
   digest: Real Mobius coefficients have exact odd-prefix dyadic reconstruction and finite clipped kernel pairing with a paid terminal remainder. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
The actual Mobius coefficients and their multiplicativity are Mathlib suppliers.
The consumed parity-coefficient and finite multiples-bijection proofs specialize
the primeDifference supplier inside FibonacciAtomic.MertensBoundary to p=2,R=1.
No new public generic reindexing helper is introduced. The exact clipped pairing
and terminal remainder realize actual-prefix theory section 453. Their statements
are finite identities for every real-valued kernel, not infinite-tail estimates.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators
namespace D5.S3.Arith.Robin.ActualOddMobiusFinitePairing

/-- The actual Mobius summatory function on the inclusive positive integer prefix. -/
def mobiusPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ)

/-- The same actual Mobius summatory function restricted to odd positive integers. -/
def oddMobiusPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 N).filter Odd, (ArithmeticFunction.moebius n : ℝ)

private def oddCoefficient (n : ℕ) : ℝ :=
  if Odd n then (ArithmeticFunction.moebius n : ℝ) else 0

private theorem twice_coefficient (m : ℕ) :
    (ArithmeticFunction.moebius (2*m) : ℝ) = -oddCoefficient m := by
  classical
  by_cases hm : Odd m
  · have hc : Nat.Coprime 2 m := hm.coprime_two_left
    have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two] at hmu
    simp only [oddCoefficient, if_pos hm, hmu, Int.cast_mul, Int.cast_neg,
      Int.cast_one, neg_one_mul]
  · have hc : ¬Nat.Coprime 2 m := by simpa only [Nat.coprime_two_left] using hm
    have hsq : ¬Squarefree (2*m) := fun h => hc (Nat.coprime_of_squarefree_mul h)
    simp [oddCoefficient, hm, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

private theorem coefficient (n : ℕ) :
    (ArithmeticFunction.moebius n : ℝ) = oddCoefficient n -
      (if 2 ∣ n then oddCoefficient (n/2) else 0) := by
  classical
  by_cases hd : 2 ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have hnot : ¬Odd (2*m) := by
      rw [← Nat.coprime_two_left, Nat.prime_two.coprime_iff_not_dvd]
      simp
    simpa [oddCoefficient, hnot] using twice_coefficient m
  · have ho : Odd n := Nat.coprime_two_left.mp
      (Nat.prime_two.coprime_iff_not_dvd.mpr hd)
    simp [oddCoefficient, ho, hd]

private theorem multiples_sum (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Ioc 0 N, if 2 ∣ n then f (n/2) else 0) =
      ∑ m ∈ Ioc 0 (N/2), f m := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun n _ => n/2) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn, hd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn0 hd) (by norm_num),
      Nat.div_le_div_right hnN⟩
  · intro n hn m hm heq
    have hn' := (Finset.mem_filter.mp hn).2
    have hm' := (Finset.mem_filter.mp hm).2
    have h := congrArg (fun k => 2*k) heq
    simpa [Nat.mul_div_cancel' hn', Nat.mul_div_cancel' hm'] using h
  · intro m hm
    obtain ⟨hm0, hmN⟩ := Finset.mem_Ioc.mp hm
    refine ⟨2*m, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨
      Nat.mul_pos (by norm_num) hm0, ?_⟩, dvd_mul_right 2 m⟩, ?_⟩
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).mp hmN
    · simp
  · intro n _
    rfl

private theorem weighted_split (N : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ)*F n) =
      (∑ n ∈ Ioc 0 N, oddCoefficient n*F n) -
        ∑ m ∈ Ioc 0 (N/2), oddCoefficient m*F (2*m) := by
  classical
  have hterm (n : ℕ) : (ArithmeticFunction.moebius n : ℝ)*F n =
      oddCoefficient n*F n -
        (if 2 ∣ n then oddCoefficient (n/2)*F (2*(n/2)) else 0) := by
    rw [coefficient]
    by_cases hd : 2 ∣ n
    · simp only [if_pos hd, Nat.mul_div_cancel' hd]
      ring
    · simp only [if_neg hd]
      ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  rw [multiples_sum N (fun m => oddCoefficient m*F (2*m))]

private theorem prefix_difference (N : ℕ) :
    mobiusPrefix N = oddMobiusPrefix N-oddMobiusPrefix (N/2) := by
  classical
  have h := weighted_split N (fun _ => 1)
  simpa only [mul_one, mobiusPrefix, oddMobiusPrefix, oddCoefficient,
    Finset.sum_filter] using h

private theorem dyadic_reconstruction (N : ℕ) :
    oddMobiusPrefix N =
      ∑ a ∈ (Finset.range (N+1)).filter (fun a => 2^a ≤ N), mobiusPrefix (N/2^a) := by
  classical
  have hstep (a : ℕ) : mobiusPrefix (N/2^a) =
      oddMobiusPrefix (N/2^a)-oddMobiusPrefix (N/2^(a+1)) := by
    rw [prefix_difference, Nat.div_div_eq_div_mul, pow_succ]
  have hzero : N/2^(N+1) = 0 := by
    apply Nat.div_eq_of_lt
    have hp := (N+1).lt_two_pow_self
    omega
  have hsum : (∑ a ∈ Finset.range (N+1), mobiusPrefix (N/2^a)) = oddMobiusPrefix N := by
    simp_rw [hstep]
    rw [Finset.sum_range_sub']
    simp [hzero, oddMobiusPrefix]
  have hfilter :
      (∑ a ∈ (Finset.range (N+1)).filter (fun a => 2^a ≤ N), mobiusPrefix (N/2^a)) =
        ∑ a ∈ Finset.range (N+1), mobiusPrefix (N/2^a) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a ha hnot
    have hp : ¬2^a ≤ N := by
      intro hp
      exact hnot (Finset.mem_filter.mpr ⟨ha, hp⟩)
    rw [Nat.div_eq_of_lt (by omega)]
    simp [mobiusPrefix]
  exact (hfilter.trans hsum).symm

private theorem prefix_succ (N : ℕ) :
    mobiusPrefix (N+1) = mobiusPrefix N+(ArithmeticFunction.moebius (N+1) : ℝ) := by
  unfold mobiusPrefix
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le N)]

private theorem prefix_abel (P : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, mobiusPrefix n*(P n-P (n+1))) =
      (∑ m ∈ Ioc 0 N, (ArithmeticFunction.moebius m : ℝ)*P m) -
        mobiusPrefix N*P (N+1) := by
  induction N with
  | zero => simp [mobiusPrefix]
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N),
      Finset.sum_Ioc_succ_top (Nat.zero_le N), ih]
    simp only [prefix_succ]
    ring

private theorem half_sum_extended (N : ℕ) (F : ℕ → ℝ) :
    (∑ m ∈ Ioc 0 (N/2), F m) =
      ∑ m ∈ Ioc 0 N, if 2*m ≤ N then F m else 0 := by
  classical
  have hset : (Ioc 0 N).filter (fun m => 2*m ≤ N) = Ioc 0 (N/2) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [← hset, Finset.sum_filter]

private theorem clipped_pairing (P : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, mobiusPrefix n*(P n-P (n+1))) =
      ∑ m ∈ (Ioc 0 N).filter Odd,
        (ArithmeticFunction.moebius m : ℝ)*(P m-P (min (2*m) (N+1))) := by
  classical
  have habel : (∑ n ∈ Ioc 0 N, mobiusPrefix n*(P n-P (n+1))) =
      ∑ m ∈ Ioc 0 N, (ArithmeticFunction.moebius m : ℝ)*(P m-P (N+1)) := by
    rw [prefix_abel]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rfl
  rw [habel, weighted_split, half_sum_extended, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hodd : Odd m
  · simp only [oddCoefficient, if_pos hodd]
    by_cases htwo : 2*m ≤ N
    · have hmin : min (2*m) (N+1) = 2*m := min_eq_left (by omega)
      rw [if_pos htwo, hmin]
      ring
    · have hmin : min (2*m) (N+1) = N+1 := min_eq_right (by omega)
      rw [if_neg htwo, hmin]
      ring
  · simp [oddCoefficient, hodd]

private theorem terminal_remainder (P : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, mobiusPrefix n*(P n-P (n+1))) -
      (∑ m ∈ (Ioc 0 N).filter Odd, (ArithmeticFunction.moebius m : ℝ)*(P m-P (2*m))) =
    ∑ m ∈ (Ioc 0 N).filter (fun m => Odd m ∧ N/2 < m),
      (ArithmeticFunction.moebius m : ℝ)*(P (2*m)-P (N+1)) := by
  classical
  rw [clipped_pairing]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hodd : Odd m
  · simp only [hodd, if_true, true_and]
    by_cases hband : N/2 < m
    · have hmin : min (2*m) (N+1) = N+1 := min_eq_right (by omega)
      rw [if_pos hband, hmin]
      ring
    · have hmin : min (2*m) (N+1) = 2*m := min_eq_left (by omega)
      rw [if_neg hband, hmin]
      ring
  · simp [hodd]

/-- Actual odd Mobius dyadic reconstruction and full finite pairing with its terminal remainder. -/
theorem result :
    (∀ N : ℕ,
      mobiusPrefix N = oddMobiusPrefix N-oddMobiusPrefix (N/2) ∧
      oddMobiusPrefix N =
        ∑ a ∈ (Finset.range (N+1)).filter (fun a => 2^a ≤ N), mobiusPrefix (N/2^a)) ∧
    (∀ (P : ℕ → ℝ) (N : ℕ),
      (∑ n ∈ Ioc 0 N, mobiusPrefix n*(P n-P (n+1))) =
        (∑ m ∈ (Ioc 0 N).filter Odd,
          (ArithmeticFunction.moebius m : ℝ)*(P m-P (min (2*m) (N+1)))) ∧
      (∑ n ∈ Ioc 0 N, mobiusPrefix n*(P n-P (n+1))) -
        (∑ m ∈ (Ioc 0 N).filter Odd,
          (ArithmeticFunction.moebius m : ℝ)*(P m-P (2*m))) =
        ∑ m ∈ (Ioc 0 N).filter (fun m => Odd m ∧ N/2 < m),
          (ArithmeticFunction.moebius m : ℝ)*(P (2*m)-P (N+1))) := by
  exact ⟨fun N => ⟨prefix_difference N, dyadic_reconstruction N⟩,
    fun P N => ⟨clipped_pairing P N, terminal_remainder P N⟩⟩

end D5.S3.Arith.Robin.ActualOddMobiusFinitePairing

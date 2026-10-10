/- GID: D5/S3/Arith/Robin/ActualOddHarmonicMobiusTail
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ActualOddHarmonicMobiusTail
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual odd harmonic Mobius bounds pay complete finite declining-weight tails. -/
import D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
import D5.S3.Arith.Robin.PrimePrefixMobiusDirectedAbel
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Finset
open scoped BigOperators
namespace D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail
open PrimePrefixMobiusDirectedAbel (harmonicPrefix)

/-- The actual odd harmonic prefix on the positive inclusive window. -/
def oddHarmonicPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 N).filter Odd, (ArithmeticFunction.moebius n : ℝ)/(n : ℝ)

/-- The actual weighted odd harmonic tail on the same finite physical window. -/
def weightedOddTail (D M : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ n ∈ (Ioc D M).filter Odd, (ArithmeticFunction.moebius n : ℝ)/(n : ℝ)*b n

private theorem harmonic_eq_Ioc (N : ℕ) : harmonicPrefix N =
    ∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ)/(n : ℝ) := by
  unfold harmonicPrefix
  rfl

private theorem floor_identity {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ)*(N/n : ℕ)) = 1 := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) N
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta] at h
  have hs : (∑ n ∈ Ioc 0 N, (1 : ArithmeticFunction ℝ) n) = 1 := by
    rw [sum_eq_single 1]
    · simp
    · intro n hn hn1
      simp [ArithmeticFunction.one_apply, hn1]
    · simp [mem_Ioc, hN.ne']
  simpa only [ArithmeticFunction.intCoe_apply, hs] using h.symm

private theorem harmonic_bound (N : ℕ) : |harmonicPrefix N| ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN, harmonicPrefix]
  have hNp : 0 < N := Nat.pos_of_ne_zero hN
  let r : ℕ → ℝ := fun n => (N : ℝ)/(n : ℝ)-(N/n : ℕ)
  have hr (n : ℕ) (hn : 0 < n) : 0 ≤ r n ∧ r n ≤ 1 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hlt : N < n*(N/n+1) :=
      by simpa [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul hn).mp (Nat.lt_succ_self (N/n))
    have hltR : (N : ℝ) < (n : ℝ)*((N/n : ℕ)+1 : ℝ) := by exact_mod_cast hlt
    have hu : (N : ℝ)/(n : ℝ) < ((N/n : ℕ)+1 : ℝ) :=
      (div_lt_iff₀ hnR).mpr (by nlinarith)
    have hl := (Nat.cast_div_le (m := N) (n := n) : (N/n : ℕ) ≤ (N : ℝ)/n)
    dsimp [r]
    constructor <;> linarith
  have hunit : r 1 = 0 := by simp [r]
  have hsum : |∑ n ∈ Ioc 1 N, (ArithmeticFunction.moebius n : ℝ)*r n| ≤ (N-1 : ℕ) := by
    calc
      _ ≤ ∑ n ∈ Ioc 1 N, |(ArithmeticFunction.moebius n : ℝ)*r n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Ioc 1 N, (1 : ℝ) := by
        apply sum_le_sum
        intro n hn
        have hn' := mem_Ioc.mp hn
        have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
        rw [abs_mul, abs_of_nonneg (hr n (by omega)).1]
        exact (mul_le_mul_of_nonneg_right hmu (hr n (by omega)).1).trans (by simpa using (hr n (by omega)).2)
      _ = _ := by simp
  have hex : (N : ℝ)*harmonicPrefix N = 1+
      ∑ n ∈ Ioc 1 N, (ArithmeticFunction.moebius n : ℝ)*r n := by
    rw [harmonic_eq_Ioc, mul_sum]
    have hterm (n : ℕ) : (N : ℝ)*((ArithmeticFunction.moebius n : ℝ)/(n : ℝ)) =
        (ArithmeticFunction.moebius n : ℝ)*(N/n : ℕ)+
          (ArithmeticFunction.moebius n : ℝ)*r n := by dsimp [r]; ring
    simp_rw [hterm]
    rw [sum_add_distrib, floor_identity hNp]
    congr 1
    rw [show Ioc 0 N = {1} ∪ Ioc 1 N by
      ext n
      simp only [mem_Ioc, mem_union, mem_singleton]
      omega,
      sum_union (by simp)]
    simp [hunit]
  have hsize : ((N-1 : ℕ) : ℝ) = (N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
  have hsides := abs_le.mp hsum
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  apply abs_le.mpr
  constructor <;> nlinarith

private theorem odd_recurrence (N : ℕ) :
    oddHarmonicPrefix N = harmonicPrefix N + oddHarmonicPrefix (N/2)/2 := by
  classical
  have h := ActualOddMobiusFinitePairing.weighted_split N (fun n => 1/(n : ℝ))
  have hhalf : (∑ m ∈ Ioc 0 (N/2),
      ActualOddMobiusFinitePairing.oddCoefficient m*(1/((2*m : ℕ) : ℝ))) =
      oddHarmonicPrefix (N/2)/2 := by
    simp only [oddHarmonicPrefix, sum_filter, ActualOddMobiusFinitePairing.oddCoefficient]
    rw [sum_div]
    apply sum_congr rfl
    intro m _
    split_ifs <;> push_cast <;> ring
  have hodd : (∑ n ∈ Ioc 0 N, ActualOddMobiusFinitePairing.oddCoefficient n*(1/(n : ℝ))) =
      oddHarmonicPrefix N := by
    simp only [oddHarmonicPrefix, sum_filter, ActualOddMobiusFinitePairing.oddCoefficient]
    apply sum_congr rfl
    intro n _
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hhalf, hodd] at h
  have hfull : (∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ)*(1/(n : ℝ))) =
      harmonicPrefix N := by
    rw [harmonic_eq_Ioc]
    simp only [div_eq_mul_inv, one_mul]
  rw [hfull] at h
  linarith

private theorem odd_bound (N : ℕ) : |oddHarmonicPrefix N| ≤ 2 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N = 0
    · simp [hN, oddHarmonicPrefix]
    have hhalf : N/2 < N := Nat.div_lt_self (Nat.pos_of_ne_zero hN) (by norm_num)
    rw [odd_recurrence]
    calc
      _ ≤ |harmonicPrefix N|+|oddHarmonicPrefix (N/2)/2| := abs_add_le _ _
      _ ≤ 1+2/2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add (harmonic_bound N) (div_le_div_of_nonneg_right (ih _ hhalf) (by norm_num))
      _ = 2 := by norm_num

private theorem odd_eq_range (N : ℕ) : oddHarmonicPrefix N =
    ∑ n ∈ range (N+1), if Odd n then (ArithmeticFunction.moebius n : ℝ)/(n : ℝ) else 0 := by
  classical
  rw [oddHarmonicPrefix, sum_filter,
    show range (N+1) = Ioc 0 N ∪ {0} by ext n; simp,
    sum_union (by simp)]
  simp

private theorem odd_anchored {D M : ℕ} (hDM : D < M) (b : ℕ → ℝ) :
    weightedOddTail D M b = b M*(oddHarmonicPrefix M-oddHarmonicPrefix D) +
      ∑ n ∈ Ioc D (M-1), (b n-b (n+1))*(oddHarmonicPrefix n-oddHarmonicPrefix D) := by
  classical
  have h := PrimePrefixMobiusDirectedAbel.anchored_sum_by_parts hDM
    (fun n => if Odd n then (ArithmeticFunction.moebius n : ℝ)/(n : ℝ) else 0) b
  simpa only [weightedOddTail, sum_filter, ite_mul, zero_mul, ← odd_eq_range] using h

/-- Unconditional arithmetic pays the full anchored odd harmonic tail, including its last endpoint. -/
theorem result :
    (∀ N : ℕ, |harmonicPrefix N| ≤ 1 ∧ |oddHarmonicPrefix N| ≤ 2) ∧
    oddHarmonicPrefix 1 = 1 ∧
    (∀ (D M : ℕ), D < M → ∀ b : ℕ → ℝ,
      weightedOddTail D M b = b M*(oddHarmonicPrefix M-oddHarmonicPrefix D) +
        ∑ n ∈ Ioc D (M-1), (b n-b (n+1))*(oddHarmonicPrefix n-oddHarmonicPrefix D)) ∧
    (∀ (D M : ℕ), D < M → ∀ b : ℕ → ℝ,
      (∀ n ∈ Icc (D+1) M, 0 ≤ b n) →
      AntitoneOn b (Set.Icc (D+1) M) →
      (-2-oddHarmonicPrefix D)*b (D+1) ≤ weightedOddTail D M b ∧
      weightedOddTail D M b ≤ (2-oddHarmonicPrefix D)*b (D+1) ∧
      |weightedOddTail D M b| ≤ 4*b (D+1)) := by
  refine ⟨fun N => ⟨harmonic_bound N, odd_bound N⟩, ?_,
    fun D M hDM b => odd_anchored hDM b, ?_⟩
  · simp [oddHarmonicPrefix, sum_filter, show Ioc 0 1 = {1} by decide]
  · intro D M hDM b hb hanti
    have hbM : 0 ≤ b M := hb M (mem_Icc.mpr ⟨by omega, le_rfl⟩)
    have hbfirst : 0 ≤ b (D+1) := hb (D+1) (mem_Icc.mpr ⟨le_rfl, by omega⟩)
    have hsteps (n : ℕ) (hn : n ∈ Ioc D (M-1)) : 0 ≤ b n-b (n+1) := by
      have hn' := mem_Ioc.mp hn
      exact sub_nonneg.mpr (hanti ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
    have hterminal := abs_le.mp (odd_bound M)
    have hlow : (-2-oddHarmonicPrefix D)*b M ≤ b M*(oddHarmonicPrefix M-oddHarmonicPrefix D) := by
      have := mul_le_mul_of_nonneg_left hterminal.1 hbM
      nlinarith
    have hhigh : b M*(oddHarmonicPrefix M-oddHarmonicPrefix D) ≤ (2-oddHarmonicPrefix D)*b M := by
      have := mul_le_mul_of_nonneg_left hterminal.2 hbM
      nlinarith
    have hsumlow :
        (∑ n ∈ Ioc D (M-1), (-2-oddHarmonicPrefix D)*(b n-b (n+1))) ≤
          ∑ n ∈ Ioc D (M-1), (b n-b (n+1))*(oddHarmonicPrefix n-oddHarmonicPrefix D) := by
      apply sum_le_sum
      intro n hn
      have := mul_le_mul_of_nonneg_left (abs_le.mp (odd_bound n)).1 (hsteps n hn)
      nlinarith
    have hsumhigh :
        (∑ n ∈ Ioc D (M-1), (b n-b (n+1))*(oddHarmonicPrefix n-oddHarmonicPrefix D)) ≤
          ∑ n ∈ Ioc D (M-1), (2-oddHarmonicPrefix D)*(b n-b (n+1)) := by
      apply sum_le_sum
      intro n hn
      have := mul_le_mul_of_nonneg_left (abs_le.mp (odd_bound n)).2 (hsteps n hn)
      nlinarith
    rw [← mul_sum, PrimePrefixMobiusDirectedAbel.step_sum hDM b] at hsumlow hsumhigh
    have htail := odd_anchored hDM b
    have hlo : (-2-oddHarmonicPrefix D)*b (D+1) ≤ weightedOddTail D M b := by nlinarith
    have hhi : weightedOddTail D M b ≤ (2-oddHarmonicPrefix D)*b (D+1) := by nlinarith
    refine ⟨hlo, hhi, abs_le.mpr ⟨?_, ?_⟩⟩
    · have := mul_le_mul_of_nonneg_right (abs_le.mp (odd_bound D)).2 hbfirst
      nlinarith
    · have := mul_le_mul_of_nonneg_right (abs_le.mp (odd_bound D)).1 hbfirst
      nlinarith

end D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail
#print axioms D5.S3.Arith.Robin.ActualOddHarmonicMobiusTail.result

/- GID: D5/S3/Arith/Robin/Analytic/LcmPowerLogLattice
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/LcmPowerLogLattice
   mirror-E: none(waiver:irrational-rotation)
   anchors: [mathlib/module/Mathlib.Topology.Instances.AddCircle.DenseSubgroup]
   utility: none
   digest: Positive-tail density for distinct prime logarithms. -/
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Irrational logarithmic lattices meet every open interval arbitrarily far along both indices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice

open Real Set Filter
open scoped Topology

/-- Distinct primes have incommensurable logarithms. -/
theorem irrational_prime_log_ratio {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : Irrational (log (p : ℝ) / log (q : ℝ)) := by
  rintro ⟨r, hr⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlp : 0 < log (p : ℝ) := log_pos hp1
  have hlq : 0 < log (q : ℝ) := log_pos hq1
  have hrpos : (0 : ℚ) < r := by
    have : (0 : ℝ) < (r : ℝ) := by rw [hr]; exact div_pos hlp hlq
    exact_mod_cast this
  have hn : 0 < r.num := Rat.num_pos.mpr hrpos
  have hd : 0 < r.den := r.pos
  have hcast : (r.num.toNat : ℝ) = (r.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn.le
  have hlin : (r.den : ℝ) * log (p : ℝ) =
      (r.num.toNat : ℝ) * log (q : ℝ) := by
    rw [Rat.cast_def] at hr
    have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [hcast]
    field_simp [hlq.ne', hden] at hr
    nlinarith only [hr]
  have hlogs : log ((p : ℝ) ^ r.den) = log ((q : ℝ) ^ r.num.toNat) := by
    simpa only [log_pow] using hlin
  have hpowers : (p : ℝ) ^ r.den = (q : ℝ) ^ r.num.toNat :=
    strictMonoOn_log.injOn (show 0 < (p : ℝ) ^ r.den by positivity)
      (show 0 < (q : ℝ) ^ r.num.toNat by positivity) hlogs
  have hnat : p ^ r.den = q ^ r.num.toNat := by exact_mod_cast hpowers
  have hdiv : p ∣ q ^ r.num.toNat := by
    rw [← hnat]
    obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    rw [hd']
    exact ⟨p ^ d, by simp [pow_succ, mul_comm]⟩
  exact hpq ((Nat.dvd_prime hq).mp (hp.dvd_of_dvd_pow hdiv) |>.resolve_left hp.ne_one)

/-- Both nonnegative coefficients can be forced into any prescribed tail. -/
theorem positive_tail_lattice {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hirr : Irrational (a / b)) (huv : u < v) (N : ℕ) :
    ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ u < (i : ℝ) * a - (j : ℝ) * b ∧
      (i : ℝ) * a - (j : ℝ) * b < v := by
  letI : Fact (0 < b) := ⟨hb⟩
  have hd : DenseRange (fun k : ℤ => k • (a : AddCircle b)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr hirr
  let x : AddCircle b := ((u + v) / 2 : ℝ)
  have hc : MapClusterPt x atTop (fun n : ℕ => n • (a : AddCircle b)) :=
    ((mapClusterPt_atTop_nsmul_tfae x (a : AddCircle b)).out 1 4).mpr (hd x)
  let U : Set (AddCircle b) := ((↑) : ℝ → AddCircle b) '' Ioo u v
  have hU : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hxU : x ∈ U := ⟨(u + v) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hf : ∃ᶠ n : ℕ in atTop, n • (a : AddCircle b) ∈ U :=
    hc.frequently (hU.mem_nhds hxU)
  obtain ⟨K, hK⟩ := exists_nat_gt (((N : ℝ) * b + v) / a)
  obtain ⟨i, hi, hmem⟩ := frequently_atTop.mp hf (max N K)
  obtain ⟨y, hy, heq⟩ := hmem
  have hzero : (((i : ℝ) * a - y : ℝ) : AddCircle b) = 0 := by
    rw [AddCircle.coe_sub, ← nsmul_eq_mul, AddCircle.coe_nsmul, heq, sub_self]
  obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff b).mp hzero
  simp only [zsmul_eq_mul] at hj
  have hKi : (K : ℝ) ≤ i := by exact_mod_cast (le_max_right N K).trans hi
  have hbig : (N : ℝ) * b + v < (i : ℝ) * a := by
    have hh := (div_lt_iff₀ ha).mp hK
    exact hh.trans_le (mul_le_mul_of_nonneg_right hKi ha.le)
  have hjN : (N : ℝ) < (j : ℝ) := by
    apply (mul_lt_mul_iff_of_pos_right hb).mp
    linarith [hy.2]
  have hjNi : (N : ℤ) ≤ j := by exact_mod_cast hjN.le
  have hj0 : 0 ≤ j := (by positivity : (0 : ℤ) ≤ N).trans hjNi
  have hjcast : (j.toNat : ℝ) = (j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hj0
  refine ⟨i, j.toNat, (le_max_left N K).trans hi, ?_, ?_, ?_⟩
  · have hh : (N : ℤ) ≤ (j.toNat : ℤ) := by
      simpa only [Int.toNat_of_nonneg hj0] using hjNi
    exact_mod_cast hh
  · rw [hjcast]
    linarith [hy.1]
  · rw [hjcast]
    linarith [hy.2]

/-- Distinct prime logarithms meet every open interval with arbitrarily large indices. -/
theorem prime_log_lattice_tail {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {u v : ℝ} (huv : u < v) (N : ℕ) :
    ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ u < (i : ℝ) * log (p : ℝ) - (j : ℝ) * log (q : ℝ) ∧
      (i : ℝ) * log (p : ℝ) - (j : ℝ) * log (q : ℝ) < v := by
  exact positive_tail_lattice (log_pos (by exact_mod_cast hp.one_lt))
    (log_pos (by exact_mod_cast hq.one_lt)) (irrational_prime_log_ratio hp hq hpq) huv N

end D5.S3.Arith.Robin.Analytic.LcmPowerLogLattice

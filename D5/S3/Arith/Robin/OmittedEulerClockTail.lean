/- GID: D5/S3/Arith/Robin/OmittedEulerClockTail
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OmittedEulerClockTail
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The inclusive omitted prime tail keeps its first atom and next-prime clock. -/

import D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
import D5.S3.Arith.Robin.LogarithmicMellinReserve
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The Mertens supplier is the Apache-licensed PrimeNumberTheoremAnd port
at 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (see its original source header).
The new estimate retains the inclusive first omitted atom, not just a window.
The clock is log p; no sign of the other terms of CS.11 is asserted. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open Set Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace D5.S3.Arith.Robin.OmittedEulerClockTail

open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
open D5.S3.Arith.Robin.LogarithmicMellinReserve

def mertensBudget : ℝ := Real.log 4 + 4

def anchorBudget (p : ℕ) : ℝ :=
  mertensBudget - ((∑ q ∈ primeCutoff p, Real.log (q : ℝ) / q) - Real.log p)
    + Real.log p / p

def cumulative (p : ℕ) (t : ℝ) : ℝ :=
  ∑ q ∈ (primeCutoff t).filter (p ≤ ·), Real.log (q : ℝ) / q

def primeTail (p : ℕ) (u : ℝ) (q : ℕ) : ℝ :=
  if q.Prime ∧ p ≤ q then (q : ℝ) ^ (-1 - u) else 0

private lemma cutoff_mem {t : ℝ} {q : ℕ} :
    q ∈ primeCutoff t ↔ 0 < q ∧ q ≤ ⌊t⌋₊ ∧ q.Prime := by
  simp only [primeCutoff, mem_filter, Finset.mem_Ioc, and_assoc]

private lemma cumulative_eq {p : ℕ} (hp : p.Prime) {t : ℝ} (ht : (p : ℝ) ≤ t) :
    cumulative p t = (∑ q ∈ primeCutoff t, Real.log (q : ℝ) / q) -
      (∑ q ∈ primeCutoff p, Real.log (q : ℝ) / q) + Real.log p / p := by
  classical
  have hpt : p ≤ ⌊t⌋₊ := Nat.le_floor ht
  have hpS : p ∈ primeCutoff p := cutoff_mem.mpr ⟨hp.pos, by simp, hp⟩
  have hsub : (primeCutoff p).erase p ⊆ primeCutoff t := by
    intro q hq
    have h := cutoff_mem.mp (mem_erase.mp hq).2
    exact cutoff_mem.mpr ⟨h.1, h.2.1.trans (by simpa using hpt), h.2.2⟩
  have heq : (primeCutoff t).filter (p ≤ ·) =
      primeCutoff t \ (primeCutoff p).erase p := by
    ext q
    simp only [mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hq, hpq⟩
      refine ⟨hq, ?_⟩
      intro hqe
      have he := Finset.mem_erase.mp hqe
      have hqle : q ≤ p := by simpa using (cutoff_mem.mp he.2).2.1
      exact he.1 (Nat.le_antisymm hqle hpq)
    · rintro ⟨hq, hqe⟩
      refine ⟨hq, ?_⟩
      by_contra h
      have hqp : q < p := lt_of_not_ge h
      apply hqe
      refine Finset.mem_erase.mpr ⟨hqp.ne, ?_⟩
      have hh := cutoff_mem.mp hq
      exact cutoff_mem.mpr ⟨hh.1, by simpa using hqp.le, hh.2.2⟩
  have hs := sum_sdiff hsub (f := fun q : ℕ => Real.log (q : ℝ) / q)
  have he := sum_erase_add (primeCutoff p) (fun q : ℕ => Real.log (q : ℝ) / q) hpS
  rw [cumulative, heq]
  linarith

private lemma anchorBudget_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ anchorBudget p := by
  have h := (abs_le.mp (Mertens.sum_log_prime_div_eq_log
    (x := (p : ℝ)) (by exact_mod_cast hp.one_le))).2
  change (∑ q ∈ primeCutoff p, Real.log (q : ℝ) / q) - Real.log p ≤ mertensBudget at h
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  dsimp [anchorBudget]
  have hd : 0 ≤ mertensBudget -
      ((∑ q ∈ primeCutoff p, Real.log (q : ℝ) / q) - Real.log p) := by linarith
  exact add_nonneg hd (div_nonneg hlog (Nat.cast_nonneg p))

private lemma cumulative_le {p : ℕ} (hp : p.Prime) {t : ℝ} (ht : (p : ℝ) ≤ t) :
    cumulative p t ≤ Real.log (t / p) + anchorBudget p := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have ht1 : 1 ≤ t := (by exact_mod_cast hp.one_le : (1 : ℝ) ≤ p).trans ht
  have h := (abs_le.mp (Mertens.sum_log_prime_div_eq_log ht1)).2
  change (∑ q ∈ primeCutoff t, Real.log (q : ℝ) / q) - Real.log t ≤ mertensBudget at h
  rw [cumulative_eq hp ht, Real.log_div (hp0.trans_le ht).ne' hp0.ne']
  dsimp [anchorBudget]
  linarith

private def tailPrimitive (p : ℕ) (u h x : ℝ) : ℝ :=
  u * highPrimitive u x + (Real.log p - h) * x ^ (-u)

private lemma tailPrimitive_deriv {p : ℕ} {u h x : ℝ}
    (hu : 0 < u) (hx : 0 < x) (hp : 0 < p) :
    HasDerivAt (tailPrimitive p u h)
      (u * x ^ (-u - 1) * (Real.log (x / p) + h)) x := by
  have hd := ((hasDerivAt_highPrimitive hu hx).const_mul u).add
    ((Real.hasDerivAt_rpow_const (p := -u) (Or.inl hx.ne')).const_mul (Real.log p - h))
  convert hd using 1 <;> try rfl
  rw [Real.log_div hx.ne' (by exact_mod_cast hp.ne')]
  ring

private lemma tailPrimitive_limit (p : ℕ) {u : ℝ} (hu : 0 < u) (h : ℝ) :
    Tendsto (tailPrimitive p u h) atTop (𝓝 0) := by
  convert ((tendsto_highPrimitive hu).const_mul u).add
    ((tendsto_rpow_neg_atTop hu).const_mul (Real.log p - h)) using 1 <;>
    first | rfl | simp

private lemma envelope_integral {p : ℕ} (hp : p.Prime) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun x : ℝ => u * x ^ (-u - 1) *
      (Real.log (x / p) + anchorBudget p)) (Ioi (p : ℝ)) ∧
    (∫ x in Ioi (p : ℝ), u * x ^ (-u - 1) *
      (Real.log (x / p) + anchorBudget p)) =
        (p : ℝ) ^ (-u) * (1 / u + anchorBudget p) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hd : ∀ x ∈ Ici (p : ℝ), HasDerivAt (tailPrimitive p u (anchorBudget p))
      (u * x ^ (-u - 1) * (Real.log (x / p) + anchorBudget p)) x := by
    intro x hx
    exact tailPrimitive_deriv hu (hp0.trans_le hx) hp.pos
  have hn : ∀ x ∈ Ioi (p : ℝ),
      0 ≤ u * x ^ (-u - 1) * (Real.log (x / p) + anchorBudget p) := by
    intro x hx
    have hlog : 0 ≤ Real.log (x / p) := Real.log_nonneg
      ((le_div_iff₀ hp0).mpr (by simpa using hx.le))
    exact mul_nonneg (mul_nonneg hu.le (Real.rpow_nonneg (hp0.trans hx).le _))
      (add_nonneg hlog (anchorBudget_nonneg hp))
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hn (tailPrimitive_limit p hu _), ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hn (tailPrimitive_limit p hu _)]
  dsimp [tailPrimitive, highPrimitive]
  field_simp [hu.ne']
  ring

private def atom (q : ℕ) (u : ℝ) : ℝ → ℝ :=
  (Ioi (q : ℝ)).indicator (fun x => u * x ^ (-u - 1) * (Real.log q / q))

private lemma atom_integral {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q)
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (atom q u) (Ioi (p : ℝ)) ∧
    (∫ x in Ioi (p : ℝ), atom q u x) = (q : ℝ) ^ (-u) * (Real.log q / q) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have hi := ((integrableOn_Ioi_rpow_of_lt
    (by linarith : -u - 1 < -1) hp0).const_mul u).mul_const (Real.log q / q)
  refine ⟨hi.indicator measurableSet_Ioi, ?_⟩
  rw [atom, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
    max_eq_right (by exact_mod_cast hpq), integral_mul_const, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -u - 1 < -1) hq0]
  congr 1
  field_simp [hu.ne']
  ring

private lemma finite_weighted_tail {p : ℕ} (hp : p.Prime) {u : ℝ} (hu : 0 < u)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime ∧ p ≤ q) :
    (∑ q ∈ S, (q : ℝ) ^ (-u) * (Real.log q / q)) ≤
      (p : ℝ) ^ (-u) * (1 / u + anchorBudget p) := by
  classical
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hsumint : IntegrableOn (fun x => ∑ q ∈ S, atom q u x) (Ioi (p : ℝ)) := by
    apply integrable_finsetSum
    intro q hq
    exact (atom_integral hp (hS q hq).1 (hS q hq).2 hu).1
  have heq : (∑ q ∈ S, (q : ℝ) ^ (-u) * (Real.log q / q)) =
      ∫ x in Ioi (p : ℝ), ∑ q ∈ S, atom q u x := by
    rw [integral_finsetSum]
    · exact sum_congr rfl fun q hq =>
        (atom_integral hp (hS q hq).1 (hS q hq).2 hu).2.symm
    · intro q hq
      exact (atom_integral hp (hS q hq).1 (hS q hq).2 hu).1
  rw [heq]
  apply le_trans (integral_mono_ae hsumint (envelope_integral hp hu).1 ?_)
    (envelope_integral hp hu).2.le
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hsub : S.filter (fun q : ℕ => (q : ℝ) < x) ⊆ (primeCutoff x).filter (fun q : ℕ => p ≤ q) := by
    intro q hq
    obtain ⟨hqS, hqx⟩ := mem_filter.mp hq
    have hqP := hS q hqS
    exact mem_filter.mpr
      ⟨cutoff_mem.mpr ⟨hqP.1.pos, Nat.le_floor hqx.le, hqP.1⟩, hqP.2⟩
  have hbd : (∑ q ∈ S.filter (fun q : ℕ => (q : ℝ) < x), Real.log (q : ℝ) / q) ≤ cumulative p x := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro q hq _
    have hqP := (cutoff_mem.mp (mem_filter.mp hq).1).2.2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hqP.one_le)) (Nat.cast_nonneg q)
  have hatom : (∑ q ∈ S, atom q u x) =
      u * x ^ (-u - 1) * ∑ q ∈ S.filter (fun q : ℕ => (q : ℝ) < x), Real.log (q : ℝ) / q := by
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro q hq
    simp only [atom, indicator_apply, Set.mem_Ioi]
    split_ifs <;> simp
  rw [hatom]
  exact mul_le_mul_of_nonneg_left (hbd.trans (cumulative_le hp hx.le))
    (mul_nonneg hu.le (Real.rpow_nonneg (hp0.trans hx).le _))

private lemma finite_prime_tail {p : ℕ} (hp : p.Prime) {u : ℝ} (hu : 0 < u)
    (S : Finset ℕ) :
    (∑ q ∈ S, primeTail p u q) ≤
      (p : ℝ) ^ (-u) * (1 / u + anchorBudget p) / Real.log p := by
  classical
  let F := S.filter (fun q => q.Prime ∧ p ≤ q)
  have hF : ∀ q ∈ F, q.Prime ∧ p ≤ q := fun q hq => (mem_filter.mp hq).2
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hs : (∑ q ∈ S, primeTail p u q) = ∑ q ∈ F, (q : ℝ) ^ (-1 - u) := by
    simp only [F, sum_filter, primeTail]
  rw [hs, le_div_iff₀ hL, sum_mul]
  apply le_trans (sum_le_sum ?_) (finite_weighted_tail hp hu F hF)
  intro q hq
  have hqP := hF q hq
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hqP.1.pos
  have hlog : Real.log (p : ℝ) ≤ Real.log q :=
    Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hqP.2)
  have heq : (q : ℝ) ^ (-1 - u) = (q : ℝ) ^ (-u) / q := by
    rw [show -1 - u = -u + (-1) by ring, Real.rpow_add hq0, Real.rpow_neg_one]
    rfl
  rw [heq]
  calc
    (q : ℝ) ^ (-u) / q * Real.log p ≤ (q : ℝ) ^ (-u) / q * Real.log q :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by ring

/-- The entire inclusive omitted prime tail, with its actual first prime retained. -/
theorem prime_tail_bound {p : ℕ} (hp : p.Prime) {u : ℝ} (hu : 0 < u) :
    Summable (primeTail p u) ∧ (∑' q : ℕ, primeTail p u q) ≤
      (p : ℝ) ^ (-u) * (1 / (u * Real.log p) + anchorBudget p / Real.log p) := by
  have hn : 0 ≤ primeTail p u := by
    intro q
    dsimp [primeTail]
    split_ifs <;> positivity
  have hb := finite_prime_tail hp hu
  refine ⟨summable_of_sum_le hn hb, ?_⟩
  apply le_trans (Real.tsum_le_of_sum_le hn hb)
  apply le_of_eq
  ring

private lemma finite_euler_defect (S T : Finset ℕ) (hST : S ⊆ T)
    (hT : ∀ q ∈ T, q.Prime) {s : ℝ} (hs : 0 < s) :
    0 ≤ eulerProduct S s - eulerProduct T s ∧
    eulerProduct S s - eulerProduct T s ≤
      eulerProduct S s * ∑ q ∈ T \ S, (q : ℝ) ^ (-s) := by
  classical
  have hx (q : ℕ) (hq : q ∈ T) :
      0 ≤ (q : ℝ) ^ (-s) ∧ (q : ℝ) ^ (-s) < 1 :=
    ⟨Real.rpow_nonneg (Nat.cast_nonneg q) _,
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hT q hq).one_lt) (by linarith)⟩
  have hn (q : ℕ) (hq : q ∈ T) : 0 ≤ localFactor q s := by
    dsimp [localFactor]
    linarith [(hx q hq).2]
  have hS0 : 0 ≤ eulerProduct S s := prod_nonneg fun q hq => hn q (hST hq)
  have hD0 : 0 ≤ eulerProduct (T \ S) s :=
    prod_nonneg fun q hq => hn q (Finset.mem_sdiff.mp hq).1
  have hD1 : eulerProduct (T \ S) s ≤ 1 := by
    apply prod_le_one (fun q hq => hn q (Finset.mem_sdiff.mp hq).1)
    intro q hq
    dsimp [localFactor]
    linarith [(hx q (Finset.mem_sdiff.mp hq).1).1]
  have hDb : 1 - eulerProduct (T \ S) s ≤ ∑ q ∈ T \ S, (q : ℝ) ^ (-s) := by
    have he := prod_one_sub_ordered (T \ S) (fun q : ℕ => (q : ℝ) ^ (-s))
    change eulerProduct (T \ S) s = _ at he
    rw [he, sub_sub_cancel]
    apply sum_le_sum
    intro q hq
    apply mul_le_of_le_one_right (hx q (Finset.mem_sdiff.mp hq).1).1
    apply prod_le_one
    · intro r hr
      have hrT := (Finset.mem_sdiff.mp (mem_filter.mp hr).1).1
      linarith [(hx r hrT).2]
    · intro r hr
      have hrT := (Finset.mem_sdiff.mp (mem_filter.mp hr).1).1
      linarith [(hx r hrT).1]
  have he : eulerProduct T s = eulerProduct S s * eulerProduct (T \ S) s := by
    exact (prod_sdiff hST).symm.trans (mul_comm _ _)
  rw [he, show eulerProduct S s - eulerProduct S s * eulerProduct (T \ S) s =
    eulerProduct S s * (1 - eulerProduct (T \ S) s) by ring]
  exact ⟨mul_nonneg hS0 (by linarith), mul_le_mul_of_nonneg_left hDb hS0⟩

private lemma euler_limit {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => eulerProduct (Nat.primesBelow n) (1 + u)) atTop
      (𝓝 (1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re)) := by
  have hs : 1 < (((1 + u : ℝ) : ℂ)).re := by simpa using hu
  have he := (riemannZeta_eulerProduct hs).inv₀ (riemannZeta_ne_zero_of_one_lt_re hs)
  have hz : riemannZeta ((1 + u : ℝ) : ℂ) =
      ((riemannZeta ((1 + u : ℝ) : ℂ)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using
        riemannZeta_im_eq_zero_of_one_lt (x := 1 + u) (by linarith)
  rw [hz, ← Complex.ofReal_inv] at he
  have hmap : ∀ n : ℕ,
      (∏ q ∈ Nat.primesBelow n, (1 - (q : ℂ) ^ (-((1 + u : ℝ) : ℂ)))⁻¹)⁻¹ =
        (eulerProduct (Nat.primesBelow n) (1 + u) : ℂ) := by
    intro n
    rw [prod_inv_distrib]
    simp only [inv_inv, eulerProduct, localFactor, Complex.ofReal_prod]
    apply prod_congr rfl
    intro q hq
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg q),
      Complex.ofReal_neg]
    norm_cast
  have hh := (Complex.continuous_re.tendsto _).comp he
  simpa only [Function.comp_def, hmap, Complex.ofReal_re, one_div] using hh

/-- `p` is the literal first prime omitted by the cutoff `z`. -/
def NextPrime (z : ℝ) (p : ℕ) : Prop :=
  p.Prime ∧ z < p ∧ ∀ q : ℕ, q.Prime → z < q → p ≤ q

/-- The actual Euler deficit is paid by the full inclusive omitted prime tail.
The original finite Euler prefactor remains on the right. -/
theorem actual_euler_defect {z : ℝ} {p : ℕ} (hp : NextPrime z p)
    {u : ℝ} (hu : 0 < u) :
    0 ≤ actualEuler z (1 + u) - 1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re ∧
    actualEuler z (1 + u) - 1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re ≤
      actualEuler z (1 + u) * (p : ℝ) ^ (-u) *
        (1 / (u * Real.log p) + anchorBudget p / Real.log p) := by
  classical
  have hs : 0 < 1 + u := by linarith
  have hE0 : 0 ≤ actualEuler z (1 + u) := by
    unfold actualEuler eulerProduct
    apply prod_nonneg
    intro q hq
    have hqP := (cutoff_mem.mp hq).2.2
    dsimp [localFactor]
    have hq1 := Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hqP.one_lt : (1 : ℝ) < q) (by linarith : -(1 + u) < 0)
    linarith
  have hbound := prime_tail_bound hp.1 hu
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 ≤ actualEuler z (1 + u) - eulerProduct (Nat.primesBelow n) (1 + u) ∧
      actualEuler z (1 + u) - eulerProduct (Nat.primesBelow n) (1 + u) ≤
        actualEuler z (1 + u) * ∑' q : ℕ, primeTail p u q := by
    filter_upwards [eventually_gt_atTop ⌊z⌋₊] with n hn
    have hsub : primeCutoff z ⊆ Nat.primesBelow n := by
      intro q hq
      have h := cutoff_mem.mp hq
      exact Nat.mem_primesBelow.mpr ⟨h.2.1.trans_lt hn, h.2.2⟩
    have hfin := finite_euler_defect (primeCutoff z) (Nat.primesBelow n) hsub
      (fun q hq => (Nat.mem_primesBelow.mp hq).2) hs
    refine ⟨hfin.1, hfin.2.trans (mul_le_mul_of_nonneg_left ?_ hE0)⟩
    have htail : (∑ q ∈ Nat.primesBelow n \ primeCutoff z, (q : ℝ) ^ (-(1 + u))) =
        ∑ q ∈ Nat.primesBelow n \ primeCutoff z, primeTail p u q := by
      apply sum_congr rfl
      intro q hq
      obtain ⟨hqT, hqS⟩ := Finset.mem_sdiff.mp hq
      have hqP := (Nat.mem_primesBelow.mp hqT).2
      have hzq : z < (q : ℝ) := by
        by_contra h
        exact hqS (cutoff_mem.mpr ⟨hqP.pos, Nat.le_floor (le_of_not_gt h), hqP⟩)
      have hqp : q.Prime ∧ p ≤ q := ⟨hqP, hp.2.2 q hqP hzq⟩
      rw [primeTail, if_pos hqp]
      congr 1
      ring
    rw [htail]
    exact hbound.1.sum_le_tsum _ (fun q _ => by
      dsimp [primeTail]
      split_ifs <;> positivity)
  have hlim : Tendsto (fun n : ℕ => actualEuler z (1 + u) -
      eulerProduct (Nat.primesBelow n) (1 + u)) atTop
      (𝓝 (actualEuler z (1 + u) - 1 / (riemannZeta ((1 + u : ℝ) : ℂ)).re)) :=
    tendsto_const_nhds.sub (euler_limit hu)
  have h0 := ge_of_tendsto hlim (hevent.mono fun n h => h.1)
  have hb := le_of_tendsto hlim (hevent.mono fun n h => h.2)
  refine ⟨h0, hb.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left hbound.2 hE0
  simpa only [mul_assoc] using hh

#print axioms prime_tail_bound
#print axioms actual_euler_defect

end D5.S3.Arith.Robin.OmittedEulerClockTail

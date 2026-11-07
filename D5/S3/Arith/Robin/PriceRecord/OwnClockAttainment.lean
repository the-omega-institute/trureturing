/- GID: D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/OwnClockAttainment
   mirror-E: none(waiver:general-real-analysis)
   anchors: []
   utility: none
   digest: Compact sublevels and attained minimum for the literal Robin interpolation on any finite p>=2 support with theta>1. -/

/- UNCOMPILED SOURCE CANDIDATE. The finite Pi-space is only a coordinate chart
for the EXACT upstream phi. No new objective or infimum is defined. Functions
on all naturals cannot have a unique minimizer as functions: values outside S
are invisible. The finite chart removes that redundancy. Existence is proved
here, before any use of minimizer first-order conditions. -/

import D5.S3.Arith.Robin.PriceRecord.OwnClockContraction
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.OwnClockAttainment

open Real Set Finset
open D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
open D5.S3.Arith.Robin.PriceRecord.OwnClockContraction
open D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
open D5.S3.Arith.GoldenResource.ContinuousPrimeMaximum

/-- Canonical extension, fixing only the irrelevant off-support coordinates. -/
def extend {S : Finset ℕ} (a : S → ℝ) (p : ℕ) : ℝ :=
  if h : p ∈ S then a ⟨p, h⟩ else 1

/-- The original boundary-one domain in a finite real Pi-space. -/
def orthant (S : Finset ℕ) : Set (S → ℝ) := {a | ∀ p, 1 ≤ a p}

/-- The constant normalization already present in the literal Euler factors. -/
def eulerNormalization (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, log (1 - (p : ℝ) ^ (-1 : ℝ))

@[simp] lemma extend_apply {S : Finset ℕ} (a : S → ℝ) (p : S) :
    extend a p = a p := by simp [extend, p.property]

lemma extend_admissible {S : Finset ℕ} {a : S → ℝ} (ha : a ∈ orthant S) :
    admissible S (extend a) := by
  intro p hp
  simpa [extend, hp] using ha (⟨p, hp⟩ : S)

lemma clock_coordinates {S : Finset ℕ} (a : S → ℝ) :
    clock S (extend a) = ∑ p : S, a p * log (p : ℝ) := by
  rw [clock, ← sum_coe_sort S]
  simp only [extend_apply]

lemma phi_coordinates {S : Finset ℕ} (a : S → ℝ) :
    phi S (extend a) = eulerMascheroniConstant +
      log (log (∑ p : S, a p * log (p : ℝ))) - ∑ p : S, benefit p (a p) := by
  rw [phi, clock_coordinates, ← sum_coe_sort S]
  simp only [terminalCost, extend_apply]

/-- Every old full vector is represented, with its literal objective unchanged. -/
lemma phi_restrict {S : Finset ℕ} (x : ℕ → ℝ) :
    phi S (extend (fun p : S => x p)) = phi S x := by
  have hL : clock S (extend (fun p : S => x p)) = clock S x := by
    exact sum_congr rfl (fun p hp => by simp [extend, hp])
  have hB : (∑ p ∈ S, benefit p (extend (fun p : S => x p) p)) =
      ∑ p ∈ S, benefit p (x p) := by
    exact sum_congr rfl (fun p hp => by simp [extend, hp])
  simp only [phi, hL, hB]

private lemma continuous_clock (S : Finset ℕ) :
    Continuous (fun a : S → ℝ => clock S (extend a)) := by
  simp_rw [clock_coordinates]
  exact continuous_finsetSum _ (fun p _ => (continuous_apply p).mul continuous_const)

/-- Continuity is asserted on the valid closed orthant, where both logs and
actual Euler factors have the required positive arguments. -/
theorem phi_continuousOn {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S) :
    ContinuousOn (fun a : S → ℝ => phi S (extend a)) (orthant S) := by
  have hclock0 : ∀ a ∈ orthant S, clock S (extend a) ≠ 0 := by
    intro a ha
    have h := theta_le_clock_of_naturalSupport hS (extend_admissible ha)
    exact ne_of_gt (by linarith [hθ, h])
  have hlog0 : ∀ a ∈ orthant S, log (clock S (extend a)) ≠ 0 := by
    intro a ha
    have h := theta_le_clock_of_naturalSupport hS (extend_admissible ha)
    exact (log_pos (lt_of_lt_of_le hθ h)).ne'
  have hcost : ContinuousOn (fun a : S → ℝ => terminalCost (clock S (extend a)))
      (orthant S) := ((continuous_clock S).continuousOn.log hclock0).log hlog0
  have hbenefit : ContinuousOn (fun a : S → ℝ => ∑ p : S, benefit p (a p)) (orthant S) := by
    apply continuousOn_finsetSum
    intro p _ a ha
    have hp : (1 : ℝ) < (p : ℕ) := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (hS p p.property)
    have hc : ContinuousAt (fun t : ℝ => benefit (p : ℝ) t) (a p) :=
      (continuous_prime_hasDerivAt (x := a p) hp (by linarith [ha p])).continuousAt
    exact (hc.comp (continuous_apply p).continuousAt).continuousWithinAt
  have hsum (a : S → ℝ) : (∑ p ∈ S, benefit p (extend a p)) =
      ∑ p : S, benefit p (a p) := by
    rw [← sum_coe_sort S]
    simp only [extend_apply]
  simpa only [phi, hsum, Pi.add_apply, Pi.sub_apply] using (continuousOn_const.add hcost).sub hbenefit

/-- The benefits are bounded above, while the SAME terminal cost grows. -/
theorem coercive_lower {S : Finset ℕ} (hS : naturalSupport S)
    {a : S → ℝ} (ha : a ∈ orthant S) :
    eulerMascheroniConstant + terminalCost (clock S (extend a)) + eulerNormalization S ≤
      phi S (extend a) := by
  have hbenefit : (∑ p ∈ S, benefit p (extend a p)) ≤ -eulerNormalization S := by
    rw [eulerNormalization, ← sum_neg_distrib]
    apply sum_le_sum
    intro p hp
    have hpR : (1 : ℝ) < p := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (hS p hp)
    have haR := extend_admissible ha p hp
    obtain ⟨hu0, hu1⟩ := probability_mem hpR haR
    have hlog : log (1 - probability p (extend a p)) ≤ 0 := by
      simpa only [log_one] using log_le_log (by linarith : 0 < 1 - probability p (extend a p))
        (show 1 - probability p (extend a p) ≤ 1 by linarith)
    rw [benefit_log hpR haR]
    linarith
  dsimp only [phi]
  linarith

private lemma coordinate_mass_le {S : Finset ℕ} (hS : naturalSupport S)
    {a : S → ℝ} (ha : a ∈ orthant S) (p : S) :
    a p * log (p : ℝ) ≤ clock S (extend a) := by
  rw [clock_coordinates]
  apply single_le_sum (s := Finset.univ)
  · intro q _
    have hq : (1 : ℝ) < (q : ℕ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (hS q q.property))
    exact mul_nonneg (by linarith [ha q]) (log_pos hq).le
  · exact mem_univ p


/-- An explicit finite box for every sublevel. -/
theorem sublevel_box {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S)
    {M : ℝ} {a : S → ℝ} (ha : a ∈ orthant S) (hM : phi S (extend a) ≤ M) :
    clock S (extend a) ≤ exp (exp (M - eulerMascheroniConstant - eulerNormalization S)) ∧
      a ∈ Icc (fun _ => (1 : ℝ))
        (fun p : S => exp (exp (M - eulerMascheroniConstant - eulerNormalization S)) /
          log (p : ℝ)) := by
  have hL : theta S ≤ clock S (extend a) :=
    theta_le_clock_of_naturalSupport hS (extend_admissible ha)
  have h0 : 0 < clock S (extend a) := by linarith [hθ, hL]
  have hlog0 : 0 < log (clock S (extend a)) :=
    log_pos (lt_of_lt_of_le hθ hL)
  have hll : log (log (clock S (extend a))) ≤
      M - eulerMascheroniConstant - eulerNormalization S := by
    have := coercive_lower hS ha
    dsimp only [terminalCost] at this
    linarith
  have hlog := (log_le_iff_le_exp hlog0).mp hll
  have hbound := (log_le_iff_le_exp h0).mp hlog
  refine ⟨hbound, ha, ?_⟩
  intro p
  have hpR : (1 : ℝ) < (p : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) (hS p p.property))
  apply (le_div_iff₀ (log_pos hpR)).mpr
  exact (coordinate_mass_le hS ha p).trans hbound

/-- Concrete coercivity in the finite-Pi sup norm. -/
theorem phi_coercive {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S) (M : ℝ) :
    ∃ R : ℝ, ∀ a : S → ℝ, a ∈ orthant S → R < ‖a‖ → M < phi S (extend a) := by
  let H := exp (exp (M - eulerMascheroniConstant - eulerNormalization S))
  refine ⟨2 * H, ?_⟩
  intro a ha hnorm
  by_contra hnot
  have hL := (sublevel_box hS hθ ha (le_of_not_gt hnot)).1
  have hcoords : ∀ p : S, ‖a p‖ ≤ 2 * H := by
    intro p
    have hlog2 : (1 / 2 : ℝ) ≤ log 2 := by
      have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      exact h
    have hwp : (1 / 2 : ℝ) ≤ log (p : ℝ) := hlog2.trans
      (log_le_log (by norm_num) (by exact_mod_cast hS p p.property))
    have hmass := coordinate_mass_le hS ha p
    have hmul := mul_le_mul_of_nonneg_left hwp (by linarith [ha p] : 0 ≤ a p)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ha p])]
    dsimp [H] at *
    nlinarith
  have hb : ‖a‖ ≤ 2 * H :=
    (pi_norm_le_iff_of_nonneg (by dsimp [H]; positivity)).mpr hcoords
  exact (not_lt_of_ge hb) hnorm

/-- Closedness plus the explicit finite box gives genuinely compact sublevels. -/
theorem compact_sublevel {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S) (M : ℝ) :
    IsCompact {a : S → ℝ | a ∈ orthant S ∧ phi S (extend a) ≤ M} := by
  have hO : IsClosed (orthant S) := by
    change IsClosed {a : S → ℝ | ∀ p, 1 ≤ a p}
    simp only [setOf_forall]
    exact isClosed_iInter (fun p => isClosed_le continuous_const (continuous_apply p))
  have hclosed : IsClosed {a : S → ℝ | a ∈ orthant S ∧ phi S (extend a) ≤ M} :=
    hO.isClosed_le (phi_continuousOn hS hθ) continuousOn_const
  obtain ⟨R, hR⟩ := phi_coercive hS hθ M
  apply (isCompact_closedBall (0 : S → ℝ) R).of_isClosed_subset hclosed
  intro a ha
  have hnorm : ‖a‖ ≤ R := le_of_not_gt (fun hlt =>
    (not_lt_of_ge ha.2) (hR a ha.1 hlt))
  simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm

/-- Existence comes from a nonempty compact literal sublevel, before KKT. -/
theorem minimum_attained {S : Finset ℕ} (hS : naturalSupport S) (hθ : 1 < theta S) :
    ∃ a : S → ℝ, a ∈ orthant S ∧
      IsMinOn (fun b : S → ℝ => phi S (extend b)) (orthant S) a := by
  let a₀ : S → ℝ := fun _ => 1
  let M := phi S (extend a₀)
  let K : Set (S → ℝ) := {a | a ∈ orthant S ∧ phi S (extend a) ≤ M}
  have ha₀ : a₀ ∈ K := ⟨fun _ => le_rfl, le_rfl⟩
  obtain ⟨a, ha, hmin⟩ := (compact_sublevel hS hθ M).exists_isMinOn
    ⟨a₀, ha₀⟩ ((phi_continuousOn hS hθ).mono (fun _ hx => hx.1))
  refine ⟨a, ha.1, ?_⟩
  intro b hb
  by_cases hM : phi S (extend b) ≤ M
  · exact (isMinOn_iff.mp hmin) b ⟨hb, hM⟩
  · exact ha.2.trans (le_of_lt (lt_of_not_ge hM))

/-- Equality with the EXACT already-defined scalar sInf. -/
lemma infimum_of_minimum {S : Finset ℕ} {a : S → ℝ} (ha : a ∈ orthant S)
    (hmin : IsMinOn (fun b : S → ℝ => phi S (extend b)) (orthant S) a) :
    realInfimum S = phi S (extend a) := by
  have hmem : phi S (extend a) ∈ realValues S :=
    ⟨extend a, extend_admissible ha, rfl⟩
  have hlower : ∀ r ∈ realValues S, phi S (extend a) ≤ r := by
    rintro r ⟨x, hx, rfl⟩
    have hrestrict : (fun p : S => x p) ∈ orthant S := fun p => hx p p.property
    simpa only [phi_restrict] using (isMinOn_iff.mp hmin) (fun p : S => x p) hrestrict
  exact le_antisymm (csInf_le ⟨phi S (extend a), hlower⟩ hmem)
    (le_csInf ⟨phi S (extend a), hmem⟩ hlower)

end D5.S3.Arith.Robin.PriceRecord.OwnClockAttainment

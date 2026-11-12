/- GID: D5/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/PaidPrefixDeletionReserve
   mirror-E: none(waiver:finite-prime-prefix-arithmetic)
   anchors: []
   utility: none
   digest: Exact complete-prefix deletions chosen before the paid repair. -/
import D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
import D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! UNCOMPILED_UNACCEPTED. The original Budget cutoff need not be prime.
The retained cutoff below is an actual prime, chosen by the existing finite
order enumeration. A PNT count pays all O(log X) deletions in advance. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve
open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerPrefixCancellation
open D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder

private theorem shell_sum {X : ℝ} (hX : 0 ≤ X) (Q : ℕ) (hQ : X / 2 ≤ (Q : ℝ)) :
    let S := Nat.primesLE Q \ Nat.primesLE ⌊X / 2⌋₊
    (∀ p ∈ S, p.Prime ∧ X / 2 < (p : ℝ) ∧ p ≤ Q) ∧
      (∑ p ∈ S, log p) = Chebyshev.theta (Q : ℝ) - Chebyshev.theta (X / 2) := by
  classical
  have hfloor : ⌊X / 2⌋₊ ≤ Q := Nat.floor_le_of_le hQ
  have hsub := Nat.primesLE_mono hfloor
  constructor
  · intro p hp
    obtain ⟨hpQ, hpn⟩ := mem_sdiff.mp hp
    obtain ⟨hpQ, hprime⟩ := Nat.mem_primesLE.mp hpQ
    refine ⟨hprime, ?_, hpQ⟩
    by_contra! hn
    exact hpn (Nat.mem_primesLE.mpr
      ⟨(Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ X / 2)).mpr hn, hprime⟩)
  · rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE]
    exact eq_sub_iff_add_eq.mpr (sum_sdiff hsub (f := fun p : ℕ => log (p : ℝ)))

/-- For every prescribed O(log X) count, choose an actual retained prime
strictly above X/2 and delete EXACTLY M largest prefix primes. All constants
precede every real X, every Budget, and the natural count M. Q in Budget.spec
is never assumed prime. The returned ledger pays the complete deleted mass. -/
theorem budget_prefix_deletion_reserve_power (d : ℕ) :
    ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧
      ∀ X : ℝ, T ≤ X → ∀ b : Budget, b.spec X →
      ∀ M : ℕ, (M : ℝ) ≤ C * log X ^ d →
        ∃ Q : ℕ, ∃ D : Finset ℕ, Q.Prime ∧ X / 2 < (Q : ℝ) ∧ Q ≤ b.Q ∧
          D = Nat.primesLE b.Q \ Nat.primesLE Q ∧ D.card = M ∧
          (∀ p ∈ D, p.Prime ∧ Q < p ∧ p ≤ b.Q) ∧
          Chebyshev.theta (b.Q : ℝ) - Chebyshev.theta (Q : ℝ) = ∑ p ∈ D, log p ∧
          (∑ p ∈ D, log p) ≤ (M : ℝ) * log (2 * X) := by
  intro C hC
  classical
  have hhalf : Tendsto (fun X : ℝ => X / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hθ := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2.comp hhalf
  have hθhalf : Tendsto (fun X : ℝ => Chebyshev.theta (X / 2) / X)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := hθ.div_const 2
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    change (Chebyshev.theta (X / 2) / (X / 2)) / 2 = Chebyshev.theta (X / 2) / X
    calc
      _ = Chebyshev.theta (X / 2) / ((X / 2) * 2) := div_div _ _ _
      _ = _ := by congr 1; ring
  have hsqrt : Tendsto (fun X : ℝ => sqrt X / X) atTop (𝓝 0) := by
    simpa only [sqrt_div_self, Function.comp_def] using tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop
  have hlog : Tendsto (fun X : ℝ => log X ^ (d + 1) / X) atTop (𝓝 0) := by
    simpa only [rpow_natCast, rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (d + 1 : ℕ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hgood : ∀ᶠ X : ℝ in atTop,
      4 < X ∧ Chebyshev.theta (X / 2) < (5 / 8) * X ∧
        3 * sqrt X < X / 8 ∧ 2 * C * log X ^ (d + 1) < X / 8 := by
    filter_upwards [eventually_gt_atTop (4 : ℝ),
      hθhalf.eventually (eventually_lt_nhds (by norm_num : (1 / 2 : ℝ) < 5 / 8)),
      hsqrt.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 24)),
      hlog.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (16 * C)))]
      with X hX hθ hs hl
    have hX0 : 0 < X := by linarith
    have hθ' := (div_lt_iff₀ hX0).mp hθ
    have hs' := (div_lt_iff₀ hX0).mp hs
    have hh := (div_lt_div_iff₀ hX0 (by positivity : 0 < 16 * C)).mp hl
    exact ⟨hX, by linarith only [hθ'], by linarith only [hs'], by nlinarith only [hh]⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hgood
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro X hXT b hb M hM
  obtain ⟨hX, hθ, hs, hlog⟩ := hT X ((le_max_left T 2).trans hXT)
  obtain ⟨hb2, hbdef, hhdef, hh0, hh, hQ, hd0, hdlog, hds,
    hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩ := hb
  let S := Nat.primesLE b.Q \ Nat.primesLE ⌊X / 2⌋₊
  obtain ⟨hS, hsum⟩ := shell_sum (by linarith : 0 ≤ X) b.Q hQ.1
  have hbudgetθ : Chebyshev.theta (b.Q : ℝ) = X - b.h - b.δ := by
    have hl : log (b.k : ℝ) = b.h + Chebyshev.theta (b.Q : ℝ) := by
      rw [hbdef, Nat.cast_mul,
        log_mul (by exact_mod_cast (higher_core_pos _).ne')
          (by exact_mod_cast (prefix_integer_pos _).ne'), prefix_integer_log, ← hhdef]
    linarith only [hl, hbudget]
  have hmass : X / 4 < ∑ p ∈ S, log p := by
    rw [hsum, hbudgetθ]
    linarith only [hθ, hs, hh, hds]
  have hlogs : log (2 * X) ≤ 2 * log X := (log_shell hX).2.2
  have hupper : (∑ p ∈ S, log p) ≤ (S.card : ℝ) * (2 * log X) := by
    calc
      _ ≤ ∑ _p ∈ S, (2 * log X) := by
        apply sum_le_sum
        intro p hp
        have hpX : (p : ℝ) ≤ 2 * X :=
          (by exact_mod_cast (hS p hp).2.2 : (p : ℝ) ≤ b.Q).trans hQ.2
        exact (log_le_log (by exact_mod_cast (hS p hp).1.pos) hpX).trans hlogs
      _ = _ := by simp
  have hcard : M < S.card := by
    by_contra! hn
    have hc : (S.card : ℝ) ≤ M := by exact_mod_cast hn
    have hL : 0 < log X := log_pos (by linarith)
    have hh := mul_le_mul_of_nonneg_right (hc.trans hM) (by positivity : 0 ≤ 2 * log X)
    have heq : C * log X ^ d * (2 * log X) = 2 * C * log X ^ (d + 1) := by rw [pow_succ]; ring
    rw [heq] at hh
    linarith only [hmass, hupper, hh, hlog, hX]
  let i : Fin S.card := ⟨S.card - 1 - M, by omega⟩
  let e : Fin S.card ↪o ℕ := S.orderEmbOfFin rfl
  let Q := e i
  let D := (Ioi i).image e
  have hQi : Q ∈ S := S.orderEmbOfFin_mem rfl i
  have hQprime := (hS Q hQi).1
  have hQlo := (hS Q hQi).2.1
  have hQle := (hS Q hQi).2.2
  have hD : D = Nat.primesLE b.Q \ Nat.primesLE Q := by
    ext p
    constructor
    · intro hp
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
      have hjS := S.orderEmbOfFin_mem rfl j
      have hjQ : Q < e j := e.strictMono (mem_Ioi.mp hj)
      exact mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨(hS _ hjS).2.2, (hS _ hjS).1⟩,
        fun hn => hjQ.not_ge (Nat.mem_primesLE.mp hn).1⟩
    · intro hp
      obtain ⟨hpQ, hnot⟩ := mem_sdiff.mp hp
      obtain ⟨hple, hprime⟩ := Nat.mem_primesLE.mp hpQ
      have hQp : Q < p := by
        by_contra! hn
        exact hnot (Nat.mem_primesLE.mpr ⟨hn, hprime⟩)
      have hpS : p ∈ S := mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hple, hprime⟩, by
        intro hn
        have hh := (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ X / 2)).mp (Nat.mem_primesLE.mp hn).1
        have hQp' : (Q : ℝ) < p := by exact_mod_cast hQp
        linarith only [hh, hQp', hQlo]⟩
      have hprange : p ∈ Set.range e := by
        rw [show Set.range e = (S : Set ℕ) from S.range_orderEmbOfFin rfl]
        exact hpS
      obtain ⟨j, rfl⟩ := hprange
      exact mem_image.mpr ⟨j, mem_Ioi.mpr ((e.lt_iff_lt).mp hQp), rfl⟩
  have hDcard : D.card = M := by
    rw [show D = (Ioi i).image e from rfl, card_image_of_injective _ e.injective, Fin.card_Ioi]
    dsimp [i]
    omega
  have hDmem : ∀ p ∈ D, p.Prime ∧ Q < p ∧ p ≤ b.Q := by
    intro p hp
    rw [hD] at hp
    obtain ⟨hpa, hpn⟩ := mem_sdiff.mp hp
    obtain ⟨hpQ, hprime⟩ := Nat.mem_primesLE.mp hpa
    refine ⟨hprime, ?_, hpQ⟩
    by_contra! hn
    exact hpn (Nat.mem_primesLE.mpr ⟨hn, hprime⟩)
  have hDsum : Chebyshev.theta (b.Q : ℝ) - Chebyshev.theta (Q : ℝ) = ∑ p ∈ D, log p := by
    rw [hD, Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
    exact sub_eq_iff_eq_add.mpr (sum_sdiff (Nat.primesLE_mono hQle)
      (f := fun p : ℕ => log (p : ℝ))).symm
  refine ⟨Q, D, hQprime, hQlo, hQle, hD, hDcard, hDmem, hDsum, ?_⟩
  calc
    _ ≤ ∑ _p ∈ D, log (2 * X) := by
      apply sum_le_sum
      intro p hp
      exact log_le_log (by exact_mod_cast (hDmem p hp).1.pos)
        ((by exact_mod_cast (hDmem p hp).2.2 : (p : ℝ) ≤ b.Q).trans hQ.2)
    _ = _ := by simp [hDcard]

theorem budget_prefix_deletion_reserve :
    ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧
      ∀ X : ℝ, T ≤ X → ∀ b : Budget, b.spec X →
      ∀ M : ℕ, (M : ℝ) ≤ C * log X →
        ∃ Q : ℕ, ∃ D : Finset ℕ, Q.Prime ∧ X / 2 < (Q : ℝ) ∧ Q ≤ b.Q ∧
          D = Nat.primesLE b.Q \ Nat.primesLE Q ∧ D.card = M ∧
          (∀ p ∈ D, p.Prime ∧ Q < p ∧ p ≤ b.Q) ∧
          Chebyshev.theta (b.Q : ℝ) - Chebyshev.theta (Q : ℝ) = ∑ p ∈ D, log p ∧
          (∑ p ∈ D, log p) ≤ (M : ℝ) * log (2 * X) := by
  simpa only [pow_one] using budget_prefix_deletion_reserve_power 1

/-- The actual complete first-layer price of shortening a prefix, together
with the deletion-prime log localization used in the mesh error estimate.
The deleted mass, not merely the number of deleted primes, is retained. -/
theorem finite_prefix_deletion_cost {X : ℝ} (hX : 4 < X)
    (b : Budget) (hb : b.spec X) {Q k M : ℕ}
    (hk : 2 ≤ k) (hkp : k.primeFactors = Nat.primesLE Q)
    (hQ : (Q : ℝ) ∈ Set.Icc (X / 2) (2 * X)) (hQb : Q ≤ b.Q)
    (D : Finset ℕ) (hD : D = Nat.primesLE b.Q \ Nat.primesLE Q) (hDM : D.card = M) :
    |completeFirstLayerLoss X k - completeFirstLayerLoss X b.k| ≤
      6 * (shellError X + 3 * sqrt X + (M : ℝ) * log (2 * X) + 1) *
        ((M : ℝ) * log (2 * X)) / (X ^ 2 * log (X / 2)) ∧
    (∀ f : ℝ, (Q : ℝ) ≤ f → f ≤ b.Q →
      |log f - log X| ≤ (2 / X) *
        (shellError X + 3 * sqrt X + (M : ℝ) * log (2 * X))) := by
  classical
  obtain ⟨hb2, hbdef, hhdef, hh0, hh, hQold, hd0, hdlog, hds,
    hbudget, hpref, hr, hXr, hrX, hroot, hhigher⟩ := hb
  have hX0 : 0 < X := by linarith
  have hlog : 0 < log (2 * X) := log_pos (by linarith)
  have hden : 0 < X ^ 2 * log (X / 2) :=
    mul_pos (sq_pos_of_pos hX0) (log_pos (by linarith))
  have hmass : (∑ p ∈ D, log p) =
      Chebyshev.theta (b.Q : ℝ) - Chebyshev.theta (Q : ℝ) := by
    rw [hD, Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
    exact eq_sub_iff_add_eq.mpr (sum_sdiff (Nat.primesLE_mono hQb)
      (f := fun p : ℕ => log (p : ℝ)))
  have hsum0 : 0 ≤ ∑ p ∈ D, log p := by
    apply sum_nonneg
    intro p hp
    rw [hD] at hp
    exact (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).2.log_pos.le
  have hsum : (∑ p ∈ D, log p) ≤ (M : ℝ) * log (2 * X) := by
    calc
      _ ≤ ∑ _p ∈ D, log (2 * X) := by
        apply sum_le_sum
        intro p hp
        rw [hD] at hp
        obtain ⟨hpQ, hprime⟩ := Nat.mem_primesLE.mp (mem_sdiff.mp hp).1
        exact log_le_log (by exact_mod_cast hprime.pos)
          ((by exact_mod_cast hpQ : (p : ℝ) ≤ b.Q).trans hQold.2)
      _ = _ := by simp [hDM]
  have hbudgetθ : Chebyshev.theta (b.Q : ℝ) = X - b.h - b.δ := by
    have hl : log (b.k : ℝ) = b.h + Chebyshev.theta (b.Q : ℝ) := by
      rw [hbdef, Nat.cast_mul,
        log_mul (by exact_mod_cast (higher_core_pos _).ne')
          (by exact_mod_cast (prefix_integer_pos _).ne'), prefix_integer_log, ← hhdef]
    linarith only [hl, hbudget]
  let A := shellError X + 3 * sqrt X + (M : ℝ) * log (2 * X)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg (add_nonneg (shellError_nonneg hX0.le) (by positivity)) (by positivity)
  have hthetaQ : Chebyshev.theta (Q : ℝ) =
      Chebyshev.theta (b.Q : ℝ) - ∑ p ∈ D, log p := by linarith only [hmass]
  have hlocal (f : ℝ) (hfQ : (Q : ℝ) ≤ f) (hfb : f ≤ b.Q) : |f - X| ≤ A := by
    have hfshell : f ∈ Set.Icc (X / 2) (2 * X) :=
      ⟨hQ.1.trans hfQ, hfb.trans hQold.2⟩
    have hpnt := pointwise_le_shellError hX0.le hfshell
    have hθlo := Chebyshev.theta_mono hfQ
    have hθhi := Chebyshev.theta_mono hfb
    have hthetaabs : |Chebyshev.theta f - X| ≤ b.h + b.δ + ∑ p ∈ D, log p := by
      rw [hbudgetθ] at hθhi
      rw [hthetaQ, hbudgetθ] at hθlo
      apply abs_le.mpr
      constructor <;> linarith only [hθlo, hθhi, hh0, hd0, hsum0]
    have ht := abs_add_le (f - Chebyshev.theta f) (Chebyshev.theta f - X)
    rw [sub_add_sub_cancel] at ht
    rw [abs_sub_comm f (Chebyshev.theta f)] at ht
    dsimp [A]
    linarith only [ht, hpnt, hthetaabs, hh, hds, hsum]
  have hrootlocal (f : ℝ) (hfQ : (Q : ℝ) ≤ f) (hfb : f ≤ b.Q) : |f - b.r| ≤ A + 1 := by
    have ht := abs_add_le (f - X) (X - b.r)
    rw [sub_add_sub_cancel, abs_of_pos hXr] at ht
    linarith only [ht, hlocal f hfQ hfb, hrX]
  constructor
  · have hcancel := complete_first_layer_prefix_cancellation hX
      hpref hkp hQold hQ hr hroot
    have hV : max (|(b.Q : ℝ) - b.r|) (|(Q : ℝ) - b.r|) ≤ A + 1 := by
      apply max_le
      · exact hrootlocal b.Q (by exact_mod_cast hQb) le_rfl
      · exact hrootlocal Q le_rfl (by exact_mod_cast hQb)
    have htheta : |Chebyshev.theta (b.Q : ℝ) - Chebyshev.theta (Q : ℝ)| = ∑ p ∈ D, log p := by
      rw [← hmass, abs_of_nonneg hsum0]
    rw [htheta] at hcancel
    have hnum := mul_le_mul hV hsum hsum0 (by linarith only [hA] : 0 ≤ A + 1)
    have hbound := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnum (by norm_num : (0 : ℝ) ≤ 6)) hden.le
    exact hcancel.trans (by simpa only [A, mul_assoc] using hbound)
  · intro f hfQ hfb
    have hfshell : f ∈ Set.Icc (X / 2) (2 * X) :=
      ⟨hQ.1.trans hfQ, hfb.trans hQold.2⟩
    have hXshell : X ∈ Set.Icc (X / 2) (2 * X) := ⟨by linarith, by linarith⟩
    have hder (u : ℝ) (hu : u ∈ Set.Icc (X / 2) (2 * X)) :
        HasDerivWithinAt log (1 / u) (Set.Icc (X / 2) (2 * X)) u := by
      simpa only [one_div] using
        (hasDerivAt_log (by linarith [hu.1] : u ≠ 0)).hasDerivWithinAt
    have hbound (u : ℝ) (hu : u ∈ Set.Icc (X / 2) (2 * X)) : ‖1 / u‖ ≤ 2 / X := by
      have hu0 : 0 < u := by linarith [hu.1]
      rw [norm_eq_abs, abs_of_pos (one_div_pos.mpr hu0)]
      apply (div_le_div_iff₀ hu0 hX0).mpr
      linarith [hu.1]
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := log) (f' := fun u : ℝ => 1 / u) (C := 2 / X)
      hder hbound (convex_Icc (X / 2) (2 * X)) hXshell hfshell
    have hh : |log f - log X| ≤ (2 / X) * |f - X| := by
      simpa only [norm_eq_abs] using hmv
    exact hh.trans (mul_le_mul_of_nonneg_left (hlocal f hfQ hfb) (by positivity))

#print axioms budget_prefix_deletion_reserve
#print axioms finite_prefix_deletion_cost
end D5.S3.Arith.Robin.PriceRecord.PaidPrefixDeletionReserve

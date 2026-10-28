/- GID: D5/S3/Combinatorics/PerfectMatchings/WeightedReattachment
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/WeightedReattachment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Factors]
   utility: none
   digest: Actual cut lengths recover the full reattached cycle inventory law. -/
import D5.S3.Combinatorics.PerfectMatchings.FiniteReturnTowers
import D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.WeightedReattachment
noncomputable section
attribute [local instance] Classical.propDecidable
open Equiv
open scoped BigOperators
open FiniteEndpointPairing FiniteReturnTowers

variable {X : Type*} [Finite X]

/-- Length of the original cut path beginning at the newly attached point.
It is chosen from a proved first-visit witness, not from a supplied orbit size. -/
noncomputable def cutLength (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (J : Perm {z // r z = z}) (x : {z // r z = z}) : ℕ :=
  (endpoint_pairing_reattach_return_data s r hs hr J x).choose

noncomputable def returnData (s r : Perm X)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (J : Perm {z // r z = z}) :
    ReturnData (s * (r * J.ofSubtype)) {z | r z = z} where
  next := endpointPairing s r hs hr * J
  length := cutLength s r hs hr J
  first x := (endpoint_pairing_reattach_return_data s r hs hr J x).choose_spec.2.1
  jump x := (endpoint_pairing_reattach_return_data s r hs hr J x).choose_spec.2.2

private theorem untouched_iff_avoids (f : Perm X) (S : Set X) (z : X) :
    (∀ x : S, ¬ f.SameCycle x z) ↔ ∀ n : ℕ, (f ^ n) z ∉ S := by
  constructor
  · intro h n hn
    apply h ⟨(f ^ n) z, hn⟩
    exact (show f.SameCycle z ((f ^ n) z) from
      ⟨(n : ℤ), by simp only [zpow_natCast]⟩).symm
  · intro h x hx
    obtain ⟨n, hn⟩ := hx.symm.exists_nat_pow_eq
    apply h n
    rw [hn]
    exact x.property

private theorem powers_eq_of_avoids (q : Perm X) (S : Set X)
    (J : Perm S) (z : X) (hz : ∀ n : ℕ, (q ^ n) z ∉ S) (n : ℕ) :
    ((q * J.ofSubtype) ^ n) z = (q ^ n) z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, Perm.mul_apply,
      Perm.ofSubtype_apply_of_not_mem J (hz n)]
    rw [← Perm.mul_apply, ← pow_succ']

private theorem powers_eq_of_reattached_avoids (q : Perm X) (S : Set X)
    (J : Perm S) (z : X)
    (hz : ∀ n : ℕ, ((q * J.ofSubtype) ^ n) z ∉ S) (n : ℕ) :
    ((q * J.ofSubtype) ^ n) z = (q ^ n) z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, Perm.mul_apply,
      Perm.ofSubtype_apply_of_not_mem J (hz n), ih]
    rw [← Perm.mul_apply, ← pow_succ']

theorem untouched_reattach_iff (q : Perm X) (S : Set X)
    (J : Perm S) (z : X) :
    (∀ x : S, ¬ (q * J.ofSubtype).SameCycle x z) ↔
      ∀ x : S, ¬ q.SameCycle x z := by
  rw [untouched_iff_avoids, untouched_iff_avoids]
  constructor
  · intro hz n
    rw [← powers_eq_of_reattached_avoids q S J z hz n]
    exact hz n
  · intro hz n
    rw [powers_eq_of_avoids q S J z hz n]
    exact hz n

private theorem untouched_period (q : Perm X) (S : Set X) (J : Perm S)
    (z : X) (hz : ∀ x : S, ¬ (q * J.ofSubtype).SameCycle x z) :
    orbitPeriod (q * J.ofSubtype) z = orbitPeriod q z := by
  have ha := (untouched_iff_avoids (q * J.ofSubtype) S z).mp hz
  have hp (n : ℕ) := powers_eq_of_reattached_avoids q S J z ha n
  apply orbit_period_unique
  simpa only [hp] using orbit_period_spec q z

/-- Complete actual reattachment theorem. The tower has no missing components,
its weights are first-return lengths in the original cut system, and its
inventory records every cycle, including singleton and untouched cycles. -/
theorem reattachment_weighted_cycle_inventory [Fintype X]
    (s r : Perm X) (hs : Function.Involutive s) (hr : Function.Involutive r)
    (J : Perm {z // r z = z}) :
    let R := returnData s r hs hr J
    (∀ x, FirstVisit (s * r) {z | r z = z} (J x) (R.length x)) ∧
    (∀ p, R.modelEquiv (R.step p) = (s * (r * J.ofSubtype)) (R.modelEquiv p)) ∧
    (∀ z, (z ∈ R.Untouched ↔
      ∀ x : {z // r z = z}, ¬ (s * r).SameCycle x z)) ∧
    (∀ z : R.Untouched, ∀ n : ℕ,
      ((s * (r * J.ofSubtype)) ^ n) z = ((s * r) ^ n) z) ∧
    cycleInventory (s * (r * J.ofSubtype)) =
      (∑ z : R.Untouched,
        Polynomial.monomial (orbitPeriod (s * r) z) (1 / (orbitPeriod (s * r) z : ℚ))) +
      ∑ x : {z // r z = z}, R.length x •
        Polynomial.monomial (R.weightedPeriod x) (1 / (R.weightedPeriod x : ℚ)) := by
  classical
  let R := returnData s r hs hr J
  change (∀ x, FirstVisit (s * r) {z | r z = z} (J x) (R.length x)) ∧ _
  refine ⟨?_, R.tower_decomposition.2.2, ?_, ?_, ?_⟩
  · intro x
    exact (endpoint_pairing_reattach_return_data s r hs hr J x).choose_spec.1
  · intro z
    change (∀ x : {z // r z = z}, ¬ (s * (r * J.ofSubtype)).SameCycle x z) ↔ _
    constructor
    · intro hz
      apply (untouched_reattach_iff (s * r) {z | r z = z} J z).mp
      intro x hc
      exact hz x (by simpa only [mul_assoc] using hc)
    · intro hz x hc
      have hn := (untouched_reattach_iff (s * r) {z | r z = z} J z).mpr hz
      exact hn x (by simpa only [mul_assoc] using hc)
  · intro z n
    have hz0 : ∀ x : {z // r z = z}, ¬ (s * (r * J.ofSubtype)).SameCycle x z :=
      z.property
    have hz : ∀ x : {z // r z = z}, ¬ ((s * r) * J.ofSubtype).SameCycle x z := by
      intro x hc
      exact hz0 x (by simpa only [mul_assoc] using hc)
    have ha := (untouched_iff_avoids ((s * r) * J.ofSubtype) {z | r z = z} z).mp hz
    simpa only [mul_assoc] using
      powers_eq_of_reattached_avoids (s * r) {z | r z = z} J z ha n
  · rw [R.weighted_cycle_inventory]
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    have hz0 : ∀ x : {z // r z = z}, ¬ (s * (r * J.ofSubtype)).SameCycle x z :=
      z.property
    have hz : ∀ x : {z // r z = z}, ¬ ((s * r) * J.ofSubtype).SameCycle x z := by
      intro x hc
      exact hz0 x (by simpa only [mul_assoc] using hc)
    have hp := untouched_period (s * r) {z | r z = z} J z hz
    simpa only [mul_assoc] using congrArg
      (fun n : ℕ => Polynomial.monomial n (1 / (n : ℚ))) hp


/-- Each independent bit selects one of the two real band attachments on its
four distinct labelled endpoints. The edge labels may encode loops or parallel
bands; no simple-graph assumption is built into this flag carrier. -/
def bandPairs {B : Type*} (ω : B → Bool) : Perm (B × Fin 4) where
  toFun p := (p.1, if ω p.1 then FiniteBandSwitch.FourEndpoint.J1 p.2
    else FiniteBandSwitch.FourEndpoint.J0 p.2)
  invFun p := (p.1, if ω p.1 then FiniteBandSwitch.FourEndpoint.J1 p.2
    else FiniteBandSwitch.FourEndpoint.J0 p.2)
  left_inv p := by
    rcases p with ⟨b, i⟩
    cases h : ω b <;> fin_cases i <;> simp [h,
      FiniteBandSwitch.FourEndpoint.J0, FiniteBandSwitch.FourEndpoint.J1,
      Perm.mul_apply, swap_apply_def]
  right_inv p := by
    rcases p with ⟨b, i⟩
    cases h : ω b <;> fin_cases i <;> simp [h,
      FiniteBandSwitch.FourEndpoint.J0, FiniteBandSwitch.FourEndpoint.J1,
      Perm.mul_apply, swap_apply_def]

/-- Exact cycle inventory distribution under independent fair unresolved band
signs, conditional on the fixed corners and all remaining band attachments.
The denominator is precisely 2^|B|. Every test function of the entire
cycle inventory is retained, hence this determines its full distribution; it
is not merely equality of the expected counts at each separate length. -/
theorem fair_band_inventory_law [Fintype X] {B : Type*} [Fintype B]
    (s r : Perm X) (hs : Function.Involutive s) (hr : Function.Involutive r)
    (e : (B × Fin 4) ≃ {z // r z = z})
    (test : Polynomial ℚ → ℚ) :
    let J := fun ω : B → Bool => e.permCongr (bandPairs ω)
    let R := fun ω => returnData s r hs hr (J ω)
    (1 / (2 : ℚ) ^ Fintype.card B) •
      (∑ ω : B → Bool, test (cycleInventory (s * (r * (J ω).ofSubtype)))) =
    (1 / (2 : ℚ) ^ Fintype.card B) •
      (∑ ω : B → Bool, test (
        (∑ z : (R ω).Untouched,
          Polynomial.monomial (orbitPeriod (s * r) z)
            (1 / (orbitPeriod (s * r) z : ℚ))) +
        ∑ x : {z // r z = z}, (R ω).length x •
          Polynomial.monomial ((R ω).weightedPeriod x)
            (1 / ((R ω).weightedPeriod x : ℚ)))) := by
  classical
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  exact congrArg test
    (reattachment_weighted_cycle_inventory s r hs hr (e.permCongr (bandPairs ω))).2.2.2.2

#print axioms reattachment_weighted_cycle_inventory
#print axioms fair_band_inventory_law
end
end D5.S3.Combinatorics.PerfectMatchings.WeightedReattachment

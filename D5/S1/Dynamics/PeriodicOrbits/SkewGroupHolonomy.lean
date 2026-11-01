/- GID: D5/S1/Dynamics/PeriodicOrbits/SkewGroupHolonomy
   generality: G
   mirror-B: D5/B/S1/Dynamics/PeriodicOrbits/SkewGroupHolonomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Noncommutative holonomy controls both lifted periods and orbit cosets. -/

import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

namespace D5.S1.Dynamics.PeriodicOrbits.SkewGroupHolonomy

open Function
open scoped BigOperators

variable {X A : Type*} [Group A]

/-- Ordered fibre transport along a base orbit.  The order of the factors is
the order in which the skew map sees them; no commutativity is assumed. -/
def groupHolonomy (f : X → X) (c : X → A) : ℕ → X → A
  | 0, _ => 1
  | n + 1, x => groupHolonomy f c n x * c (f^[n] x)

@[simp] theorem groupHolonomy_zero (f : X → X) (c : X → A) (x : X) :
    groupHolonomy f c 0 x = 1 := by
  simp [groupHolonomy]

theorem groupHolonomy_add (f : X → X) (c : X → A) (m n : ℕ) (x : X) :
    groupHolonomy f c (m + n) x =
      groupHolonomy f c m x * groupHolonomy f c n (f^[m] x) := by
  induction n with
  | zero => simp [groupHolonomy]
  | succ n ih =>
    rw [Nat.add_succ, groupHolonomy, ih, groupHolonomy]
    rw [Nat.add_comm m n, iterate_add_apply]
    simp [mul_assoc]

/-- The charge is evaluated at the current base state before the base advances;
    the fibre coordinate is transported by right multiplication. -/
def groupSkewStepRight (f : X → X) (c : X → A) : X × A → X × A :=
  fun z => (f z.1, z.2 * c z.1)

theorem groupSkew_iterate (f : X → X) (c : X → A) (n : ℕ) (x : X) (a : A) :
    (groupSkewStepRight f c)^[n] (x, a) =
      (f^[n] x, a * groupHolonomy f c n x) := by
  induction n with
  | zero => simp [groupHolonomy]
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    change (f (f^[n] x), (a * groupHolonomy f c n x) * c (f^[n] x)) = _
    rw [show f^[n + 1] x = f (f^[n] x) from iterate_succ_apply' f n x]
    simp [groupHolonomy, groupSkewStepRight, mul_assoc]

theorem groupSkew_iterate_block (f : X → X) (c : X → A) {p : ℕ} {x : X}
    (hp : IsPeriodicPt f p x) (k : ℕ) (a : A) :
    (groupSkewStepRight f c)^[p * k] (x, a) =
      (x, a * (groupHolonomy f c p x) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (p * k) p, iterate_add_apply, ih,
      groupSkew_iterate, hp.eq]
    simp [pow_succ, mul_assoc]

theorem groupSkew_return_iff (f : X → X) (c : X → A) (n : ℕ) (x : X) (a : A)
    [Finite A] :
    (groupSkewStepRight f c)^[n] (x, a) = (x, a) ↔
      minimalPeriod f x * orderOf (groupHolonomy f c (minimalPeriod f x) x) ∣ n := by
  constructor
  · intro hr
    have hb : IsPeriodicPt f n x := by
      change f^[n] x = x
      have hfst := congrArg Prod.fst hr
      simpa only [groupSkew_iterate] using hfst
    obtain ⟨k, hk⟩ := isPeriodicPt_iff_minimalPeriod_dvd.mp hb
    rw [hk, groupSkew_iterate_block f c (isPeriodicPt_minimalPeriod f x)] at hr
    have hz : (groupHolonomy f c (minimalPeriod f x) x) ^ k = 1 := by
      have hsnd := congrArg Prod.snd hr
      exact (mul_left_cancel (hsnd.trans (mul_one a).symm))
    obtain ⟨l, hl⟩ := orderOf_dvd_iff_pow_eq_one.mpr hz
    refine ⟨l, ?_⟩
    rw [hk, hl, Nat.mul_assoc]
  · rintro ⟨k, rfl⟩
    rw [Nat.mul_assoc,
      groupSkew_iterate_block f c (isPeriodicPt_minimalPeriod f x)]
    have hz := orderOf_dvd_iff_pow_eq_one.mp
      (dvd_mul_right (orderOf (groupHolonomy f c (minimalPeriod f x) x)) k)
    simp only [hz, mul_one]

theorem groupSkew_minimalPeriod (f : X → X) (c : X → A) (x : X) (a : A)
    [Finite A] :
    minimalPeriod (groupSkewStepRight f c) (x, a) =
      minimalPeriod f x * orderOf (groupHolonomy f c (minimalPeriod f x) x) := by
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    exact (groupSkew_return_iff f c _ x a).mpr dvd_rfl
  · exact (groupSkew_return_iff f c _ x a).mp (isPeriodicPt_minimalPeriod _ _).eq

private theorem groupSkew_periodic (f : X → X) (c : X → A) (x : X) (a : A)
    (hx : x ∈ periodicPts f) [Finite A] :
    (x, a) ∈ periodicPts (groupSkewStepRight f c) := by
  apply mk_mem_periodicPts
    (n := minimalPeriod f x * orderOf (groupHolonomy f c (minimalPeriod f x) x))
    (Nat.mul_pos (minimalPeriod_pos_of_mem_periodicPts hx) (orderOf_pos _))
  exact (groupSkew_return_iff f c _ x a).mpr dvd_rfl

/-- Two lifts over one periodic base point are on the same orbit exactly when
their initial fibre coordinates differ by a power of the ordered holonomy. -/
theorem groupSkew_periodicOrbit_eq_iff
    (f : X → X) (c : X → A) (x : X) (hx : x ∈ periodicPts f)
    [Finite A] (a b : A) :
    periodicOrbit (groupSkewStepRight f c) (x, a) =
        periodicOrbit (groupSkewStepRight f c) (x, b) ↔
      a⁻¹ * b ∈ Subgroup.zpowers
        (groupHolonomy f c (minimalPeriod f x) x) := by
  let h := groupHolonomy f c (minimalPeriod f x) x
  have hper (z : A) : (x, z) ∈ periodicPts (groupSkewStepRight f c) :=
    groupSkew_periodic f c x z hx
  constructor
  · intro horb
    have hmem : (x, b) ∈ periodicOrbit (groupSkewStepRight f c) (x, a) := by
      rw [horb]
      exact self_mem_periodicOrbit (hper b)
    obtain ⟨n, hn⟩ := (mem_periodicOrbit_iff (hper a)).mp hmem
    have hbase : f^[n] x = x := by
      have hfst := congrArg Prod.fst hn
      simpa only [groupSkew_iterate] using hfst
    have hdiv : minimalPeriod f x ∣ n :=
      (isPeriodicPt_iff_minimalPeriod_dvd).mp hbase
    obtain ⟨k, rfl⟩ := hdiv
    rw [groupSkew_iterate_block f c
      (isPeriodicPt_minimalPeriod f x) k a] at hn
    have hab : a * h ^ k = b := congrArg Prod.snd hn
    refine (Subgroup.mem_zpowers_iff).2 ⟨(k : ℤ), ?_⟩
    rw [zpow_natCast]
    calc
      h ^ k = a⁻¹ * (a * h ^ k) := by simp [mul_assoc]
      _ = a⁻¹ * b := by rw [hab]
  · intro hmem
    have hpow : a⁻¹ * b ∈ Submonoid.powers h :=
      ((isOfFinOrder_of_finite h).mem_powers_iff_mem_zpowers).2 hmem
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 hpow
    have hab : a * h ^ k = b := by
      calc
        a * h ^ k = a * (a⁻¹ * b) := by rw [hk]
        _ = b := by simp
    have hit :
        (groupSkewStepRight f c)^[minimalPeriod f x * k] (x, a) = (x, b) := by
      rw [groupSkew_iterate_block f c
        (isPeriodicPt_minimalPeriod f x) k a, hab]
    have horb := periodicOrbit_apply_iterate_eq (hper a)
      (minimalPeriod f x * k)
    rw [hit] at horb
    exact horb.symm

def groupSkewOrbitFamily (f : X → X) (c : X → A) (x : X) :
    Set (Cycle (X × A)) :=
  Set.range (fun a : A => periodicOrbit (groupSkewStepRight f c) (x, a))

private noncomputable def groupSkewQuotientToFamily
    (f : X → X) (c : X → A) (x : X) (hx : x ∈ periodicPts f) [Finite A] :
    (A ⧸ Subgroup.zpowers (groupHolonomy f c (minimalPeriod f x) x)) →
      {o : Cycle (X × A) // o ∈ groupSkewOrbitFamily f c x} :=
  Quotient.lift
    (fun a : A =>
      (⟨periodicOrbit (groupSkewStepRight f c) (x, a), ⟨a, rfl⟩⟩ :
        {o : Cycle (X × A) // o ∈ groupSkewOrbitFamily f c x}))
    (by
      intro a b hab
      apply Subtype.ext
      apply (groupSkew_periodicOrbit_eq_iff f c x hx a b).2
      exact QuotientGroup.leftRel_apply.mp hab)

private theorem groupSkewQuotientToFamily_injective
    (f : X → X) (c : X → A) (x : X) (hx : x ∈ periodicPts f) [Finite A] :
    Function.Injective (groupSkewQuotientToFamily f c x hx) := by
  intro u v huv
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective
    (s := Subgroup.zpowers (groupHolonomy f c (minimalPeriod f x) x)) u
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective
    (s := Subgroup.zpowers (groupHolonomy f c (minimalPeriod f x) x)) v
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  exact (groupSkew_periodicOrbit_eq_iff f c x hx a b).1
    (congrArg Subtype.val huv)

private theorem groupSkewQuotientToFamily_surjective
    (f : X → X) (c : X → A) (x : X) (hx : x ∈ periodicPts f) [Finite A] :
    Function.Surjective (groupSkewQuotientToFamily f c x hx) := by
  intro o
  rcases o.property with ⟨a, ha⟩
  refine ⟨QuotientGroup.mk a, ?_⟩
  apply Subtype.ext
  exact ha

/-- The left-coset quotient by the holonomy subgroup parametrizes the lifted
periodic orbit family above a periodic base point. -/
noncomputable def groupSkewOrbitQuotientEquivFamily
    (f : X → X) (c : X → A) (x : X) (hx : x ∈ periodicPts f) [Finite A] :
    (A ⧸ Subgroup.zpowers (groupHolonomy f c (minimalPeriod f x) x)) ≃
      {o : Cycle (X × A) // o ∈ groupSkewOrbitFamily f c x} :=
  Equiv.ofBijective (groupSkewQuotientToFamily f c x hx)
    ⟨groupSkewQuotientToFamily_injective f c x hx,
      groupSkewQuotientToFamily_surjective f c x hx⟩

/-- Noncommutative holonomy gives the orbit-family cardinality as a subgroup
index.  The cyclic ZMod gcd formula is its abelian special case. -/
theorem groupSkewOrbitFamily_card
    (f : X → X) (c : X → A) (x : X) (hx : x ∈ periodicPts f) [Finite A] :
    Nat.card {o : Cycle (X × A) // o ∈ groupSkewOrbitFamily f c x} =
      (Subgroup.zpowers (groupHolonomy f c (minimalPeriod f x) x)).index := by
  exact (Nat.card_congr (Equiv.ofBijective
    (groupSkewQuotientToFamily f c x hx)
    ⟨groupSkewQuotientToFamily_injective f c x hx,
      groupSkewQuotientToFamily_surjective f c x hx⟩)).symm.trans
    (Subgroup.index_eq_card _).symm

#print axioms groupHolonomy_add
#print axioms groupSkew_iterate
#print axioms groupSkew_iterate_block
#print axioms groupSkew_return_iff
#print axioms groupSkew_minimalPeriod
#print axioms groupSkew_periodicOrbit_eq_iff
#print axioms groupSkewOrbitFamily_card

end D5.S1.Dynamics.PeriodicOrbits.SkewGroupHolonomy

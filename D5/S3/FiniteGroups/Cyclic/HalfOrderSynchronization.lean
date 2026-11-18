/- GID: D5/S3/FiniteGroups/Cyclic/HalfOrderSynchronization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/HalfOrderSynchronization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.SpecificGroups.Cyclic]
   utility: none
   digest: An anchored generator encoding bounds the actual half-order failure count in arbitrary finite cyclic families. -/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace HalfOrderSynchronization

private theorem eq_involution_iff {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (epsilon y : G) (he : orderOf epsilon = 2) : y = epsilon ↔ orderOf y = 2 := by
  classical
  have hdiv : 2 ∣ Fintype.card G := he ▸ orderOf_dvd_card (x := epsilon)
  have hc : ({z : G | orderOf z = 2} : Finset G).card = 1 :=
    (IsCyclic.card_orderOf_eq_totient (α := G) hdiv).trans Nat.totient_two
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
  have hez : epsilon = z := by
    simpa [hz] using (show epsilon ∈ ({z : G | orderOf z = 2} : Finset G) by simp [he])
  constructor
  · intro h; simpa [h] using he
  · intro hy
    have : y ∈ ({z : G | orderOf z = 2} : Finset G) := by simp [hy]
    have hyz : y = z := by simpa [hz] using this
    exact hyz.trans hez.symm

private theorem dvd_half_iff {d m : ℕ} (hd : d ≠ 0) (hm : m ≠ 0)
    (hdm : d ∣ m) (he : Even m) :
    d ∣ m / 2 ↔ d.factorization 2 < m.factorization 2 := by
  have hle := (Nat.factorization_le_iff_dvd hd hm).mpr hdm
  rw [Nat.dvd_div_iff_mul_dvd he.two_dvd,
    ← Nat.factorization_le_iff_dvd (mul_ne_zero (by norm_num) hd) hm,
    Nat.factorization_mul (by norm_num : (2 : ℕ) ≠ 0) hd, Finsupp.le_def]
  constructor
  · intro h
    have h2 := h 2
    simp only [Nat.prime_two.factorization, Finsupp.single_eq_same, Finsupp.add_apply] at h2
    omega
  · intro h p
    by_cases hp : p = 2
    · subst p
      simp only [Nat.prime_two.factorization, Finsupp.single_eq_same, Finsupp.add_apply]
      omega
    · simpa [Nat.prime_two.factorization, Finsupp.single_apply, hp, Ne.symm hp] using hle p

/-- Actual local half-power at an even common multiple of the order. -/
private theorem half_power_eq_iff {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (epsilon g : G) (he : orderOf epsilon = 2) {m : ℕ} (hm : m ≠ 0)
    (hme : Even m) (hgm : orderOf g ∣ m) :
    g ^ (m / 2) = epsilon ↔ (orderOf g).factorization 2 = m.factorization 2 := by
  have hs : (g ^ (m / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hme.two_dvd]
    exact orderOf_dvd_iff_pow_eq_one.mp hgm
  have hne : g ^ (m / 2) ≠ 1 ↔ (orderOf g).factorization 2 = m.factorization 2 := by
    rw [ne_eq, ← orderOf_dvd_iff_pow_eq_one, dvd_half_iff (orderOf_pos g).ne' hm hgm hme]
    have hle := (Nat.factorization_le_iff_dvd (orderOf_pos g).ne' hm).mpr hgm 2
    omega
  rw [eq_involution_iff epsilon _ he, orderOf_eq_prime_iff]
  exact and_iff_right hs |>.trans hne

/-- Failure is exactly synchronization of all local binary order valuations. -/
private theorem failure_iff {I : Type*} [Fintype I] [Nonempty I]
    {G : I → Type*} [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, IsCyclic (G i)]
    (epsilon x : ∀ i, G i) (he : ∀ i, orderOf (epsilon i) = 2) :
    ¬ (Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ epsilon) ↔
      ∃ t : ℕ, ∀ i, (orderOf (x i)).factorization 2 = t := by
  classical
  have hv : (orderOf x).factorization 2 =
      Finset.univ.sup (fun i => (orderOf (x i)).factorization 2) := by
    rw [Pi.orderOf, Finset.factorization_lcm (fun i _ => (orderOf_pos (x i)).ne')]
  have hpos := (orderOf_pos x).ne'
  by_cases hxe : Even (orderOf x)
  · have hlocal (i : I) := half_power_eq_iff (epsilon i) (x i) (he i) hpos hxe
      (orderOf_apply_dvd_orderOf i)
    have hpow : x ^ (orderOf x / 2) = epsilon ↔
        ∀ i, (orderOf (x i)).factorization 2 = (orderOf x).factorization 2 := by
      rw [funext_iff]
      exact forall_congr' hlocal
    simp only [hxe, true_and, not_not, hpow]
    constructor
    · intro h; exact ⟨_, h⟩
    · rintro ⟨t, ht⟩
      have hvt : (orderOf x).factorization 2 = t := by
        rw [hv]; simp_rw [ht]; exact Finset.sup_const Finset.univ_nonempty t
      intro i; exact (ht i).trans hvt.symm
  · have hz : (orderOf x).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => hxe (even_iff_two_dvd.mpr h))
    simp only [hxe, false_and, not_false_eq_true, true_iff]
    refine ⟨0, fun i => ?_⟩
    have hle := (Nat.factorization_le_iff_dvd (orderOf_pos (x i)).ne' hpos).mpr
      (orderOf_apply_dvd_orderOf (x := x) i) 2
    omega


private theorem valuation_mul_generator_ne {G : Type*} [Group G] [Fintype G] [IsCyclic G]
    (epsilon g x : G) (he : orderOf epsilon = 2) (hg : orderOf g = Fintype.card G) :
    (orderOf (x * g)).factorization 2 ≠ (orderOf x).factorization 2 := by
  classical
  let : CommGroup G := IsCyclic.commGroup
  have hcpos : 0 < Fintype.card G := Fintype.card_pos
  have hce : Even (Fintype.card G) := even_iff_two_dvd.mpr
    (he ▸ orderOf_dvd_card (x := epsilon))
  have hgp : g ^ (Fintype.card G / 2) = epsilon :=
    (half_power_eq_iff epsilon g he hcpos.ne' hce (hg ▸ dvd_rfl)).mpr (by rw [hg])
  have hene : epsilon ≠ 1 := by
    intro h; simp [h] at he
  have hs (y : G) : y ^ (Fintype.card G / 2) = 1 ∨
      y ^ (Fintype.card G / 2) = epsilon := by
    have hp : (y ^ (Fintype.card G / 2)) ^ 2 = 1 := by
      rw [← pow_mul, Nat.div_mul_cancel hce.two_dvd]
      exact pow_card_eq_one
    by_cases hy : y ^ (Fintype.card G / 2) = 1
    · exact Or.inl hy
    · exact Or.inr ((eq_involution_iff epsilon _ he).mpr
        (orderOf_eq_prime_iff.mpr ⟨hp, hy⟩))
  intro hv
  have hi : x ^ (Fintype.card G / 2) = epsilon ↔
      (x * g) ^ (Fintype.card G / 2) = epsilon := by
    rw [half_power_eq_iff epsilon x he hcpos.ne' hce orderOf_dvd_card,
      half_power_eq_iff epsilon (x * g) he hcpos.ne' hce orderOf_dvd_card, hv]
  have hpow : (x * g) ^ (Fintype.card G / 2) =
      x ^ (Fintype.card G / 2) * epsilon := by rw [mul_pow, hgp]
  rcases hs x with hx | hx
  · have hxg : (x * g) ^ (Fintype.card G / 2) = epsilon := by rw [hpow, hx, one_mul]
    exact hene ((hi.mpr hxg).symm.trans hx)
  · have hxg := hi.mp hx
    have hcancel : epsilon * epsilon = epsilon := by simpa [hpow, hx] using hxg
    exact hene (mul_left_cancel (show epsilon * epsilon = epsilon * 1 by simpa using hcancel))


/-- The actual failure count for a nonempty family of finite cyclic groups. -/
theorem failure_count_le {I : Type*} [Fintype I] [Nonempty I]
    {G : I → Type*} [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, IsCyclic (G i)]
    (epsilon : ∀ i, G i) (he : ∀ i, orderOf (epsilon i) = 2) :
    Nat.card {x : ∀ i, G i // ¬ (Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ epsilon)} *
      2 ^ (Fintype.card I - 1) ≤ Nat.card (∀ i, G i) := by
  classical
  choose g hg using fun i : I => IsCyclic.exists_ofOrder_eq_natCard (α := G i)
  have hg' (i : I) : orderOf (g i) = Fintype.card (G i) := by
    simpa only [Nat.card_eq_fintype_card] using hg i
  let a : I := Classical.choice inferInstance
  let B := {x : ∀ i, G i // ¬ (Even (orderOf x) ∧ x ^ (orderOf x / 2) ≠ epsilon)}
  let J := {i : I // i ≠ a}
  have hcommon (x : B) (i : I) :
      (orderOf (x.val i)).factorization 2 = (orderOf (x.val a)).factorization 2 := by
    obtain ⟨t, ht⟩ := (failure_iff epsilon x.val he).mp x.property
    exact (ht i).trans (ht a).symm
  let encode : B × (J → Bool) → ∀ i, G i := fun p i =>
    if hi : i = a then p.1.val i else
      if p.2 ⟨i, hi⟩ then p.1.val i * g i else p.1.val i
  have hinj : Function.Injective encode := by
    intro p q hpq
    have ha : p.1.val a = q.1.val a := by
      simpa only [encode, dite_eq_left rfl] using congrFun hpq a
    have hv (i : I) :
        (orderOf (p.1.val i)).factorization 2 = (orderOf (q.1.val i)).factorization 2 :=
      (hcommon p.1 i).trans ((congrArg (fun z => (orderOf z).factorization 2) ha).trans
        (hcommon q.1 i).symm)
    have hb : p.2 = q.2 := by
      funext j
      have hij := congrFun hpq j.val
      dsimp only [encode] at hij
      simp only [dite_eq_right j.property] at hij
      change (if p.2 j then p.1.val j.val * g j.val else p.1.val j.val) =
        (if q.2 j then q.1.val j.val * g j.val else q.1.val j.val) at hij
      cases hp : p.2 j <;> cases hq : q.2 j
      · rfl
      · simp only [hp, hq, Bool.false_eq_true, ite_false, ite_true] at hij
        exfalso
        apply valuation_mul_generator_ne (epsilon j.val) (g j.val) (q.1.val j.val)
          (he j.val) (hg' j.val)
        exact (congrArg (fun z => (orderOf z).factorization 2) hij).symm.trans (hv j.val)
      · simp only [hp, hq, Bool.false_eq_true, ite_false, ite_true] at hij
        exfalso
        apply valuation_mul_generator_ne (epsilon j.val) (g j.val) (p.1.val j.val)
          (he j.val) (hg' j.val)
        exact (congrArg (fun z => (orderOf z).factorization 2) hij).trans (hv j.val).symm
      · rfl
    have hx : p.1 = q.1 := by
      apply Subtype.ext
      funext i
      have hij := congrFun hpq i
      by_cases hi : i = a
      · subst i; exact ha
      · dsimp only [encode] at hij
        simp only [dite_eq_right hi, hb] at hij
        cases hbit : q.2 ⟨i, hi⟩ <;> simpa only [hbit, Bool.false_eq_true,
          ite_false, ite_true, mul_left_inj] using hij
    exact Prod.ext hx hb
  have hcardJ : Fintype.card J = Fintype.card I - 1 := by
    dsimp only [J]
    simp only [Fintype.card_subtype_compl, Fintype.card_unique]
  have hc := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, hcardJ,
    Nat.card_eq_fintype_card] using hc

end HalfOrderSynchronization

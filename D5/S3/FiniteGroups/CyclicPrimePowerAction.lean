/- GID: D5/S3/FiniteGroups/CyclicPrimePowerAction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/CyclicPrimePowerAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual cyclic prime-power actions on prime cyclic groups and their split extensions. -/

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19077 (cyclic_card, kernel_power_card).
   cyclic_card: proof_shape: bind-only; escape_witness: none; consumers: over_card,
   complement_card, quotient_sum_bound in TarnauceanuReciprocalSubgroupOrders.
   kernel_power_card: proof_shape: bind-only; escape_witness: none; consumer:
   TarnauceanuReciprocalSubgroupOrders.quotient_sum_bound. -/

import D5.S3.FiniteGroups.SubgroupConjugacyRatio
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.Data.Fintype.Sum

namespace D5.S3.FiniteGroups.CyclicPrimePowerAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Subgroup
open MonoidHom
open D5.S3.FiniteGroups.SubgroupConjugacyRatio

abbrev Cyclic (m : ℕ) := Multiplicative (ZMod m)

def generator (m : ℕ) : Cyclic m := Multiplicative.ofAdd 1

private theorem generator_generates (m : ℕ) :
    ∀ x : Cyclic m, x ∈ zpowers (generator m) := by
  intro x
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective x.toAdd
  refine ⟨z, ?_⟩
  change Multiplicative.ofAdd (z • (1 : ZMod m)) = x
  rw [zsmul_one]
  exact congrArg Multiplicative.ofAdd hz

private theorem generator_order (m : ℕ) : orderOf (generator m) = m :=
  ZMod.addOrderOf_one m

/-- A cyclic action whose generator has exactly the prescribed prime order. -/
structure ActionData (p q s : ℕ) where
  action : Cyclic (q ^ s) →* MulAut (Cyclic p)
  order_generator : orderOf (action (generator (q ^ s))) = q

/-- Construct the action from Cauchy's theorem in the actual automorphism group. -/
noncomputable def actionData (p q s : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hd : q ∣ p - 1) (hs : 0 < s) : ActionData p q s := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (Cyclic p) = p := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hdiv : q ∣ Nat.card (MulAut (Cyclic p)) := by
    rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime hp]
    exact hd
  let hex := exists_prime_orderOf_dvd_card' q hdiv
  let α := hex.choose
  have hα : orderOf α = q := hex.choose_spec
  have horder : orderOf α ∣ orderOf (generator (q ^ s)) := by
    rw [hα, generator_order]
    exact dvd_pow_self q (Nat.ne_of_gt hs)
  refine ⟨monoidHomOfForallMemZpowers (generator_generates (q ^ s)) horder, ?_⟩
  rw [monoidHomOfForallMemZpowers_apply_gen, hα]

/-- The constructed extension is an actual group, with the usual semidirect multiplication. -/
abbrev SplitGroup {p q s : ℕ} (A : ActionData p q s) :=
  Cyclic p ⋊[A.action] Cyclic (q ^ s)

instance {p q s : ℕ} (A : ActionData p q s) [NeZero p] [NeZero (q ^ s)] :
    Finite (SplitGroup A) :=
  Finite.of_equiv (Cyclic p × Cyclic (q ^ s)) SemidirectProduct.equivProd.symm

/-- Package the split extension together with its actual finite carrier. -/
noncomputable def finiteSplitGroup (p q s : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hd : q ∣ p - 1) (hs : 0 < s) : FiniteGroup := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (q ^ s) := ⟨pow_ne_zero s hq.ne_zero⟩
  let A := actionData p q s hp hq hd hs
  exact ⟨SplitGroup A, inferInstance,
    Finite.of_equiv (Cyclic p × Cyclic (q ^ s)) SemidirectProduct.equivProd.symm⟩

section CyclicSubgroups

variable {P : Type*} [CommGroup P] [IsCyclic P] [Finite P]

private theorem cyclic_subgroup_eq_kernel (H : Subgroup P) :
    H = (powMonoidHom (Nat.card H) : P →* P).ker := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    change x ^ Nat.card H = 1
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : H)))
  · rw [IsCyclic.card_powMonoidHom_ker,
      Nat.gcd_eq_right (card_subgroup_dvd_card H)]

private theorem cyclic_subgroup_card_injective (H J : Subgroup P)
    (h : Nat.card H = Nat.card J) : H = J := by
  rw [cyclic_subgroup_eq_kernel H, cyclic_subgroup_eq_kernel J, h]

omit [IsCyclic P] [Finite P] in
private theorem subgroup_exponent {q s : ℕ} (hq : q.Prime)
    (hc : Nat.card P = q ^ s) (H : Subgroup P) :
    ∃ j : Fin (s + 1), Nat.card H = q ^ j.val := by
  obtain ⟨j, hj, he⟩ := (Nat.dvd_prime_pow hq).mp (hc ▸ card_subgroup_dvd_card H)
  exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, he⟩

theorem kernel_power_card {q s : ℕ}
    (hc : Nat.card P = q ^ s) (j : Fin (s + 1)) :
    Nat.card (powMonoidHom (q ^ j.val) : P →* P).ker = q ^ j.val := by
  rw [IsCyclic.card_powMonoidHom_ker, hc, Nat.gcd_eq_right]
  exact pow_dvd_pow q (Nat.le_of_lt_succ j.isLt)

/-- The full subgroup lattice of a cyclic group of order q^s has one subgroup
of order q^j for each j from zero through s. -/
noncomputable def cyclicSubgroupEquiv {q s : ℕ} (hq : q.Prime)
    (hc : Nat.card P = q ^ s) : Subgroup P ≃ Fin (s + 1) where
  toFun H := (subgroup_exponent hq hc H).choose
  invFun j := (powMonoidHom (q ^ j.val) : P →* P).ker
  left_inv H := by
    apply cyclic_subgroup_card_injective
    rw [kernel_power_card hc, (subgroup_exponent hq hc H).choose_spec]
  right_inv j := by
    apply Fin.ext
    apply (Nat.pow_right_injective hq.one_lt)
    exact ((subgroup_exponent hq hc _).choose_spec).symm.trans
      (kernel_power_card hc j)

end CyclicSubgroups

section SplitSubgroups

variable {p q s : ℕ} [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)]

theorem cyclic_card (m : ℕ) [NeZero m] : Nat.card (Cyclic m) = m := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

private theorem prime_automorphism_fixedPointFree {N : Type*} [Group N]
    [Fact (Nat.card N).Prime] (α : MulAut N) (hne : α ≠ 1) :
    MonoidHom.FixedPointFree α := by
  intro x hx
  by_contra h
  have hgen : ∀ y : N, y ∈ zpowers x := fun _ => mem_zpowers_of_prime_card rfl h
  apply hne
  exact (MulEquiv.eq_iff_eq_on_generator hgen α 1).mpr (by simpa using hx)

variable (A : ActionData p q s)

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem projection_injective (H : Subgroup (SplitGroup A))
    (hN : H.comap SemidirectProduct.inl = ⊥) :
    Function.Injective (SemidirectProduct.rightHom.domRestrict H) := by
  apply (SemidirectProduct.rightHom.domRestrict H).ker_eq_bot_iff.mp
  apply bot_unique
  intro h hh
  have hr : h.val.right = 1 := hh
  have hi : SemidirectProduct.inl h.val.left ∈ H := by
    have he : (SemidirectProduct.inl h.val.left : SplitGroup A) = h.val := by
      ext <;> simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, hr]
    exact he ▸ h.property
  have hl : h.val.left = 1 := by
    have hmem : h.val.left ∈ H.comap SemidirectProduct.inl := hi
    rwa [hN, Subgroup.mem_bot] at hmem
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  ext <;> assumption

omit [NeZero (q ^ s)] in
private theorem complement_eq_conjugate (H : Subgroup (SplitGroup A))
    (hN : H.comap SemidirectProduct.inl = ⊥)
    (hP : H.map SemidirectProduct.rightHom = ⊤) :
    ∃ x : Cyclic p, H =
      (SemidirectProduct.inr : Cyclic (q ^ s) →* SplitGroup A).range.map
        (MulAut.conj (SemidirectProduct.inl x : SplitGroup A)).toMonoidHom := by
  let v := generator (q ^ s)
  have hv : v ∈ H.map SemidirectProduct.rightHom := hP ▸ Subgroup.mem_top v
  obtain ⟨h, hh, hvh⟩ := hv
  have : Fact (Nat.card (Cyclic p)).Prime := ⟨by
    rw [cyclic_card p]
    exact (Fact.out : p.Prime)⟩
  have hα : A.action v ≠ 1 := by
    intro he
    have horder := A.order_generator
    change orderOf (A.action v) = q at horder
    rw [he, orderOf_one] at horder
    exact (Fact.out : q.Prime).ne_one horder.symm
  have hfree := prime_automorphism_fixedPointFree (A.action v) hα
  obtain ⟨x, hx⟩ := hfree.commutatorMap_surjective h.left
  have hconj : MulAut.conj (SemidirectProduct.inl x) (SemidirectProduct.inr v) = h := by
    apply SemidirectProduct.ext
    · simpa [MulAut.conj_apply, commutatorMap, div_eq_mul_inv] using hx
    · simpa [MulAut.conj_apply] using hvh.symm
  have hgen : H = zpowers h := by
    apply le_antisymm
    · intro y hy
      obtain ⟨z, hz⟩ := generator_generates (q ^ s) y.right
      have hright : (h ^ z).right = y.right := by
        change SemidirectProduct.rightHom (h ^ z) = y.right
        rw [map_zpow, hvh]
        exact hz
      have he : (⟨h ^ z, H.zpow_mem hh z⟩ : H) = ⟨y, hy⟩ :=
        projection_injective A H hN hright
      have he' : h ^ z = y := congrArg Subtype.val he
      exact he' ▸ Subgroup.zpow_mem_zpowers h z
    · exact zpowers_le_of_mem hh
  have hbase : (SemidirectProduct.inr : Cyclic (q ^ s) →* SplitGroup A).range =
      zpowers (SemidirectProduct.inr v) := by
    rw [← MonoidHom.map_zpowers, (zpowers v).eq_top_iff'.mpr
      (fun y => generator_generates (q ^ s) y), ← MonoidHom.range_eq_map]
  refine ⟨x, ?_⟩
  rw [hgen, hbase, MonoidHom.map_zpowers]
  exact congrArg zpowers hconj.symm

omit [Fact p.Prime] in
private theorem action_eq_one_of_mem_proper (hs : 0 < s)
    (B : Subgroup (Cyclic (q ^ s))) (hB : B ≠ ⊤)
    {y : Cyclic (q ^ s)} (hy : y ∈ B) : A.action y = 1 := by
  have hq := (Fact.out : q.Prime)
  have hc := cyclic_card (q ^ s)
  obtain ⟨j, hj⟩ := subgroup_exponent hq hc B
  have hjs : j.val < s := by
    have hjle := Nat.le_of_lt_succ j.isLt
    by_contra hn
    have he : j.val = s := by omega
    apply hB
    apply cyclic_subgroup_card_injective
    rw [hj, he, Nat.card_congr (Subgroup.topEquiv.toEquiv), hc]
  let M : Subgroup (Cyclic (q ^ s)) := zpowers (generator (q ^ s) ^ q)
  have hm : Nat.card M = q ^ (s - 1) := by
    rw [Nat.card_zpowers, orderOf_pow, generator_order,
      Nat.gcd_eq_right (dvd_pow_self q (Nat.ne_of_gt hs))]
    have he : q ^ s = q ^ (s - 1) * q := by
      rw [← pow_succ]
      congr 1
      omega
    rw [he, Nat.mul_div_cancel _ hq.pos]
  have hyM : y ∈ M := by
    rw [cyclic_subgroup_eq_kernel M, hm]
    change y ^ (q ^ (s - 1)) = 1
    apply orderOf_dvd_iff_pow_eq_one.mp
    have hyord : orderOf y ∣ Nat.card B := by
      simpa only [Subgroup.orderOf_mk] using
        (_root_.orderOf_dvd_natCard (x := (⟨y, hy⟩ : B)))
    exact hyord.trans (by
      rw [hj]
      exact pow_dvd_pow q (by omega))
  obtain ⟨z, hz⟩ := hyM
  rw [← hz, map_zpow, map_pow]
  have he : A.action (generator (q ^ s)) ^ q = 1 := by
    simpa only [A.order_generator] using pow_orderOf_eq_one (A.action (generator (q ^ s)))
  rw [he, one_zpow]

private theorem subgroup_eq_inr_of_proper (hs : 0 < s)
    (hc : p.Coprime q) (H : Subgroup (SplitGroup A))
    (hN : H.comap SemidirectProduct.inl = ⊥)
    (hP : H.map SemidirectProduct.rightHom ≠ ⊤) :
    H = (H.map SemidirectProduct.rightHom).map SemidirectProduct.inr := by
  let f : H →* Cyclic p := {
    toFun h := h.val.left
    map_one' := rfl
    map_mul' h k := by
      change h.val.left * A.action h.val.right k.val.left = h.val.left * k.val.left
      have ha : A.action h.val.right = 1 :=
        action_eq_one_of_mem_proper A hs _ hP (y := h.val.right) ⟨h.val, h.property, rfl⟩
      rw [ha]
      rfl }
  have hd : Nat.card H ∣ q ^ s := by
    have hi := projection_injective A H hN
    have hh : Nat.card H = Nat.card (SemidirectProduct.rightHom.domRestrict H).range :=
      Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
    rw [hh]
    simpa only [cyclic_card (q ^ s)] using
      card_subgroup_dvd_card (SemidirectProduct.rightHom.domRestrict H).range
  have hl : ∀ h : H, h.val.left = 1 := by
    intro h
    have hp : orderOf (f h) ∣ p := by
      simpa only [cyclic_card p] using _root_.orderOf_dvd_natCard (f h)
    have hq : orderOf (f h) ∣ q ^ s := (orderOf_map_dvd f h).trans
      ((_root_.orderOf_dvd_natCard h).trans hd)
    have hone : orderOf (f h) ∣ 1 := by
      simpa only [(hc.pow_right s).gcd_eq_one] using Nat.dvd_gcd hp hq
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hone)
  ext h
  constructor
  · intro hh
    refine ⟨h.right, ⟨h, hh, rfl⟩, ?_⟩
    apply SemidirectProduct.ext
    · exact (hl ⟨h, hh⟩).symm
    · rfl
  · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
    have he : (SemidirectProduct.inr h.right : SplitGroup A) = h :=
      SemidirectProduct.ext (hl ⟨h, hh⟩).symm rfl
    exact he ▸ hh

/-- Every subgroup is an inverse image from the cyclic quotient, an embedded
proper subgroup of that quotient, or a conjugate of the full complement. -/
theorem subgroup_classification (hs : 0 < s) (hc : p.Coprime q)
    (H : Subgroup (SplitGroup A)) :
    (∃ B : Subgroup (Cyclic (q ^ s)), H = B.comap SemidirectProduct.rightHom) ∨
    (∃ B : Subgroup (Cyclic (q ^ s)), B ≠ ⊤ ∧ H = B.map SemidirectProduct.inr) ∨
    (∃ x : Cyclic p, H =
      (SemidirectProduct.inr : Cyclic (q ^ s) →* SplitGroup A).range.map
        (MulAut.conj (SemidirectProduct.inl x : SplitGroup A)).toMonoidHom) := by
  have : Fact (Nat.card (Cyclic p)).Prime := ⟨by
    rw [cyclic_card p]
    exact (Fact.out : p.Prime)⟩
  rcases (H.comap SemidirectProduct.inl).eq_bot_or_eq_top_of_prime_card with hN | hN
  · by_cases hP : H.map SemidirectProduct.rightHom = ⊤
    · exact Or.inr (Or.inr (complement_eq_conjugate A H hN hP))
    · exact Or.inr (Or.inl ⟨_, hP, subgroup_eq_inr_of_proper A hs hc H hN hP⟩)
  · refine Or.inl ⟨H.map SemidirectProduct.rightHom, ?_⟩
    apply (Subgroup.comap_map_eq_self ?_).symm
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    rintro x ⟨y, rfl⟩
    have hy : y ∈ H.comap SemidirectProduct.inl := hN ▸ Subgroup.mem_top y
    exact hy

private def over (B : Subgroup (Cyclic (q ^ s))) : Subgroup (SplitGroup A) :=
  B.comap SemidirectProduct.rightHom

private def pure (B : Subgroup (Cyclic (q ^ s))) : Subgroup (SplitGroup A) :=
  B.map SemidirectProduct.inr

private def complement (x : Cyclic p) : Subgroup (SplitGroup A) :=
  (SemidirectProduct.inr : Cyclic (q ^ s) →* SplitGroup A).range.map
    (MulAut.conj (SemidirectProduct.inl x : SplitGroup A)).toMonoidHom

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem projection_over (B : Subgroup (Cyclic (q ^ s))) :
    (over A B).map SemidirectProduct.rightHom = B :=
  Subgroup.map_comap_eq_self_of_surjective SemidirectProduct.rightHom_surjective B

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem projection_pure (B : Subgroup (Cyclic (q ^ s))) :
    (pure A B).map SemidirectProduct.rightHom = B := by
  ext y
  constructor
  · rintro ⟨g, ⟨z, hz, rfl⟩, rfl⟩
    exact hz
  · intro hy
    exact ⟨SemidirectProduct.inr y, ⟨y, hy, rfl⟩, rfl⟩

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem projection_complement (x : Cyclic p) :
    (complement A x).map SemidirectProduct.rightHom = ⊤ := by
  apply top_unique
  intro y _
  refine ⟨MulAut.conj (SemidirectProduct.inl x) (SemidirectProduct.inr y),
    ⟨SemidirectProduct.inr y, ⟨y, rfl⟩, rfl⟩, ?_⟩
  simp [MulAut.conj_apply]

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem intersection_over (B : Subgroup (Cyclic (q ^ s))) :
    (over A B).comap SemidirectProduct.inl = ⊤ := by
  ext x
  simp [over, Subgroup.mem_comap]

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem intersection_pure (B : Subgroup (Cyclic (q ^ s))) :
    (pure A B).comap SemidirectProduct.inl = ⊥ := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    exact Subgroup.mem_bot.mpr (congrArg SemidirectProduct.left he).symm
  · intro hx
    rw [Subgroup.mem_bot] at hx
    subst x
    exact (pure A B).one_mem

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem intersection_complement (x : Cyclic p) :
    (complement A x).comap SemidirectProduct.inl = ⊥ := by
  ext y
  constructor
  · rintro ⟨g, ⟨z, rfl⟩, he⟩
    have hz : z = 1 := by
      simpa [MulAut.conj_apply] using congrArg SemidirectProduct.right he
    subst z
    simpa using (congrArg SemidirectProduct.left he).symm
  · intro hy
    rw [Subgroup.mem_bot] at hy
    subst y
    exact (complement A x).one_mem

omit [NeZero (q ^ s)] in
private theorem complement_injective : Function.Injective (complement A) := by
  intro x y he
  let v := generator (q ^ s)
  have hmem : MulAut.conj (SemidirectProduct.inl x) (SemidirectProduct.inr v) ∈
      complement A y := he ▸ ⟨SemidirectProduct.inr v, ⟨v, rfl⟩, rfl⟩
  obtain ⟨g, ⟨z, rfl⟩, hg⟩ := hmem
  have hz : z = v := by
    simpa [MulAut.conj_apply] using congrArg SemidirectProduct.right hg
  subst z
  have : Fact (Nat.card (Cyclic p)).Prime := ⟨by
    rw [cyclic_card p]
    exact (Fact.out : p.Prime)⟩
  have hne : A.action v ≠ 1 := by
    intro h
    have ho := A.order_generator
    change orderOf (A.action v) = q at ho
    rw [h, orderOf_one] at ho
    exact (Fact.out : q.Prime).ne_one ho.symm
  apply (prime_automorphism_fixedPointFree (A.action v) hne).commutatorMap_injective
  simpa [MulAut.conj_apply, commutatorMap, div_eq_mul_inv] using
    (congrArg SemidirectProduct.left hg).symm

/-- Labels for all subgroups: inverse images, proper embedded subgroups, and complements. -/
abbrev SubgroupLabel (p q s : ℕ) :=
  Subgroup (Cyclic (q ^ s)) ⊕ ({B : Subgroup (Cyclic (q ^ s)) // B ≠ ⊤} ⊕ Cyclic p)

private def decodeSubgroup : SubgroupLabel p q s → Subgroup (SplitGroup A)
  | .inl B => over A B
  | .inr (.inl B) => pure A B.val
  | .inr (.inr x) => complement A x

omit [NeZero (q ^ s)] in
private theorem decode_injective : Function.Injective (decodeSubgroup A) := by
  have hbt : (⊥ : Subgroup (Cyclic p)) ≠ ⊤ := bot_ne_top
  intro u v he
  cases u with
  | inl B =>
    cases v with
    | inl C =>
      exact congrArg Sum.inl (by
        simpa only [decodeSubgroup, projection_over] using
          congrArg (Subgroup.map SemidirectProduct.rightHom) he)
    | inr v =>
      cases v with
      | inl C =>
        exact False.elim (hbt (by simpa only [decodeSubgroup, intersection_over,
          intersection_pure] using (congrArg (Subgroup.comap SemidirectProduct.inl) he).symm))
      | inr x =>
        exact False.elim (hbt (by simpa only [decodeSubgroup, intersection_over,
          intersection_complement] using (congrArg (Subgroup.comap SemidirectProduct.inl) he).symm))
  | inr u =>
    cases v with
    | inl B =>
      cases u with
      | inl C =>
        exact False.elim (hbt (by simpa only [decodeSubgroup, intersection_over,
          intersection_pure] using congrArg (Subgroup.comap SemidirectProduct.inl) he))
      | inr x =>
        exact False.elim (hbt (by simpa only [decodeSubgroup, intersection_over,
          intersection_complement] using congrArg (Subgroup.comap SemidirectProduct.inl) he))
    | inr v =>
      cases u with
      | inl B =>
        cases v with
        | inl C =>
          apply congrArg (fun z => Sum.inr (Sum.inl z))
          apply Subtype.ext
          simpa only [decodeSubgroup, projection_pure] using
            congrArg (Subgroup.map SemidirectProduct.rightHom) he
        | inr x =>
          exact False.elim (B.property (by simpa only [decodeSubgroup, projection_pure,
            projection_complement] using congrArg (Subgroup.map SemidirectProduct.rightHom) he))
      | inr x =>
        cases v with
        | inl B =>
          exact False.elim (B.property (by simpa only [decodeSubgroup, projection_pure,
            projection_complement] using
              (congrArg (Subgroup.map SemidirectProduct.rightHom) he).symm))
        | inr y => exact congrArg (fun z => Sum.inr (Sum.inr z)) (complement_injective A he)

/-- A bijective enumeration of the whole subgroup lattice of the actual split group. -/
noncomputable def subgroupEnumeration (hs : 0 < s) (hc : p.Coprime q) :
    Subgroup (SplitGroup A) ≃ SubgroupLabel p q s :=
  (Equiv.ofBijective (decodeSubgroup A) ⟨decode_injective A, by
    intro H
    rcases subgroup_classification A hs hc H with ⟨B, hB⟩ | ⟨B, hB, he⟩ | ⟨x, hx⟩
    · exact ⟨.inl B, hB.symm⟩
    · exact ⟨.inr (.inl ⟨B, hB⟩), he.symm⟩
    · exact ⟨.inr (.inr x), hx.symm⟩⟩).symm

private theorem cyclic_lattice_card : Nat.card (Subgroup (Cyclic (q ^ s))) = s + 1 :=
  (Nat.card_congr (cyclicSubgroupEquiv (Fact.out : q.Prime) (cyclic_card (q ^ s)))).trans
    (Nat.card_fin (s + 1))

private instance cyclic_subgroups_finite : Finite (Subgroup (Cyclic (q ^ s))) :=
  Finite.of_equiv (Fin (s + 1))
    (cyclicSubgroupEquiv (Fact.out : q.Prime) (cyclic_card (q ^ s))).symm

private theorem proper_subgroup_card :
    Nat.card {B : Subgroup (Cyclic (q ^ s)) // B ≠ ⊤} = s := by
  classical
  let := Fintype.ofFinite (Subgroup (Cyclic (q ^ s)))
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun B => B = ⊤),
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, cyclic_lattice_card]
  omega

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem over_normal (B : Subgroup (Cyclic (q ^ s))) : (over A B).Normal := by
  change (B.comap SemidirectProduct.rightHom).Normal
  have : B.Normal := Subgroup.normalizer_eq_top_iff.mp
    (CommGroup.normalizer_eq_top (B : Set (Cyclic (q ^ s))))
  infer_instance

omit [Fact p.Prime] in
private theorem pure_normal (hs : 0 < s)
    (B : Subgroup (Cyclic (q ^ s))) (hB : B ≠ ⊤) : (pure A B).Normal := by
  constructor
  intro n hn g
  obtain ⟨y, hy, rfl⟩ := hn
  refine ⟨y, hy, ?_⟩
  have ha : A.action y = 1 := action_eq_one_of_mem_proper A hs B hB hy
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
      map_one, mul_one, SemidirectProduct.mul_right, SemidirectProduct.right_inr,
      SemidirectProduct.inv_left]
    rw [← MulAut.mul_apply, ← map_mul]
    have he : (g.right * y) * g.right⁻¹ = y := by
      rw [mul_right_comm, mul_inv_cancel, one_mul]
    rw [he, ha]
    simp
  · simp [mul_left_comm, mul_assoc]

open scoped Pointwise

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem conjugate_subgroup (g : SplitGroup A) (H : Subgroup (SplitGroup A)) :
    ConjAct.toConjAct g • H = H.map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom, ConjAct.toConjAct_smul_eq_mulAut_conj]

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem normal_orbit_iff (H J : Subgroup (SplitGroup A)) [J.Normal] :
    MulAction.orbitRel (ConjAct (SplitGroup A)) (Subgroup (SplitGroup A)) H J ↔ H = J := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨g, rfl⟩ := ConjAct.toConjAct.surjective g
    rw [Subgroup.conjAct_pointwise_smul_eq_self
      (show g ∈ Subgroup.normalizer (J : Set (SplitGroup A)) from by
        rw [@Subgroup.normalizer_eq_top (SplitGroup A) _ J _]
        exact Subgroup.mem_top g)] at hg
    exact hg.symm
  · intro h
    subst H
    exact ⟨1, one_smul _ _⟩

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem complement_orbit (x : Cyclic p) :
    MulAction.orbitRel (ConjAct (SplitGroup A)) (Subgroup (SplitGroup A))
      (complement A x) (complement A 1) := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨ConjAct.toConjAct (SemidirectProduct.inl x), ?_⟩
  rw [conjugate_subgroup]
  have hc : complement A 1 =
      (SemidirectProduct.inr : Cyclic (q ^ s) →* SplitGroup A).range := by
    ext g
    simp [complement, Subgroup.mem_map]
  rw [hc]
  rfl

/-- Labels for the inner-conjugacy classes; all complements share the final label. -/
abbrev OrbitLabel (q s : ℕ) :=
  Subgroup (Cyclic (q ^ s)) ⊕ ({B : Subgroup (Cyclic (q ^ s)) // B ≠ ⊤} ⊕ Unit)

private def liftLabel : OrbitLabel q s → SubgroupLabel p q s
  | .inl B => .inl B
  | .inr (.inl B) => .inr (.inl B)
  | .inr (.inr _) => .inr (.inr 1)

omit [Fact p.Prime] [Fact q.Prime] [NeZero (q ^ s)] in
private theorem liftLabel_injective :
    Function.Injective (liftLabel (p := p) (q := q) (s := s)) := by
  intro u v h
  cases u <;> cases v <;> simp_all only [liftLabel, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq]
  all_goals rename_i u v
  all_goals cases u <;> cases v <;> simp_all only [liftLabel, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, Subsingleton.elim]

private def representative (u : OrbitLabel q s) : Subgroup (SplitGroup A) :=
  decodeSubgroup A (liftLabel u)

private def quotientRepresentative (u : OrbitLabel q s) : SubgroupClasses (SplitGroup A) :=
  Quotient.mk _ (representative A u)

private theorem representative_orbit_injective (hs : 0 < s) :
    Function.Injective (quotientRepresentative A) := by
  intro u v he
  have hr := Quotient.exact he
  have heq (hn : (representative A v).Normal) : u = v := by
    have := hn
    exact liftLabel_injective (decode_injective A
      ((normal_orbit_iff A (representative A u) (representative A v)).mp hr))
  have heq' (hn : (representative A u).Normal) : u = v := by
    have := hn
    exact (liftLabel_injective (decode_injective A
      ((normal_orbit_iff A (representative A v) (representative A u)).mp
        ((MulAction.orbitRel (ConjAct (SplitGroup A)) _).symm hr)))).symm
  cases v with
  | inl B => exact heq (over_normal A B)
  | inr v =>
    cases v with
    | inl B => exact heq (pure_normal A hs B.val B.property)
    | inr v =>
      cases u with
      | inl B => exact heq' (over_normal A B)
      | inr u =>
        cases u with
        | inl B => exact heq' (pure_normal A hs B.val B.property)
        | inr u => exact congrArg (fun z => Sum.inr (Sum.inr z)) (Subsingleton.elim u v)

/-- An exact enumeration of the inner-conjugacy quotient of the full subgroup lattice. -/
noncomputable def classesEnumeration (hs : 0 < s) (hc : p.Coprime q) :
    SubgroupClasses (SplitGroup A) ≃ OrbitLabel q s :=
  (Equiv.ofBijective (quotientRepresentative A) ⟨representative_orbit_injective A hs, by
    intro c
    refine Quotient.inductionOn c ?_
    intro H
    rcases subgroup_classification A hs hc H with ⟨B, hB⟩ | ⟨B, hB, he⟩ | ⟨x, hx⟩
    · exact ⟨.inl B, congrArg (Quotient.mk _) hB.symm⟩
    · exact ⟨.inr (.inl ⟨B, hB⟩), congrArg (Quotient.mk _) he.symm⟩
    · refine ⟨.inr (.inr ()), ?_⟩
      rw [hx]
      exact Quotient.sound
        ((MulAction.orbitRel (ConjAct (SplitGroup A)) _).symm (complement_orbit A x))⟩).symm

/-- Exact subgroup and inner-conjugacy class counts for the actual split extension. -/
theorem split_counts (hs : 0 < s) (hc : p.Coprime q) :
    latticeCount (SplitGroup A) = 2 * s + p + 1 ∧
    classCount (SplitGroup A) = 2 * s + 2 := by
  constructor
  · rw [latticeCount, Nat.card_congr (subgroupEnumeration A hs hc),
      Nat.card_sum, Nat.card_sum, cyclic_lattice_card, proper_subgroup_card, cyclic_card p]
    omega
  · rw [classCount, Nat.card_congr (classesEnumeration A hs hc),
      Nat.card_sum, Nat.card_sum, cyclic_lattice_card, proper_subgroup_card, Nat.card_unique]
    omega

end SplitSubgroups

end D5.S3.FiniteGroups.CyclicPrimePowerAction

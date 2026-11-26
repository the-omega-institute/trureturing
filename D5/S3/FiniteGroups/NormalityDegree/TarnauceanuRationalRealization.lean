/- GID: D5/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NormalityDegree/TarnauceanuRationalRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational realization of finite group normality degrees. -/

import D5.S3.FiniteGroups.CyclicPrimePowerAction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! This module realizes every positive rational at most one as a normality degree. -/

namespace D5.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Subgroup MonoidHom SemidirectProduct
open D5.S3.FiniteGroups.CyclicPrimePowerAction
open D5.S3.FiniteGroups.SubgroupConjugacyRatio (latticeCount)

/-- All normal subgroups, including bottom and top. -/
abbrev NormalSubgroups (G : Type) [Group G] :=
  {H : Subgroup G // H.Normal}

/-- Tărnăuceanu's normality degree. -/
noncomputable def ndeg (G : Type) [Group G] [Finite G] : ℚ :=
  (Nat.card (NormalSubgroups G) : ℚ) /
    D5.S3.FiniteGroups.SubgroupConjugacyRatio.latticeCount G

/-- Conjecture 4.4 of arXiv:1312.1427v1, published as Conjecture 4.1. -/
def claim : Prop :=
  ∀ (x : ℚ), 0 < x → x ≤ 1 →
    ∃ (G : Type) (group : Group G) (finite : Finite G),
      @ndeg G group finite = x

private theorem ndeg_one_of_comm (G : Type) [CommGroup G] [Finite G] : ndeg G = 1 := by
  let e : NormalSubgroups G ≃ Subgroup G :=
    { toFun := Subtype.val
      invFun := fun H => ⟨H, inferInstance⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  unfold ndeg latticeCount
  rw [Nat.card_congr e, div_self]
  exact_mod_cast Nat.card_pos.ne'

private def multiplier (p : ℕ) : MulAut (Cyclic p) ≃* (ZMod p)ˣ :=
  (MulAutMultiplicative (ZMod p)).trans (ZMod.AddAutEquivUnits p).toMultiplicative

private theorem exists_multiplier (p t : ℕ) [Fact p.Prime] (hd : 2 ^ t ∣ p - 1) :
    ∃ r : (ZMod p)ˣ, orderOf r = 2 ^ t := by
  obtain ⟨g, hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := (ZMod p)ˣ)).mp inferInstance
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  refine ⟨g ^ ((p - 1) / 2 ^ t), ?_⟩
  rw [← hg] at hd ⊢
  have hn : orderOf g ≠ 0 := by
    rw [hg]
    exact Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt
  exact orderOf_pow_orderOf_div hn hd


section Projection

variable {N C : Type} [Group N] [CommGroup C] (φ : C →* MulAut N)

private abbrev Extension := N ⋊[φ] C

private def throughKernel (J : Subgroup C) : Subgroup (Extension φ) :=
  J.comap rightHom

private def sectionAt (a : N) : C →* Extension φ :=
  (MulAut.conj (inl a : Extension φ)).toMonoidHom.comp inr

private def overTrivial (J : Subgroup C) (a : N) : Subgroup (Extension φ) :=
  J.map (sectionAt φ a)

@[simp] private theorem sectionAt_right (a : N) (v : C) :
    (sectionAt φ a v).right = v := by
  simp [sectionAt, MulAut.conj_apply]

@[simp] private theorem sectionAt_left (a : N) (v : C) :
    (sectionAt φ a v).left = commutatorMap (φ v) a := by
  simp [sectionAt, MulAut.conj_apply, commutatorMap, div_eq_mul_inv]

@[simp] private theorem sectionAt_one (v : C) :
    sectionAt φ 1 v = inr v := by simp [sectionAt]

@[simp] private theorem projection_throughKernel (J : Subgroup C) :
    (throughKernel φ J).map rightHom = J :=
  map_comap_eq_self_of_surjective rightHom_surjective J

@[simp] private theorem intersection_throughKernel (J : Subgroup C) :
    (throughKernel φ J).comap inl = ⊤ := by
  ext a
  simp [throughKernel]

@[simp] private theorem projection_overTrivial (J : Subgroup C) (a : N) :
    (overTrivial φ J a).map rightHom = J := by
  rw [overTrivial, map_map]
  have h : rightHom.comp (sectionAt φ a) = MonoidHom.id C := by
    ext v
    exact sectionAt_right φ a v
  rw [h, Subgroup.map_id]

@[simp] private theorem intersection_overTrivial (J : Subgroup C) (a : N) :
    (overTrivial φ J a).comap inl = ⊥ := by
  ext x
  constructor
  · rintro ⟨v, -, h⟩
    have hv : v = 1 := by simpa using congrArg SemidirectProduct.right h
    subst v
    simpa using (congrArg SemidirectProduct.left h).symm
  · intro hx
    rw [Subgroup.mem_bot] at hx
    subst x
    exact (overTrivial φ J a).one_mem

private theorem unique_lift (H : Subgroup (Extension φ))
    (hbot : H.comap inl = ⊥) {g h : Extension φ} (hg : g ∈ H) (hh : h ∈ H)
    (he : g.right = h.right) : g = h := by
  have hz : (g * h⁻¹).right = 1 := by simp [he]
  have hi : (inl ((g * h⁻¹).left) : Extension φ) = g * h⁻¹ :=
    SemidirectProduct.ext rfl hz.symm
  have hl : (g * h⁻¹).left ∈ H.comap inl := by
    change SemidirectProduct.inl _ ∈ H
    rw [hi]
    exact H.mul_mem hg (H.inv_mem hh)
  rw [hbot, Subgroup.mem_bot] at hl
  exact mul_inv_eq_one.mp (SemidirectProduct.ext hl hz)

private theorem subgroup_generated_by_lift (H : Subgroup (Extension φ))
    (hbot : H.comap inl = ⊥) {v : C} (hJ : H.map rightHom = zpowers v)
    {g : Extension φ} (hg : g ∈ H) (hgv : g.right = v) : H = zpowers g := by
  apply le_antisymm _ (zpowers_le_of_mem hg)
  intro h hh
  have hm : h.right ∈ zpowers v := hJ ▸ ⟨h, hh, rfl⟩
  obtain ⟨k, hk⟩ := hm
  have hr : (g ^ k).right = h.right := by
    change rightHom (g ^ k) = h.right
    rw [map_zpow]
    exact (congrArg (fun w : C => w ^ k) hgv).trans hk
  have he := unique_lift φ H hbot (H.zpow_mem hg k) hh hr
  exact he ▸ zpow_mem_zpowers g k

private theorem throughKernel_of_comap_top (H : Subgroup (Extension φ))
    (htop : H.comap inl = ⊤) : H = throughKernel φ (H.map rightHom) := by
  apply (Subgroup.comap_map_eq_self ?_).symm
  rw [← range_inl_eq_ker_rightHom]
  rintro _ ⟨a, rfl⟩
  exact (show a ∈ H.comap inl by rw [htop]; trivial)

private theorem throughKernel_normal (J : Subgroup C) : (throughKernel φ J).Normal := by
  unfold throughKernel
  infer_instance

private theorem overTrivial_of_quiet (H : Subgroup (Extension φ))
    (hbot : H.comap inl = ⊥) (v : C) (hJ : H.map rightHom = zpowers v)
    (hquiet : φ v = 1) (hc : (Nat.card N).Coprime (orderOf v)) :
    H = overTrivial φ (zpowers v) 1 := by
  have hv : v ∈ H.map rightHom := hJ ▸ mem_zpowers v
  obtain ⟨g, hg, hgv⟩ := hv
  change g.right = v at hgv
  have hpow : g ^ orderOf v = 1 := by
    apply unique_lift φ H hbot (H.pow_mem hg _) H.one_mem
    change rightHom (g ^ orderOf v) = 1
    simp [map_pow, rightHom_eq_right, hgv]
  have hcomm : Commute (inl g.left : Extension φ) (inr v) := by
    apply SemidirectProduct.ext <;> simp [hquiet]
  have hdecomp : g = (inl g.left : Extension φ) * inr v := by
    rw [← hgv, inl_left_mul_inr_right]
  have hlpow : g.left ^ orderOf v = 1 := by
    have he := congrArg SemidirectProduct.left (hdecomp ▸ hpow :
      ((inl g.left : Extension φ) * inr v) ^ orderOf v = 1)
    rwa [hcomm.mul_pow, ← map_pow, ← map_pow, mul_left, left_inl, left_inr,
      map_one, mul_one, one_left] at he
  have hdiv := Nat.dvd_gcd (_root_.orderOf_dvd_natCard g.left)
    (orderOf_dvd_iff_pow_eq_one.mpr hlpow)
  rw [hc.gcd_eq_one] at hdiv
  have hl : g.left = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hdiv)
  rw [subgroup_generated_by_lift φ H hbot hJ hg hgv, overTrivial, MonoidHom.map_zpowers,
    sectionAt_one]
  exact congrArg zpowers (SemidirectProduct.ext hl hgv)

private theorem overTrivial_quiet_normal (J : Subgroup C)
    (hquiet : ∀ v ∈ J, φ v = 1) : (overTrivial φ J 1).Normal := by
  constructor
  rintro _ ⟨v, hv, rfl⟩ g
  have hc : Commute ((inr v : Extension φ)) g := by
    apply SemidirectProduct.ext
    · simp [hquiet v hv]
    · simp [mul_comm]
  refine ⟨v, hv, ?_⟩
  rw [sectionAt_one, ← hc.eq, mul_inv_cancel_right]

section PrimeKernel
variable [Finite N] [Fact (Nat.card N).Prime]

private theorem overTrivial_of_active (H : Subgroup (Extension φ))
    (hbot : H.comap inl = ⊥) (v : C) (hJ : H.map rightHom = zpowers v)
    (hactive : φ v ≠ 1) : ∃ a : N, H = overTrivial φ (zpowers v) a := by
  have hv : v ∈ H.map rightHom := hJ ▸ mem_zpowers v
  obtain ⟨g, hg, hgv⟩ := hv
  change g.right = v at hgv
  obtain ⟨a, ha⟩ := (prime_automorphism_fixedPointFree (φ v) hactive).commutatorMap_surjective
    g.left
  refine ⟨a, ?_⟩
  rw [subgroup_generated_by_lift φ H hbot hJ hg hgv, overTrivial, MonoidHom.map_zpowers]
  apply congrArg zpowers
  exact SemidirectProduct.ext (by simpa using ha.symm) (by simpa using hgv)

omit [Finite N] in
private theorem overTrivial_active_injective (v : C) (hactive : φ v ≠ 1) :
    Function.Injective (overTrivial φ (zpowers v)) := by
  intro a b he
  have ha : sectionAt φ a v ∈ overTrivial φ (zpowers v) a := ⟨v, mem_zpowers v, rfl⟩
  have hb : sectionAt φ b v ∈ overTrivial φ (zpowers v) b := ⟨v, mem_zpowers v, rfl⟩
  have hs := unique_lift φ _ (intersection_overTrivial φ _ b) (he ▸ ha) hb
    (by simp)
  apply (prime_automorphism_fixedPointFree (φ v) hactive).commutatorMap_injective
  simpa using congrArg SemidirectProduct.left hs

private theorem overTrivial_active_not_normal (v : C) (hactive : φ v ≠ 1) (a : N) :
    ¬(overTrivial φ (zpowers v) a).Normal := by
  have conjugate (b : N) :
      (overTrivial φ (zpowers v) 1).map (MulAut.conj (inl b : Extension φ)) =
        overTrivial φ (zpowers v) b := by
    simp [overTrivial, sectionAt]
  have hbase : ¬(overTrivial φ (zpowers v) 1).Normal := by
    have : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp
      (Fact.out : (Nat.card N).Prime).one_lt
    obtain ⟨b, hb⟩ := exists_ne (1 : N)
    intro hn
    have he := Subgroup.normal_iff_map_conj_eq.mp hn (inl b)
    rw [conjugate b] at he
    exact hb (overTrivial_active_injective φ v hactive he)
  intro hn
  apply hbase
  apply (MulEquiv.normal_map_iff (f := MulAut.conj (inl a : Extension φ))).mp
  rw [conjugate a]
  exact hn

end PrimeKernel
end Projection

private abbrev QuotientCyclic (B : ℕ) := Cyclic (2 ^ B)

private instance (B : ℕ) : NeZero (2 ^ B) := ⟨by positivity⟩

private def levelGenerator (B : ℕ) (j : Fin (B + 1)) : QuotientCyclic B :=
  generator (2 ^ B) ^ (2 ^ (B - j.val) : ℕ)

private abbrev level (B : ℕ) (j : Fin (B + 1)) : Subgroup (QuotientCyclic B) :=
  zpowers (levelGenerator B j)

private theorem levelGenerator_order (B : ℕ) (j : Fin (B + 1)) :
    orderOf (levelGenerator B j) = 2 ^ j.val := by
  have hj : j.val ≤ B := Nat.le_of_lt_succ j.isLt
  have hd : (2 : ℕ) ^ (B - j.val) ∣ 2 ^ B := pow_dvd_pow 2 (Nat.sub_le _ _)
  unfold levelGenerator
  rw [orderOf_pow_of_dvd (by positivity) (by simpa only [generator_order] using hd),
      generator_order, Nat.pow_div (Nat.sub_le B j.val) (by decide : 0 < 2)]
  congr 1
  omega

private noncomputable def allLevels (B : ℕ) : Subgroup (QuotientCyclic B) ≃ Fin (B + 1) :=
  cyclicSubgroupEquiv Nat.prime_two (cyclic_card (2 ^ B))

private theorem allLevels_symm (B : ℕ) (j : Fin (B + 1)) :
    (allLevels B).symm j = level B j := by
  apply IsCyclic.subgroup_eq_iff_card_eq.mpr
  change Nat.card ((powMonoidHom (2 ^ j.val) : QuotientCyclic B →* QuotientCyclic B).ker) =
    Nat.card (zpowers (levelGenerator B j))
  rw [kernel_power_card (cyclic_card (2 ^ B)) j, Nat.card_zpowers, levelGenerator_order]

private theorem level_injective (B : ℕ) : Function.Injective (level B) := by
  intro i j he
  apply (allLevels B).symm.injective
  rw [allLevels_symm, allLevels_symm, he]

private theorem level_surjective (B : ℕ) : Function.Surjective (level B) := by
  intro J
  exact ⟨allLevels B J, (allLevels_symm B _).symm.trans ((allLevels B).symm_apply_apply J)⟩

private noncomputable def powerAction {p B : ℕ} (t : ℕ) (ht : t ≤ B)
    (r : (ZMod p)ˣ) (hr : orderOf r = 2 ^ t) : QuotientCyclic B →* MulAut (Cyclic p) := by
  have ha : orderOf ((multiplier p).symm r) = 2 ^ t :=
    ((multiplier p).symm.orderOf_eq r).trans hr
  refine monoidHomOfForallMemZpowers (g' := (multiplier p).symm r) (generator_generates _) ?_
  rw [ha, generator_order]
  exact pow_dvd_pow 2 ht

private theorem powerAction_generator {p B t : ℕ} (ht : t ≤ B)
    (r : (ZMod p)ˣ) (hr : orderOf r = 2 ^ t) :
    powerAction t ht r hr (generator (2 ^ B)) = (multiplier p).symm r := by
  unfold powerAction
  exact monoidHomOfForallMemZpowers_apply_gen _ _

private theorem powerAction_order {p B t : ℕ} (ht : t ≤ B)
    (r : (ZMod p)ˣ) (hr : orderOf r = 2 ^ t) :
    orderOf (powerAction t ht r hr (generator (2 ^ B))) = 2 ^ t := by
  rw [powerAction_generator, (multiplier p).symm.orderOf_eq, hr]

private theorem level_quiet_iff {p B t : ℕ} (φ : QuotientCyclic B →* MulAut (Cyclic p))
    (hord : orderOf (φ (generator (2 ^ B))) = 2 ^ t) (ht : t ≤ B)
    (j : Fin (B + 1)) : φ (levelGenerator B j) = 1 ↔ j.val ≤ B - t := by
  rw [levelGenerator, map_pow, ← orderOf_dvd_iff_pow_eq_one, hord,
    Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)]
  omega

private theorem level_action_quiet {p B t : ℕ} (φ : QuotientCyclic B →* MulAut (Cyclic p))
    (hord : orderOf (φ (generator (2 ^ B))) = 2 ^ t) (ht : t ≤ B)
    {j : Fin (B + 1)} (hj : j.val ≤ B - t) :
    ∀ v ∈ level B j, φ v = 1 := by
  rintro v ⟨k, rfl⟩
  rw [map_zpow, (level_quiet_iff φ hord ht j).mpr hj, one_zpow]

private abbrev SubgroupLabel (p B t : ℕ) :=
  Fin (B + 1) ⊕ (Fin (B - t + 1) ⊕ (Fin t × Cyclic p))

private def quietLevel {B t : ℕ} (i : Fin (B - t + 1)) : Fin (B + 1) :=
  ⟨i.val, by have := i.isLt; omega⟩

private def activeLevel {B t : ℕ} (ht : t ≤ B) (i : Fin t) : Fin (B + 1) :=
  ⟨B - t + 1 + i.val, by have := i.isLt; omega⟩

private def decode (p B t : ℕ) (ht : t ≤ B)
    (φ : QuotientCyclic B →* MulAut (Cyclic p)) :
    SubgroupLabel p B t → Subgroup (Extension φ)
  | .inl j => throughKernel φ (level B j)
  | .inr (.inl i) => overTrivial φ (level B (quietLevel i)) 1
  | .inr (.inr (i, a)) => overTrivial φ (level B (activeLevel ht i)) a

section Counts

variable {p B t : ℕ} [Fact p.Prime]
variable (φ : QuotientCyclic B →* MulAut (Cyclic p))
variable (hord : orderOf (φ (generator (2 ^ B))) = 2 ^ t) (ht : t ≤ B)

private theorem projection_decode (z : SubgroupLabel p B t) :
    (decode p B t ht φ z).map rightHom = level B
      (z.elim id (Sum.elim quietLevel (fun u => activeLevel ht u.1))) := by
  rcases z with j | i | ⟨i, a⟩ <;> simp [decode]

include hord in
private theorem decode_injective : Function.Injective (decode p B t ht φ) := by
  have : Fact (Nat.card (Cyclic p)).Prime := ⟨by rw [cyclic_card]; exact Fact.out⟩
  have : Nontrivial (Cyclic p) :=
    Finite.one_lt_card_iff_nontrivial.mp (Fact.out : (Nat.card (Cyclic p)).Prime).one_lt
  intro u v he
  have hlevel := level_injective B (by
    simpa only [projection_decode] using congrArg (Subgroup.map rightHom) he)
  have hinter := congrArg (Subgroup.comap inl) he
  have htopbot : (⊤ : Subgroup (Cyclic p)) ≠ ⊥ := top_ne_bot
  rcases u with i | i | ⟨i, a⟩ <;> rcases v with j | j | ⟨j, b⟩
  · exact congrArg Sum.inl hlevel
  · simp [decode] at hinter
  · simp [decode] at hinter
  · exact (htopbot (by simpa [decode] using hinter.symm)).elim
  · have hij := congrArg Fin.val hlevel
    exact congrArg (fun i => Sum.inr (Sum.inl i)) (Fin.ext hij)
  · have hij := congrArg Fin.val hlevel
    have hi := i.isLt
    simp [quietLevel, activeLevel] at hij
    omega
  · exact (htopbot (by simpa [decode] using hinter.symm)).elim
  · have hij := congrArg Fin.val hlevel
    have hj := j.isLt
    simp [quietLevel, activeLevel] at hij
    omega
  · have hij := congrArg Fin.val hlevel
    simp [quietLevel, activeLevel] at hij
    have hij' : i = j := Fin.ext (by omega)
    subst j
    have hactive : φ (levelGenerator B (activeLevel ht i)) ≠ 1 := by
      rw [ne_eq, level_quiet_iff φ hord ht]
      simp only [activeLevel]
      omega
    have hab := overTrivial_active_injective φ _ hactive he
    subst b
    rfl

include hord in
private theorem decode_surjective (hp2 : p.Coprime 2) :
    Function.Surjective (decode p B t ht φ) := by
  have : Fact (Nat.card (Cyclic p)).Prime := ⟨by rw [cyclic_card]; exact Fact.out⟩
  intro H
  obtain ⟨j, hj⟩ := level_surjective B (H.map rightHom)
  rcases (H.comap inl).eq_bot_or_eq_top_of_prime_card with hbot | htop
  · by_cases hquiet : j.val ≤ B - t
    · let i : Fin (B - t + 1) := ⟨j.val, by omega⟩
      have hi : quietLevel i = j := Fin.ext rfl
      refine ⟨.inr (.inl i), ?_⟩
      change overTrivial φ (level B (quietLevel i)) 1 = H
      rw [hi]
      apply (overTrivial_of_quiet φ H hbot _ hj.symm
        ((level_quiet_iff φ hord ht j).mpr hquiet) ?_).symm
      rw [cyclic_card, levelGenerator_order]
      exact hp2.pow_right _
    · let i : Fin t := ⟨j.val - (B - t + 1), by have := j.isLt; omega⟩
      have hi : activeLevel ht i = j := Fin.ext (by dsimp [i, activeLevel]; omega)
      have hactive : φ (levelGenerator B j) ≠ 1 := mt ((level_quiet_iff φ hord ht j).mp) hquiet
      obtain ⟨a, ha⟩ := overTrivial_of_active φ H hbot _ hj.symm hactive
      refine ⟨.inr (.inr (i, a)), ?_⟩
      change overTrivial φ (level B (activeLevel ht i)) a = H
      exact (congrArg (fun k => overTrivial φ (level B k) a) hi).trans ha.symm
  · refine ⟨.inl j, ?_⟩
    exact (congrArg (throughKernel φ) hj).trans (throughKernel_of_comap_top φ H htop).symm

include hord in
private theorem decode_quiet_normal (i : Fin (B - t + 1)) :
    (decode p B t ht φ (.inr (.inl i))).Normal := by
  apply overTrivial_quiet_normal
  apply level_action_quiet φ hord ht
  exact Nat.le_of_lt_succ i.isLt

include hord in
private theorem decode_active_not_normal (i : Fin t) (a : Cyclic p) :
    ¬(decode p B t ht φ (.inr (.inr (i, a)))).Normal := by
  have : Fact (Nat.card (Cyclic p)).Prime := ⟨by rw [cyclic_card]; exact Fact.out⟩
  apply overTrivial_active_not_normal
  rw [ne_eq, level_quiet_iff φ hord ht]
  simp only [activeLevel]
  omega

include hord in
private noncomputable def normalDecode :
    Fin (B + 1) ⊕ Fin (B - t + 1) → NormalSubgroups (Extension φ)
  | .inl j => ⟨decode p B t ht φ (.inl j), throughKernel_normal φ _⟩
  | .inr i => ⟨decode p B t ht φ (.inr (.inl i)), decode_quiet_normal φ hord ht i⟩

private theorem normalDecode_bijective (hp2 : p.Coprime 2) :
    Function.Bijective (normalDecode φ hord ht) := by
  constructor
  · intro u v he
    have hins : Function.Injective (Sum.elim Sum.inl (fun i => Sum.inr (Sum.inl i)) :
      Fin (B + 1) ⊕ Fin (B - t + 1) → SubgroupLabel p B t) := by
      intro a b h
      cases a <;> cases b <;> simp_all
    apply hins
    apply decode_injective φ hord ht
    have hv := congrArg Subtype.val he
    cases u <;> cases v <;> exact hv
  · rintro ⟨H, hH⟩
    obtain ⟨j, hj⟩ := decode_surjective φ hord ht hp2 H
    rcases j with j | i | ⟨i, a⟩
    · exact ⟨.inl j, Subtype.ext hj⟩
    · exact ⟨.inr i, Subtype.ext hj⟩
    · exact (decode_active_not_normal φ hord ht i a (hj ▸ hH)).elim

include hord ht in
private theorem split_counts (hp2 : p.Coprime 2) :
    Nat.card (NormalSubgroups (Extension φ)) = 2 * B - t + 2 ∧
      latticeCount (Extension φ) = 2 * B - t + 2 + p * t := by
  have hN := Nat.card_congr (Equiv.ofBijective _ (normalDecode_bijective φ hord ht hp2)).symm
  have hL := Nat.card_congr (Equiv.ofBijective _ ⟨decode_injective φ hord ht,
    decode_surjective φ hord ht hp2⟩).symm
  rw [Nat.card_sum, Nat.card_fin, Nat.card_fin] at hN
  rw [Nat.card_sum, Nat.card_sum, Nat.card_prod, Nat.card_fin, Nat.card_fin,
    Nat.card_fin, cyclic_card] at hL
  change Nat.card (Subgroup (Extension φ)) = _ at hL
  unfold latticeCount
  rw [hN, hL, Nat.mul_comm t p]
  omega

end Counts

private theorem ndeg_fraction (u v : ℕ) (hu : 0 < u) (huv : u < v) :
    ∃ (G : Type) (group : Group G) (finite : Finite G),
      @ndeg G group finite = (u : ℚ) / (v : ℚ) := by
  let d := v - u
  let t := 2 * d
  have hd : 0 < d := by dsimp [d]; omega
  have ht0 : 0 < t := by dsimp [t]; omega
  obtain ⟨p, hp, hpt, hpmod⟩ := Nat.exists_prime_gt_modEq_one (k := 2 ^ t) (2 * t)
    (by positivity)
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have hdiv : 2 ^ t ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_lt.le).mp hpmod.symm
  obtain ⟨r, hr⟩ := exists_multiplier p t hdiv
  let B := p * u + d - 1
  have hpu : p ≤ p * u := by simpa using Nat.mul_le_mul_left p (show 1 ≤ u by omega)
  have hB : t ≤ B := by dsimp [B]; omega
  let φ := powerAction t hB r hr
  let G := Extension φ
  have : Finite G :=
    Finite.of_equiv (Cyclic p × QuotientCyclic B) SemidirectProduct.equivProd.symm
  have hc := split_counts φ (powerAction_order hB r hr) hB hp2
  have hN : Nat.card (NormalSubgroups G) = 2 * p * u := by
    change Nat.card (NormalSubgroups (Extension φ)) = _
    rw [hc.1, Nat.mul_assoc]
    dsimp [B, t]
    omega
  have hL : latticeCount G = 2 * p * v := by
    change latticeCount (Extension φ) = _
    rw [hc.2]
    have hbase : 2 * B - t + 2 = 2 * p * u := by
      rw [Nat.mul_assoc]
      dsimp [B, t]
      omega
    rw [hbase]
    have hv : u + d = v := by dsimp [d]; omega
    rw [← hv]
    dsimp [t]
    ring
  refine ⟨G, inferInstance, inferInstance, ?_⟩
  unfold ndeg
  rw [hN, hL]
  push_cast
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast (show v ≠ 0 by omega)
  field_simp

/-- Every rational in `(0,1]` is the normality degree of a finite group. -/
theorem result : claim := by
  intro x hx hle
  by_cases h : x = 1
  · refine ⟨Cyclic 2, inferInstance, inferInstance, ?_⟩
    rw [h, ndeg_one_of_comm]
  · have hx1 : x < 1 := lt_of_le_of_ne hle h
    have hpos := Rat.num_pos.mpr hx
    have hnum : (x.num.toNat : ℤ) = x.num := Int.toNat_of_nonneg hpos.le
    have hu : 0 < x.num.toNat := by omega
    have huv : x.num.toNat < x.den := by
      have hl := Rat.num_lt_denom_iff.mpr hx1
      omega
    obtain ⟨G, group, finite, hg⟩ := ndeg_fraction x.num.toNat x.den hu huv
    refine ⟨G, group, finite, hg.trans ?_⟩
    rw [← Int.cast_natCast (R := ℚ), hnum, Rat.num_div_den]

end D5.FiniteGroups.NormalityDegree.TarnauceanuRationalRealization

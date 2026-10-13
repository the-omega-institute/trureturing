/- GID: D5/S3/FiniteGroups/SubgroupConjugacyRatio
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubgroupConjugacyRatio
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Subgroup lattices and inner-conjugacy quotients split over coprime products. -/

import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Quot
import Mathlib.Tactic.NormNum

namespace D5.S3.FiniteGroups.SubgroupConjugacyRatio

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Pointwise

/-- The quotient of the entire subgroup lattice by inner conjugation. -/
abbrev SubgroupClasses (G : Type*) [Group G] :=
  Quotient (MulAction.orbitRel (ConjAct G) (Subgroup G))

/-- All subgroups, including the trivial subgroup and the whole group. -/
noncomputable def latticeCount (G : Type*) [Group G] : ℕ := Nat.card (Subgroup G)

/-- The number of inner-conjugacy classes of subgroups. -/
noncomputable def classCount (G : Type*) [Group G] : ℕ := Nat.card (SubgroupClasses G)

/-- The subgroup-conjugacy ratio of an actual finite group. -/
noncomputable def ratio (G : Type*) [Group G] : ℚ :=
  (classCount G : ℚ) / latticeCount G

/-- An actual finite group, with no structural restriction. -/
structure FiniteGroup where
  Carrier : Type
  group : Group Carrier
  finite : Finite Carrier

attribute [instance] FiniteGroup.group FiniteGroup.finite

/-- Problem 4.1 of arXiv:2508.14267v2, in integer cross-multiplied form.
The existential witness supplies the group operation and finiteness. -/
def RationalAttainment : Prop :=
  ∀ a b : ℤ, 1 ≤ a → a < b → ∃ W : FiniteGroup,
    b * (classCount W.Carrier : ℤ) = a * (latticeCount W.Carrier : ℤ)

variable {G K : Type*} [Group G] [Group K]

private theorem split_fst_mem [Finite G] [Finite K]
    (hc : (Nat.card G).Coprime (Nat.card K))
    (H : Subgroup (G × K)) {g : G} {k : K} (h : (g, k) ∈ H) : (g, 1) ∈ H := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (hc.symm.coprime_dvd_right (orderOf_dvd_natCard (x := g)))
  have hp := H.pow_mem h (Nat.card K)
  have hpm := H.pow_mem hp m
  simpa only [Prod.pow_mk, pow_card_eq_one', one_pow, hm] using hpm

private theorem split_snd_mem [Finite G] [Finite K]
    (hc : (Nat.card G).Coprime (Nat.card K))
    (H : Subgroup (G × K)) {g : G} {k : K} (h : (g, k) ∈ H) : (1, k) ∈ H := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (hc.coprime_dvd_right (orderOf_dvd_natCard (x := k)))
  have hp := H.pow_mem h (Nat.card G)
  have hpm := H.pow_mem hp m
  simpa only [Prod.pow_mk, pow_card_eq_one', one_pow, hm] using hpm

private theorem subgroup_eq_prod [Finite G] [Finite K]
    (hc : (Nat.card G).Coprime (Nat.card K)) (H : Subgroup (G × K)) :
    H = (H.map (MonoidHom.fst G K)).prod (H.map (MonoidHom.snd G K)) := by
  ext x
  rcases x with ⟨x, y⟩
  constructor
  · intro hx
    exact ⟨⟨(x, y), hx, rfl⟩, ⟨(x, y), hx, rfl⟩⟩
  · rintro ⟨⟨⟨g, k⟩, hgk, hg⟩, ⟨⟨g', k'⟩, hgk', hk⟩⟩
    have hfst := split_fst_mem hc H hgk
    have hsnd := split_snd_mem hc H hgk'
    have hh := H.mul_mem hfst hsnd
    change g = x at hg
    change k' = y at hk
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, hg, hk] using hh

private theorem map_fst_prod (H : Subgroup G) (J : Subgroup K) :
    (H.prod J).map (MonoidHom.fst G K) = H := by
  ext g
  constructor
  · rintro ⟨⟨g, k⟩, h, rfl⟩
    exact h.1
  · intro h
    exact ⟨(g, 1), ⟨h, J.one_mem⟩, rfl⟩

private theorem map_snd_prod (H : Subgroup G) (J : Subgroup K) :
    (H.prod J).map (MonoidHom.snd G K) = J := by
  ext k
  constructor
  · rintro ⟨⟨g, k⟩, h, rfl⟩
    exact h.2
  · intro h
    exact ⟨(1, k), ⟨H.one_mem, h⟩, rfl⟩

/-- Every subgroup of a coprime-order product is the product of its projections. -/
noncomputable def subgroupProductEquiv [Finite G] [Finite K]
    (hc : (Nat.card G).Coprime (Nat.card K)) :
    Subgroup (G × K) ≃ Subgroup G × Subgroup K where
  toFun H := (H.map (MonoidHom.fst G K), H.map (MonoidHom.snd G K))
  invFun H := H.1.prod H.2
  left_inv H := (subgroup_eq_prod hc H).symm
  right_inv H := by simp only [map_fst_prod, map_snd_prod]

private theorem conj_prod (g : G) (k : K) (H : Subgroup G) (J : Subgroup K) :
    ConjAct.toConjAct (g, k) • H.prod J =
      (ConjAct.toConjAct g • H).prod (ConjAct.toConjAct k • J) := by
  ext x
  simp only [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_prod]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, he⟩
    exact ⟨⟨u, hu, congrArg Prod.fst he⟩, ⟨v, hv, congrArg Prod.snd he⟩⟩
  · rintro ⟨⟨u, hu, he⟩, ⟨v, hv, hf⟩⟩
    refine ⟨(u, v), ⟨hu, hv⟩, ?_⟩
    exact Prod.ext he hf

private theorem prod_orbit_iff (H H' : Subgroup G) (J J' : Subgroup K) :
    MulAction.orbitRel (ConjAct (G × K)) (Subgroup (G × K)) (H.prod J) (H'.prod J') ↔
      MulAction.orbitRel (ConjAct G) (Subgroup G) H H' ∧
      MulAction.orbitRel (ConjAct K) (Subgroup K) J J' := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨⟨g, k⟩, rfl⟩ := ConjAct.toConjAct.surjective c
    rw [conj_prod] at hc
    refine ⟨⟨ConjAct.toConjAct g, ?_⟩, ⟨ConjAct.toConjAct k, ?_⟩⟩
    · simpa only [map_fst_prod] using congrArg (Subgroup.map (MonoidHom.fst G K)) hc
    · simpa only [map_snd_prod] using congrArg (Subgroup.map (MonoidHom.snd G K)) hc
  · rintro ⟨⟨g, hg⟩, ⟨k, hk⟩⟩
    refine ⟨ConjAct.toConjAct (ConjAct.ofConjAct g, ConjAct.ofConjAct k), ?_⟩
    simp only [conj_prod, ConjAct.toConjAct_ofConjAct, hg, hk]

private def classesProd (q : SubgroupClasses G) (r : SubgroupClasses K) :
    SubgroupClasses (G × K) :=
  Quotient.map₂' (fun H J => H.prod J)
    (fun _ _ hH _ _ hJ => (prod_orbit_iff _ _ _ _).mpr ⟨hH, hJ⟩) q r

private theorem classesProd_injective :
    Function.Injective (fun q : SubgroupClasses G × SubgroupClasses K =>
      classesProd q.1 q.2) := by
  rintro ⟨q, r⟩ ⟨q', r'⟩
  refine Quotient.inductionOn₂ q q' ?_ r r'
  intro H H' r r'
  refine Quotient.inductionOn₂ r r' ?_
  intro J J' h
  have hh := (prod_orbit_iff H H' J J').mp (Quotient.exact h)
  exact Prod.ext (Quotient.sound hh.1) (Quotient.sound hh.2)

/-- The inner-conjugacy quotient of a coprime product splits into the two quotients. -/
noncomputable def classesProductEquiv [Finite G] [Finite K]
    (hc : (Nat.card G).Coprime (Nat.card K)) :
    SubgroupClasses (G × K) ≃ SubgroupClasses G × SubgroupClasses K :=
  (Equiv.ofBijective (fun q => classesProd q.1 q.2)
    ⟨classesProd_injective, by
      intro q
      refine Quotient.inductionOn q ?_
      intro H
      refine ⟨(Quotient.mk _ (H.map (MonoidHom.fst G K)),
        Quotient.mk _ (H.map (MonoidHom.snd G K))), ?_⟩
      change Quotient.mk _ ((H.map (MonoidHom.fst G K)).prod
        (H.map (MonoidHom.snd G K))) = Quotient.mk _ H
      rw [← subgroup_eq_prod hc H]⟩).symm

/-- Both counts, and hence the ratio, multiply for finite groups of coprime orders. -/
theorem coprime_product_counts [Finite G] [Finite K]
    (hc : (Nat.card G).Coprime (Nat.card K)) :
    latticeCount (G × K) = latticeCount G * latticeCount K ∧
    classCount (G × K) = classCount G * classCount K ∧
    ratio (G × K) = ratio G * ratio K := by
  have hL : latticeCount (G × K) = latticeCount G * latticeCount K :=
    (Nat.card_congr (subgroupProductEquiv hc)).trans (Nat.card_prod _ _)
  have hC : classCount (G × K) = classCount G * classCount K :=
    (Nat.card_congr (classesProductEquiv hc)).trans (Nat.card_prod _ _)
  refine ⟨hL, hC, ?_⟩
  simp only [ratio, hL, hC, Nat.cast_mul, mul_div_mul_comm]

end D5.S3.FiniteGroups.SubgroupConjugacyRatio

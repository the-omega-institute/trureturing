/- GID: D5/S3/FiniteGroups/GroupAlgebra/CyclicSubgroupProjectivity
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/CyclicSubgroupProjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.SpecificGroups.Cyclic, mathlib/module/Mathlib.LinearAlgebra.GeneralLinearGroup.Basic]
   utility: none
   digest: Prime-support subgroups detect projectivity for every finite cyclic group over arbitrary commutative coefficients. -/

import D5.S3.FiniteGroups.GroupAlgebra.CyclicNormOne
import D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
Prime-support subgroups detect projectivity over every finite cyclic group.
The coefficient ring and module are arbitrary and their universes are
independent of the group universe. Zero rings/modules and trivial groups
remain in scope. Coefficient projectivity is retained by the general
conjugation-trace criterion.

The period-free norm lift and the general trace criterion are reused at their
original owners. Strong induction on q lifts an (sigma^q,r)-norm-one witness
whenever q,r>0 and each prime dividing q divides r. For q=p*q', first lift
with sigma^q', p,r,c (where r=c*p), then recurse on q' with new length p*r.
Only natural exponents and powers of the same automorphism are rearranged;
no two arbitrary endomorphism factors are commuted.

The ordinary finite-cyclic proof was supplied by Pro (observed gpt_6, pro
effort; task cbbd2223-6e8f-48bd-9076-3c7fe0a6f854). Its mathematical input
is the period-free Aljadeff--Kassel lift supplied by CyclicNormOne.
Source context: E. Aljadeff and C. Kassel, Explicit elements of norm one for
cyclic groups, https://arxiv.org/abs/math/0012038. This attribution does not
assert literature novelty.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.CyclicSubgroupProjectivity

open Finset
open scoped MonoidAlgebra

universe uR uG uV uA uB

section RingInduction

variable {A : Type uA} [Ring A]

/-- Prime-support norm lifting for an arbitrary ring and automorphism.
The induction is on the index q; r may grow during the induction. -/
private theorem prime_support_norm_one (sigma : A ≃+* A) (q r : ℕ)
    (hq : 0 < q) (hr : 0 < r)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ r)
    (hx : ∃ x : A, CyclicNormOne.norm (sigma ^ q) r x = 1) :
    ∃ y : A, CyclicNormOne.norm sigma (q * r) y = 1 := by
  revert sigma r hq hr hsupport hx
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro sigma r hq hr hsupport hx
      by_cases hqone : q = 1
      · simpa only [hqone, pow_one, one_mul] using hx
      · obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hqone
        have hpr : p ∣ r := hsupport p hp hpq
        obtain ⟨q', hqfac⟩ := hpq
        have hq' : 0 < q' := by
          apply Nat.pos_of_ne_zero
          intro hz
          rw [hz, Nat.mul_zero] at hqfac
          exact hq.ne' hqfac
        have hlt : q' < q := by
          rw [hqfac]
          exact lt_mul_of_one_lt_left hq' hp.one_lt
        obtain ⟨c, hc⟩ := hpr
        have hrc : r = c * p := hc.trans (Nat.mul_comm p c)
        obtain ⟨x, hx⟩ := hx
        have hxstep :
            (∑ i ∈ range r, ((sigma ^ q') ^ (p * i)) x) = 1 := by
          change (∑ i ∈ range r, ((sigma ^ q) ^ i) x) = 1 at hx
          simpa only [← pow_mul, hqfac,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hx
        obtain ⟨z, hz⟩ := CyclicNormOne.exists_norm_one_lift (sigma ^ q')
          p r c hp.pos hr hrc x hxstep
        have hz' : ∃ z : A, CyclicNormOne.norm (sigma ^ q') (p * r) z = 1 :=
          ⟨z, hz⟩
        have hsupport' : ∀ l : ℕ, l.Prime → l ∣ q' → l ∣ p * r := by
          intro l hl hlq'
          have hlq : l ∣ q := by
            rw [hqfac]
            exact dvd_mul_of_dvd_right hlq' p
          exact dvd_mul_of_dvd_right (hsupport l hl hlq) p
        obtain ⟨y, hy⟩ := ih q' hlt sigma (p * r) hq'
          (Nat.mul_pos hp.pos hr) hsupport' hz'
        refine ⟨y, ?_⟩
        simpa only [hqfac, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hy

end RingInduction

section Enumeration

variable {G : Type uG} [Group G] [Fintype G]

/-- The bounded powers of an actual generator enumerate G exactly once. -/
private theorem generator_powers_bijective (g : G)
    (hg : ∀ a : G, a ∈ Subgroup.zpowers g) :
    Function.Bijective (fun i : Fin (Nat.card G) => g ^ i.val) := by
  classical
  have horder : orderOf g = Nat.card G :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  constructor
  · intro i j hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (x := g)
      (by simpa only [horder, Set.mem_Iio] using i.isLt)
      (by simpa only [horder, Set.mem_Iio] using j.isLt) hij
  · intro a
    have ha : a ∈ (range (Nat.card G)).image (fun i : ℕ => g ^ i) := by
      rw [IsCyclic.image_range_card hg]
      exact mem_univ a
    obtain ⟨i, hi, hia⟩ := mem_image.mp ha
    exact ⟨⟨i, mem_range.mp hi⟩, hia⟩

/-- Sum conversion uses that bijection, so no terms are lost or repeated. -/
private theorem sum_generator_powers {B : Type uB} [AddCommMonoid B]
    (g : G) (hg : ∀ a : G, a ∈ Subgroup.zpowers g) (f : G → B) :
    (∑ a : G, f a) = ∑ i ∈ range (Nat.card G), f (g ^ i) := by
  classical
  have he := Fintype.sum_bijective (fun i : Fin (Nat.card G) => g ^ i.val)
    (generator_powers_bijective g hg) (fun i => f (g ^ i.val)) f (fun _ => rfl)
  exact he.symm.trans (Fin.sum_univ_eq_sum_range (fun i : ℕ => f (g ^ i))
    (Nat.card G))

/-- The index-th power of a full cyclic generator generates the supplied H. -/
private theorem index_generator_subgroup [IsCyclic G] (g : G)
    (horder : orderOf g = Nat.card G) (H : Subgroup G) (hq : 0 < H.index) :
    Subgroup.zpowers (g ^ H.index) = H := by
  have hdvd : H.index ∣ orderOf g := by
    rw [horder]
    exact H.index_dvd_card
  have ho : orderOf (g ^ H.index) = Nat.card H := by
    rw [orderOf_pow_of_dvd hq.ne' hdvd, horder, ← H.index_mul_card]
    exact Nat.mul_div_cancel_left (Nat.card H) hq
  apply IsCyclic.subgroup_eq_iff_card_eq.mpr
  rw [Nat.card_zpowers, ho]

end Enumeration

section Conjugation

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- This is the actual conjugation ring automorphism induced by rho(g),
constructed via its unit and linear equivalence, not assumed as a premise. -/
private def conjugation (rho : Representation R G V) (g : G) :
    Module.End R V ≃+* Module.End R V :=
  (LinearMap.GeneralLinearGroup.toLinearEquiv (rho.asGroupHom g)).conjRingEquiv

private theorem conjugation_apply (rho : Representation R G V) (g : G)
    (t : Module.End R V) :
    conjugation rho g t = (rho g).comp (t.comp (rho g⁻¹)) := by
  have hi : (↑((rho.asGroupHom g)⁻¹) : Module.End R V) = rho g⁻¹ := by
    rw [← map_inv, Representation.asGroupHom_apply]
  apply LinearMap.ext
  intro v
  change (↑(rho.asGroupHom g) : Module.End R V)
      (t ((↑((rho.asGroupHom g)⁻¹) : Module.End R V) v)) =
    rho g (t (rho g⁻¹ v))
  rw [hi, Representation.asGroupHom_apply]

private theorem conjugation_one (rho : Representation R G V) :
    conjugation rho (1 : G) = 1 := by
  ext t v
  simp [conjugation_apply]

private theorem conjugation_mul (rho : Representation R G V) (g h : G) :
    conjugation rho (g * h) = conjugation rho g * conjugation rho h := by
  ext t v
  simp only [RingAut.mul_apply, conjugation_apply, LinearMap.comp_apply,
    mul_inv_rev, map_mul, Module.End.mul_apply]

/-- RingAut multiplication is composition; it agrees with the order of
the representation product, including the inverse factors on the right. -/
private theorem conjugation_pow (rho : Representation R G V) (g : G) (i : ℕ) :
    conjugation rho (g ^ i) = conjugation rho g ^ i := by
  induction i with
  | zero => simpa only [pow_zero] using conjugation_one rho
  | succ i ih => rw [pow_succ, conjugation_mul, ih, pow_succ]

variable [Fintype G]

private theorem group_trace_eq_norm (rho : Representation R G V) (g : G)
    (hg : ∀ a : G, a ∈ Subgroup.zpowers g) (t : Module.End R V) :
    (∑ a : G, (rho a).comp (t.comp (rho a⁻¹))) =
      CyclicNormOne.norm (conjugation rho g) (Nat.card G) t := by
  rw [sum_generator_powers g hg]
  change (∑ i ∈ range (Nat.card G),
      (rho (g ^ i)).comp (t.comp (rho (g ^ i)⁻¹))) =
    ∑ i ∈ range (Nat.card G), (conjugation rho g ^ i) t
  apply sum_congr rfl
  intro i _
  rw [← conjugation_apply, conjugation_pow]

/-- Lift the chosen subgroup generator into H, prove it generates H there,
and enumerate H itself. The left sum is literally the restricted action. -/
private theorem subgroup_trace_eq_norm (rho : Representation R G V) (g : G)
    (H : Subgroup G) [Fintype H] (m : ℕ)
    (hH : Subgroup.zpowers (g ^ m) = H) (t : Module.End R V) :
    (∑ a : H, ((rho.comp H.subtype) a).comp
      (t.comp ((rho.comp H.subtype) a⁻¹))) =
      CyclicNormOne.norm (conjugation rho g ^ m) (Nat.card H) t := by
  have hmem : g ^ m ∈ H := by
    rw [← hH]
    exact Subgroup.mem_zpowers (g ^ m)
  let h : H := ⟨g ^ m, hmem⟩
  have hgen : ∀ a : H, a ∈ Subgroup.zpowers h := by
    intro a
    have ha : (a : G) ∈ Subgroup.zpowers (g ^ m) := by
      rw [hH]
      exact a.property
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp ha
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change (g ^ m) ^ z = (a : G)
    exact hz
  rw [sum_generator_powers h hgen]
  change (∑ i ∈ range (Nat.card H),
      (rho ((g ^ m) ^ i)).comp (t.comp (rho (((g ^ m) ^ i)⁻¹)))) =
    ∑ i ∈ range (Nat.card H), ((conjugation rho g ^ m) ^ i) t
  apply sum_congr rfl
  intro i _
  rw [← conjugation_apply, conjugation_pow, conjugation_pow]

end Conjugation

/-- For every finite cyclic group, a subgroup whose order is divisible by
every prime dividing the group order detects projectivity over arbitrary
commutative coefficients.
The universes are independent and the representation module is arbitrary. -/
theorem projective_iff_projective_prime_support_subgroup
    {R : Type uR} {G : Type uG} {V : Type uV}
    [CommRing R] [Group G] [Fintype G] [IsCyclic G]
    [AddCommGroup V] [Module R V]
    (rho : Representation R G V) (H : Subgroup G)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p ∣ Nat.card H) :
    Module.Projective R[G] rho.asModule ↔
      Module.Projective R[H]
        (Representation.asModule (rho.comp H.subtype : Representation R H V)) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  let rhoH : Representation R H V := rho.comp H.subtype
  change Module.Projective R[G] rho.asModule ↔ Module.Projective R[H] rhoH.asModule
  have hq : 0 < H.index := Nat.pos_of_ne_zero H.index_ne_zero_of_finite
  have hr : 0 < Nat.card H := Nat.card_pos
  have hsupportq : ∀ p : ℕ, p.Prime → p ∣ H.index → p ∣ Nat.card H := by
    intro p hp hpq
    exact hsupport p hp (hpq.trans H.index_dvd_card)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have horder : orderOf g = Nat.card G :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hsub : Subgroup.zpowers (g ^ H.index) = H :=
    index_generator_subgroup g horder H hq
  let sigma : Module.End R V ≃+* Module.End R V := conjugation rho g
  have hG (t : Module.End R V) :
      (∑ a : G, (rho a).comp (t.comp (rho a⁻¹))) =
        CyclicNormOne.norm sigma (H.index * Nat.card H) t := by
    rw [H.index_mul_card]
    exact group_trace_eq_norm rho g hg t
  have hHt (t : Module.End R V) :
      (∑ a : H, ((rho.comp H.subtype) a).comp
        (t.comp ((rho.comp H.subtype) a⁻¹))) =
          CyclicNormOne.norm (sigma ^ H.index) (Nat.card H) t := by
    exact subgroup_trace_eq_norm rho g H H.index hsub t
  rw [ProjectiveConjugationTrace.projective_iff_projective_and_conjugation_trace_one rho,
    ProjectiveConjugationTrace.projective_iff_projective_and_conjugation_trace_one
      rhoH]
  constructor
  · rintro ⟨hR, t, ht⟩
    refine ⟨hR, CyclicNormOne.norm sigma H.index t, ?_⟩
    rw [hHt, CyclicNormOne.norm_comm, ← CyclicNormOne.norm_blocks]
    rw [hG] at ht
    exact ht
  · rintro ⟨hR, t, ht⟩
    rw [hHt] at ht
    obtain ⟨s, hs⟩ := prime_support_norm_one sigma H.index (Nat.card H)
      hq hr hsupportq ⟨t, ht⟩
    refine ⟨hR, s, ?_⟩
    rw [hG]
    exact hs

end D5.S3.FiniteGroups.GroupAlgebra.CyclicSubgroupProjectivity

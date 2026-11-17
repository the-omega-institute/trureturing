/- GID: D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.claim; result=D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.result; claim=D5/S3/FiniteGroups/Frobenius/MartinezLargestOrderPrimeCommutingRefutation.claim
   digest: The largest order prime does not bound the fixed-element pi-commuting fraction. -/

/-
# The largest-order-prime commuting question

The definitions express the prime support of element and subgroup orders,
the supremum of normal pi-subgroups, and the rational fixed-element fraction.
They retain the expressions of the source question in issue #24851.

For every prime q >= 5, in DihedralGroup 3 × DihedralGroup q the element
(sr 0, r 1) has order 2q, lies outside the pi-core for pi = {2,q}, and has
fixed-element pi-commuting fraction 1/4. The result specializes to q = 5.

result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#24851; Refuted)
  Direct frozen dependencies: none

Every private theorem below has proof_shape bind-only and escape_witness none.
Direct frozen dependencies for every declaration: none.
Consumers (consumer -> prerequisite):
  family_pi_iff -> pi_prod, dihedral_all_pi, d3_pi
  core_le_fst_kernel -> normal_d3_pi_bot
  family_pi_card -> family_pi_iff
  family_centralizing_iff -> d3_centralizer, dq_centralizer, family_pi_iff
  family_centralizing_card -> family_centralizing_iff
  family_core -> core_le_fst_kernel
  family_fraction -> family_pi_card, family_centralizing_card
  family_counterexample -> family_pi_iff, family_core, family_order, family_fraction
  result -> family_counterexample
The familyElement definition is consumed by the family centralizer, order,
fraction and counterexample statements and their proofs.

The public result is the designated refutation result (`basis=refutes`) and
is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/


import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace D5.S3.FiniteGroups.Frobenius.MartinezLargestOrderPrimeCommutingRefutation

set_option autoImplicit false

/-- G_π: elements whose order has no prime divisor outside π; includes 1. -/
def piElements (G : Type*) [Group G] [Finite G] (π : Set ℕ) : Set G :=
  {x | ∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∈ π}

/-- A π-subgroup: all prime divisors of its cardinality belong to π. -/
def isPiSubgroup {G : Type*} [Group G] [Finite G]
    (π : Set ℕ) (N : Subgroup G) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ Nat.card N → p ∈ π

/-- O_π(G): the supremum of all normal π-subgroups of the finite group G. -/
noncomputable def piCore (G : Type*) [Group G] [Finite G] (π : Set ℕ) : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ isPiSubgroup π N}

/-- |C_G(x)_π| / |G_π|, using the existing centralizer and rational division. -/
noncomputable def commutingFraction (G : Type*) [Group G] [Finite G]
    (π : Set ℕ) (x : G) : ℚ :=
  (Nat.card {y : G // y ∈ piElements G π ∧ y ∈ Subgroup.centralizer ({x} : Set G)} : ℚ) /
    (Nat.card {y : G // y ∈ piElements G π} : ℚ)

/-- The unnumbered largest-prime question following Theorem 4.7 in §4 of
arXiv:2307.09868v3: Theorem A with the largest prime divisor of o(x). -/
def claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    ∀ π : Set ℕ, (∀ p : ℕ, p ∈ π → p.Prime) → π.Nonempty →
      ∀ x : G, x ∈ piElements G π → x ∉ piCore G π →
        ∃ q : ℕ, q.Prime ∧ q ∣ orderOf x ∧
          (∀ p : ℕ, p.Prime → p ∣ orderOf x → p ≤ q) ∧
          commutingFraction G π x ≤ 1 / (q : ℚ)

open DihedralGroup


private theorem pi_prod {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (π : Set ℕ) (a : H) (b : K) :
    (a,b) ∈ piElements (H × K) π ↔ a ∈ piElements H π ∧ b ∈ piElements K π := by
  constructor
  · intro h
    constructor
    · intro p hp hd
      exact h p hp (by rw [Prod.orderOf_mk]; exact hd.trans (Nat.dvd_lcm_left _ _))
    · intro p hp hd
      exact h p hp (by rw [Prod.orderOf_mk]; exact hd.trans (Nat.dvd_lcm_right _ _))
  · rintro ⟨ha,hb⟩ p hp hd
    rw [Prod.orderOf_mk] at hd
    exact (hp.dvd_lcm.mp hd).elim (ha p hp) (hb p hp)

private theorem dihedral_all_pi {q : ℕ} (hq : q.Prime) [NeZero q]
    (x : DihedralGroup q) : x ∈ piElements (DihedralGroup q) ({2,q} : Set ℕ) := by
  intro p hp hd
  have hcard : p ∣ 2*q := by
    simpa only [DihedralGroup.nat_card] using hd.trans (orderOf_dvd_natCard x)
  rcases hp.dvd_mul.mp hcard with h|h
  · exact Or.inl ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp h).symm
  · exact Or.inr ((hq.dvd_iff_eq hp.ne_one).mp h).symm

private theorem d3_pi {q : ℕ} (hq : 5 ≤ q) (x : DihedralGroup 3) :
    x ∈ piElements (DihedralGroup 3) ({2,q} : Set ℕ) ↔
      x = 1 ∨ ∃ i : ZMod 3, x = sr i := by
  cases x with
  | r i =>
    fin_cases i
    · constructor
      · intro _; exact Or.inl rfl
      · intro _ p hp hd
        change p ∣ orderOf (1 : DihedralGroup 3) at hd
        rw [orderOf_one] at hd
        exact (hp.not_dvd_one hd).elim
    · constructor
      · intro h
        have ho : orderOf (r (1 : ZMod 3)) = 3 := DihedralGroup.orderOf_r_one
        have h3 := h 3 (by decide) (by change 3 ∣ orderOf (r (1 : ZMod 3)); rw [ho])
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3
        omega
      · rintro (he | ⟨j,he⟩)
        · exact ((by decide : (r (1 : ZMod 3)) ≠ (1 : DihedralGroup 3)) he).elim
        · cases he
    · constructor
      · intro h
        have ho : orderOf (r (2 : ZMod 3)) = 3 := by rw [orderOf_r]; decide
        have h3 := h 3 (by decide) (by change 3 ∣ orderOf (r (2 : ZMod 3)); rw [ho])
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3
        omega
      · rintro (he | ⟨j,he⟩)
        · exact ((by decide : (r (2 : ZMod 3)) ≠ (1 : DihedralGroup 3)) he).elim
        · cases he
  | sr i =>
    constructor
    · intro _; exact Or.inr ⟨i,rfl⟩
    · intro _ p hp hd
      rw [DihedralGroup.orderOf_sr] at hd
      exact Or.inl ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp hd).symm


private theorem normal_d3_pi_bot {q : ℕ} (hq : 5 ≤ q)
    (N : Subgroup (DihedralGroup 3)) (hn : N.Normal)
    (hpi : isPiSubgroup ({2,q} : Set ℕ) N) : N = ⊥ := by
  have hn3 : ¬ 3 ∣ Nat.card N := by
    intro hd
    have h3 := hpi 3 (by decide) hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3
    omega
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  cases x with
  | r i =>
    fin_cases i
    · rfl
    · have hd : orderOf (r (1 : ZMod 3)) ∣ Nat.card N := N.orderOf_dvd_natCard hx
      rw [DihedralGroup.orderOf_r_one] at hd
      exact (hn3 hd).elim
    · have hd : orderOf (r (2 : ZMod 3)) ∣ Nat.card N := N.orderOf_dvd_natCard hx
      have ho : orderOf (r (2 : ZMod 3)) = 3 := by rw [orderOf_r]; decide
      rw [ho] at hd
      exact (hn3 hd).elim
  | sr i =>
    have hc := N.mul_mem hx (hn.conj_mem (sr i) hx (r 1))
    have he : (sr i : DihedralGroup 3) * (r 1 * sr i * (r 1)⁻¹) = r 1 := by
      simp only [inv_r, r_mul_sr, sr_mul_r, sr_mul_sr]
      congr 1
      calc
        (i - 1 + -1) - i = (-2 : ZMod 3) := by ring
        _ = 1 := by decide
    rw [he] at hc
    have hd : orderOf (r (1 : ZMod 3)) ∣ Nat.card N := N.orderOf_dvd_natCard hc
    rw [DihedralGroup.orderOf_r_one] at hd
    exact (hn3 hd).elim

private theorem core_le_fst_kernel {K : Type*} [Group K] [Finite K]
    {q : ℕ} (hq : 5 ≤ q) :
    piCore (DihedralGroup 3 × K) ({2,q} : Set ℕ) ≤
      (MonoidHom.fst (DihedralGroup 3) K).ker := by
  apply sSup_le
  rintro N ⟨hn,hpi⟩
  have hm : N.map (MonoidHom.fst (DihedralGroup 3) K) = ⊥ :=
    normal_d3_pi_bot hq _ (hn.map _ Prod.fst_surjective)
      (fun p hp hd => hpi p hp (hd.trans (Subgroup.card_map_dvd N _)))
  intro x hx
  have hm' : x.1 ∈ N.map (MonoidHom.fst (DihedralGroup 3) K) :=
    Subgroup.mem_map.mpr ⟨x,hx,rfl⟩
  change x.1 = 1
  exact Subgroup.mem_bot.mp (hm ▸ hm')


private def familyElement (q : ℕ) : (DihedralGroup 3 × DihedralGroup q) := (sr 0, r 1)

private theorem family_pi_iff {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) [NeZero q]
    (x : (DihedralGroup 3 × DihedralGroup q)) : x ∈ piElements ((DihedralGroup 3 × DihedralGroup q)) ({2,q} : Set ℕ) ↔
      x.1 = 1 ∨ ∃ i : ZMod 3, x.1 = sr i := by
  rw [pi_prod, d3_pi hq5]
  exact and_iff_left (dihedral_all_pi hq x.2)

private theorem family_pi_card {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) [NeZero q] :
    Nat.card {x : (DihedralGroup 3 × DihedralGroup q) // x ∈ piElements ((DihedralGroup 3 × DihedralGroup q)) ({2,q} : Set ℕ)} = 8*q := by
  have he := (Equiv.subtypeEquivRight (family_pi_iff hq hq5)).trans
    (Equiv.prodSubtypeFstEquivSubtypeProd
      (α := DihedralGroup 3) (β := DihedralGroup q)
      (p := fun a => a = 1 ∨ ∃ i : ZMod 3, a = sr i))
  rw [Nat.card_congr he, Nat.card_prod, DihedralGroup.nat_card]
  have hc : Nat.card {x : DihedralGroup 3 // x = 1 ∨ ∃ i : ZMod 3, x = sr i} = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hc]
  omega

private theorem d3_centralizer (x : DihedralGroup 3) :
    sr 0 * x = x * sr 0 ↔ x = 1 ∨ x = sr 0 := by
  cases x with
  | r i => fin_cases i <;> decide
  | sr i => fin_cases i <;> decide

private theorem dq_centralizer {q : ℕ} (hq5 : 5 ≤ q) [NeZero q]
    (x : DihedralGroup q) :
    r 1 * x = x * r 1 ↔ ∃ i : ZMod q, r i = x := by
  cases x with
  | r i => simp [add_comm]
  | sr i =>
    simp only [r_mul_sr, sr_mul_r, sr.injEq, reduceCtorEq, exists_false, iff_false]
    intro he
    have ht : (2 : ZMod q) = 0 := by linear_combination -he
    have hd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp ht
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega

private theorem family_centralizing_iff {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    [NeZero q] (x : (DihedralGroup 3 × DihedralGroup q)) :
    (x ∈ piElements ((DihedralGroup 3 × DihedralGroup q)) ({2,q} : Set ℕ) ∧
      x ∈ Subgroup.centralizer ({familyElement q} : Set ((DihedralGroup 3 × DihedralGroup q)))) ↔
      (x.1 = 1 ∨ x.1 = sr 0) ∧ ∃ i : ZMod q, r i = x.2 := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  change (x ∈ piElements ((DihedralGroup 3 × DihedralGroup q)) ({2,q} : Set ℕ) ∧
    (sr 0 * x.1, r 1 * x.2) = (x.1 * sr 0, x.2 * r 1)) ↔ _
  rw [Prod.mk.injEq, d3_centralizer, dq_centralizer hq5]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(family_pi_iff hq hq5 x).mpr
      (h.1.elim Or.inl (fun hs => Or.inr ⟨0,hs⟩)),h⟩

private theorem family_centralizing_card {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    [NeZero q] :
    Nat.card {x : (DihedralGroup 3 × DihedralGroup q) // x ∈ piElements ((DihedralGroup 3 × DihedralGroup q)) ({2,q} : Set ℕ) ∧
      x ∈ Subgroup.centralizer ({familyElement q} : Set ((DihedralGroup 3 × DihedralGroup q)))} = 2*q := by
  have he := (Equiv.subtypeEquivRight (family_centralizing_iff hq hq5)).trans
    (Equiv.subtypeProdEquivProd
      (α := DihedralGroup 3) (β := DihedralGroup q)
      (p := fun a => a = 1 ∨ a = sr 0) (q := fun b => ∃ i : ZMod q, r i = b))
  rw [Nat.card_congr he, Nat.card_prod]
  have hc : Nat.card {x : DihedralGroup 3 // x = 1 ∨ x = sr 0} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have heq : {x : DihedralGroup q // ∃ i : ZMod q, r i = x} ≃ ZMod q :=
    (Equiv.ofInjective (r : ZMod q → DihedralGroup q) (fun _ _ h => r.inj h)).symm
  rw [hc, Nat.card_congr heq, Nat.card_zmod]


private theorem family_core {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) [NeZero q] :
    piCore ((DihedralGroup 3 × DihedralGroup q)) ({2,q} : Set ℕ) =
      (⊥ : Subgroup (DihedralGroup 3)).prod (⊤ : Subgroup (DihedralGroup q)) := by
  apply le_antisymm
  · simpa only [MonoidHom.ker_fst] using (core_le_fst_kernel (K := DihedralGroup q) hq5)
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    intro p hp hd
    have hc : Nat.card ((⊥ : Subgroup (DihedralGroup 3)).prod
        (⊤ : Subgroup (DihedralGroup q))) = 2*q := by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
      rw [Subgroup.card_bot, Subgroup.card_top, DihedralGroup.nat_card, one_mul]
    rw [hc] at hd
    rcases hp.dvd_mul.mp hd with h|h
    · exact Or.inl ((Nat.prime_two.dvd_iff_eq hp.ne_one).mp h).symm
    · exact Or.inr ((hq.dvd_iff_eq hp.ne_one).mp h).symm

private theorem family_order {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) :
    orderOf (familyElement q) = 2*q := by
  simp only [familyElement, Prod.orderOf_mk, orderOf_sr, orderOf_r_one]
  exact (Nat.coprime_two_left.mpr (hq.odd_of_ne_two (by omega))).lcm_eq_mul

private theorem family_fraction {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) [NeZero q] :
    commutingFraction ((DihedralGroup 3 × DihedralGroup q)) ({2,q} : Set ℕ) (familyElement q) = 1/4 := by
  rw [commutingFraction, family_centralizing_card hq hq5, family_pi_card hq hq5]
  have hn : (q : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  push_cast
  field_simp; ring

private theorem family_counterexample {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) [NeZero q] :
    familyElement q ∈ piElements ((DihedralGroup 3 × DihedralGroup q)) ({2,q} : Set ℕ) ∧
    familyElement q ∉ piCore ((DihedralGroup 3 × DihedralGroup q)) ({2,q} : Set ℕ) ∧
    orderOf (familyElement q) = 2*q ∧
    commutingFraction ((DihedralGroup 3 × DihedralGroup q)) ({2,q} : Set ℕ) (familyElement q) = 1/4 := by
  refine ⟨(family_pi_iff hq hq5 _).mpr (Or.inr ⟨0,rfl⟩), ?_,
    family_order hq hq5, family_fraction hq hq5⟩
  rw [family_core hq hq5]
  simp [familyElement, Subgroup.mem_prod, -DihedralGroup.r_zero, DihedralGroup.one_def]

theorem result : ¬ claim := by
  intro h
  obtain ⟨hm,hn,ho,hf⟩ := family_counterexample (by decide : Nat.Prime 5) (by decide)
  obtain ⟨q,hq,hd,hmax,hbound⟩ := h ((DihedralGroup 3 × DihedralGroup 5)) ({2,5} : Set ℕ)
    (by
      intro p hp
      rcases hp with rfl|hp
      · exact Nat.prime_two
      · have : p = 5 := hp
        subst p
        decide)
    ⟨2,Or.inl rfl⟩ (familyElement 5) hm hn
  have hq5 : q = 5 := by
    have h5 := hmax 5 (by decide) (by rw [ho]; decide)
    rw [ho] at hd
    have hdiv := hq.dvd_mul.mp hd
    rcases hdiv with h2|h5'
    · have := (Nat.prime_two.dvd_iff_eq hq.ne_one).mp h2
      omega
    · exact (((by decide : Nat.Prime 5).dvd_iff_eq hq.ne_one).mp h5').symm
  rw [hq5,hf] at hbound
  norm_num at hbound

end D5.S3.FiniteGroups.Frobenius.MartinezLargestOrderPrimeCommutingRefutation

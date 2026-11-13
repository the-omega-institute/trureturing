/- GID: D5/S3/Combinatorics/CayleySumCodes/FiniteNormalTransversal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/FiniteNormalTransversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The elementary arbitrary-finite-group normal-transversal characterization of commutativity. -/

import D5.S3.Combinatorics.CayleySumCodes.SolvableNormalTransversal
import D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal
import D5.S3.FiniteGroups.SimpleOrderSixty
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic

/- The only Atlas results used below are its general simple-center lemma and
its general injection of disjoint subgroup nonidentity elements. Neither has
an order-sixty premise. Their Moonshine-in-Kansas/atlas attribution and
Apache-2.0 source license remain at the imported canonical source. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.CayleySumCodes.FiniteNormalTransversal

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
open D5.S3.Combinatorics.CayleySumCodes.NormalTransversal
open scoped Pointwise

universe u
variable {G : Type u} [Group G] [Finite G]

private theorem nonidentity_bound {ι : Type*} [Fintype ι]
    (H : ι → Subgroup G) (hd : Pairwise (fun i j => Disjoint (H i) (H j))) :
    (∑ i, (Nat.card (H i) - 1)) ≤ Nat.card G - 1 := by
  classical
  let f : (Σ i, {x : H i // x ≠ 1}) → {x : G // x ≠ 1} :=
    fun z => ⟨z.2.1.1, fun h => z.2.2 (Subtype.ext h)⟩
  have hf : Function.Injective f := fun x y h =>
    Atlas.GroupTheory.subgroup_nonidentity_sigma_injective H hd (congrArg Subtype.val h)
  have hb := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sigma] at hb
  simp_rw [Atlas.GroupTheory.card_subgroup_nonidentity] at hb
  have he : Nat.card {x : G // x ≠ 1} = Nat.card G - 1 := by
    letI := Fintype.ofFinite G
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  exact he ▸ hb

private def conjugationOrderIso (a : ConjAct G) : Subgroup G ≃o Subgroup G where
  toEquiv :=
    { toFun := fun H => a • H
      invFun := fun H => a⁻¹ • H
      left_inv := fun H => inv_smul_smul a H
      right_inv := fun H => smul_inv_smul a H }
  map_rel_iff' := Subgroup.pointwise_smul_le_pointwise_smul_iff

private theorem orbit_coatom (M : Subgroup G) (hm : IsCoatom M)
    (N : MulAction.orbit (ConjAct G) M) : IsCoatom N.1 := by
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp N.2
  rw [← ha]
  exact ((conjugationOrderIso a).isCoatom_iff M).mpr hm

private theorem orbit_card (M : Subgroup G)
    (N : MulAction.orbit (ConjAct G) M) : Nat.card N.1 = Nat.card M := by
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp N.2
  rw [← ha]
  exact (Nat.card_congr (Subgroup.equivSMul a M).toEquiv).symm

private theorem orbit_mass (M : Subgroup G) (hn : Subgroup.normalizer (M : Set G) = M) :
    Nat.card (MulAction.orbit (ConjAct G) M) * Nat.card M = Nat.card G := by
  classical
  letI : Finite (ConjAct G) := Finite.of_equiv G ConjAct.toConjAct.toEquiv
  let S := MulAction.stabilizer (ConjAct G) M
  let e : S ≃ M :=
    { toFun := fun a => ⟨ConjAct.ofConjAct a.1, by
        rw [← hn]
        exact Subgroup.conjAct_pointwise_smul_iff.mp a.2⟩
      invFun := fun m => ⟨ConjAct.toConjAct m.1, by
        apply Subgroup.conjAct_pointwise_smul_iff.mpr
        exact hn.symm ▸ m.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  letI := Fintype.ofFinite (ConjAct G)
  letI := Fintype.ofFinite (MulAction.orbit (ConjAct G) M)
  letI := Fintype.ofFinite S
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ConjAct G) M
  have hcS : Nat.card S = Nat.card M := Nat.card_congr e
  have h' : Nat.card (MulAction.orbit (ConjAct G) M) * Nat.card S =
      Nat.card (ConjAct G) := by
    simpa only [← Nat.card_eq_fintype_card] using h
  rw [hcS] at h'
  exact h'.trans (Nat.card_congr (ConjAct.ofConjAct : ConjAct G ≃* G).toEquiv)

private theorem simple_all_proper_abelian [IsSimpleGroup G]
    (hn : ¬IsMulCommutative G)
    (hab : ∀ M : Subgroup G, M ≠ ⊤ → ∀ x y : M, x * y = y * x) : False := by
  classical
  have center : Subgroup.center G = ⊥ :=
    Atlas.GroupTheory.center_eq_bot_of_simple_nonabelian G hn
  have cp (x : G) (hx : x ≠ 1) : Subgroup.centralizer {x} ≠ ⊤ := by
    intro he
    have hm : x ∈ Subgroup.center G :=
      (Subgroup.centralizer_eq_top_iff_subset.mp he) (Set.mem_singleton x)
    rw [center] at hm
    exact hx hm
  have cm (M : Subgroup G) (hm : IsCoatom M) (x : G) (hx : x ∈ M) :
      M ≤ Subgroup.centralizer {x} := by
    intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have he : z = x := Set.mem_singleton_iff.mp hz
    subst z
    exact congrArg Subtype.val (hab M hm.ne_top ⟨x, hx⟩ ⟨g, hg⟩)
  have nb (M : Subgroup G) (hm : IsCoatom M) : M ≠ ⊥ := by
    intro he
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    have hxb : Subgroup.centralizer {x} ≠ ⊥ := by
      intro hz
      have ht : x ∈ Subgroup.centralizer {x} := by
        simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff]
        intro z hz; subst z; rfl
      rw [hz] at ht
      exact hx ht
    have hlt : M < Subgroup.centralizer {x} := he ▸ bot_lt_iff_ne_bot.mpr hxb
    exact cp x hx (hm.2 _ hlt)
  have norm (M : Subgroup G) (hm : IsCoatom M) : Subgroup.normalizer (M : Set G) = M := by
    rcases hm.le_iff.mp M.le_normalizer with he | he
    · haveI : M.Normal := Subgroup.normalizer_eq_top_iff.mp he
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hb | ht
      · exact (nb M hm hb).elim
      · exact (hm.ne_top ht).elim
    · exact he
  have disj (M N : Subgroup G) (hm : IsCoatom M) (hn' : IsCoatom N) (hne : M ≠ N) :
      Disjoint M N := by
    apply Subgroup.disjoint_def.mpr
    intro x hxM hxN
    by_contra hx
    have heM : Subgroup.centralizer {x} = M :=
      (hm.le_iff_eq (cp x hx)).mp (cm M hm x hxM)
    have heN : Subgroup.centralizer {x} = N :=
      (hn'.le_iff_eq (cp x hx)).mp (cm N hn' x hxN)
    exact hne (heM.symm.trans heN)
  have cover (x : G) (hx : x ≠ 1) : ∃ M : Subgroup G, IsCoatom M ∧ x ∈ M := by
    obtain ⟨M, hm, hle⟩ :=
      (eq_top_or_exists_le_coatom (Subgroup.centralizer {x})).resolve_left (cp x hx)
    refine ⟨M, hm, hle ?_⟩
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff]
    intro z hz; subst z; rfl
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  obtain ⟨M, hm, _⟩ := cover x hx
  let O (N : Subgroup G) := MulAction.orbit (ConjAct G) N
  letI (N : Subgroup G) : Fintype (O N) := Fintype.ofFinite _
  have half (N : Subgroup G) (hN : IsCoatom N) :
      Nat.card G ≤ 2 * (Nat.card (O N) * (Nat.card N - 1)) := by
    have hmass := orbit_mass N (norm N hN)
    have hc : 2 ≤ Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr (nb N hN)
    have hp : Nat.card N - 1 + 1 = Nat.card N := Nat.sub_add_cancel (by omega)
    have hh : Nat.card N ≤ 2 * (Nat.card N - 1) := by omega
    have hh' := Nat.mul_le_mul_left (Nat.card (O N)) hh
    dsimp [O] at *
    nlinarith
  have all_orbit : ∀ N : Subgroup G, IsCoatom N → N ∈ O M := by
    intro N hN
    by_contra ho
    let J : O M ⊕ O N → Subgroup G := Sum.elim Subtype.val Subtype.val
    have dj : Pairwise (fun i j => Disjoint (J i) (J j)) := by
      intro i j hij
      have neq : J i ≠ J j := by
        intro he
        cases i with
        | inl i =>
          cases j with
          | inl j => exact hij (congrArg Sum.inl (Subtype.ext he))
          | inr j =>
            apply ho
            exact MulAction.mem_orbit_trans
              (MulAction.mem_orbit_symm.mp j.2) (by
                have hij : i.1 = j.1 := he
                rw [← hij]
                exact i.2)
        | inr i =>
          cases j with
          | inl j =>
            apply ho
            exact MulAction.mem_orbit_trans
              (MulAction.mem_orbit_symm.mp i.2) (by
                have hij : j.1 = i.1 := he.symm
                rw [← hij]
                exact j.2)
          | inr j => exact hij (congrArg Sum.inr (Subtype.ext he))
      have hi : IsCoatom (J i) := by
        cases i with
        | inl i => exact orbit_coatom M hm i
        | inr i => exact orbit_coatom N hN i
      have hj : IsCoatom (J j) := by
        cases j with
        | inl j => exact orbit_coatom M hm j
        | inr j => exact orbit_coatom N hN j
      exact disj _ _ hi hj neq
    have hb := nonidentity_bound J dj
    simp only [Fintype.sum_sum_type, J, Sum.elim_inl, Sum.elim_inr,
      orbit_card, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card] at hb
    have hpos : 0 < Nat.card G := Nat.card_pos
    have hM := half M hm
    have hN' := half N hN
    omega
  let f : (Σ N : O M, {g : N.1 // g ≠ 1}) → {g : G // g ≠ 1} :=
    fun z => ⟨z.2.1.1, fun h => z.2.2 (Subtype.ext h)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      apply Atlas.GroupTheory.subgroup_nonidentity_sigma_injective
        (fun N : O M => N.1) (fun A B hne => disj _ _
          (orbit_coatom M hm A) (orbit_coatom M hm B)
          (fun he => hne (Subtype.ext he)))
      exact congrArg Subtype.val he
    · intro g
      obtain ⟨N, hN, hg⟩ := cover g.1 g.2
      exact ⟨⟨⟨N, all_orbit N hN⟩, ⟨⟨g.1, hg⟩, fun he =>
        g.2 (congrArg Subtype.val he)⟩⟩, Subtype.ext rfl⟩
  have count := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_sigma] at count
  simp_rw [Atlas.GroupTheory.card_subgroup_nonidentity, orbit_card] at count
  have hg : Nat.card {g : G // g ≠ 1} = Nat.card G - 1 := by
    letI := Fintype.ofFinite G
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, hg] at count
  have hmprod := orbit_mass M (norm M hm)
  have hmpos : 1 ≤ Nat.card M := Nat.card_pos
  have hpred := Nat.sub_add_cancel hmpos
  have hp : Nat.card (O M) * (Nat.card M - 1) + Nat.card (O M) = Nat.card G := by
    dsimp [O] at *
    nlinarith
  have ho : Nat.card (O M) = 1 := by
    have hG : 0 < Nat.card G := Nat.card_pos
    omega
  have he : Nat.card M = Nat.card G := by
    dsimp [O] at ho
    simpa [ho] using hmprod
  have hlt : Nat.card M < Nat.card G := by
    simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt hm.lt_top
  omega

private theorem induction (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n →
      (∀ H : Subgroup G, NLT H) → ∀ x y : G, x * y = y * x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ hcard hAll
    classical
    by_cases ht : Subsingleton G
    · exact fun _ _ => ht.elim _ _
    letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp ht
    by_cases hn : IsMulCommutative G
    · letI := hn
      exact fun x y => mul_comm' x y
    have proper (M : Subgroup G) (hm : M ≠ ⊤) : ∀ x y : M, x * y = y * x := by
      have hc : Nat.card M < n := by
        rw [← hcard]
        simpa only [Subgroup.card_top] using Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hm)
      exact ih (Nat.card M) hc M rfl (SolvableNormalTransversal.all_restrict hAll M)
    by_cases hs : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤
    · obtain ⟨N, hN, hb, htop⟩ := hs
      letI : N.Normal := hN
      letI : IsMulCommutative N := ⟨⟨proper N htop⟩⟩
      have hq : Nat.card (G ⧸ N) < n := by
        have hn2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hb
        have hpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
        have he := Subgroup.card_eq_card_quotient_mul_card_subgroup N
        rw [hcard] at he
        nlinarith
      have qcomm := ih (Nat.card (G ⧸ N)) hq (G ⧸ N) rfl
        (SolvableNormalTransversal.all_map (QuotientGroup.mk' N)
          (QuotientGroup.mk'_surjective N) hAll)
      letI : IsMulCommutative (G ⧸ N) := ⟨⟨qcomm⟩⟩
      letI : Group.IsSolvable G := Group.isSolvable_of_subgroup_quotient N
      exact SolvableNormalTransversal.result hAll
    · letI : IsSimpleGroup G :=
        { eq_bot_or_eq_top_of_normal := fun N hN => by
            by_cases hb : N = ⊥
            · exact Or.inl hb
            · right
              by_contra ht
              exact hs ⟨N, hN, hb, ht⟩ }
      exact (simple_all_proper_abelian hn proper).elim

/-- Arbitrary finite groups, without a solvability or order hypothesis. -/
theorem result (h : ∀ H : Subgroup G, NLT H) : ∀ x y : G, x * y = y * x :=
  induction (Nat.card G) G rfl h

/-- The full three-way equivalence. The connection set and code type may
vary with the subgroup; the abelian direction supplies perfect codes. -/
theorem equivalence :
    (∀ x y : G, x * y = y * x) ↔
      (∀ H : Subgroup G, ∃ Y : Set G, ∃ hn : NormalSubset Y,
        PerfectCodeTransversal.IsPerfectCode (sumGraph Y hn) H ∨
          IsTotalPerfectCode (sumGraph Y hn) H) := by
  constructor
  · intro hc
    letI : IsMulCommutative G := ⟨⟨hc⟩⟩
    intro H
    obtain ⟨Y, hn, hp⟩ := PerfectCodeTransversal.abelian_exists H
    exact ⟨Y, hn, Or.inl hp⟩
  · intro hc
    apply result
    intro H
    obtain ⟨Y, hn, hp | ht⟩ := hc H
    · obtain ⟨T, hnT, _, hT⟩ :=
        (PerfectCodeTransversal.exists_iff H).mp ⟨Y, hn, hp⟩
      exact ⟨T, hnT, hT⟩
    · exact NormalTransversal.result H Y hn ht

#print axioms result
#print axioms equivalence

end D5.S3.Combinatorics.CayleySumCodes.FiniteNormalTransversal

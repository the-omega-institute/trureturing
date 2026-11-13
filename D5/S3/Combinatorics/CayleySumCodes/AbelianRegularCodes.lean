/- GID: D5/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/AbelianRegularCodes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Square-free transversal constructions and the full abelian regular-code criteria. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal
import D5.S3.Combinatorics.CayleySumCodes.NormalSubgroupCriterion
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace


set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.AbelianRegularCodes

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
open D5.S3.Combinatorics.CayleySumCodes.PerfectCodeTransversal

section GeneralGroup

variable {G : Type*} [Group G]

private noncomputable def neighborEquiv (Y : Set G) (hn : NormalSubset Y) (g : G) :
    (sumGraph Y hn).neighborSet g ≃ ↥(Y \ {g * g}) where
  toFun h := ⟨g * h.1, h.2.2, by
    intro he
    have eqh : h.1 = g := mul_left_cancel (Set.mem_singleton_iff.mp he)
    exact h.2.1 eqh.symm⟩
  invFun y := ⟨g⁻¹ * y.1, by
    refine ⟨?_, ?_⟩
    · intro he
      apply y.2.2
      apply Set.mem_singleton_iff.mpr
      have hh := congrArg (fun z : G => g * z) he
      simpa using hh.symm
    · simpa using y.2.1⟩
  left_inv h := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp

/-- Every vertex has |Y| neighbors except that its own square, when present
in Y, removes exactly one open neighbor. The graph is the actual loopless
sum graph and the bijection is h maps to g*h. -/
theorem degree_card [Finite G] (Y : Set G) (hn : NormalSubset Y) (g : G) :
    Nat.card ((sumGraph Y hn).neighborSet g) =
      Nat.card Y - if g * g ∈ Y then 1 else 0 := by
  classical
  rw [Nat.card_congr (neighborEquiv Y hn g)]
  change (Y \ {g * g}).ncard = Y.ncard - if g * g ∈ Y then 1 else 0
  by_cases hm : g * g ∈ Y
  · rw [if_pos hm]
    have he := Set.ncard_sdiff_singleton_add_one hm
    omega
  · rw [if_neg hm, Nat.sub_zero]
    congr 1
    exact Set.sdiff_singleton_eq_self hm

/-- Full finite-group regularity dichotomy. Equality of the actual neighbor
cardinality at every vertex with its value at 1 is precisely regularity:
the group is nonempty, and that common value is its regular degree. -/
theorem regularity_iff [Finite G] (Y : Set G) (hn : NormalSubset Y) :
    (∀ g : G, Nat.card ((sumGraph Y hn).neighborSet g) =
      Nat.card ((sumGraph Y hn).neighborSet 1)) ↔
    Y ∩ squares (⊤ : Subgroup G) = ∅ ∨ squares (⊤ : Subgroup G) ⊆ Y := by
  classical
  have positive (x : G) (hx : x ∈ Y) : 0 < Nat.card Y := by
    letI : Nonempty Y := ⟨⟨x, hx⟩⟩
    exact Nat.card_pos
  constructor
  · intro hreg
    by_cases h1 : (1 : G) ∈ Y
    · right
      rintro z ⟨g, _, rfl⟩
      by_contra hn
      have he := hreg g
      rw [degree_card, degree_card] at he
      simp only [one_mul, if_neg hn, if_pos h1, Nat.sub_zero] at he
      have hp := positive 1 h1
      omega
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hz, g, _, rfl⟩
      have he := hreg g
      rw [degree_card, degree_card] at he
      simp only [one_mul, if_pos hz, if_neg h1, Nat.sub_zero] at he
      have hp := positive (g * g) hz
      omega
  · rintro (hfree | hall) g
    · have hsq (x : G) : x * x ∉ Y := by
        intro hx
        have hm : x * x ∈ Y ∩ squares (⊤ : Subgroup G) := ⟨hx, x, by trivial, rfl⟩
        rw [hfree] at hm
        exact hm
      rw [degree_card, degree_card]
      simp only [ite_eq_right (hsq g), ite_eq_right (hsq 1)]
    · have hsq (x : G) : x * x ∈ Y := hall ⟨x, by trivial, rfl⟩
      rw [degree_card, degree_card]
      simp only [ite_eq_left (hsq g), ite_eq_left (hsq 1)]

end GeneralGroup

variable {G : Type*} [CommGroup G]

/-- The actual subgroup of ambient squares in an abelian group. -/
def squareSubgroup : Subgroup G := (powMonoidHom 2 : G →* G).range

/-- The subgroup carrier agrees with the elementwise square set, without a
finite-group or exponent-two assumption. -/
theorem squares_eq : squares (⊤ : Subgroup G) = (squareSubgroup (G := G) : Set G) := by
  ext x
  change (∃ h : G, h ∈ (⊤ : Subgroup G) ∧ h * h = x) ↔
    ∃ h : G, (powMonoidHom 2 : G →* G) h = x
  simp [pow_two]

private theorem normal (Y : Set G) : NormalSubset Y := by
  intro a x hx
  simpa [mul_comm a x, mul_assoc] using hx

/-- Replacing each chosen representative within its own left H-coset
preserves the complete transversal, including uniqueness. -/
private theorem modify (H : Subgroup G) (T : Set G)
    (ht : Subgroup.IsComplement T (H : Set G)) (f : G → G)
    (hf : ∀ t ∈ T, t⁻¹ * f t ∈ H) :
    Subgroup.IsComplement (f '' T) (H : Set G) := by
  have equiv_mem (t g : G) (hT : t ∈ T) :
      (f t)⁻¹ * g ∈ H ↔ t⁻¹ * g ∈ H := by
    have he : (f t)⁻¹ * g = (t⁻¹ * f t)⁻¹ * (t⁻¹ * g) := by group
    rw [he, H.mul_mem_cancel_left (H.inv_mem (hf t hT))]
  apply Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mpr
  intro g
  obtain ⟨t, hh, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht g
  refine ⟨⟨f t.1, t.1, t.2, rfl⟩, (equiv_mem t.1 g t.2).mpr hh, ?_⟩
  rintro z hz
  obtain ⟨u, huT, he⟩ := z.2
  have huH : u⁻¹ * g ∈ H := (equiv_mem u g huT).mp (he.symm ▸ hz)
  have eqt := congrArg Subtype.val (hu ⟨u, huT⟩ huH)
  apply Subtype.ext
  exact he.symm.trans (congrArg f eqt)

/-- A nonsquare of G in H permits a normalized transversal whose only
square is 1. This is a construction over every coset, not a finite sample. -/
theorem square_free_normalized (H : Subgroup G) (z : G) (hzH : z ∈ H)
    (hz : z ∉ squareSubgroup (G := G)) :
    ∃ T : Set G, (1 : G) ∈ T ∧ Subgroup.IsComplement T (H : Set G) ∧
      ∀ t ∈ T, t ≠ 1 → t ∉ squareSubgroup (G := G) := by
  classical
  obtain ⟨U, hU, h1⟩ := H.exists_isComplement_left 1
  let f : G → G := fun t => if t = 1 then 1 else
    if t ∈ squareSubgroup (G := G) then t * z else t
  have hf (t : G) (_ : t ∈ U) : t⁻¹ * f t ∈ H := by
    by_cases he : t = 1
    · simp [f, he]
    by_cases hs : t ∈ squareSubgroup (G := G)
    · simpa [f, he, hs] using hzH
    · simp [f, he, hs]
  refine ⟨f '' U, ⟨1, h1, by simp [f]⟩, modify H U hU f hf, ?_⟩
  rintro t ⟨u, hu, rfl⟩ hne
  by_cases he : u = 1
  · exact (hne (by simp [f, he])).elim
  by_cases hs : u ∈ squareSubgroup (G := G)
  · simp only [f, if_neg he, if_pos hs]
    intro hm
    exact hz ((squareSubgroup (G := G)).mul_mem_cancel_left hs |>.mp hm)
  · simpa [f, he, hs] using hs

private theorem regular_of_square_free [Finite G] (Y : Set G)
    (hfree : ∀ y ∈ Y, y ∉ squareSubgroup (G := G)) :
    ∀ g : G, Nat.card ((sumGraph Y (normal Y)).neighborSet g) =
      Nat.card ((sumGraph Y (normal Y)).neighborSet 1) := by
  apply (regularity_iff Y (normal Y)).mpr
  left
  rw [squares_eq (G := G)]
  exact Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hfree y hy.1 hy.2)

private theorem normalized_regular [Finite G] (H : Subgroup G) (T : Set G)
    (h1 : (1 : G) ∈ T) (ht : Subgroup.IsComplement T (H : Set G))
    (hfree : ∀ t ∈ T, t ≠ 1 → t ∉ squareSubgroup (G := G)) :
    ∃ Y : Set G, IsPerfectCode (sumGraph Y (normal Y)) H ∧
      ∀ g : G, Nat.card ((sumGraph Y (normal Y)).neighborSet g) =
        Nat.card ((sumGraph Y (normal Y)).neighborSet 1) := by
  refine ⟨T \ {1}, of_transversal H T (normal T) ht h1, ?_⟩
  exact regular_of_square_free _ (fun t ht => hfree t ht.1 ht.2)

/-- The complete regular perfect-code existence criterion, explicitly
including the trivial subgroup. The nontrivial all-square case is H=Sq(G).
The separate Sylow/Frattini description of Sq(G) is not assumed here. -/
theorem perfect_iff [Finite G] (H : Subgroup G) :
    (∃ Y : Set G, IsPerfectCode (sumGraph Y (normal Y)) H ∧
      ∀ g : G, Nat.card ((sumGraph Y (normal Y)).neighborSet g) =
        Nat.card ((sumGraph Y (normal Y)).neighborSet 1)) ↔
    H = ⊥ ∨ (∃ h : G, h ∈ H ∧ h ∉ squareSubgroup (G := G)) ∨
      H = squareSubgroup (G := G) := by
  classical
  constructor
  · rintro ⟨Y, hc, hr⟩
    by_cases hb : H = ⊥
    · exact Or.inl hb
    right
    by_cases hn : ∃ h : G, h ∈ H ∧ h ∉ squareSubgroup (G := G)
    · exact Or.inl hn
    right
    have hHS : H ≤ squareSubgroup (G := G) := by
      intro h hh
      by_contra hs
      exact hn ⟨h, hh, hs⟩
    obtain ⟨h', hne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb
    have hh : (h' : G) ∈ H := h'.2
    have hne : (h' : G) ≠ 1 := fun he => hne' (Subtype.ext he)
    let h : G := h'
    rcases (regularity_iff Y (normal Y)).mp hr with hfree | hfull
    · apply le_antisymm hHS
      intro x hx
      by_contra hxH
      obtain ⟨y, ⟨hyH, he⟩, _⟩ := hc x
      have edge := he.resolve_left (fun he => hxH (he.symm ▸ hyH))
      have hs : x * y ∈ squareSubgroup (G := G) :=
        (squareSubgroup (G := G)).mul_mem hx (hHS hyH)
      have hem : x * y ∈ Y ∩ squares (⊤ : Subgroup G) := ⟨edge.2, (squares_eq (G := G)).symm ▸ hs⟩
      rw [hfree] at hem
      exact hem
    · obtain ⟨v, _, hu⟩ := hc 1
      have e1 : (1 : G) = v := hu 1 ⟨H.one_mem, Or.inl rfl⟩
      have eh : h = v := hu h ⟨hh, Or.inr ⟨Ne.symm hne, by
        simpa using hfull ((squares_eq (G := G)).symm ▸ hHS hh)⟩⟩
      exact (hne (eh.trans e1.symm)).elim
  · rintro (hb | hn | hs)
    · subst H
      refine ⟨Set.univ, ?_, ?_⟩
      · intro g
        refine ⟨1, ⟨by simp, ?_⟩, ?_⟩
        · by_cases he : g = 1
          · exact Or.inl he
          · exact Or.inr ⟨he, Set.mem_univ _⟩
        · intro h hh
          simpa using hh.1
      · apply (regularity_iff Set.univ (normal Set.univ)).mpr
        exact Or.inr (Set.subset_univ _)
    · obtain ⟨z, hzH, hz⟩ := hn
      obtain ⟨T, h1, ht, hfree⟩ := square_free_normalized H z hzH hz
      exact normalized_regular H T h1 ht hfree
    · subst H
      obtain ⟨T, ht, h1⟩ := (squareSubgroup (G := G)).exists_isComplement_left 1
      exact normalized_regular _ T h1 ht (fun t ht' hne hs =>
        hne (PerfectCodeTransversal.transversal_inter _ T ht h1 t ht' hs))

private theorem internal_singleton (H : Subgroup G) (T : Set G)
    (ht : Subgroup.IsComplement T (H : Set G)) (z : G)
    (hzT : z ∈ T) (hzH : z ∈ H) : T ∩ (H : Set G) = {z} := by
  obtain ⟨s, hs, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht 1
  ext t
  constructor
  · intro h
    exact Set.mem_singleton_iff.mpr (congrArg Subtype.val
      ((hu ⟨t, h.1⟩ (by simpa using H.inv_mem h.2)).trans
        (hu ⟨z, hzT⟩ (by simpa using H.inv_mem hzH)).symm))
  · intro h
    exact Set.mem_singleton_iff.mp h |>.symm ▸ ⟨hzT, hzH⟩

private theorem total_square_free [Finite G] (H : Subgroup G) (z : G)
    (hzH : z ∈ H) (hz : z ∉ squareSubgroup (G := G)) :
    ∃ Y : Set G, IsTotalPerfectCode (sumGraph Y (normal Y)) H ∧
      ∀ g : G, Nat.card ((sumGraph Y (normal Y)).neighborSet g) =
        Nat.card ((sumGraph Y (normal Y)).neighborSet 1) := by
  classical
  obtain ⟨U, hU, h1⟩ := H.exists_isComplement_left 1
  let f : G → G := fun t => if t ∈ squareSubgroup (G := G) then t * z else t
  have hf (t : G) (_ : t ∈ U) : t⁻¹ * f t ∈ H := by
    by_cases hs : t ∈ squareSubgroup (G := G)
    · simpa [f, hs] using hzH
    · simp [f, hs]
  let Y := f '' U
  have ht : Subgroup.IsComplement Y (H : Set G) := modify H U hU f hf
  have hzY : z ∈ Y := ⟨1, h1, by simp [f]⟩
  have hfree : ∀ y ∈ Y, y ∉ squareSubgroup (G := G) := by
    rintro y ⟨u, hu, rfl⟩
    by_cases hs : u ∈ squareSubgroup (G := G)
    · simp only [f, if_pos hs]
      intro hm
      exact hz ((squareSubgroup (G := G)).mul_mem_cancel_left hs |>.mp hm)
    · simpa [f, hs] using hs
  refine ⟨Y, ?_, regular_of_square_free Y hfree⟩
  apply (TotalPerfectCriterion.result H Y (normal Y)).mpr
  refine ⟨fun g _ => NormalSubgroupCriterion.coset_card H Y ht g, Or.inl ⟨z, hzH, ?_, ?_⟩⟩
  · rintro ⟨h, hh, he⟩
    apply hz
    change z ∈ (squareSubgroup (G := G) : Set G)
    rw [← squares_eq (G := G)]
    exact ⟨h, by trivial, he⟩
  · exact internal_singleton H Y ht z hzY hzH

private theorem total_two_squares [Finite G] (H : Subgroup G)
    (hs : Nat.card (squareSubgroup (G := G)) = 2)
    (hSH : squareSubgroup (G := G) ≤ H) :
    ∃ Y : Set G, IsTotalPerfectCode (sumGraph Y (normal Y)) H ∧
      ∀ g : G, Nat.card ((sumGraph Y (normal Y)).neighborSet g) =
        Nat.card ((sumGraph Y (normal Y)).neighborSet 1) := by
  classical
  obtain ⟨T, ht, h1⟩ := H.exists_isComplement_left 1
  let S : Set G := squareSubgroup (G := G)
  let Y := (T \ {1}) ∪ S
  have he : Y ∩ (H : Set G) = S := by
    ext y
    constructor
    · rintro ⟨hy | hy, hh⟩
      · exact (hy.2 (PerfectCodeTransversal.transversal_inter H T ht h1 y hy.1 hh)).elim
      · exact hy
    · intro hy
      exact ⟨Or.inr hy, hSH hy⟩
  refine ⟨Y, ?_, (regularity_iff Y (normal Y)).mpr (Or.inr ?_)⟩
  · apply (TotalPerfectCriterion.result H Y (normal Y)).mpr
    refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
    · intro g hg
      have eqset : {y : G | y ∈ Y ∧ g⁻¹ * y ∈ H} =
          {y : G | y ∈ T ∧ g⁻¹ * y ∈ H} := by
        have notH (y : G) (hh : g⁻¹ * y ∈ H) : y ∉ H := by
          intro hy
          apply hg
          have eqg : g = y * (g⁻¹ * y)⁻¹ := by group
          rw [eqg]
          exact H.mul_mem hy (H.inv_mem hh)
        ext y
        constructor
        · rintro ⟨hy | hy, hh⟩
          · exact ⟨hy.1, hh⟩
          · exact (notH y hh (hSH hy)).elim
        · rintro ⟨hy, hh⟩
          exact ⟨Or.inl ⟨hy, fun he => notH y hh (he.symm ▸ H.one_mem)⟩, hh⟩
      change Nat.card ↥{y : G | y ∈ Y ∧ g⁻¹ * y ∈ H} = 1
      rw [eqset]
      exact NormalSubgroupCriterion.coset_card H T ht g
    · change Nat.card ↥(Y ∩ (H : Set G)) = 2
      rw [he]
      exact hs
    · rintro z ⟨h, hh, rfl⟩
      rw [he]
      change h * h ∈ (squareSubgroup (G := G) : Set G)
      rw [← squares_eq (G := G)]
      exact ⟨h, by trivial, rfl⟩
  · rw [squares_eq (G := G)]
    exact Set.subset_union_right

/-- The corrected universal regular total-code criterion for finite abelian
groups. It applies to every subgroup, hence in particular to the stated
even-order domain; it asserts no finite-enumeration reproduction. -/
theorem total_iff [Finite G] (H : Subgroup G) :
    (∃ Y : Set G, IsTotalPerfectCode (sumGraph Y (normal Y)) H ∧
      ∀ g : G, Nat.card ((sumGraph Y (normal Y)).neighborSet g) =
        Nat.card ((sumGraph Y (normal Y)).neighborSet 1)) ↔
    (∃ h : G, h ∈ H ∧ h ∉ squareSubgroup (G := G)) ∨
      (Nat.card (squareSubgroup (G := G)) = 2 ∧ squareSubgroup (G := G) ≤ H) := by
  classical
  constructor
  · rintro ⟨Y, hc, hr⟩
    by_cases hn : ∃ h : G, h ∈ H ∧ h ∉ squareSubgroup (G := G)
    · exact Or.inl hn
    right
    have hHS : H ≤ squareSubgroup (G := G) := by
      intro h hh
      by_contra hs
      exact hn ⟨h, hh, hs⟩
    rcases (regularity_iff Y (normal Y)).mp hr with hfree | hfull
    · obtain ⟨h, ⟨hh, he⟩, _⟩ := hc 1
      have hm : h ∈ Y ∩ squares (⊤ : Subgroup G) :=
        ⟨by simpa using he.2, (squares_eq (G := G)).symm ▸ hHS hh⟩
      rw [hfree] at hm
      exact hm.elim
    · have h1Y : (1 : G) ∈ Y := hfull ⟨1, by trivial, by simp⟩
      obtain ⟨_, ha | hb⟩ := (TotalPerfectCriterion.result H Y (normal Y)).mp hc
      · obtain ⟨z, hzH, hzs, he⟩ := ha
        have eqz : (1 : G) = z := Set.mem_singleton_iff.mp (he ▸ ⟨h1Y, H.one_mem⟩)
        exact (hzs ⟨1, H.one_mem, by simpa using eqz⟩).elim
      · have hHY : (H : Set G) ⊆ Y := fun h hh => hfull ((squares_eq (G := G)).symm ▸ hHS hh)
        have hi : Y ∩ (H : Set G) = H := Set.inter_eq_right.mpr hHY
        have cardH : Nat.card H = 2 := by
          have hbcard : Nat.card ↥(Y ∩ (H : Set G)) = 2 := hb.1
          rw [hi] at hbcard
          exact hbcard
        letI : Fintype H := Fintype.ofFinite H
        have nontr : Nontrivial H := Fintype.one_lt_card_iff_nontrivial.mp (by
          simpa only [← Nat.card_eq_fintype_card] using (show 1 < Nat.card H by omega))
        letI : Nontrivial H := nontr
        obtain ⟨h, hne⟩ := exists_ne (1 : H)
        have hSH : squareSubgroup (G := G) ≤ H := by
          intro x hx
          by_contra hxH
          obtain ⟨v, _, hu⟩ := hc x
          have adj (k : H) : (sumGraph Y (normal Y)).Adj x k := by
            refine ⟨fun he => hxH (he.symm ▸ k.2), ?_⟩
            apply hfull
            rw [squares_eq (G := G)]
            exact (squareSubgroup (G := G)).mul_mem hx (hHS k.2)
          have e1 : (1 : G) = v := hu 1 ⟨H.one_mem, adj 1⟩
          have eh : (h : G) = v := hu h ⟨h.2, adj h⟩
          exact hne (Subtype.ext (eh.trans e1.symm))
        have eqH : H = squareSubgroup (G := G) := le_antisymm hHS hSH
        exact ⟨eqH ▸ cardH, hSH⟩
  · rintro (⟨z, hzH, hz⟩ | ⟨hs, hSH⟩)
    · exact total_square_free H z hzH hz
    · exact total_two_squares H hs hSH

/-- An even finite abelian group has an actual nonsquare. Cauchy's theorem
provides a nonidentity element of the squaring kernel, so the finite squaring
map is not surjective. -/
theorem even_nonsquare [Finite G] (heven : 2 ∣ Nat.card G) :
    ∃ z : G, ¬ IsSquare z := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 heven
  have hne : x ≠ 1 := by intro he; simp [he] at hx
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hnot : ¬ Function.Injective (fun y : G => y ^ 2) := by
    intro hi
    exact hne (hi (by simpa using hx2))
  have hns : ¬ Function.Surjective (fun y : G => y ^ 2) := by
    intro hs
    exact hnot (Finite.injective_iff_surjective.mpr hs)
  obtain ⟨z, hz⟩ := not_forall.mp hns
  refine ⟨z, ?_⟩
  rintro ⟨w, hw⟩
  exact hz ⟨w, by simpa only [pow_two] using hw.symm⟩

/-- Every even-order subgroup of every finite abelian group admits a total
perfect sum-graph witness. The nonsquare is in H, with no claim that it is a
nonsquare of the ambient G or that the constructed graph is regular. -/
theorem even_total_exists [Finite G] (H : Subgroup G) (heven : 2 ∣ Nat.card H) :
    ∃ (Y : Set G) (hn : NormalSubset Y), IsTotalPerfectCode (sumGraph Y hn) H := by
  obtain ⟨z, hz⟩ := even_nonsquare (G := H) heven
  have hzs : (z : G) ∉ squares H := by
    rintro ⟨h, hh, he⟩
    apply hz
    exact ⟨⟨h, hh⟩, Subtype.ext he.symm⟩
  apply (NormalSubgroupCriterion.result H).mpr
  refine ⟨abelian_exists H, Or.inl ⟨z, ?_, z.2, hzs⟩⟩
  exact Subgroup.mem_center_iff.mpr (fun a => mul_comm a z)

#print axioms even_nonsquare
#print axioms even_total_exists

#print axioms total_iff

#print axioms squares_eq
#print axioms square_free_normalized
#print axioms perfect_iff

/- The Frattini and vector-complement proof below adapts
Qiuzhen-CFSG/CFSG at immutable revision
0c6635528a02dd46f2e93e2ade0c4ac647ad1eb7,
Theory/Frattini/PGroup.lean and Theory/ElementaryAbelian/VectorSpace.lean.
Apache-2.0; original license retained in
  docs/reports/licenses/cfsg-frattini-kernel-LICENSE.txt.
Only the used commutative exponent-two specialization is ported; current
Mathlib supplies complement, maximal-index, quotient and Schur-Zassenhaus facts.
Replace this scoped port by direct Mathlib import when that pin supplies the
same Frattini statement. The final Hall decomposition is the C7 consumer. -/

private theorem exponent_two_frattini {R : Type*} [CommGroup R] [Finite R]
    (hpow : ∀ x : R, x ^ 2 = 1) : frattini R = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  · let B : Subgroup R := Subgroup.zpowers x
    have hB_card : Nat.card B = 2 :=
      (Nat.card_zpowers x).trans (by
        rcases (Nat.dvd_prime Nat.prime_two).1
          (orderOf_dvd_of_pow_eq_one (hpow x)) with h1 | hp
        · exact False.elim (hx1 (orderOf_eq_one_iff.mp h1))
        · exact hp)
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Module (ZMod 2) (Additive R) :=
      AddCommGroup.zmodModule (fun x => toMul_eq_one.mp (hpow x))
    let φ : AddSubgroup (Additive R) ≃o Submodule (ZMod 2) (Additive R) :=
      AddSubgroup.toZModSubmodule (n := 2)
    let ψ : AddSubgroup (Additive R) ≃o Subgroup R := AddSubgroup.toSubgroup'
    let S : AddSubgroup (Additive R) := Subgroup.toAddSubgroup B
    obtain ⟨C', hC'⟩ := Submodule.exists_isCompl (K := ZMod 2) (φ S)
    let T := φ.symm C'
    let C : Subgroup R := ψ T
    have hcompl_add : IsCompl S T := (φ.isCompl_iff).mpr hC'
    have hcompl : IsCompl B C :=
      IsCompl.of_orderEmbedding (RelIso.toRelEmbedding Subgroup.toAddSubgroup) hcompl_add
    have hx_not_C : x ∉ C := by
      intro hxC
      exact hx1 (by
        have hx_bot : x ∈ (⊥ : Subgroup R) := by
          rw [← hcompl.inf_eq_bot]
          exact ⟨(Subgroup.mem_zpowers x : x ∈ B), hxC⟩
        simpa using hx_bot)
    have hC_coatom : IsCoatom C := by
      refine ⟨?_, ?_⟩
      · intro hCtop
        exact hx_not_C (by simp [hCtop])
      · intro D hCD
        rcases SetLike.exists_of_lt hCD with ⟨d, hdD, hdnotC⟩
        rcases (Subgroup.mem_sup (s := B) (t := C) (x := d)).1 (by
          simp [(by simpa [sup_comm] using hcompl.sup_eq_top : B ⊔ C = ⊤)]) with
          ⟨b, hbB, c, hcC, hbc_eq⟩
        have hbD : b ∈ D := by
          simpa [mul_assoc, ← hbc_eq]
            using (D.mul_mem hdD (D.inv_mem ((le_of_lt hCD) hcC)))
        have hb_ne_one : b ≠ 1 := by
          intro hb1
          exact hdnotC (by simpa [← hbc_eq, hb1] using hcC)
        let E : Subgroup B := (B ⊓ D).subgroupOf B
        have hbE : (⟨b, hbB⟩ : B) ∈ E := by
          change b ∈ B ⊓ D
          exact ⟨hbB, hbD⟩
        have hE_ne_bot : E ≠ ⊥ := by
          intro hEbot
          have hbE_bot : (⟨b, hbB⟩ : B) ∈ (⊥ : Subgroup B) := by simpa [hEbot] using hbE
          have hb_eq_one : (⟨b, hbB⟩ : B) = 1 := by simpa using hbE_bot
          exact hb_ne_one (Subtype.ext_iff.mp hb_eq_one)
        have : Fact (Nat.card B).Prime := ⟨by simpa [hB_card] using Nat.prime_two⟩
        have hB_le_D : B ≤ D :=
          fun y hy => ((Subgroup.subgroupOf_eq_top).1
            ((Subgroup.eq_bot_or_eq_top_of_prime_card (G := B) E).resolve_left hE_ne_bot) hy).2
        exact top_le_iff.mp
          (by
            rw [← hcompl.sup_eq_top]
            exact sup_le hB_le_D (le_of_lt hCD))
    exact False.elim (hx_not_C ((frattini_le_coatom hC_coatom) hx))

private theorem square_frattini {R : Type*} [CommGroup R] [Finite R]
    (hR : IsPGroup 2 R) : squareSubgroup (G := R) = frattini R := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    unfold frattini Order.radical
    simp only [Subgroup.mem_iInf]
    intro M hM
    have hidx : M.index = 2 := hR.isCoatom_iff_index_eq_prime.mp hM
    change y ^ 2 ∈ M
    apply (QuotientGroup.eq_one_iff (N := M) (x := y ^ 2)).mp
    have hh := pow_card_eq_one' (x := (QuotientGroup.mk' M y : R ⧸ M))
    rw [← Subgroup.index_eq_card, hidx] at hh
    simpa only [QuotientGroup.mk'_apply, QuotientGroup.mk_pow] using hh
  · let S := squareSubgroup (G := R)
    have hpow : ∀ x : R ⧸ S, x ^ 2 = 1 := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H x =>
        exact (QuotientGroup.eq_one_iff (N := S) (x := x ^ 2)).mpr ⟨x, rfl⟩
    have hphi := exponent_two_frattini hpow
    have hle := frattini_le_comap_frattini_of_surjective
      (φ := QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S)
    rw [hphi] at hle
    intro x hx
    have hx' := hle hx
    exact (QuotientGroup.eq_one_iff (N := S) (x := x)).mp (by simpa using hx')

/-- Every actual Sylow-2 subgroup has an actual odd Hall complement, and
its Frattini subgroup times that complement is exactly the ambient square subgroup. -/
theorem square_frattini_hall {R : Type*} [CommGroup R] [Finite R] (Q : Sylow 2 R) :
    ∃ K : Subgroup R, Subgroup.IsComplement' (Q : Subgroup R) K ∧
      Odd (Nat.card K) ∧
      squareSubgroup (G := R) = (frattini Q).map (Q : Subgroup R).subtype ⊔ K := by
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime Q.card_coprime_index
  have hcard : Nat.card K = Q.index := hK.symm.index_eq_card.symm
  have hodd : Odd (Nat.card K) := by
    rw [hcard, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact Q.not_dvd_index
  refine ⟨K, hK, hodd, ?_⟩
  rw [← square_frattini Q.isPGroup']
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    obtain ⟨q, hq, k, hk, rfl⟩ := Subgroup.mem_sup.mp
      (show y ∈ (Q : Subgroup R) ⊔ K by rw [hK.sup_eq_top]; trivial)
    change (q*k)^2 ∈ _
    rw [mul_pow]
    apply Subgroup.mul_mem_sup
    · exact ⟨(⟨q, hq⟩ : Q)^2, ⟨⟨q, hq⟩, rfl⟩, rfl⟩
    · exact K.pow_mem hk 2
  · apply sup_le
    · rintro x ⟨q, ⟨u, rfl⟩, rfl⟩
      exact ⟨(u : R), rfl⟩
    · intro k hk
      have hc : (Nat.card K).Coprime 2 := Nat.coprime_two_right.mpr hodd
      obtain ⟨u, hu⟩ := (powCoprime hc).surjective (⟨k, hk⟩ : K)
      exact ⟨(u : R), congrArg Subtype.val hu⟩

#print axioms square_frattini_hall

end D5.S3.Combinatorics.CayleySumCodes.AbelianRegularCodes

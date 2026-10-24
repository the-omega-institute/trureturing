/- GID: D5/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/LemosMouraRibasSilvaConsecutiveDavenport
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The consecutive Davenport constant of every finite group equals its order. -/

/-
HasConsecutiveProductOne, C, claim: source definitions; escape_witness: none.
interval_prod: proof_shape: bind-only; consumer: free_of_prefix_injective.
upper_bound: proof_shape: bind-only; consumer: result.
free_of_prefix_injective: proof_shape: bind-only; consumer: avoiding_word.
quotient_word_prefix: proof_shape: bind-only; consumer: avoiding_word.
avoiding_word: proof_shape: bind-only; consumer: result.
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#19765; Proved).
Direct frozen dependencies:
  upper_bound, result (same-delivery helpers inlined):
  D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterBlockConstruction.actual_finite_identity_interval
  declaration statement_id: sha256:86e6cbf7d61cd6efff299324e70a8d056dfe49ec95296aef424acba0c3cbe85b.
  HasConsecutiveProductOne, C, claim, interval_prod, free_of_prefix_injective,
  quotient_word_prefix, avoiding_word: none.
All private helpers have escape_witness: none.
The claim retains the source's unweighted contiguous-block definitions.
The prefix products of the quotient word are the normalized enumeration e(0)⁻¹ * e(i).
Utility is none: arbitrary finite-group existence and list identities; no finite
computation, certified instance, bounded enumeration, checker or numeric reduction.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19869.
-/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.PartIIOuterBlockConstruction

set_option autoImplicit false

namespace D5.S3.FiniteGroups.LemosMouraRibasSilvaConsecutiveDavenport

/-- `S` has a consecutive product-one subsequence: a nonempty ordered subsequence `T = gᵢ · … · gⱼ` of `S`
(`1 ≤ i ≤ j ≤ |S|`) whose ordered product `π*(T) = gᵢ ⋯ gⱼ` is `1`. -/
def HasConsecutiveProductOne {G : Type*} [Monoid G] (S : List G) : Prop :=
  ∃ T : List G, T ≠ [] ∧ T <:+: S ∧ T.prod = 1

/-- `C(G)`: the smallest positive integer `ℓ` such that every sequence over `G` of length at least `ℓ` has a
consecutive product-one subsequence. -/
noncomputable def C (G : Type*) [Monoid G] : ℕ :=
  sInf {ℓ : ℕ | 0 < ℓ ∧ ∀ S : List G, ℓ ≤ S.length → HasConsecutiveProductOne S}

/-- Conjecture 3.4: for every finite group `G`, `C(G) = |G|`. -/
def claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C G = Nat.card G

end D5.S3.FiniteGroups.LemosMouraRibasSilvaConsecutiveDavenport

namespace D5.S3.FiniteGroups.LemosMouraRibasSilvaConsecutiveDavenport

private theorem interval_prod {G : Type*} [Group G] (S : List G)
    {a b : ℕ} (hab : a ≤ b) :
    ((S.take b).drop a).prod = (S.take a).prod⁻¹ * (S.take b).prod := by
  have h := List.prod_take_mul_prod_drop (S.take b) a
  rw [List.take_take, Nat.min_eq_left hab] at h
  rw [← h, inv_mul_cancel_left]

private theorem upper_bound {G : Type*} [Group G] [Finite G]
    (S : List G) (hlen : Nat.card G ≤ S.length) : HasConsecutiveProductOne S := by
  classical
  let := Fintype.ofFinite G
  obtain ⟨a, b, hab, hb, hp⟩ :=
    NikolovSegal.PartIIOuterBlockConstruction.actual_finite_identity_interval S
      (by simpa only [← Nat.card_eq_fintype_card] using hlen)
  refine ⟨(S.drop a).take (b - a), ?_, ?_, hp⟩
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_take, List.length_drop, List.length_nil] at hl
    omega
  · exact (List.take_prefix (b - a) (S.drop a)).isInfix.trans
      (List.drop_suffix a S).isInfix

private theorem free_of_prefix_injective {G : Type*} [Group G] (S : List G)
    (hinj : Function.Injective (fun i : Fin (S.length + 1) => (S.take i.val).prod)) :
    ¬ HasConsecutiveProductOne S := by
  rintro ⟨T, hT, ⟨A, B, rfl⟩, hp⟩
  have hpos : 0 < T.length := List.length_pos_iff.mpr hT
  let a : Fin ((A ++ T ++ B).length + 1) := ⟨A.length, by simp only [List.length_append]; omega⟩
  let b : Fin ((A ++ T ++ B).length + 1) := ⟨A.length + T.length, by simp only [List.length_append]; omega⟩
  have heq : ((A ++ T ++ B).take a.val).prod = ((A ++ T ++ B).take b.val).prod := by
    apply inv_mul_eq_one.mp
    change ((A ++ T ++ B).take A.length).prod⁻¹ *
      ((A ++ T ++ B).take (A.length + T.length)).prod = 1
    rw [← interval_prod (A ++ T ++ B) (show A.length ≤ A.length + T.length by omega)]
    rw [← List.length_append, List.take_left, List.drop_left]
    exact hp
  have h := congrArg Fin.val (hinj heq)
  change A.length = A.length + T.length at h
  omega

private theorem quotient_word_prefix {G : Type*} [Group G]
    (f : ℕ → G) (n t : ℕ) (ht : t ≤ n) :
    (((List.range n).map (fun k => (f k)⁻¹ * f (k + 1))).take t).prod =
      (f 0)⁻¹ * f t := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left ht]
  simpa only [div_eq_mul_inv, inv_inv] using
    (List.prod_range_div' t (fun k => (f k)⁻¹))

private theorem avoiding_word (G : Type*) [Group G] [Finite G] :
    ∃ S : List G, S.length = Nat.card G - 1 ∧ ¬ HasConsecutiveProductOne S := by
  classical
  let n := Nat.card G - 1
  have hn : n + 1 = Nat.card G :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt Nat.card_pos)
  let e : Fin (n + 1) ≃ G := (finCongr hn).trans (Finite.equivFin G).symm
  let f : ℕ → G := fun k => e ⟨min k n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  let S := (List.range n).map (fun k => (f k)⁻¹ * f (k + 1))
  refine ⟨S, by simp [S, n], free_of_prefix_injective S ?_⟩
  intro i j h
  have hi : i.val ≤ n := by
    have := i.isLt
    simpa only [S, List.length_map, List.length_range] using Nat.le_of_lt_succ this
  have hj : j.val ≤ n := by
    have := j.isLt
    simpa only [S, List.length_map, List.length_range] using Nat.le_of_lt_succ this
  change (S.take i.val).prod = (S.take j.val).prod at h
  rw [quotient_word_prefix f n i.val hi, quotient_word_prefix f n j.val hj] at h
  have hij := e.injective (mul_left_cancel h)
  apply Fin.ext
  simpa only [f, Fin.mk.injEq, Nat.min_eq_left hi, Nat.min_eq_left hj] using hij

theorem result : claim := by
  intro G _ _
  have hmem : Nat.card G ∈ {ℓ : ℕ | 0 < ℓ ∧ ∀ S : List G,
      ℓ ≤ S.length → HasConsecutiveProductOne S} :=
    ⟨Nat.card_pos, fun S h => upper_bound S h⟩
  apply Nat.le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨Nat.card G, hmem⟩
  intro ℓ hℓ
  by_contra hnot
  have hlt : ℓ < Nat.card G := Nat.lt_of_not_ge hnot
  obtain ⟨S, hlen, hfree⟩ := avoiding_word G
  exact hfree (hℓ.2 S (by omega))


end D5.S3.FiniteGroups.LemosMouraRibasSilvaConsecutiveDavenport

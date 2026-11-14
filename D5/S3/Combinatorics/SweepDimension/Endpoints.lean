/- GID: D5/S3/Combinatorics/SweepDimension/Endpoints
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SweepDimension/Endpoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Antichain]
   utility: none
   digest: Sweep dimension equals the three-chain-free maximum and has exact lower and upper width endpoints. -/

import D5.S3.Combinatorics.SweepDimension.Upper

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SweepDimension.Endpoints

open Basic Upper FiniteDilworth

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

private theorem free_of_antichain {S : Finset α}
    (hS : IsAntichain (· ≤ ·) (S : Set α)) : ThreeChainFree S := by
  intro a b c ha hb _ hab
  exact hS ha hb hab.1.ne hab.1.le

private theorem free_union {A B : Finset α}
    (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hB : IsAntichain (· ≤ ·) (B : Set α)) : ThreeChainFree (A ∪ B) := by
  intro a b c ha hb hc hlt
  have hab := hlt.1
  have hbc := hlt.2
  have hac := hab.trans hbc
  rcases Finset.mem_union.mp ha with ha | ha <;>
    rcases Finset.mem_union.mp hb with hb | hb <;>
    rcases Finset.mem_union.mp hc with hc | hc
  all_goals first
    | exact hA ha hb hab.ne hab.le
    | exact hA hb hc hbc.ne hbc.le
    | exact hA ha hc hac.ne hac.le
    | exact hB ha hb hab.ne hab.le
    | exact hB hb hc hbc.ne hbc.le
    | exact hB ha hc hac.ne hac.le

private theorem free_split {S : Finset α} (hS : ThreeChainFree S) :
    ∃ A B : Finset α, IsAntichain (· ≤ ·) (A : Set α) ∧
      IsAntichain (· ≤ ·) (B : Set α) ∧ Disjoint A B ∧ A ∪ B = S := by
  classical
  let A := S.filter fun a => ∀ b ∈ S, ¬b < a
  let B := S \ A
  have hAsub : A ⊆ S := Finset.filter_subset _ _
  refine ⟨A, B, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hne hab
    exact (Finset.mem_filter.mp hb).2 a (hAsub ha) (lt_of_le_of_ne hab hne)
  · intro a ha b hb hne hab
    have haS : a ∈ S := (Finset.mem_sdiff.mp ha).1
    have hbS : b ∈ S := (Finset.mem_sdiff.mp hb).1
    have hnmin : ¬∀ c ∈ S, ¬c < a := by
      intro h
      exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_filter.mpr ⟨haS, h⟩)
    push_neg at hnmin
    obtain ⟨c, hc, hca⟩ := hnmin
    exact hS hc haS hbS ⟨hca, lt_of_le_of_ne hab hne⟩
  · exact Finset.disjoint_sdiff_right
  · exact Finset.union_sdiff_of_subset hAsub

private theorem theta_le_twice_width :
    theta (α := α) ≤ 2 * maxAntichainSize α := by
  obtain ⟨S, hS, hcard⟩ := theta_witness (α := α)
  obtain ⟨A, B, hA, hB, hdis, hunion⟩ := free_split hS
  have hAc := card_le_maxAntichainSize hA
  have hBc := card_le_maxAntichainSize hB
  have hsum : A.card + B.card = theta (α := α) := by
    rw [← Finset.card_union_of_disjoint hdis, hunion, hcard]
  omega

private theorem width_le_theta : maxAntichainSize α ≤ theta (α := α) := by
  obtain ⟨A, hA, hc⟩ := exists_isAntichain_card_eq_maxAntichainSize (α := α)
  have := card_le_theta (free_of_antichain hA)
  omega

private theorem theta_upper_endpoint :
    theta (α := α) = 2 * maxAntichainSize α ↔
      ∃ A B : Finset α, IsAntichain (· ≤ ·) (A : Set α) ∧
        IsAntichain (· ≤ ·) (B : Set α) ∧ Disjoint A B ∧
        A.card = maxAntichainSize α ∧ B.card = maxAntichainSize α := by
  constructor
  · intro heq
    obtain ⟨S, hS, hc⟩ := theta_witness (α := α)
    obtain ⟨A, B, hA, hB, hd, hu⟩ := free_split hS
    have hAc := card_le_maxAntichainSize hA
    have hBc := card_le_maxAntichainSize hB
    have hsum : A.card + B.card = theta (α := α) := by
      rw [← Finset.card_union_of_disjoint hd, hu, hc]
    exact ⟨A, B, hA, hB, hd, by omega, by omega⟩
  · rintro ⟨A, B, hA, hB, hd, hAc, hBc⟩
    have hle := card_le_theta (free_union hA hB)
    rw [Finset.card_union_of_disjoint hd, hAc, hBc] at hle
    have hupper := theta_le_twice_width (α := α)
    omega

private theorem two_le_theta (hn : 2 ≤ Fintype.card α) : 2 ≤ theta (α := α) := by
  classical
  have hnt : (Finset.univ : Finset α).Nontrivial :=
    Finset.one_lt_card_iff_nontrivial.mp (by simpa using hn)
  obtain ⟨a, _, b, _, hab⟩ := hnt
  have ha : IsAntichain (· ≤ ·) (({a} : Finset α) : Set α) := by simp
  have hb : IsAntichain (· ≤ ·) (({b} : Finset α) : Set α) := by simp
  have h := card_le_theta (free_union ha hb)
  simpa [hab] using h

private theorem chain_of_width_le_one (hw : maxAntichainSize α ≤ 1) :
    IsChain (· ≤ ·) (Set.univ : Set α) := by
  classical
  intro x _ y _ hne
  by_contra hn
  have hnxy : ¬x ≤ y := fun h => hn (Or.inl h)
  have hnyx : ¬y ≤ x := fun h => hn (Or.inr h)
  have hanti : IsAntichain (· ≤ ·) (({x, y} : Finset α) : Set α) := by
    intro a ha b hb hneab hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> aesop
  have h := card_le_maxAntichainSize hanti
  have htwo : ({x, y} : Finset α).card = 2 := by simp [hne]
  omega

private theorem width_le_one_of_chain
    (hchain : IsChain (· ≤ ·) (Set.univ : Set α)) : maxAntichainSize α ≤ 1 := by
  obtain ⟨A, hA, hc⟩ := exists_isAntichain_card_eq_maxAntichainSize (α := α)
  rw [← hc]
  apply Finset.card_le_one_iff.mpr
  intro a b ha hb
  by_contra hne
  rcases hchain.total (Set.mem_univ a) (Set.mem_univ b) with h | h
  · exact hA ha hb hne h
  · exact hA hb ha (Ne.symm hne) h

private theorem theta_lower_endpoint (hn : 2 ≤ Fintype.card α) :
    theta (α := α) = max 2 (maxAntichainSize α) ↔
      IsChain (· ≤ ·) (Set.univ : Set α) ∨
      IsAntichain (· ≤ ·) (Set.univ : Set α) := by
  classical
  constructor
  · intro heq
    by_cases hw : 2 ≤ maxAntichainSize α
    · right
      have heq' : theta (α := α) = maxAntichainSize α := by
        simpa [max_eq_right hw] using heq
      obtain ⟨A, hA, hc⟩ := exists_isAntichain_card_eq_maxAntichainSize (α := α)
      have hfull : A = Finset.univ := by
        by_contra hne
        have hx : ∃ x : α, x ∉ A := by
          by_contra h
          push_neg at h
          exact hne (Finset.eq_univ_iff_forall.mpr h)
        obtain ⟨x, hx⟩ := hx
        have hs : IsAntichain (· ≤ ·) (({x} : Finset α) : Set α) := by simp
        have hfree : ThreeChainFree (insert x A) := by
          simpa using free_union hs hA
        have hle := card_le_theta hfree
        rw [Finset.card_insert_of_notMem hx, hc, heq'] at hle
        omega
      simpa [hfull] using hA
    · left
      apply chain_of_width_le_one
      omega
  · rintro (hchain | hanti)
    · have hw := width_le_one_of_chain hchain
      have hlo := two_le_theta hn
      have hhi := theta_le_twice_width (α := α)
      have hm : max 2 (maxAntichainSize α) = 2 := max_eq_left (by omega)
      omega
    · have hwu : Fintype.card α ≤ maxAntichainSize α := by
        simpa using (card_le_maxAntichainSize (A := (Finset.univ : Finset α))
          (by simpa using hanti))
      have hθu : theta (α := α) ≤ Fintype.card α := by
        obtain ⟨S, _, hc⟩ := theta_witness (α := α)
        rw [← hc]
        exact Finset.card_le_univ S
      have hwθ := width_le_theta (α := α)
      have hw : 2 ≤ maxAntichainSize α := hn.trans hwu
      rw [max_eq_right hw]
      omega

/-- The full general identity and both endpoint classifications requested in
Boldi--Vigna, arXiv:2610.41385v1, Section 6. Intervals are all order-convex
subsets and the carried linear orders are arbitrary, with repetitions allowed. -/
theorem result (hn : 2 ≤ Fintype.card α) :
    sweepDimension (α := α) = theta (α := α) ∧
    (sweepDimension (α := α) = max 2 (maxAntichainSize α) ↔
      IsChain (· ≤ ·) (Set.univ : Set α) ∨
      IsAntichain (· ≤ ·) (Set.univ : Set α)) ∧
    (sweepDimension (α := α) = 2 * maxAntichainSize α ↔
      ∃ A B : Finset α, IsAntichain (· ≤ ·) (A : Set α) ∧
        IsAntichain (· ≤ ·) (B : Set α) ∧ Disjoint A B ∧
        A.card = maxAntichainSize α ∧ B.card = maxAntichainSize α) := by
  rw [sweepDimension_eq_theta]
  exact ⟨rfl, theta_lower_endpoint hn, theta_upper_endpoint⟩

end D5.S3.Combinatorics.SweepDimension.Endpoints

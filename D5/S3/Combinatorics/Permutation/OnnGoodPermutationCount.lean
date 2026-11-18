/- GID: D5/S3/Combinatorics/Permutation/OnnGoodPermutationCount
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Permutation/OnnGoodPermutationCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact good-permutation counts in every positive dimension. -/

/-
admission_basis: open-problem-resolution (#26707; Proved)
escape_witness: none (settling result)
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30704
Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9
F1: gid:D5/S1/Words/Patterns/A398542FixedBottom; declaration D5.S1.Words.Patterns.A398542FixedBottom.Shuffle; sha256:dd5fc640ababf1df241ef657ca84389b857beae142dde85339d0803f0d505f6e
F2: gid:D5/S1/Words/Patterns/A398542FixedBottom; declaration D5.S1.Words.Patterns.A398542FixedBottom.Shuffle.casesOn; sha256:ef821427d8fa29568d12f476cb8a47500bff84af0acc02f48359210ab7d12295
F3: gid:D5/S1/Words/Patterns/A398542FixedBottom; declaration D5.S1.Words.Patterns.A398542FixedBottom.Shuffle.lower_mono; sha256:429b30d3b271cdbab97e06329d4f625ee19844576f45921ccc5e8435843f1e37
F4: gid:D5/S1/Words/Patterns/A398542FixedBottom; declaration D5.S1.Words.Patterns.A398542FixedBottom.Shuffle.mk; sha256:74c85131299e5efa919a9a01e2250ffc457ca814d37918293fbc5f6b2f9565e9
F5: gid:D5/S1/Words/Patterns/A398542FixedBottom; declaration D5.S1.Words.Patterns.A398542FixedBottom.Shuffle.positions; sha256:1c8390956fe434af253a13095086928ae8d4266dc62485aa5a931a5c69beaf07
F6: gid:D5/S1/Words/Patterns/A398542FixedBottom; declaration D5.S1.Words.Patterns.A398542FixedBottom.Shuffle.upper_mono; sha256:8f0123cb940a52c3beb7a6eb52d80b15e8c52290a117cfe8bc36f6ea9a7b992b
F7: gid:D5/S3/Combinatorics/SubsetSpectrum/EvenBridge; declaration D5.S3.Combinatorics.SubsetSpectrum.evenSubsets; sha256:8f998106944694dc001e4e894e5e2310ef44c82b679b5a0f0ffdc390f7138888
F8: gid:D5/S3/Combinatorics/SubsetSpectrum/EvenBridge; declaration D5.S3.Combinatorics.SubsetSpectrum.oddSubsets; sha256:56b4be0ffa94347164e3cf25c867fb1e1b26642bea6c6ce662b2513f6f49990e
F9: gid:D5/S3/Combinatorics/SubsetSpectrum/EvenBridge; declaration D5.S3.Combinatorics.SubsetSpectrum.parity_counts; sha256:f5b6949c783ee6090ac971afce6b5e56b48a77b3a9d59cdafe5c3e80e9eaf734
Declaration classifications inline the same-delivery helpers and stop at frozen or pinned upstream owners.
goodCount — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.count_two, OnnGoodPermutationCount.count_large, OnnGoodPermutationCount.count_three, OnnGoodPermutationCount.result, OnnGoodPermutationCount.count_one, OnnGoodPermutationCount.count_transpose, OnnGoodPermutationCount.claim, OnnGoodPermutationCount.count_formula.
proposedCount — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.result, OnnGoodPermutationCount.claim, OnnGoodPermutationCount.count_formula.
claim — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.result.
count_transpose — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.count_formula.
count_one — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.count_formula.
count_large — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.count_formula.
leftLabels — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.rightLabels_compl, OnnGoodPermutationCount.leftLabels_card, OnnGoodPermutationCount.orderedSplitSubsetEquiv.
leftLabels_card — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: settling result.
rightLabels_compl — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: settling result.
shuffle_ext — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F2, F4, F5; consumers: settling result.
orderedSplitSubsetEquiv — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: OnnGoodPermutationCount.orderedSplit_card, OnnGoodPermutationCount.rowSplitSubsetEquiv.
orderedSplit_card — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: OnnGoodPermutationCount.typeA_card.
chainLayout — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.partitionOrderEquiv, OnnGoodPermutationCount.chainLayout_left, OnnGoodPermutationCount.chainLayout_right.
chainLayout_left — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: settling result.
chainLayout_right — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: settling result.
partitionOrderEquiv — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: OnnGoodPermutationCount.rowSplitSubsetEquiv.
evenFinset_card — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F7, F8, F9; consumers: OnnGoodPermutationCount.count_two.
splitSubsetEvenEquiv — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.rowsEvenEquiv.
lowPositions — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.rowPositions_nodup, OnnGoodPermutationCount.rowPositions_order, OnnGoodPermutationCount.rowPositions_all, OnnGoodPermutationCount.rowSplitSubsetEquiv.
highPositions — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.rowPositions_nodup, OnnGoodPermutationCount.rowPositions_order, OnnGoodPermutationCount.rowPositions_all, OnnGoodPermutationCount.rowSplitSubsetEquiv.
rowPositions_nodup — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.rowSplitSubsetEquiv.
rowPositions_all — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.rowSplitSubsetEquiv.
rowPositions_order — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.rowSplitSubsetEquiv.
rowSplitSubsetEquiv — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: OnnGoodPermutationCount.rowsEvenEquiv.
twoChains_unique — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.good_of_twoChains.
good_of_twoChains — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: settling result.
rowsSigmaEquiv — proof_shape: content; escape_witness: D5.S3.Combinatorics.Permutation.OnnGoodPermutationStructure.pairgood_sign_split; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.rowsEvenEquiv.
rowsEvenEquiv — proof_shape: content; escape_witness: D5.S3.Combinatorics.Permutation.OnnGoodPermutationStructure.pairgood_sign_split; Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: OnnGoodPermutationCount.count_two.
count_two — proof_shape: content; escape_witness: D5.S3.Combinatorics.Permutation.OnnGoodPermutationStructure.pairgood_sign_split; Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9; consumers: OnnGoodPermutationCount.count_formula.
lowerPos — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.typeA_center, OnnGoodPermutationCount.assembleA_type, OnnGoodPermutationCount.extractHigh, OnnGoodPermutationCount.typeA_bounds, OnnGoodPermutationCount.assembleA_lower, OnnGoodPermutationCount.extractLow, OnnGoodPermutationCount.positionFun, OnnGoodPermutationCount.lowerPos_injective.
upperPos — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.typeA_center, OnnGoodPermutationCount.assembleA_type, OnnGoodPermutationCount.extractHigh, OnnGoodPermutationCount.typeA_bounds, OnnGoodPermutationCount.extractLow, OnnGoodPermutationCount.positionFun, OnnGoodPermutationCount.upperPos_injective, OnnGoodPermutationCount.assembleA_upper.
lowerPos_injective — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.typeA_center.
upperPos_injective — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.typeA_center.
positionFun — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.positionEquiv.
positionEquiv — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.assembleA, OnnGoodPermutationCount.assembleA_lower, OnnGoodPermutationCount.assembleA_upper, OnnGoodPermutationCount.assembleA_middle.
labelEquiv — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.assembleA, OnnGoodPermutationCount.assembleA_lower, OnnGoodPermutationCount.assembleA_upper, OnnGoodPermutationCount.assembleA_middle.
typeA_edges — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.assembleA_type, OnnGoodPermutationCount.typeA_bounds.
typeA_bounds — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.typeA_center, OnnGoodPermutationCount.extractHigh, OnnGoodPermutationCount.extractLow.
typeA_center — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.extractHigh, OnnGoodPermutationCount.extractLow.
extractLow — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F4; consumers: OnnGoodPermutationCount.typeAEquiv.
extractHigh — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F4; consumers: OnnGoodPermutationCount.typeAEquiv.
assembleA — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F5; consumers: OnnGoodPermutationCount.assembleA_type, OnnGoodPermutationCount.assembleA_lower, OnnGoodPermutationCount.typeAEquiv, OnnGoodPermutationCount.assembleA_upper, OnnGoodPermutationCount.assembleA_middle.
assembleA_lower — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F5; consumers: OnnGoodPermutationCount.assembleA_type.
assembleA_upper — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F5; consumers: OnnGoodPermutationCount.assembleA_type.
assembleA_middle — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F5; consumers: OnnGoodPermutationCount.assembleA_type.
assembleA_type — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F3, F5, F6; consumers: settling result.
typeAEquiv — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: OnnGoodPermutationCount.typeA_card.
typeA_card — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: OnnGoodPermutationCount.typeB_card, OnnGoodPermutationCount.count_three.
typeA_transpose — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: settling result.
typeABEquiv — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.typeB_card.
typeB_card — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: OnnGoodPermutationCount.count_three.
types_disjoint — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: settling result.
typesGoodEquiv — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none; consumers: OnnGoodPermutationCount.count_three.
count_three — proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: F1, F2, F3, F4, F5, F6; consumers: OnnGoodPermutationCount.count_formula.
count_formula — proof_shape: content; escape_witness: D5.S3.Combinatorics.Permutation.OnnGoodPermutationStructure.pairgood_sign_split; Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9; consumers: OnnGoodPermutationCount.result.
result — proof_shape: content; escape_witness: D5.S3.Combinatorics.Permutation.OnnGoodPermutationStructure.pairgood_sign_split; Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F8, F9; consumers: none (settling result).
The rank-array type is the existing equivalence type, with no type alias.
-/

import D5.S3.Combinatorics.Permutation.OnnGoodPermutationStructure
import D5.S3.Combinatorics.SubsetSpectrum.EvenBridge
import D5.S1.Words.Patterns.A398542FixedBottom
import Mathlib.Data.Fintype.Sort

open D5.S3.Combinatorics.Permutation.OnnGoodPermutationStructure
open D5.S1.Words.Patterns.A398542FixedBottom (Shuffle)

namespace D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount


/-- Cardinality of all rank arrays satisfying the source's local condition. -/
noncomputable def goodCount (m n : ℕ) : ℕ :=
  Nat.card {σ : ((Fin m × Fin n) ≃ Fin (m * n)) // Good σ}

/-- Proposed answer; its zero case for min≥3,max≥4 is already in Onn's Theorem 1.3. -/
def proposedCount (m n : ℕ) : ℕ :=
  if min m n = 1 then (max m n).factorial
  else if min m n = 2 then 2 ^ (2 * max m n - 1)
  else if m = 3 ∧ n = 3 then 72
  else 0

/-- The full answer to the unnumbered referee question preceding Lemma 2.2. -/
def claim : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    goodCount m n = proposedCount m n ∧
    ∀ σ : ((Fin m × Fin n) ≃ Fin (m * n)), Good σ ↔ Structure σ

private theorem count_transpose (m n : ℕ) : goodCount m n = goodCount n m := by
  apply Nat.card_congr
  exact {
    toFun := fun σ => ⟨transpose σ.val,(good_transpose σ.val).mpr σ.property⟩
    invFun := fun σ => ⟨transpose σ.val,(good_transpose σ.val).mpr σ.property⟩
    left_inv := fun σ => Subtype.ext (show transpose (transpose σ.val) = σ.val from Equiv.coe_inj.mp rfl)
    right_inv := fun σ => Subtype.ext (show transpose (transpose σ.val) = σ.val from Equiv.coe_inj.mp rfl) }

private theorem count_one (n : ℕ) : goodCount 1 n = n.factorial := by
  unfold goodCount
  let e : {σ : ((Fin 1 × Fin n) ≃ Fin (1 * n)) // Good σ} ≃ ((Fin 1 × Fin n) ≃ Fin (1 * n)) := {
    toFun := Subtype.val
    invFun := fun σ => ⟨σ, good_of_one σ (Or.inl rfl)⟩
    left_inv := fun σ => Subtype.ext rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  let e' : (Fin 1 × Fin n) ≃ Fin (1*n) := Fintype.equivFinOfCardEq (by simp)
  rw [Fintype.card_equiv e']
  simp

private theorem count_large (m n : ℕ) (hm : 3 ≤ m) (hn : 4 ≤ n) : goodCount m n = 0 := by
  unfold goodCount
  letI : IsEmpty {σ : ((Fin m × Fin n) ≃ Fin (m * n)) // Good σ} := ⟨fun σ => no_good_large σ.val hm hn σ.property⟩
  exact Nat.card_of_isEmpty



private def leftLabels {p q N : ℕ} (e : (Fin p ⊕ Fin q) ≃ Fin N) : Finset (Fin N) :=
  Finset.univ.image (fun i => e (Sum.inl i))

private theorem leftLabels_card {p q N : ℕ} (e : (Fin p ⊕ Fin q) ≃ Fin N) :
    (leftLabels e).card = p := by
  unfold leftLabels
  have hi : Function.Injective (fun i : Fin p => e (Sum.inl i)) :=
    fun i j hij => Sum.inl.inj (e.injective hij)
  rw [Finset.card_image_of_injective _ hi]
  exact Fintype.card_fin p

private theorem rightLabels_compl {p q N : ℕ} (e : (Fin p ⊕ Fin q) ≃ Fin N) :
    Finset.univ.image (fun i => e (Sum.inr i)) = (leftLabels e)ᶜ := by
  classical
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_compl, leftLabels]
  constructor
  · rintro ⟨i,rfl⟩ ⟨j,hj⟩
    exact Sum.inl_ne_inr (e.injective hj)
  · intro hy
    obtain ⟨i | i,rfl⟩ := e.surjective y
    · exact (hy ⟨i,rfl⟩).elim
    · exact ⟨i,rfl⟩

private theorem shuffle_ext {p q : ℕ} (s t : Shuffle p q)
    (h : s.positions = t.positions) : s = t := by
  rcases s with ⟨s, hs, hs'⟩
  rcases t with ⟨t, ht, ht'⟩
  cases h
  rfl

private noncomputable def orderedSplitSubsetEquiv (p q N : ℕ) (h : p+q=N) :
    Shuffle p q ≃ {S : Finset (Fin N) // S.card=p} := by
  subst N
  exact {
    toFun := fun e => ⟨leftLabels e.positions,leftLabels_card e.positions⟩
    invFun := fun S => ⟨finSumEquivOfFinset S.property (by
      rw [Finset.card_compl, Fintype.card_fin, S.property]; omega),
      by simpa (config := { congrConsts := false }) only [finSumEquivOfFinset_inl] using
        (S.val.orderEmbOfFin S.property).strictMono,
      by simpa (config := { congrConsts := false }) only [finSumEquivOfFinset_inr] using
        (S.valᶜ.orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, S.property]; omega)).strictMono⟩
    left_inv := fun e => by
      have heq : (finSumEquivOfFinset (leftLabels_card e.positions) (by
          rw [Finset.card_compl, Fintype.card_fin, leftLabels_card]; omega)) = e.positions := by
        apply Equiv.ext
        intro x
        cases x with
        | inl i =>
          have he := Finset.orderEmbOfFin_unique (leftLabels_card e.positions)
            (f := fun j => e.positions (Sum.inl j)) (by intro j; simp (config := { congrConsts := false }) [leftLabels]) e.lower_mono
          simpa (config := { congrConsts := false }) only [finSumEquivOfFinset_inl] using (congrFun he i).symm
        | inr i =>
          have hc : (leftLabels e.positions)ᶜ.card = q := by
            rw [Finset.card_compl, Fintype.card_fin, leftLabels_card]; omega
          have he := Finset.orderEmbOfFin_unique hc
            (f := fun j => e.positions (Sum.inr j)) (by
              intro j; rw [← rightLabels_compl]
              exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) e.upper_mono
          simpa (config := { congrConsts := false }) only [finSumEquivOfFinset_inr] using (congrFun he i).symm
      exact shuffle_ext _ _ heq
    right_inv := fun S => by
      apply Subtype.ext
      change Finset.univ.image (fun i => finSumEquivOfFinset S.property _ (Sum.inl i)) = S.val
      simpa (config := { congrConsts := false }) only [finSumEquivOfFinset_inl] using Finset.image_orderEmbOfFin_univ S.val S.property }

private theorem orderedSplit_card (p q N : ℕ) (h : p+q=N) :
    Nat.card (Shuffle p q) = N.choose p := by
  rw [Nat.card_congr (orderedSplitSubsetEquiv p q N h), Nat.card_eq_fintype_card,
    Fintype.card_finset_len, Fintype.card_fin]

end D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

namespace D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

private noncomputable def chainLayout {α : Type} [DecidableEq α] (L R : List α)
    (hd : (L++R).Nodup) (hm : ∀ x, x ∈ L++R) :
    (Fin L.length ⊕ Fin R.length) ≃ α :=
  finSumFinEquiv.trans ((finCongr (by simp)).trans
    (List.Nodup.getEquivOfForallMemList (L++R) hd hm))

@[simp] private theorem chainLayout_left {α : Type} [DecidableEq α] (L R : List α)
    (hd : (L++R).Nodup) (hm : ∀ x, x ∈ L++R) (i : Fin L.length) :
    chainLayout L R hd hm (Sum.inl i) = L.get i := by
  simp (config := { congrConsts := false }) [chainLayout, List.getElem_append_left, i.isLt]

@[simp] private theorem chainLayout_right {α : Type} [DecidableEq α] (L R : List α)
    (hd : (L++R).Nodup) (hm : ∀ x, x ∈ L++R) (i : Fin R.length) :
    chainLayout L R hd hm (Sum.inr i) = R.get i := by
  simp (config := { congrConsts := false }) [chainLayout, List.getElem_append_right, i.isLt]

private noncomputable def partitionOrderEquiv {α : Type} [DecidableEq α] (N : ℕ) (L R : List α)
    (hd : (L++R).Nodup) (hm : ∀ x, x ∈ L++R) (hlen : L.length + R.length = N) :
    {σ : α ≃ Fin N // L.Pairwise (fun x y => σ x < σ y) ∧ R.Pairwise (fun x y => σ x < σ y)} ≃ Shuffle L.length R.length := by
  subst N
  exact {
    toFun := fun σ => ⟨(chainLayout L R hd hm).trans σ.val,
      by
        have hl : (List.ofFn (fun i : Fin L.length => σ.val (L.get i))).Pairwise (· < ·) := by
          simp (config := { congrConsts := false }) only [List.get_eq_getElem]
          rw [List.ofFn_getElem_eq_map]
          simpa (config := { congrConsts := false }) only [List.pairwise_map] using σ.property.1
        simpa (config := { congrConsts := false }) only [StrictMono, Equiv.trans_apply, chainLayout_left] using List.pairwise_ofFn.mp hl,
      by
        have hr : (List.ofFn (fun i : Fin R.length => σ.val (R.get i))).Pairwise (· < ·) := by
          simp (config := { congrConsts := false }) only [List.get_eq_getElem]
          rw [List.ofFn_getElem_eq_map]
          simpa (config := { congrConsts := false }) only [List.pairwise_map] using σ.property.2
        simpa (config := { congrConsts := false }) only [StrictMono, Equiv.trans_apply, chainLayout_right] using List.pairwise_ofFn.mp hr⟩
    invFun := fun e => ⟨(chainLayout L R hd hm).symm.trans e.positions, by
      constructor
      · have hl : StrictMono (fun i : Fin L.length =>
            ((chainLayout L R hd hm).symm.trans e.positions) (L.get i)) := by
          simpa (config := { congrConsts := false }) only [← chainLayout_left L R hd hm, Equiv.trans_apply,
            Equiv.symm_apply_apply] using e.lower_mono
        have h := List.pairwise_ofFn.mpr hl
        simp (config := { congrConsts := false }) only [List.get_eq_getElem] at h
        rw [List.ofFn_getElem_eq_map] at h
        simpa (config := { congrConsts := false }) only [List.pairwise_map] using h
      · have hr : StrictMono (fun i : Fin R.length =>
            ((chainLayout L R hd hm).symm.trans e.positions) (R.get i)) := by
          simpa (config := { congrConsts := false }) only [← chainLayout_right L R hd hm, Equiv.trans_apply,
            Equiv.symm_apply_apply] using e.upper_mono
        have h := List.pairwise_ofFn.mpr hr
        simp (config := { congrConsts := false }) only [List.get_eq_getElem] at h
        rw [List.ofFn_getElem_eq_map] at h
        simpa (config := { congrConsts := false }) only [List.pairwise_map] using h⟩
    left_inv := fun σ => by
      apply Subtype.ext
      exact (Equiv.trans_cancel_left (chainLayout L R hd hm).symm
        ((chainLayout L R hd hm).trans σ.val) σ.val).mpr rfl
    right_inv := fun e => by
      have h : (chainLayout L R hd hm).trans ((chainLayout L R hd hm).symm.trans e.positions) = e.positions :=
        (Equiv.trans_cancel_left (chainLayout L R hd hm) ((chainLayout L R hd hm).symm.trans e.positions) e.positions).mpr rfl
      exact shuffle_ext _ _ h }

end D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

namespace D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

private theorem evenFinset_card (N : ℕ) (hN : 0 < N) :
    Nat.card {S : Finset (Fin N) // Even S.card} = 2^(N-1) := by
  classical
  have h := (D5.S3.Combinatorics.SubsetSpectrum.parity_counts
    (Finset.univ : Finset (Fin N)) (by exact ⟨⟨0,hN⟩,Finset.mem_univ _⟩)).1
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at h
  have hc : (D5.S3.Combinatorics.SubsetSpectrum.evenSubsets (Finset.univ : Finset (Fin N))).card =
      2^(N-1) := by exact_mod_cast h
  rw [← hc, Nat.card_eq_fintype_card]
  simp [D5.S3.Combinatorics.SubsetSpectrum.evenSubsets, Fintype.card_subtype]

end D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

namespace D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

private noncomputable def splitSubsetEvenEquiv (n : ℕ) :
    (Σ k : Fin (n+1), {S : Finset (Fin (2*n)) // S.card=2*k.val}) ≃
      {S : Finset (Fin (2*n)) // Even S.card} := by
  let f : (Σ k : Fin (n+1), {S : Finset (Fin (2*n)) // S.card=2*k.val}) →
      {S : Finset (Fin (2*n)) // Even S.card} :=
    fun p => ⟨p.2.val,⟨p.1.val,by have := p.2.property; omega⟩⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨k,S⟩ ⟨l,T⟩ h
    have hST : S.val = T.val := congrArg Subtype.val h
    have hkl : k = l := by
      apply Fin.ext
      have hs := S.property
      have ht := T.property
      rw [hST] at hs
      omega
    subst l
    have : S = T := Subtype.ext hST
    subst T
    rfl
  · intro S
    obtain ⟨k,hk⟩ := S.property
    have hc : S.val.card ≤ 2*n := by simpa using Finset.card_le_univ S.val
    have hk' : k < n+1 := by omega
    refine ⟨⟨⟨k,hk'⟩,⟨S.val,by change S.val.card=2*k; omega⟩⟩,?_⟩
    apply Subtype.ext
    rfl

end D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

namespace D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

private def lowPositions (n k : ℕ) (hk : k ≤ n) : List (Fin 2 × Fin n) :=
  List.ofFn (fun j : Fin k => ((1 : Fin 2), (⟨j.val, by omega⟩ : Fin n))) ++
    (List.ofFn (fun j : Fin k => ((0 : Fin 2), (⟨j.val, by omega⟩ : Fin n)))).reverse

private def highPositions (n k : ℕ) (hk : k ≤ n) : List (Fin 2 × Fin n) :=
  (List.ofFn (fun j : Fin (n-k) => ((0 : Fin 2), (⟨k+j.val, by omega⟩ : Fin n)))).reverse ++
    List.ofFn (fun j : Fin (n-k) => ((1 : Fin 2), (⟨k+j.val, by omega⟩ : Fin n)))

private theorem rowPositions_nodup (n k : ℕ) (hk : k ≤ n) :
    (lowPositions n k hk ++ highPositions n k hk).Nodup := by
  simp (config := { congrConsts := false }) only [lowPositions, highPositions, List.nodup_append, List.nodup_reverse,
    List.nodup_ofFn, List.mem_append, List.mem_reverse, List.mem_ofFn,
    forall_exists_index, forall_apply_eq_imp_iff, Function.Injective,
    Prod.mk.injEq, Fin.mk.injEq]
  simp (config := { congrConsts := false }) only [Fin.ext_iff]
  aesop <;> omega

private theorem rowPositions_all (n k : ℕ) (hk : k ≤ n) :
    ∀ x : Fin 2 × Fin n, x ∈ lowPositions n k hk ++ highPositions n k hk := by
  rintro ⟨i,j⟩
  simp (config := { congrConsts := false }) only [lowPositions, highPositions, List.mem_append, List.mem_reverse, List.mem_ofFn]
  fin_cases i
  · by_cases hj : j.val < k
    · exact Or.inl (Or.inr ⟨⟨j.val,hj⟩,rfl⟩)
    · right; left
      refine ⟨⟨j.val-k,by omega⟩,?_⟩
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp (config := { congrConsts := false }) only
        omega
  · by_cases hj : j.val < k
    · exact Or.inl (Or.inl ⟨⟨j.val,hj⟩,rfl⟩)
    · right; right
      refine ⟨⟨j.val-k,by omega⟩,?_⟩
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp (config := { congrConsts := false }) only
        omega

private theorem rowPositions_order (n k : ℕ) (hk : k ≤ n) (σ : ((Fin 2 × Fin n) ≃ Fin (2 * n))) :
    TwoChains n (entry σ 0) (entry σ 1) k ↔
      (lowPositions n k hk).Pairwise (fun x y => σ x < σ y) ∧
      (highPositions n k hk).Pairwise (fun x y => σ x < σ y) := by
  have hpre : ∀ j : Fin k, j.val < n := fun j => lt_of_lt_of_le j.isLt hk
  have hsuf : ∀ j : Fin (n-k), k+j.val < n := by intro j; omega
  simp (config := { congrConsts := false }) only [TwoChains, hk, true_and]
  have hl :
      (lowPositions n k hk).map (fun p => (σ p).val+1) =
        List.ofFn (fun j : Fin k => entry σ 1 j.val) ++
          (List.ofFn (fun j : Fin k => entry σ 0 j.val)).reverse := by
    simp (config := { congrConsts := false }) [lowPositions, List.map_ofFn, entry, hpre, Function.comp_def]
  have hr :
      (highPositions n k hk).map (fun p => (σ p).val+1) =
        (List.ofFn (fun j : Fin (n-k) => entry σ 0 (k+j.val))).reverse ++
          List.ofFn (fun j : Fin (n-k) => entry σ 1 (k+j.val)) := by
    simp (config := { congrConsts := false }) [highPositions, List.map_ofFn, entry, hsuf, Function.comp_def]
  rw [← hl, ← hr]
  simp (config := { congrConsts := false }) only [List.pairwise_map, Nat.add_lt_add_iff_right, Fin.lt_def]

private noncomputable def rowSplitSubsetEquiv (n k : ℕ) (hk : k ≤ n) :
    {σ : ((Fin 2 × Fin n) ≃ Fin (2 * n)) // TwoChains n (entry σ 0) (entry σ 1) k} ≃
      {S : Finset (Fin (2*n)) // S.card=2*k} := by
  let e : {σ : ((Fin 2 × Fin n) ≃ Fin (2 * n)) // TwoChains n (entry σ 0) (entry σ 1) k} ≃
      {σ : (Fin 2 × Fin n) ≃ Fin (2*n) // (lowPositions n k hk).Pairwise (fun x y => σ x < σ y) ∧ (highPositions n k hk).Pairwise (fun x y => σ x < σ y)} :=
    Equiv.subtypeEquivRight (rowPositions_order n k hk)
  exact e.trans ((partitionOrderEquiv (2*n) _ _ (rowPositions_nodup n k hk)
    (rowPositions_all n k hk) (by simp (config := { congrConsts := false }) [lowPositions,highPositions]; omega)).trans ((orderedSplitSubsetEquiv _ _ (2*n)
      (by simp (config := { congrConsts := false }) [lowPositions,highPositions]; omega)).trans
        (Equiv.subtypeEquivRight (by intro S; simp (config := { congrConsts := false }) [lowPositions,two_mul]))))

private theorem twoChains_unique (n : ℕ) (T B : ℕ → ℕ) (k l : ℕ)
    (hk : TwoChains n T B k) (hl : TwoChains n T B l) : k=l := by
  have hkn := hk.1
  have hln := hl.1
  by_contra hkl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have ha := (List.pairwise_append.mp hk.2.2).2.2 (T k)
      (List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨⟨0, by omega⟩, by simp⟩))
      (B k) (List.mem_ofFn.mpr ⟨⟨0, by omega⟩, by simp⟩)
    have hb := (List.pairwise_append.mp hl.2.1).2.2 (B k)
      (List.mem_ofFn.mpr ⟨⟨k, hlt⟩, rfl⟩)
      (T k) (List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨⟨k, hlt⟩, rfl⟩))
    omega
  · have ha := (List.pairwise_append.mp hl.2.2).2.2 (T l)
      (List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨⟨0, by omega⟩, by simp⟩))
      (B l) (List.mem_ofFn.mpr ⟨⟨0, by omega⟩, by simp⟩)
    have hb := (List.pairwise_append.mp hk.2.1).2.2 (B l)
      (List.mem_ofFn.mpr ⟨⟨l, hgt⟩, rfl⟩)
      (T l) (List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨⟨l, hgt⟩, rfl⟩))
    omega

private theorem good_of_twoChains {n : ℕ} (σ : ((Fin 2 × Fin n) ≃ Fin (2 * n))) (k : ℕ)
    (h : TwoChains n (entry σ 0) (entry σ 1) k) : Good σ :=
  (two_good_iff σ).mpr ⟨k,h,fun l hl => twoChains_unique n _ _ l k hl h⟩

private noncomputable def rowsSigmaEquiv (n : ℕ) :
    (Σ k : Fin (n+1), {σ : ((Fin 2 × Fin n) ≃ Fin (2 * n)) // TwoChains n (entry σ 0) (entry σ 1) k.val}) ≃
      {σ : ((Fin 2 × Fin n) ≃ Fin (2 * n)) // Good σ} := by
  let f : (Σ k : Fin (n+1), {σ : ((Fin 2 × Fin n) ≃ Fin (2 * n)) // TwoChains n (entry σ 0) (entry σ 1) k.val}) →
      {σ : ((Fin 2 × Fin n) ≃ Fin (2 * n)) // Good σ} :=
    fun p => ⟨p.2.val,good_of_twoChains p.2.val p.1.val p.2.property⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨k,σ⟩ ⟨l,τ⟩ h
    have hστ : σ.val=τ.val := congrArg Subtype.val h
    have hkl : k=l := by
      apply Fin.ext
      apply twoChains_unique n (entry σ.val 0) (entry σ.val 1) k.val l.val σ.property
      simpa only [hστ] using τ.property
    subst l
    have : σ=τ := Subtype.ext hστ
    subst τ
    rfl
  · intro σ
    obtain ⟨k,hk,_⟩ := (two_good_iff σ.val).mp σ.property
    refine ⟨⟨⟨k,by have := hk.1; omega⟩,⟨σ.val,hk⟩⟩,?_⟩
    apply Subtype.ext
    rfl

private noncomputable def rowsEvenEquiv (n : ℕ) :
    {σ : ((Fin 2 × Fin n) ≃ Fin (2 * n)) // Good σ} ≃ {S : Finset (Fin (2*n)) // Even S.card} :=
  (rowsSigmaEquiv n).symm.trans ((Equiv.sigmaCongrRight (fun k : Fin (n+1) =>
    rowSplitSubsetEquiv n k.val (by omega))).trans (splitSubsetEvenEquiv n))

private theorem count_two (n : ℕ) (hn : 0 < n) : goodCount 2 n = 2^(2*n-1) := by
  unfold goodCount
  rw [Nat.card_congr (rowsEvenEquiv n), evenFinset_card (2*n) (by omega)]

end D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount


private def lowerPos : (Fin 2 ⊕ Fin 2) → Fin 3 × Fin 3
  | Sum.inl i => (⟨2-i.val,by omega⟩,0)
  | Sum.inr i => (⟨i.val,by omega⟩,2)

private def upperPos : (Fin 2 ⊕ Fin 2) → Fin 3 × Fin 3
  | Sum.inl i => (0,⟨1-i.val,by omega⟩)
  | Sum.inr i => (2,⟨1+i.val,by omega⟩)

private theorem lowerPos_injective : Function.Injective lowerPos := by decide

private theorem upperPos_injective : Function.Injective upperPos := by decide

private def positionFun : (Fin 2 ⊕ Fin 2) ⊕ (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) → Fin 3 × Fin 3 :=
  Sum.elim lowerPos (Sum.elim (fun _ => (1,1)) upperPos)

private noncomputable def positionEquiv : (Fin 2 ⊕ Fin 2) ⊕ (Fin 1 ⊕ (Fin 2 ⊕ Fin 2)) ≃ Fin 3 × Fin 3 :=
  Equiv.ofBijective positionFun (by decide)

private def labelEquiv : (Fin 4 ⊕ (Fin 1 ⊕ Fin 4)) ≃ Fin 9 :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

private theorem typeA_edges (σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3))) :
    TypeA (entry σ) ↔
      σ (2,0) < σ (1,0) ∧ σ (1,0) < σ (1,1) ∧
      σ (1,1) < σ (0,1) ∧ σ (0,1) < σ (0,0) ∧
      σ (0,2) < σ (1,2) ∧ σ (1,2) < σ (1,1) ∧
      σ (1,1) < σ (2,1) ∧ σ (2,1) < σ (2,2) := by
  simp [TypeA, List.pairwise_cons, entry]
  omega

private theorem typeA_bounds (σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3))) (h : TypeA (entry σ)) :
    (∀ x, σ (lowerPos x) < σ (1,1)) ∧
      (∀ x, σ (1,1) < σ (upperPos x)) := by
  have he := (typeA_edges σ).mp h
  constructor <;> rintro (x | x) <;> fin_cases x <;>
    norm_num [lowerPos,upperPos] <;> omega

private theorem typeA_center (σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3))) (h : TypeA (entry σ)) :
    (σ (1,1)).val = 4 := by
  have hb := typeA_bounds σ h
  let e := (σ (1,1)).val
  let fL : (Fin 2 ⊕ Fin 2) → Fin e := fun x => ⟨(σ (lowerPos x)).val,hb.1 x⟩
  have hL : Function.Injective fL := by
    intro x y hxy
    apply lowerPos_injective
    apply σ.injective
    apply Fin.ext
    exact congrArg (fun z : Fin e => z.val) hxy
  have hLc := Fintype.card_le_of_injective fL hL
  have hfourL : 4 ≤ e := by simpa using hLc
  let fU : (Fin 2 ⊕ Fin 2) → Fin (8-e) := fun x =>
    ⟨(σ (upperPos x)).val-(e+1),by
      have hlo := hb.2 x
      have hhi := (σ (upperPos x)).isLt
      dsimp [e]
      omega⟩
  have hU : Function.Injective fU := by
    intro x y hxy
    apply upperPos_injective
    apply σ.injective
    apply Fin.ext
    have heq := congrArg Fin.val hxy
    have hx := hb.2 x
    have hy := hb.2 y
    change (σ (upperPos x)).val-(e+1) = (σ (upperPos y)).val-(e+1) at heq
    dsimp [e] at heq
    omega
  have hUc := Fintype.card_le_of_injective fU hU
  have hfourU : 4 ≤ 8-e := by simpa using hUc
  dsimp [e] at *
  omega

private noncomputable def extractLow (σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3))) (h : TypeA (entry σ)) : Shuffle 2 2 := by
  have hb := typeA_bounds σ h
  have hc := typeA_center σ h
  let f : (Fin 2 ⊕ Fin 2) → Fin 4 := fun x => ⟨(σ (lowerPos x)).val,by have := hb.1 x; omega⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact lowerPos_injective (σ.injective (Fin.ext (congrArg (fun z : Fin 4 => z.val) hxy)))
  refine ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,by simp⟩),?_,?_⟩
  · intro i j hij
    change (σ (lowerPos (Sum.inl i))).val < (σ (lowerPos (Sum.inl j))).val
    have he := (typeA_edges σ).mp h
    fin_cases i <;> fin_cases j <;> simp_all [lowerPos] <;> omega
  · intro i j hij
    change (σ (lowerPos (Sum.inr i))).val < (σ (lowerPos (Sum.inr j))).val
    have he := (typeA_edges σ).mp h
    fin_cases i <;> fin_cases j <;> simp_all [lowerPos] <;> omega

private noncomputable def extractHigh (σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3))) (h : TypeA (entry σ)) : Shuffle 2 2 := by
  have hb := typeA_bounds σ h
  have hc := typeA_center σ h
  let f : (Fin 2 ⊕ Fin 2) → Fin 4 := fun x => ⟨(σ (upperPos x)).val-5,by
    have := hb.2 x
    have := (σ (upperPos x)).isLt
    omega⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply upperPos_injective
    apply σ.injective
    apply Fin.ext
    have heq := congrArg Fin.val hxy
    have hx := hb.2 x
    have hy := hb.2 y
    change (σ (upperPos x)).val-5 = (σ (upperPos y)).val-5 at heq
    omega
  refine ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf,by simp⟩),?_,?_⟩
  · intro i j hij
    change (σ (upperPos (Sum.inl i))).val-5 < (σ (upperPos (Sum.inl j))).val-5
    have he := (typeA_edges σ).mp h
    fin_cases i <;> fin_cases j <;> simp_all [upperPos] <;> omega
  · intro i j hij
    change (σ (upperPos (Sum.inr i))).val-5 < (σ (upperPos (Sum.inr j))).val-5
    have he := (typeA_edges σ).mp h
    fin_cases i <;> fin_cases j <;> simp_all [upperPos] <;> omega

private noncomputable def assembleA (L H : Shuffle 2 2) : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) :=
  positionEquiv.symm.trans ((Equiv.sumCongr L.positions (Equiv.sumCongr (Equiv.refl (Fin 1)) H.positions)).trans labelEquiv)

@[simp] private theorem assembleA_lower (L H : Shuffle 2 2) (x : (Fin 2 ⊕ Fin 2)) :
    (assembleA L H (lowerPos x)).val = (L.positions x).val := by
  change (assembleA L H (positionEquiv (Sum.inl x))).val = _
  simp only [assembleA,Equiv.trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inl]
  rfl

@[simp] private theorem assembleA_upper (L H : Shuffle 2 2) (x : (Fin 2 ⊕ Fin 2)) :
    (assembleA L H (upperPos x)).val = 5+(H.positions x).val := by
  change (assembleA L H (positionEquiv (Sum.inr (Sum.inr x)))).val = _
  simp only [assembleA,Equiv.trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inr]
  change 4+(1+(H.positions x).val) = 5+(H.positions x).val
  omega

@[simp] private theorem assembleA_middle (L H : Shuffle 2 2) :
    (assembleA L H (1,1)).val = 4 := by
  change (assembleA L H (positionEquiv (Sum.inr (Sum.inl (0 : Fin 1))))).val = _
  simp only [assembleA,Equiv.trans_apply,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inr,Sum.map_inl]
  rfl

private theorem assembleA_type (L H : Shuffle 2 2) : TypeA (entry (assembleA L H)) := by
  apply (typeA_edges _).mpr
  have hl0 := L.lower_mono (by decide : (0 : Fin 2) < 1)
  have hl1 := L.upper_mono (by decide : (0 : Fin 2) < 1)
  have hh0 := H.lower_mono (by decide : (0 : Fin 2) < 1)
  have hh1 := H.upper_mono (by decide : (0 : Fin 2) < 1)
  have hg := assembleA_lower L H (Sum.inl 0)
  have hd := assembleA_lower L H (Sum.inl 1)
  have hc := assembleA_lower L H (Sum.inr 0)
  have hf := assembleA_lower L H (Sum.inr 1)
  have hb := assembleA_upper L H (Sum.inl 0)
  have ha := assembleA_upper L H (Sum.inl 1)
  have hh := assembleA_upper L H (Sum.inr 0)
  have hi := assembleA_upper L H (Sum.inr 1)
  have he := assembleA_middle L H
  norm_num [lowerPos,upperPos] at hg hd hc hf hb ha hh hi
  have hlt0 := (L.positions (Sum.inl 0)).isLt
  have hlt1 := (L.positions (Sum.inl 1)).isLt
  have hlt2 := (L.positions (Sum.inr 0)).isLt
  have hlt3 := (L.positions (Sum.inr 1)).isLt
  dsimp only at hl0 hl1 hh0 hh1
  omega

private noncomputable def typeAEquiv :
    (Shuffle 2 2 × Shuffle 2 2) ≃
      {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // TypeA (entry σ)} where
  toFun p := ⟨assembleA p.1 p.2,assembleA_type p.1 p.2⟩
  invFun σ := (extractLow σ.val σ.property,extractHigh σ.val σ.property)
  left_inv p := by
    apply Prod.ext
    · apply shuffle_ext
      apply Equiv.ext
      intro x
      apply Fin.ext
      change (assembleA p.1 p.2 (lowerPos x)).val = (p.1.positions x).val
      exact assembleA_lower p.1 p.2 x
    · apply shuffle_ext
      apply Equiv.ext
      intro x
      apply Fin.ext
      change (assembleA p.1 p.2 (upperPos x)).val-5 = (p.2.positions x).val
      rw [assembleA_upper]
      omega
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨p,rfl⟩ := positionEquiv.surjective x
    apply Fin.ext
    rcases p with y | (z | y)
    · change (assembleA (extractLow σ.val σ.property) (extractHigh σ.val σ.property) (lowerPos y)).val =
        (σ.val (lowerPos y)).val
      rw [assembleA_lower]
      rfl
    · have hz : z = 0 := Subsingleton.elim _ _
      subst z
      change (assembleA (extractLow σ.val σ.property) (extractHigh σ.val σ.property) (1,1)).val =
        (σ.val (1,1)).val
      rw [assembleA_middle,typeA_center σ.val σ.property]
    · change (assembleA (extractLow σ.val σ.property) (extractHigh σ.val σ.property) (upperPos y)).val =
        (σ.val (upperPos y)).val
      rw [assembleA_upper]
      change 5+((σ.val (upperPos y)).val-5) = (σ.val (upperPos y)).val
      have hb := (typeA_bounds σ.val σ.property).2 y
      have hc := typeA_center σ.val σ.property
      omega

private theorem typeA_card : Nat.card {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // TypeA (entry σ)} = 36 := by
  calc
    _ = Nat.card (Shuffle 2 2 × Shuffle 2 2) := (Nat.card_congr typeAEquiv).symm
    _ = 36 := by rw [Nat.card_prod,orderedSplit_card 2 2 4 rfl]; norm_num [Nat.choose]

private theorem typeA_transpose (σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3))) :
    TypeA (entry (transpose σ)) ↔ TypeB (entry σ) := by
  exact Eq.to_iff rfl

private noncomputable def typeABEquiv : {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // TypeA (entry σ)} ≃
    {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // TypeB (entry σ)} where
  toFun σ := ⟨transpose σ.val,(typeA_transpose (transpose σ.val)).mp
    (by change TypeA (entry σ.val); exact σ.property)⟩
  invFun σ := ⟨transpose σ.val,(typeA_transpose σ.val).mpr σ.property⟩
  left_inv σ := Subtype.ext (show transpose (transpose σ.val) = σ.val from Equiv.coe_inj.mp rfl)
  right_inv σ := Subtype.ext (show transpose (transpose σ.val) = σ.val from Equiv.coe_inj.mp rfl)

private theorem typeB_card : Nat.card {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // TypeB (entry σ)} = 36 := by
  rw [← Nat.card_congr typeABEquiv,typeA_card]

private theorem types_disjoint (σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3))) (ha : TypeA (entry σ)) (hb : TypeB (entry σ)) : False := by
  simp [TypeA,TypeB,List.pairwise_cons] at ha hb
  omega

private noncomputable def typesGoodEquiv :
    ({σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // TypeA (entry σ)} ⊕ {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // TypeB (entry σ)}) ≃
      {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // Good σ} := by
  let f : ({σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // TypeA (entry σ)} ⊕ {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // TypeB (entry σ)}) →
      {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // Good σ}
    | Sum.inl σ => ⟨σ.val,(three_good_iff σ.val).mpr (Or.inl σ.property)⟩
    | Sum.inr σ => ⟨σ.val,(three_good_iff σ.val).mpr (Or.inr σ.property)⟩
  apply Equiv.ofBijective f
  constructor
  · rintro (σ | σ) (τ | τ) h
    · have heq : σ.val=τ.val := congrArg (fun p : {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // Good σ} => p.val) h
      exact congrArg Sum.inl (Subtype.ext heq)
    · have heq : σ.val=τ.val := congrArg (fun p : {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // Good σ} => p.val) h
      exact (types_disjoint σ.val σ.property (heq.symm ▸ τ.property)).elim
    · have heq : σ.val=τ.val := congrArg (fun p : {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // Good σ} => p.val) h
      exact (types_disjoint τ.val τ.property (heq ▸ σ.property)).elim
    · have heq : σ.val=τ.val := congrArg (fun p : {σ : ((Fin 3 × Fin 3) ≃ Fin (3 * 3)) // Good σ} => p.val) h
      exact congrArg Sum.inr (Subtype.ext heq)
  · intro σ
    rcases (three_good_iff σ.val).mp σ.property with ha | hb
    · exact ⟨Sum.inl ⟨σ.val,ha⟩,rfl⟩
    · exact ⟨Sum.inr ⟨σ.val,hb⟩,rfl⟩

private theorem count_three : goodCount 3 3 = 72 := by
  unfold goodCount
  rw [← Nat.card_congr typesGoodEquiv,Nat.card_sum,typeA_card,typeB_card]

end D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

namespace D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

private theorem count_formula (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    goodCount m n = proposedCount m n := by
  by_cases hm1 : m=1
  · subst m
    rw [count_one]
    simp [proposedCount,min_eq_left (by omega : 1 ≤ n),max_eq_right (by omega : 1 ≤ n)]
  by_cases hn1 : n=1
  · subst n
    rw [count_transpose,count_one]
    simp [proposedCount,min_eq_right (by omega : 1 ≤ m),max_eq_left (by omega : 1 ≤ m)]
  by_cases hm2 : m=2
  · subst m
    rw [count_two n hn]
    simp [proposedCount,min_eq_left (by omega : 2 ≤ n),max_eq_right (by omega : 2 ≤ n)]
  by_cases hn2 : n=2
  · subst n
    rw [count_transpose,count_two m hm]
    simp [proposedCount,min_eq_right (by omega : 2 ≤ m),max_eq_left (by omega : 2 ≤ m)]
  have hmin1 : min m n ≠ 1 := by omega
  have hmin2 : min m n ≠ 2 := by omega
  simp only [proposedCount,ite_eq_right hmin1,ite_eq_right hmin2]
  by_cases h33 : m=3 ∧ n=3
  · rcases h33 with ⟨rfl,rfl⟩
    simpa using count_three
  · rw [ite_eq_right h33]
    by_cases hn4 : 4 ≤ n
    · exact count_large m n (by omega) hn4
    · rw [count_transpose]
      exact count_large n m (by omega) (by omega)

theorem result : D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount.claim := by
  intro m n hm hn
  exact ⟨count_formula m n hm hn,fun σ => good_iff_structure σ hm hn⟩

end D5.S3.Combinatorics.Permutation.OnnGoodPermutationCount

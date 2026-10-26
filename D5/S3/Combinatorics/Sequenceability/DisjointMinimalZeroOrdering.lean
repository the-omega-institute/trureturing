/- GID: D5/S3/Combinatorics/Sequenceability/DisjointMinimalZeroOrdering
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/DisjointMinimalZeroOrdering
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Order.Minimal]
   utility: none
   digest: Disjoint minimal zero decompositions and original-occurrence Good orders. -/

import D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
import Mathlib.Data.List.FinRange
import Mathlib.Order.Minimal

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering
open scoped Classical BigOperators
open D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum (Good)
universe u v
variable {α : Type u} {G : Type v} [AddCommGroup G]

/-- Inclusion minimal among the nonempty coefficient-one zero supports. -/
def MinimalZeroSupport (f : α → G) (B : Finset α) : Prop :=
  B.Nonempty ∧ (∑ x ∈ B, f x) = 0 ∧
    ∀ C : Finset α, C ⊆ B → C.Nonempty → (∑ x ∈ C, f x) = 0 → C = B

private lemma interval_membership {w : List α} (hn : w.Nodup)
    {i j p : ℕ} (hij : i ≤ j) (hj : j ≤ w.length) (hp : p < w.length) :
    w[p] ∈ (w.drop i).take (j-i) ↔ i ≤ p ∧ p < j := by
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := List.mem_take_iff_getElem.mp h
    have hqi : i + q < w.length := by simp only [List.length_drop] at hq; omega
    rw [List.getElem_drop] at he
    have heq : i + q = p := hn.getElem_inj_iff.mp he
    omega
  · intro h
    apply List.mem_take_iff_getElem.mpr
    refine ⟨p-i, by simp only [List.length_drop]; omega, ?_⟩
    simp only [List.getElem_drop]
    congr 1
    omega

/-- Equal-order endpoint pairs prevent a nonempty pair-closed proper interval. -/
private lemma interlaced_interval {k : ℕ} (a b : Fin k → α) (M : List α)
    (hn : (List.ofFn a ++ M ++ List.ofFn b).Nodup)
    {i j : ℕ} (hij : i < j)
    (hj : j ≤ (List.ofFn a ++ M ++ List.ofFn b).length)
    (hc : ∀ t, a t ∈ ((List.ofFn a ++ M ++ List.ofFn b).drop i).take (j-i) ↔
      b t ∈ ((List.ofFn a ++ M ++ List.ofFn b).drop i).take (j-i))
    (he : ∃ t, a t ∈ ((List.ofFn a ++ M ++ List.ofFn b).drop i).take (j-i)) :
    i = 0 ∧ j = (List.ofFn a ++ M ++ List.ofFn b).length := by
  let w := List.ofFn a ++ M ++ List.ofFn b
  have hlen : w.length = k + M.length + k := by simp [w, Nat.add_assoc]
  have ha (t : Fin k) : w[t.val]'(by rw [hlen]; omega) = a t := by
    dsimp [w]
    rw [List.getElem_append_left (by simp only [List.length_append, List.length_ofFn]; omega),
      List.getElem_append_left (by simpa using t.isLt), List.getElem_ofFn]
  have hb (t : Fin k) : w[k + M.length + t.val]'(by rw [hlen]; omega) = b t := by
    dsimp [w]
    rw [List.getElem_append_right (by simp)]
    simp
  have hA (t : Fin k) : a t ∈ (w.drop i).take (j-i) ↔ i ≤ t.val ∧ t.val < j := by
    rw [← ha t]
    exact interval_membership hn hij.le hj (by rw [hlen]; omega)
  have hB (t : Fin k) : b t ∈ (w.drop i).take (j-i) ↔
      i ≤ k + M.length + t.val ∧ k + M.length + t.val < j := by
    rw [← hb t]
    exact interval_membership hn hij.le hj (by rw [hlen]; omega)
  obtain ⟨t,ht⟩ := he
  have htA := (hA t).mp ht
  have htB := (hB t).mp ((hc t).mp ht)
  have hk : 0 < k := by omega
  have hzero : a ⟨0,hk⟩ ∈ (w.drop i).take (j-i) := by
    apply (hc _).mpr
    apply (hB _).mpr
    change i ≤ k + M.length + 0 ∧ k + M.length + 0 < j
    constructor <;> omega
  have hlast : b ⟨k-1,by omega⟩ ∈ (w.drop i).take (j-i) := by
    apply (hc _).mp
    apply (hA _).mpr
    change i ≤ k - 1 ∧ k - 1 < j
    constructor <;> omega
  have hz := (hA _).mp hzero
  have hl := (hB _).mp hlast
  change i ≤ 0 ∧ 0 < j at hz
  change i ≤ k + M.length + (k-1) ∧ k + M.length + (k-1) < j at hl
  change i = 0 ∧ j = w.length
  rw [hlen] at hj ⊢
  constructor <;> omega

/-- Every coefficient-one zero support is a disjoint union of inclusion-minimal
nonempty zero supports, without any disjointness assumption on all minimal supports. -/
theorem zero_decomposition_pairwise_disjoint (f : α → G) (X C : Finset α)
    (hCX : C ⊆ X) (hz : (∑ x ∈ C, f x) = 0) :
    ∃ Q : Finset (Finset α),
      (∀ B ∈ Q, B ⊆ X ∧ MinimalZeroSupport f B) ∧
      Set.PairwiseDisjoint (Q : Set (Finset α)) id ∧ C = Q.biUnion id := by
  classical
  revert hCX hz
  refine Finset.strongInductionOn C ?_
  intro C ih hCX hz
  by_cases hC : C = ∅
  · subst C
    exact ⟨∅, by simp, by simp, by simp⟩
  have hne : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hC
  obtain ⟨B, hBC, hB⟩ := exists_minimal_le_of_wellFoundedLT
    (fun B : Finset α => B.Nonempty ∧ (∑ x ∈ B, f x) = 0) C ⟨hne, hz⟩
  have hmin : MinimalZeroSupport f B := by
    refine ⟨hB.1.1, hB.1.2, ?_⟩
    intro D hDB hDn hDz
    exact hDB.antisymm (hB.2 ⟨hDn, hDz⟩ hDB)
  have hproper : C \ B ⊂ C := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset, ?_⟩
    intro he
    obtain ⟨x, hx⟩ := hB.1.1
    exact (Finset.mem_sdiff.mp (he.symm ▸ hBC hx)).2 hx
  have hrem : (∑ x ∈ C \ B, f x) = 0 := by
    rw [Finset.sum_sdiff_eq_sub hBC, hz, hB.1.2, sub_self]
  obtain ⟨Q, hQ, hdis, hcover⟩ :=
    ih (C \ B) hproper (Finset.sdiff_subset.trans hCX) hrem
  have hQrem {D : Finset α} (hD : D ∈ Q) : D ⊆ C \ B := by
    intro x hx
    rw [hcover]
    exact Finset.mem_biUnion.mpr ⟨D, hD, hx⟩
  have hBdis {D : Finset α} (hD : D ∈ Q) : Disjoint B D := by
    apply Finset.disjoint_left.mpr
    intro x hxB hxD
    exact (Finset.mem_sdiff.mp (hQrem hD hxD)).2 hxB
  refine ⟨insert B Q, ?_, ?_, ?_⟩
  · intro D hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact ⟨hBC.trans hCX, hmin⟩
    · exact hQ D hD
  · intro D hD E hE hDE
    change Disjoint D E
    rcases Finset.mem_insert.mp hD with hDB | hDQ
    · rcases Finset.mem_insert.mp hE with hEB | hEQ
      · exact (hDE (hDB.trans hEB.symm)).elim
      · rw [hDB]
        exact hBdis hEQ
    · rcases Finset.mem_insert.mp hE with hEB | hEQ
      · rw [hEB]
        exact (hBdis hDQ).symm
      · exact hdis hDQ hEQ hDE
  · rw [Finset.biUnion_insert, ← hcover]
    exact (Finset.union_sdiff_of_subset hBC).symm


lemma zero_decomposition (f : α → G) (X C : Finset α)
    (hCX : C ⊆ X) (hz : (∑ x ∈ C, f x) = 0) :
    ∃ Q : Finset (Finset α),
      (∀ B ∈ Q, B ⊆ X ∧ MinimalZeroSupport f B) ∧ C = Q.biUnion id := by
  obtain ⟨Q, hQ, _, hcover⟩ := zero_decomposition_pairwise_disjoint f X C hCX hz
  exact ⟨Q, hQ, hcover⟩

/-- A constructor with no assumed Good intermediate order. Blocks need not cover X;
every nonempty zero support must be a union of complete disjoint blocks. -/
theorem good_order_of_disjoint_zero_blocks (X : Finset α) (f : α → G)
    (P : Finset (Finset α))
    (hsub : ∀ B ∈ P, B ⊆ X)
    (hsize : ∀ B ∈ P, 2 ≤ B.card)
    (hdis : ∀ B ∈ P, ∀ D ∈ P, B ≠ D → Disjoint B D)
    (hzero : ∀ C : Finset α, C ⊆ X → C.Nonempty → (∑ x ∈ C, f x) = 0 →
      ∃ Q : Finset (Finset α), Q ⊆ P ∧ C = Q.biUnion id) :
    ∃ w : List α, w.Perm X.toList ∧ Good (w.map f) := by
  classical
  let k := P.toList.length
  let B : Fin k → Finset α := P.toList.get
  have hBP (t : Fin k) : B t ∈ P := Finset.mem_toList.mp (List.get_mem _ _)
  have hBi : Function.Injective B := List.nodup_iff_injective_get.mp P.nodup_toList
  have hBe (D : Finset α) (hD : D ∈ P) : ∃ t, B t = D :=
    List.mem_iff_get.mp (Finset.mem_toList.mpr hD)
  have hpick (t : Fin k) : ∃ x ∈ B t, ∃ y ∈ B t, x ≠ y :=
    Finset.one_lt_card.mp (by have := hsize (B t) (hBP t); omega)
  choose a ha b hb hab using hpick
  have same {D E : Finset α} (hD : D ∈ P) (hE : E ∈ P)
      {x : α} (hxD : x ∈ D) (hxE : x ∈ E) : D = E := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdis D hD E hE hne) hxD hxE
  have hai : Function.Injective a := by
    intro t s he
    exact hBi (same (hBP t) (hBP s) (ha t) (he.symm ▸ ha s))
  have hbi : Function.Injective b := by
    intro t s he
    exact hBi (same (hBP t) (hBP s) (hb t) (he.symm ▸ hb s))
  have haball (t s : Fin k) : a t ≠ b s := by
    intro he
    have hts := hBi (same (hBP t) (hBP s) (ha t) (he.symm ▸ hb s))
    subst s
    exact hab t he
  let A := (List.ofFn a).toFinset
  let T := (List.ofFn b).toFinset
  let M := (X \ (A ∪ T)).toList
  let w := List.ofFn a ++ M ++ List.ofFn b
  have hAX : A ⊆ X := by
    intro x hx
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hx)
    exact hsub (B t) (hBP t) (ha t)
  have hTX : T ⊆ X := by
    intro x hx
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hx)
    exact hsub (B t) (hBP t) (hb t)
  have hnd : w.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨?_, List.nodup_ofFn.mpr hbi, ?_⟩
    · apply List.nodup_append.mpr
      refine ⟨List.nodup_ofFn.mpr hai, Finset.nodup_toList _, ?_⟩
      intro x hx y hy he
      subst y
      exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hy)).2
        (Finset.mem_union_left T (List.mem_toFinset.mpr hx))
    · intro x hx y hy he
      subst y
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hx
        obtain ⟨s,he⟩ := List.mem_ofFn.mp hy
        exact haball t s he.symm
      · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).2
          (Finset.mem_union_right A (List.mem_toFinset.mpr hy))
  have hp : w.Perm X.toList := by
    apply (List.perm_ext_iff_of_nodup hnd X.nodup_toList).mpr
    intro x
    simp only [w, List.mem_append, Finset.mem_toList, M, Finset.mem_sdiff,
      Finset.mem_union]
    change (x ∈ List.ofFn a ∨ (x ∈ X ∧ ¬ (x ∈ A ∨ x ∈ T))) ∨
      x ∈ List.ofFn b ↔ x ∈ X
    have hA : x ∈ List.ofFn a ↔ x ∈ A := List.mem_toFinset.symm
    have hT : x ∈ List.ofFn b ↔ x ∈ T := List.mem_toFinset.symm
    rw [hA,hT]
    constructor
    · rintro ((hx | hx) | hx)
      · exact hAX hx
      · exact hx.1
      · exact hTX hx
    · intro hx
      by_cases hxa : x ∈ A
      · exact Or.inl (Or.inl hxa)
      by_cases hxt : x ∈ T
      · exact Or.inr hxt
      · exact Or.inl (Or.inr ⟨hx, by simp [hxa,hxt]⟩)
  refine ⟨w,hp,?_⟩
  intro i j hij hj hproper hz
  have hjw : j ≤ w.length := by simpa using hj
  let u := (w.drop i).take (j-i)
  have hund : u.Nodup := hnd.drop.take
  have hune : u ≠ [] := by
    apply List.length_pos_iff.mp
    simp only [u,List.length_take,List.length_drop]
    omega
  have huX : u.toFinset ⊆ X := by
    intro x hx
    exact Finset.mem_toList.mp (hp.mem_iff.mp
      (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_toFinset.mp hx))))
  have husum : (∑ x ∈ u.toFinset, f x) = 0 := by
    rw [List.sum_toFinset f hund]
    simpa only [u,List.map_take,List.map_drop] using hz
  obtain ⟨Q,hQP,hcover⟩ := hzero u.toFinset huX
    (by simpa using (List.toFinset_nonempty_iff u).mpr hune) husum
  have sat {x : α} (hx : x ∈ u) : ∃ D ∈ P, x ∈ D ∧ D ⊆ u.toFinset := by
    have hx' : x ∈ Q.biUnion id := hcover ▸ List.mem_toFinset.mpr hx
    obtain ⟨D,hDQ,hxD⟩ := Finset.mem_biUnion.mp hx'
    exact ⟨D,hQP hDQ,hxD,fun y hy => hcover.symm ▸
      Finset.mem_biUnion.mpr ⟨D,hDQ,hy⟩⟩
  have closed (t : Fin k) : a t ∈ u ↔ b t ∈ u := by
    constructor
    · intro ht
      obtain ⟨D,hDP,hxD,hDu⟩ := sat ht
      have he := same (hBP t) hDP (ha t) hxD
      exact List.mem_toFinset.mp (hDu (he ▸ hb t))
    · intro ht
      obtain ⟨D,hDP,hxD,hDu⟩ := sat ht
      have he := same (hBP t) hDP (hb t) hxD
      exact List.mem_toFinset.mp (hDu (he ▸ ha t))
  have hex : ∃ t, a t ∈ u := by
    obtain ⟨x,hxu⟩ := List.exists_mem_of_ne_nil u hune
    obtain ⟨D,hDP,_,hDu⟩ := sat hxu
    obtain ⟨t,rfl⟩ := hBe D hDP
    exact ⟨t,List.mem_toFinset.mp (hDu (ha t))⟩
  obtain ⟨hi0,hjl⟩ := interlaced_interval a b M hnd hij hjw closed hex
  have hproper' : i ≠ 0 ∨ j ≠ w.length := by simpa using hproper
  exact hproper'.elim (fun h => h hi0) (fun h => h hjl)

/-- Pairwise disjoint inclusion-minimal nonempty zero supports suffice in every
additive commutative group. The returned permutation is on original indices. -/
theorem good_order_of_disjoint_minimal_zero_supports (X : Finset α) (f : α → G)
    (hnonzero : ∀ x ∈ X, f x ≠ 0)
    (hdis : ∀ B : Finset α, B ⊆ X → MinimalZeroSupport f B →
      ∀ D : Finset α, D ⊆ X → MinimalZeroSupport f D → B ≠ D → Disjoint B D) :
    ∃ w : List α, w.Perm X.toList ∧ Good (w.map f) := by
  classical
  let P := X.powerset.filter (MinimalZeroSupport f)
  have hmem (B : Finset α) : B ∈ P ↔ B ⊆ X ∧ MinimalZeroSupport f B := by
    simp [P]
  apply good_order_of_disjoint_zero_blocks X f P
  · intro B hB
    exact ((hmem B).mp hB).1
  · intro B hB
    obtain ⟨hBX,hBn,hBz,_⟩ := (hmem B).mp hB
    by_contra hn
    have hcard : B.card = 1 := by have := hBn.card_pos; omega
    obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hcard
    exact hnonzero x (hBX (Finset.mem_singleton_self _)) (by simpa using hBz)
  · intro B hB D hD hne
    exact hdis B ((hmem B).mp hB).1 ((hmem B).mp hB).2
      D ((hmem D).mp hD).1 ((hmem D).mp hD).2 hne
  · intro C hCX hCn hCz
    obtain ⟨Q,hQ,hcover⟩ := zero_decomposition f X C hCX hCz
    exact ⟨Q,fun B hB => (hmem B).mpr (hQ B hB),hcover⟩

end D5.S3.Combinatorics.Sequenceability.DisjointMinimalZeroOrdering

/- GID: D5/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity
   generality: G
   mirror - B: D5/B/S3/Arith/FibonacciAtomic/FourMessageTreeRigidity
   mirror - E: none(waiver:unbounded - symbolic - proof)
   anchors: []
   utility: none
   digest: Four - message window computation forces complementary peeling spines. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import D5.S3.Arith.FibonacciAtomic.TreeMessageRealization

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FourMessageTreeRigidity

open TreeMessageRealization
open FirstRejectionCutCapacity
  (interval boolean d epsilon crossings internals Cross Internal left right)
open LiteralWindowEnd (Window)
open D5.S3.Observer.Separation.SurjectiveColumnSharpWidth (capacity)

/-- Global proper prefixes, global proper suffixes, and internal singleton blocks. -/
def SmallBlock {k : ℕ} (A : Finset (Fin (k + 1))) : Prop :=
  (∃ j, 0 < j ∧ j < k + 1 ∧ A = interval k 0 j) ∨
  (∃ j, 0 < j ∧ j < k + 1 ∧ A = interval k j (k + 1)) ∨
  (∃ i : Fin (k + 1), 0 < i.val ∧ i.val < k ∧ A = {i})

/-- A prefix spine peels its highest remaining coordinate at each fork.
The two constructors allow the actual children to be exchanged independently. -/
inductive PrefixSpine (k : ℕ) : ℕ → TreeMessageRealization.Tree (Fin (k + 1)) → Prop
  | one : PrefixSpine k 1 (leaf ⟨0, Nat.zero_lt_succ k⟩)
  | peel {j : ℕ} {t : TreeMessageRealization.Tree (Fin (k + 1))} (hj : j < k + 1)
      (h : PrefixSpine k j t) : PrefixSpine k (j + 1) (fork t (leaf ⟨j,hj⟩))
  | peel_swap {j : ℕ} {t : TreeMessageRealization.Tree (Fin (k + 1))} (hj : j < k + 1)
      (h : PrefixSpine k j t) : PrefixSpine k (j + 1) (fork (leaf ⟨j,hj⟩) t)

/-- A suffix spine peels its lowest remaining coordinate at each fork. -/
inductive SuffixSpine (k : ℕ) : ℕ → TreeMessageRealization.Tree (Fin (k + 1)) → Prop
  | one : SuffixSpine k k (leaf (Fin.last k))
  | peel {j : ℕ} {t : TreeMessageRealization.Tree (Fin (k + 1))} (hj : j < k)
      (h : SuffixSpine k (j + 1) t) : SuffixSpine k j (fork (leaf ⟨j,by omega⟩) t)
  | peel_swap {j : ℕ} {t : TreeMessageRealization.Tree (Fin (k + 1))} (hj : j < k)
      (h : SuffixSpine k (j + 1) t) : SuffixSpine k j (fork t (leaf ⟨j,by omega⟩))

/-- Exact child - swap freedom at all forks is built into the two spine predicates. -/
def DoubleComb {k : ℕ} (t : TreeMessageRealization.Tree (Fin (k + 1))) : Prop :=
  ∃ j, 0 < j ∧ j < k + 1 ∧ ∃ l r, PrefixSpine k j l ∧ SuffixSpine k j r ∧
    (t = fork l r ∨ t = fork r l)

private theorem classify (k : ℕ) (hk : 2 ≤ k) (A : Finset (Fin (k + 1))) (hA : A.Nonempty) (hproper : A ≠ Finset.univ)
    (hwidth : capacity (fun _ => Window) boolean (fun i => i ∈ A) ≤ 4) :
    SmallBlock A := by
  classical
  let z : Fin (k + 1) := ⟨0, by omega⟩
  have mem_interval (a b : ℕ) (i : Fin (k + 1)) :
      i ∈ interval k a b ↔ a ≤ i.val ∧ i.val < b := by simp [interval]
  rw [(FirstRejectionCutCapacity.result k A).2.2.2.2.2.2.2.2.1] at hwidth
  have hd : d A ≤ 2 := by
    apply (pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp
    norm_num
    omega
  by_cases heps : Fin.last k ∈ A ∨ (internals A).Nonempty
  · have hd1 : d A ≤ 1 := by
      have hp : (2:ℕ)^d A ≤ 2 := by
        have h := hwidth
        simp only [epsilon, if_pos heps] at h
        interval_cases hda : d A <;> norm_num [hda] at *
      simpa using (pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp hp
    have unique : ∀ a ∈ crossings A, ∀ b ∈ crossings A, a = b :=
      Finset.card_le_one.mp hd1
    have crosses : (crossings A).Nonempty := by
      by_contra hn
      have no : ∀ i : Fin k, ¬ Cross A i := by
        intro i hi
        exact hn ⟨i,by simp [crossings,hi]⟩
      have constant (j : ℕ) (hj : j ≤ k) :
          (⟨j,by omega⟩ : Fin (k + 1)) ∈ A ↔ z ∈ A := by
        induction j with
        | zero => rfl
        | succ j ih =>
          have h := no ⟨j,by omega⟩
          have prev := ih (by omega)
          simp only [Cross,left,right,Fin.castSucc_mk,Fin.succ_mk] at h
          tauto
      obtain ⟨i,hi⟩ := hA
      have hz : z ∈ A := (constant i.val (by omega)).mp hi
      apply hproper
      apply Finset.eq_univ_of_forall
      intro j
      exact (constant j.val (by omega)).mpr hz
    obtain ⟨edge, hedge⟩ := crosses
    have boundary : Cross A edge := by simpa [crossings] using hedge
    have pattern (j : ℕ) (hj : j ≤ k) :
        (⟨j,by omega⟩ : Fin (k + 1)) ∈ A ↔ (j ≤ edge.val ↔ z ∈ A) := by
      induction j with
      | zero => simp [z]
      | succ j ih =>
        have prev := ih (by omega)
        by_cases je : j = edge.val
        · have ee : (⟨j,by omega⟩ : Fin k) = edge := Fin.ext je
          have hc := boundary
          rw [← ee] at hc
          simp only [Cross,left,right,Fin.castSucc_mk,Fin.succ_mk] at hc
          have hjle : j ≤ edge.val := by omega
          have hjnle : ¬ j + 1 ≤ edge.val := by omega
          simp only [hjle,true_iff] at prev
          simp only [hjnle,false_iff]
          tauto
        · have nc : ¬ Cross A ⟨j,by omega⟩ := by
            intro hc
            have eq := unique (⟨j,by omega⟩ : Fin k) (by simp [crossings,hc]) edge hedge
            exact je (congrArg Fin.val eq)
          simp only [Cross,left,right,Fin.castSucc_mk,Fin.succ_mk] at nc
          have step : (j + 1 ≤ edge.val) = (j ≤ edge.val) := by
            apply propext; omega
          rw [step]
          tauto
    by_cases hz : z ∈ A
    · left
      refine ⟨edge.val + 1,by omega,by omega,?_⟩
      ext i
      rw [mem_interval]
      have h : i ∈ A ↔ i.val ≤ edge.val := by
        simpa only [hz,iff_true] using pattern i.val (by omega)
      rw [h]
      omega
    · right; left
      refine ⟨edge.val + 1,by omega,by omega,?_⟩
      ext i
      rw [mem_interval]
      have h : i ∈ A ↔ ¬ i.val ≤ edge.val := by
        simpa only [hz,iff_false] using pattern i.val (by omega)
      rw [h]
      omega
  · have hlast : Fin.last k ∉ A := fun h => heps (Or.inl h)
    have nointernal : ∀ i : Fin k, ¬ Internal A i := by
      intro i hi
      exact heps (Or.inr ⟨i,by simp [internals,hi]⟩)
    have below (i : Fin (k + 1)) (hi : i ∈ A) : i.val < k := by
      by_contra hn
      have ie : i = Fin.last k := Fin.ext (by simp; omega)
      exact hlast (ie ▸ hi)
    have single : ∀ a ∈ A, ∀ b ∈ A, a = b := by
      intro a ha b hb
      by_contra hab
      wlog hlt : a.val < b.val generalizing a b
      · exact this b hb a ha (Ne.symm hab) (by
          have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)
          omega)
      have hak := below a ha
      have hbk := below b hb
      let x : Fin k := ⟨a.val,hak⟩
      let y : Fin k := ⟨b.val - 1,by omega⟩
      let q : Fin k := ⟨b.val,hbk⟩
      have ax : left x = a := Fin.ext rfl
      have bq : left q = b := Fin.ext rfl
      have by' : right y = b := Fin.ext (by dsimp [y,right]; omega)
      have nx : right x ∉ A := fun h => nointernal x ⟨ax ▸ ha,h⟩
      have nq : right q ∉ A := fun h => nointernal q ⟨bq ▸ hb,h⟩
      have ny : left y ∉ A := fun h => nointernal y ⟨h,by' ▸ hb⟩
      have xcross : x ∈ crossings A := by simp [crossings,Cross,ax,ha,nx]
      have ycross : y ∈ crossings A := by simp [crossings,Cross,by',hb,ny]
      have qcross : q ∈ crossings A := by simp [crossings,Cross,bq,hb,nq]
      have gap : a.val + 1 < b.val := by
        by_contra hn
        have xe : right x = b := Fin.ext (by dsimp [x,right]; omega)
        exact nx (xe ▸ hb)
      have xne : x ≠ y := by intro h; have := congrArg Fin.val h; dsimp [x,y] at this; omega
      have xq : x ≠ q := by intro h; have := congrArg Fin.val h; dsimp [x,q] at this; omega
      have yq : y ≠ q := by intro h; have := congrArg Fin.val h; dsimp [y,q] at this; omega
      have ht := Finset.two_lt_card_iff.mpr
        ⟨x,y,q,xcross,ycross,qcross,xne,xq,yq⟩
      change 2 < d A at ht
      omega
    obtain ⟨i,hi⟩ := hA
    have eq : A = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi,fun j hj => single j hj i hi⟩
    by_cases hz : i.val = 0
    · left
      refine ⟨1,by omega,by omega,?_⟩
      rw [eq]
      ext j
      rw [mem_interval,Finset.mem_singleton]
      constructor
      · intro h; subst j; omega
      · intro h; apply Fin.ext; omega
    · right; right
      exact ⟨i,by omega,below i hi,eq⟩

set_option maxHeartbeats 2000000 in
-- Capacity classification and the two spine inductions are elaborated in one proof.
/-- Arbitrary leaf - labelled full binary trees whose proper blocks are small
have precisely the two peeling spines, with independent child exchanges. -/
theorem rigidity_from_implementation (k : ℕ) (hk : 2 ≤ k)
    (t : TreeMessageRealization.Tree (Fin (k + 1))) (ht : Full t)
    (hall : leaves t = Finset.univ)
    (m : Implementation (fun _ : Fin (k + 1) => Window))
    (read : m.Message t → Bool) (hm : Correct boolean t m read) (hp : peak m t ≤ 4) :
    ∃ j, 0 < j ∧ j < k + 1 ∧ ∃ l r, PrefixSpine k j l ∧ SuffixSpine k j r ∧
      (t = fork l r ∨ t = fork r l) ∧ height t = max j (k + 1 - j) ∧ (k + 2) / 2 ≤ height t := by
  classical
  have : Nonempty Window := ⟨.middle⟩
  have hcap : ∀ s ∈ subtrees t, s ≠ t →
      capacity (fun _ => Window) boolean (fun i => i ∈ leaves s) ≤ 4 := by
    intro s hs _
    exact (implementation_lower_bound boolean t ht m read hm s hs).trans
      ((Finset.le_sup hs).trans hp)
  let z : Fin (k + 1) := ⟨0, by omega⟩
  let e : Fin (k + 1) := Fin.last k
  have mem_interval (a b : ℕ) (i : Fin (k + 1)) :
      i ∈ interval k a b ↔ a ≤ i.val ∧ i.val < b := by simp [interval]
  have nonempty (u : TreeMessageRealization.Tree (Fin (k + 1))) (hu : Full u) :
      (leaves u).Nonempty := by
    induction u with
    | nil => simp [Full] at hu
    | node a l r hl hr =>
      cases a with
      | some i => exact ⟨i, by simp [leaves]⟩
      | none =>
        obtain ⟨i,hi⟩ := hl hu.1
        exact ⟨i, by simp [leaves, hi]⟩
  have proper_subtree (u : TreeMessageRealization.Tree (Fin (k + 1))) (hu : Full u)
      (s : TreeMessageRealization.Tree (Fin (k + 1))) (hs : s ∈ subtrees u)
      (hne : s ≠ u) : leaves s ≠ leaves u := by
    intro he
    induction u with
    | nil => simp [Full] at hu
    | node a l r hl hr =>
      cases a with
      | some i =>
        have hs' : s = .node (some i) l r := by simpa [subtrees] using hs
        exact hne hs'
      | none =>
        simp only [subtrees,Finset.mem_insert,Finset.mem_union] at hs
        rcases hs with hs | hs | hs
        · exact hne hs
        · obtain ⟨i,hi⟩ := nonempty r hu.2.1
          have hm : i ∈ leaves s := by rw [he]; simp [leaves,hi]
          exact Finset.disjoint_left.mp hu.2.2 ((subtree_structure l hu.1 s hs).2 hm) hi
        · obtain ⟨i,hi⟩ := nonempty l hu.1
          have hm : i ∈ leaves s := by rw [he]; simp [leaves,hi]
          exact Finset.disjoint_left.mp hu.2.2 hi ((subtree_structure r hu.2.1 s hs).2 hm)
  have hsmall : ∀ s ∈ subtrees t, s ≠ t → SmallBlock (leaves s) := by
    intro s hs hne
    apply classify k hk _ (nonempty s (subtree_structure t ht s hs).1)
    · rw [← hall]
      exact proper_subtree t ht s hs hne
    · exact hcap s hs hne
  have self (u : TreeMessageRealization.Tree (Fin (k + 1))) (hu : Full u) : u ∈ subtrees u := by
    cases u with
    | nil => simp [Full] at hu
    | node a l r => cases a <;> simp [subtrees]
  have single (u : TreeMessageRealization.Tree (Fin (k + 1))) (hu : Full u)
      (i : Fin (k + 1)) (hi : leaves u = {i}) : u = leaf i := by
    cases u with
    | nil => simp [Full] at hu
    | node a l r =>
      cases a with
      | some j =>
        obtain ⟨rfl,rfl⟩ := hu
        have he : j = i := by simpa [leaves] using hi
        subst j
        rfl
      | none =>
        obtain ⟨a,ha⟩ := nonempty l hu.1
        obtain ⟨b,hb⟩ := nonempty r hu.2.1
        have ha' : a = i := by
          have : a ∈ leaves (.node none l r) := by simp [leaves, ha]
          simpa [hi] using this
        have hb' : b = i := by
          have : b ∈ leaves (.node none l r) := by simp [leaves, hb]
          simpa [hi] using this
        subst a; subst b
        exact False.elim (Finset.disjoint_left.mp hu.2.2 ha hb)
  have small_endpoints (A : Finset (Fin (k + 1))) (hA : SmallBlock A) :
      ¬ (z ∈ A ∧ e ∈ A) := by
    rcases hA with ⟨j,hj,hjn,rfl⟩ | ⟨j,hj,hjn,rfl⟩ | ⟨i,hi,hik,rfl⟩
    · simp only [mem_interval] at *
      dsimp [e]
      omega
    · simp only [mem_interval] at *
      dsimp [z]
      omega
    · intro h
      have hz : z = i := Finset.mem_singleton.mp h.1
      have he : e = i := Finset.mem_singleton.mp h.2
      have := congrArg Fin.val hz
      dsimp [z] at this
      omega
  have prefix_at_zero (A : Finset (Fin (k + 1))) (hA : SmallBlock A)
      (hz : z ∈ A) (he : e ∉ A) : ∃ a, 0 < a ∧ a < k + 1 ∧ A = interval k 0 a := by
    rcases hA with h | ⟨a,ha,han,rfl⟩ | ⟨i,hi,hik,rfl⟩
    · exact h
    · have := (mem_interval a (k + 1) z).mp hz
      dsimp [z] at this
      omega
    · have := congrArg Fin.val (Finset.mem_singleton.mp hz)
      dsimp [z] at this
      omega
  have suffix_at_end (A : Finset (Fin (k + 1))) (hA : SmallBlock A)
      (he : e ∈ A) (hz : z ∉ A) : ∃ a, 0 < a ∧ a < k + 1 ∧ A = interval k a (k + 1) := by
    rcases hA with ⟨a,ha,han,rfl⟩ | h | ⟨i,hi,hik,rfl⟩
    · have := (mem_interval 0 a e).mp he
      dsimp [e] at this
      omega
    · exact h
    · have := congrArg Fin.val (Finset.mem_singleton.mp he)
      dsimp [e] at this
      omega
  have internal_only (A : Finset (Fin (k + 1))) (hA : SmallBlock A)
      (hz : z ∉ A) (he : e ∉ A) : ∃ i : Fin (k + 1), 0 < i.val ∧ i.val < k ∧ A = {i} := by
    rcases hA with ⟨a,ha,han,rfl⟩ | ⟨a,ha,han,rfl⟩ | h
    · apply False.elim; apply hz
      apply (mem_interval _ _ _).mpr
      dsimp [z]; omega
    · apply False.elim; apply he
      apply (mem_interval _ _ _).mpr
      dsimp [e]; omega
    · exact h
  have prefix_ordered (A B : Finset (Fin (k + 1))) (j : ℕ)
      (hj : 0 < j) (hjn : j < k + 1) (hdis : Disjoint A B)
      (hu : A ∪ B = interval k 0 j) (hA : SmallBlock A) (hB : SmallBlock B)
      (hz : z ∈ A) :
      ∃ (a : ℕ) (ha : a < k + 1), j = a + 1 ∧
        A = interval k 0 a ∧ B = {⟨a,ha⟩} ∧ 0 < a := by
    have noend : e ∉ A ∧ e ∉ B := by
      have hn : e ∉ A ∪ B := by rw [hu, mem_interval]; dsimp [e]; omega
      simpa using hn
    obtain ⟨a,ha,han,hAe⟩ := prefix_at_zero A hA hz noend.1
    have hBz : z ∉ B := fun h => Finset.disjoint_left.mp hdis hz h
    obtain ⟨i,hi,hik,hBe⟩ := internal_only B hB hBz noend.2
    have iA : i ∉ A := fun h => Finset.disjoint_left.mp hdis h (by simp [hBe])
    have ai : a ≤ i.val := by rw [hAe, mem_interval] at iA; omega
    have ij : i.val < j := by
      have him : i ∈ A ∪ B := by simp [hBe]
      rw [hu, mem_interval] at him
      omega
    let q : Fin (k + 1) := ⟨a,han⟩
    have qm : q ∈ A ∪ B := by rw [hu, mem_interval]; dsimp [q]; omega
    have qi : q = i := by
      rw [hAe,hBe,Finset.mem_union,mem_interval,Finset.mem_singleton] at qm
      dsimp [q] at qm
      rcases qm with h | h
      · omega
      · exact h
    have ia : i.val = a := (congrArg Fin.val qi).symm
    have ja : j ≤ a + 1 := by
      by_contra hn
      let q' : Fin (k + 1) := ⟨a + 1,by omega⟩
      have qm' : q' ∈ A ∪ B := by rw [hu, mem_interval]; dsimp [q']; omega
      rw [hAe,hBe,Finset.mem_union,mem_interval,Finset.mem_singleton] at qm'
      rcases qm' with h | h
      · dsimp [q'] at h; omega
      · have := congrArg Fin.val h
        dsimp [q'] at this
        omega
    refine ⟨a,han,by omega,hAe,?_,ha⟩
    rw [hBe]
    congr 1
    exact Fin.ext ia
  have suffix_ordered (A B : Finset (Fin (k + 1))) (j : ℕ)
      (hj : 0 < j) (hjn : j < k + 1) (hdis : Disjoint A B)
      (hu : A ∪ B = interval k j (k + 1)) (hA : SmallBlock A) (hB : SmallBlock B)
      (he : e ∈ B) :
      ∃ (hj' : j < k), A = {⟨j,by omega⟩} ∧ B = interval k (j + 1) (k + 1) := by
    have nozero : z ∉ A ∧ z ∉ B := by
      have hn : z ∉ A ∪ B := by rw [hu, mem_interval]; dsimp [z]; omega
      simpa using hn
    obtain ⟨a,ha,han,hBe⟩ := suffix_at_end B hB he nozero.2
    have hAe : e ∉ A := fun h => Finset.disjoint_left.mp hdis h he
    obtain ⟨i,hi,hik,hAi⟩ := internal_only A hA nozero.1 hAe
    have iB : i ∉ B := fun h => Finset.disjoint_left.mp hdis (by simp [hAi]) h
    have ia : i.val < a := by rw [hBe,mem_interval] at iB; omega
    have ji : j ≤ i.val := by
      have him : i ∈ A ∪ B := by simp [hAi]
      rw [hu, mem_interval] at him
      omega
    let q : Fin (k + 1) := ⟨j,hjn⟩
    have qm : q ∈ A ∪ B := by rw [hu,mem_interval]; dsimp [q]; omega
    have qi : q = i := by
      rw [hAi,hBe,Finset.mem_union,mem_interval,Finset.mem_singleton] at qm
      dsimp [q] at qm
      rcases qm with h | h
      · exact h
      · omega
    have ij : i.val = j := (congrArg Fin.val qi).symm
    let p : Fin (k + 1) := ⟨a - 1,by omega⟩
    have pm : p ∈ A ∪ B := by rw [hu,mem_interval]; dsimp [p]; omega
    have pi : p = i := by
      rw [hAi,hBe,Finset.mem_union,mem_interval,Finset.mem_singleton] at pm
      dsimp [p] at pm
      rcases pm with h | h
      · exact h
      · omega
    have pa := congrArg Fin.val pi
    dsimp [p] at pa
    have aj : a = j + 1 := by omega
    refine ⟨by omega,?_,by simpa [aj] using hBe⟩
    rw [hAi]
    congr 1
    exact Fin.ext ij
  have prefix_force (u : TreeMessageRealization.Tree (Fin (k + 1))) (hu : Full u)
      (j : ℕ) (hj : 0 < j) (hjn : j < k + 1) (hset : leaves u = interval k 0 j)
      (hblocks : ∀ s ∈ subtrees u, SmallBlock (leaves s)) : PrefixSpine k j u := by
    induction u generalizing j with
    | nil => simp [Full] at hu
    | node a l r hl hr =>
      cases a with
      | some i =>
        obtain ⟨rfl,rfl⟩ := hu
        have zm : z ∈ leaves (leaf i) := by rw [hset,mem_interval]; dsimp [z]; omega
        have zi : z = i := by simpa [leaves] using zm
        have jone : j = 1 := by
          by_contra hn
          let q : Fin (k + 1) := ⟨1,by omega⟩
          have qm : q ∈ leaves (leaf i) := by rw [hset,mem_interval]; dsimp [q]; omega
          have qi : q = i := by simpa [leaves] using qm
          have he := congrArg Fin.val (qi.trans zi.symm)
          dsimp [q,z] at he
          omega
        subst j
        subst i
        exact PrefixSpine.one
      | none =>
        have hlb : ∀ s ∈ subtrees l, SmallBlock (leaves s) := fun s hs =>
          hblocks s (by simp only [subtrees,Finset.mem_insert,Finset.mem_union]; tauto)
        have hrb : ∀ s ∈ subtrees r, SmallBlock (leaves s) := fun s hs =>
          hblocks s (by simp only [subtrees,Finset.mem_insert,Finset.mem_union]; tauto)
        have zlr : z ∈ leaves l ∨ z ∈ leaves r := by
          have : z ∈ leaves (.node none l r) := by rw [hset,mem_interval]; dsimp [z]; omega
          simpa [leaves] using this
        have union_set : leaves l ∪ leaves r = interval k 0 j := by
          ext i
          simpa only [leaves, Finset.mem_union] using (Finset.ext_iff.mp hset i)
        rcases zlr with hzl | hzr
        · obtain ⟨a,ha,rfl,hla,hra,ha0⟩ := prefix_ordered (leaves l) (leaves r) j hj hjn
            hu.2.2 union_set (hlb l (self l hu.1)) (hrb r (self r hu.2.1)) hzl
          have hre := single r hu.2.1 ⟨a,ha⟩ hra
          rw [hre]
          exact PrefixSpine.peel ha (hl hu.1 a ha0 ha hla hlb)
        · obtain ⟨a,ha,rfl,hra,hla,ha0⟩ := prefix_ordered (leaves r) (leaves l) j hj hjn
            hu.2.2.symm (by rw [Finset.union_comm]; exact union_set)
            (hrb r (self r hu.2.1)) (hlb l (self l hu.1)) hzr
          have hle := single l hu.1 ⟨a,ha⟩ hla
          rw [hle]
          exact PrefixSpine.peel_swap ha (hr hu.2.1 a ha0 ha hra hrb)
  have suffix_force (u : TreeMessageRealization.Tree (Fin (k + 1))) (hu : Full u)
      (j : ℕ) (hj : 0 < j) (hjn : j < k + 1) (hset : leaves u = interval k j (k + 1))
      (hblocks : ∀ s ∈ subtrees u, SmallBlock (leaves s)) : SuffixSpine k j u := by
    induction u generalizing j with
    | nil => simp [Full] at hu
    | node a l r hl hr =>
      cases a with
      | some i =>
        obtain ⟨rfl,rfl⟩ := hu
        have em : e ∈ leaves (leaf i) := by rw [hset,mem_interval]; dsimp [e]; omega
        have ei : e = i := by simpa [leaves] using em
        have jk : j = k := by
          let q : Fin (k + 1) := ⟨j,hjn⟩
          have qm : q ∈ leaves (leaf i) := by rw [hset,mem_interval]; dsimp [q]; omega
          have qi : q = i := by simpa [leaves] using qm
          have he := congrArg Fin.val (qi.trans ei.symm)
          dsimp [q,e] at he
          omega
        subst j
        subst i
        exact SuffixSpine.one
      | none =>
        have hlb : ∀ s ∈ subtrees l, SmallBlock (leaves s) := fun s hs =>
          hblocks s (by simp only [subtrees,Finset.mem_insert,Finset.mem_union]; tauto)
        have hrb : ∀ s ∈ subtrees r, SmallBlock (leaves s) := fun s hs =>
          hblocks s (by simp only [subtrees,Finset.mem_insert,Finset.mem_union]; tauto)
        have elr : e ∈ leaves l ∨ e ∈ leaves r := by
          have : e ∈ leaves (.node none l r) := by rw [hset,mem_interval]; dsimp [e]; omega
          simpa [leaves] using this
        have union_set : leaves l ∪ leaves r = interval k j (k + 1) := by
          ext i
          simpa only [leaves, Finset.mem_union] using (Finset.ext_iff.mp hset i)
        rcases elr with hel | her
        · obtain ⟨hjk,hra,hla⟩ := suffix_ordered (leaves r) (leaves l) j hj hjn hu.2.2.symm
            (by rw [Finset.union_comm]; exact union_set)
            (hrb r (self r hu.2.1)) (hlb l (self l hu.1)) hel
          have hre := single r hu.2.1 ⟨j,by omega⟩ hra
          rw [hre]
          exact SuffixSpine.peel_swap hjk
            (hl hu.1 (j + 1) (by omega) (by omega) hla hlb)
        · obtain ⟨hjk,hla,hra⟩ := suffix_ordered (leaves l) (leaves r) j hj hjn hu.2.2 union_set
            (hlb l (self l hu.1)) (hrb r (self r hu.2.1)) her
          have hle := single l hu.1 ⟨j,by omega⟩ hla
          rw [hle]
          exact SuffixSpine.peel hjk
            (hr hu.2.1 (j + 1) (by omega) (by omega) hra hrb)
  have shape : DoubleComb t := by
    cases t with
    | nil => simp [Full] at ht
    | node a l r =>
      cases a with
      | some i =>
        have hz : z = i := by
          have : z ∈ leaves (.node (some i) l r) := by rw [hall]; simp
          simpa [leaves] using this
        have he : e = i := by
          have : e ∈ leaves (.node (some i) l r) := by rw [hall]; simp
          simpa [leaves] using this
        have := congrArg Fin.val (hz.trans he.symm)
        dsimp [z,e] at this
        omega
      | none =>
        have hlb : ∀ s ∈ subtrees l, SmallBlock (leaves s) := by
          intro s hs
          apply hsmall s (by simp only [subtrees,Finset.mem_insert,Finset.mem_union]; tauto)
          intro he
          have hsub := (subtree_structure l ht.1 s hs).2
          obtain ⟨i,hi⟩ := nonempty r ht.2.1
          have him : i ∈ leaves s := by rw [he,hall]; simp
          exact Finset.disjoint_left.mp ht.2.2 (hsub him) hi
        have hrb : ∀ s ∈ subtrees r, SmallBlock (leaves s) := by
          intro s hs
          apply hsmall s (by simp only [subtrees,Finset.mem_insert,Finset.mem_union]; tauto)
          intro he
          have hsub := (subtree_structure r ht.2.1 s hs).2
          obtain ⟨i,hi⟩ := nonempty l ht.1
          have him : i ∈ leaves s := by rw [he,hall]; simp
          exact Finset.disjoint_left.mp ht.2.2 hi (hsub him)
        have hL := hlb l (self l ht.1)
        have hR := hrb r (self r ht.2.1)
        have zm : z ∈ leaves l ∨ z ∈ leaves r := by
          have : z ∈ leaves (.node none l r) := by rw [hall]; simp
          simpa [leaves] using this
        have em : e ∈ leaves l ∨ e ∈ leaves r := by
          have : e ∈ leaves (.node none l r) := by rw [hall]; simp
          simpa [leaves] using this
        rcases zm with hzl | hzr
        · have her : e ∈ leaves r := by
            rcases em with h | h
            · exact False.elim (small_endpoints (leaves l) hL ⟨hzl,h⟩)
            · exact h
          have hel : e ∉ leaves l := fun h => Finset.disjoint_left.mp ht.2.2 h her
          obtain ⟨j,hj,hjn,hla⟩ := prefix_at_zero (leaves l) hL hzl hel
          have hra : leaves r = interval k j (k + 1) := by
            ext i
            have cover : i ∈ leaves l ∨ i ∈ leaves r := by
              have : i ∈ leaves (.node none l r) := by rw [hall]; simp
              simpa [leaves] using this
            have dis : ¬ (i ∈ leaves l ∧ i ∈ leaves r) := fun h =>
              Finset.disjoint_left.mp ht.2.2 h.1 h.2
            rw [hla,mem_interval] at cover dis
            rw [mem_interval]
            constructor
            · intro hi
              have hn : ¬ (0 ≤ i.val ∧ i.val < j) := fun hp => dis ⟨hp,hi⟩
              omega
            · intro hi
              rcases cover with h | h
              · omega
              · exact h
          exact ⟨j,hj,hjn,l,r,prefix_force l ht.1 j hj hjn hla hlb,
            suffix_force r ht.2.1 j hj hjn hra hrb,Or.inl rfl⟩
        · have hel : e ∈ leaves l := by
            rcases em with h | h
            · exact h
            · exact False.elim (small_endpoints (leaves r) hR ⟨hzr,h⟩)
          have her : e ∉ leaves r := fun h => Finset.disjoint_left.mp ht.2.2 hel h
          obtain ⟨j,hj,hjn,hra⟩ := prefix_at_zero (leaves r) hR hzr her
          have hla : leaves l = interval k j (k + 1) := by
            ext i
            have cover : i ∈ leaves l ∨ i ∈ leaves r := by
              have : i ∈ leaves (.node none l r) := by rw [hall]; simp
              simpa [leaves] using this
            have dis : ¬ (i ∈ leaves l ∧ i ∈ leaves r) := fun h =>
              Finset.disjoint_left.mp ht.2.2 h.1 h.2
            rw [hra,mem_interval] at cover dis
            rw [mem_interval]
            constructor
            · intro hi
              have hn : ¬ (0 ≤ i.val ∧ i.val < j) := fun hp => dis ⟨hi,hp⟩
              omega
            · intro hi
              rcases cover with h | h
              · exact h
              · omega
          exact ⟨j,hj,hjn,r,l,prefix_force r ht.2.1 j hj hjn hra hrb,
            suffix_force l ht.1 j hj hjn hla hlb,Or.inr rfl⟩
  have prefix_height (j : ℕ) (u : TreeMessageRealization.Tree (Fin (k + 1)))
      (h : PrefixSpine k j u) : u.height = j ∧ 0 < j := by
    induction h with
    | one => simp
    | peel hj h ih =>
      simp only [BinaryTree.height,leaf] at *
      omega
    | peel_swap hj h ih =>
      simp only [BinaryTree.height,leaf] at *
      omega
  have suffix_height (j : ℕ) (u : TreeMessageRealization.Tree (Fin (k + 1)))
      (h : SuffixSpine k j u) : u.height = k + 1 - j := by
    induction h with
    | one => simp
    | @peel j u hj h ih =>
      simp only [BinaryTree.height,leaf] at *
      omega
    | @peel_swap j u hj h ih =>
      simp only [BinaryTree.height,leaf] at *
      omega
  obtain ⟨j,hj,hjn,l,r,hl,hr,he⟩ := shape
  have hL := (prefix_height j l hl).1
  have hR := suffix_height j r hr
  have hh : height t = max j (k + 1 - j) := by
    rcases he with rfl | rfl <;>
      simp only [height,BinaryTree.height,hL,hR,Nat.add_sub_cancel,Nat.max_comm]
  refine ⟨j,hj,hjn,l,r,hl,hr,he,hh,?_⟩
  rw [hh]
  omega



set_option maxHeartbeats 2000000 in
/-- Small proper coordinate blocks are exactly the endpoint intervals and internal singletons. -/
theorem result (k : ℕ) (hk : 2 ≤ k) :
    (∀ A : Finset (Fin (k + 1)), A.Nonempty → A ≠ Finset.univ →
      (capacity (fun _ => Window) boolean (fun i => i ∈ A) ≤ 4 ↔ SmallBlock A)) ∧
    (∀ i : Fin (k + 1), 0 < i.val → i.val < k →
      capacity (fun _ => Window) boolean (fun j => j ∈ ({i} : Finset _)) = 4) := by
  classical
  have singleton_capacity (i : Fin (k + 1)) (hi : 0 < i.val) (hik : i.val < k) :
      capacity (fun _ => Window) boolean (fun j => j ∈ ({i} : Finset _)) = 4 := by
    have he : ({i} : Finset (Fin (k + 1))) = interval k i.val (i.val + 1) := by
      ext j
      simp only [Finset.mem_singleton, interval, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
      omega
    rw [he, (FirstRejectionCutCapacity.result k _).2.2.2.2.2.2.2.2.1]
    obtain ⟨hd,hj,hc,ht,hdel⟩ := FirstRejectionCutCapacity.interval_data k i.val (i.val + 1) (by omega) (by omega)
    have hint : internals (interval k i.val (i.val + 1)) = ∅ := Finset.card_eq_zero.mp (by omega)
    have hn : i.val + 1 ≠ k + 1 := by omega
    norm_num [hd, epsilon, ht, hint, hn, show i.val ≠ 0 by omega, show i.val ≠ k by omega]
  have sufficient (A : Finset (Fin (k + 1))) (hA : SmallBlock A) :
      capacity (fun _ => Window) boolean (fun i => i ∈ A) ≤ 4 := by
    rcases hA with ⟨j,hj,hjn,rfl⟩ | ⟨j,hj,hjn,rfl⟩ | ⟨i,hi,hik,rfl⟩
    · rw [(FirstRejectionCutCapacity.result k _).2.2.2.2.2.2.2.2.1]
      have hd := (FirstRejectionCutCapacity.interval_data k 0 j hj (by omega)).1
      have hn : j ≠ k + 1 := by omega
      norm_num [hd, hn]
      unfold epsilon
      split_ifs <;> omega
    · rw [(FirstRejectionCutCapacity.result k _).2.2.2.2.2.2.2.2.1]
      have hd := (FirstRejectionCutCapacity.interval_data k j (k + 1) hjn le_rfl).1
      norm_num [hd, show j ≠ 0 by omega]
      unfold epsilon
      split_ifs <;> omega
    · exact le_of_eq (singleton_capacity i hi hik)
  exact ⟨fun A hA hp => ⟨classify k hk A hA hp, sufficient A⟩, singleton_capacity⟩

end D5.S3.Arith.FibonacciAtomic.FourMessageTreeRigidity

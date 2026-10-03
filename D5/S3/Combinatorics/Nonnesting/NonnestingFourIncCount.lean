/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingFourIncCount
   mirror-E: none(waiver:row-four-increasing-bijection)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   utility: none
   digest: Counts increasing-first-order avoiders through a binary recursion. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingFourRecursive
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingFourIncCount

open D5.S3.Combinatorics.Nonnesting
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicOrders
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicDeletion
open D5.S3.Combinatorics.Nonnesting.NonnestingFourIncreasing
open D5.S3.Combinatorics.Nonnesting.NonnestingFourInsert
open D5.S3.Combinatorics.Nonnesting.NonnestingFourRecursive

def increasingWords (n : ℕ) : Type :=
  {w : List ℕ // w ∈ NonnestingDefs.avoiders n
      [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] ∧
    ∀ a b, 1 ≤ a → a < b → b ≤ n → (w).idxOf a < (w).idxOf b}

noncomputable def increasingStep (n : ℕ) (hn : 1 ≤ n) :
    Bool × increasingWords n ≃ increasingWords (n + 1) := by
  have increasing_delete_lowest (w : List ℕ) (n : ℕ)
      (hw : w ∈ NonnestingDefs.avoiders (n + 1)
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]])
      (hfirst : ∀ a b, 1 ≤ a → a < b → b ≤ n + 1 →
        (w).idxOf a < (w).idxOf b) :
      let v := (w.filter (fun x => decide (1 < x))).map (fun x => x - 1)
      v ∈ NonnestingDefs.avoiders n
        [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] ∧
        ∀ a b, 1 ≤ a → a < b → b ≤ n → (v).idxOf a < (v).idxOf b := by
    have count_two_positions (a : ℕ) (w : List ℕ)
        (hw : w.count a = 2) :
        (w).idxOf a < secondPos a w ∧
          w[(w).idxOf a]? = some a ∧ w[secondPos a w]? = some a := by
      obtain ⟨u, v, z, hu, hv, _, rfl⟩ := count_two_decomposition a w hw
      have hfirst : ((u ++ [a] ++ v ++ [a] ++ z)).idxOf a = u.length := by
        simp [List.idxOf_append, hu]
      have hsecond : secondPos a (u ++ [a] ++ v ++ [a] ++ z) =
          u.length + 1 + v.length := by
        have hdrop : u.drop (u.length + 1) = [] := by
          apply List.drop_eq_nil_iff.mpr
          omega
        simp [secondPos, List.idxOf_append, hu, hv, List.drop_append, hdrop]
      constructor
      · rw [hfirst, hsecond]
        omega
      constructor
      · rw [hfirst]
        simp
      · rw [hsecond]
        have hle : ¬ u.length + 1 + v.length < u.length := by omega
        simp [List.getElem?_append, hle]
        have heq : u.length + 1 + v.length - u.length = v.length + 1 := by omega
        rw [heq]
        simp
    let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
    let u := w.filter (fun x => decide (1 < x))
    let v := u.map (fun x => x - 1)
    have huPositive : ∀ x ∈ u, 1 < x := by
      intro x hx
      simpa [u] using (List.mem_filter.mp hx).2
    have hrestore : v.map (fun x => x + 1) = u := by
      unfold v
      rw [List.map_map]
      calc
        u.map ((fun x => x + 1) ∘ (fun x => x - 1)) = u.map id := by
          apply List.map_congr_left
          intro x hx
          simp only [Function.comp_apply, id_eq]
          have := huPositive x hx
          omega
        _ = u := List.map_id u
    have hidx (l : List ℕ) (a : ℕ) :
        (l.map (fun x => x + 1)).idxOf (a + 1) = l.idxOf a := by
      induction l with
      | nil => simp
      | cons x xs ih =>
        by_cases hxa : x = a
        · subst x
          simp
        · have hne : x + 1 ≠ a + 1 := by omega
          simp [List.idxOf_cons_ne _ hne, List.idxOf_cons_ne _ hxa, ih]
    have hv : v ∈ NonnestingDefs.avoiders n Λ :=
      delete_lowest_avoider w n Λ hw
    change v ∈ NonnestingDefs.avoiders n Λ ∧ _
    refine ⟨hv, ?_⟩
    intro a b ha hab hbn
    have hmem (x : ℕ) (hx : 1 ≤ x ∧ x ≤ n + 1) : x ∈ w := by
      have hrange : x ∈ List.range' 1 (n + 1) := by
        rw [List.mem_range'_1]
        omega
      exact List.mem_of_getElem?
        (count_two_positions x w (doubled_count (n + 1) x w hw.1 hrange)).2.1
    have horder := first_order_after_filter w 1 (a + 1) (b + 1)
      (by omega) (by omega)
      (hmem (a + 1) ⟨by omega, by omega⟩)
      (hmem (b + 1) ⟨by omega, by omega⟩)
      (hfirst (a + 1) (b + 1) (by omega) (by omega) (by omega))
    change u.idxOf (a + 1) < u.idxOf (b + 1) at horder
    rw [← hrestore, hidx v a, hidx v b] at horder
    exact horder
  have sumAvoiders (Λ : List (List ℕ)) (m n : ℕ) (u v : List ℕ)
      (hΛ : ∀ σ ∈ Λ, sumIndecomposable σ ∧
        (∀ a ∈ σ, 1 ≤ a) ∧
        (∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → i ∈ σ))
      (hpermU : u.Perm ((List.range' 1 m).flatMap fun i => [i, i]))
      (hpermV : v.Perm ((List.range' 1 n).flatMap fun i => [i, i])) :
      directSum m u v ∈ NonnestingDefs.avoiders (m + n) Λ ↔
        u ∈ NonnestingDefs.avoiders m Λ ∧
          v ∈ NonnestingDefs.avoiders n Λ := by
    have hubound : ∀ a ∈ u, a ≤ m := by
      intro a ha
      have hbase := hpermU.mem_iff.mp ha
      obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hbase
      have hai : a = i := by simpa using hii
      subst a
      have hirange : 1 ≤ i ∧ i < 1 + m := by simpa using hi
      omega
    have hvpositive : ∀ b ∈ v, 1 ≤ b := by
      intro b hb
      have hbase := hpermV.mem_iff.mp hb
      obtain ⟨i, hi, hii⟩ := List.mem_flatMap.mp hbase
      have hbi : b = i := by simpa using hii
      subst b
      have hirange : 1 ≤ i ∧ i < 1 + n := by simpa using hi
      omega
    have hnest1 : sumIndecomposable [1, 2, 2, 1] := by
      intro k hk
      fin_cases k
      · simp at hk
      · dsimp at *; exact ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide⟩
      · dsimp at *; exact ⟨⟨1, by decide⟩, ⟨1, by decide⟩, by decide⟩
      · dsimp at *; exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩, by decide⟩
    have hnest2 : sumIndecomposable [2, 1, 1, 2] := by
      intro k hk
      fin_cases k
      · simp at hk
      · dsimp at *; exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, by decide⟩
      · dsimp at *; exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, by decide⟩
      · dsimp at *; exact ⟨⟨0, by decide⟩, ⟨0, by decide⟩, by decide⟩
    have hnest1iff := occurs_directSum_iff m u v [1, 2, 2, 1]
      hubound hvpositive hnest1 (by decide) (by decide)
    have hnest2iff := occurs_directSum_iff m u v [2, 1, 1, 2]
      hubound hvpositive hnest2 (by decide) (by decide)
    constructor
    · intro hsum
      refine ⟨⟨hpermU, ?_, ?_, ?_⟩, ⟨hpermV, ?_, ?_, ?_⟩⟩
      · intro h
        exact hsum.2.1 (hnest1iff.mpr (Or.inl h))
      · intro h
        exact hsum.2.2.1 (hnest2iff.mpr (Or.inl h))
      · intro σ hσ h
        obtain ⟨hindec, hpos, hfull⟩ := hΛ σ hσ
        exact hsum.2.2.2 σ hσ
          ((occurs_directSum_iff m u v σ hubound hvpositive hindec hpos hfull).mpr
            (Or.inl h))
      · intro h
        exact hsum.2.1 (hnest1iff.mpr (Or.inr h))
      · intro h
        exact hsum.2.2.1 (hnest2iff.mpr (Or.inr h))
      · intro σ hσ h
        obtain ⟨hindec, hpos, hfull⟩ := hΛ σ hσ
        exact hsum.2.2.2 σ hσ
          ((occurs_directSum_iff m u v σ hubound hvpositive hindec hpos hfull).mpr
            (Or.inr h))
    · rintro ⟨hu, hv⟩
      change (directSum m u v).Perm
          ((List.range' 1 (m + n)).flatMap fun i => [i, i]) ∧
        ¬ NonnestingDefs.Occurs [1, 2, 2, 1] (directSum m u v) ∧
        ¬ NonnestingDefs.Occurs [2, 1, 1, 2] (directSum m u v) ∧
        ∀ σ ∈ Λ, ¬ NonnestingDefs.Occurs σ (directSum m u v)
      refine ⟨directSum_perm m n u v hpermU hpermV, ?_, ?_, ?_⟩
      · intro hocc
        rcases hnest1iff.mp hocc with h | h
        · exact hu.2.1 h
        · exact hv.2.1 h
      · intro hocc
        rcases hnest2iff.mp hocc with h | h
        · exact hu.2.2.1 h
        · exact hv.2.2.1 h
      · intro σ hσ hocc
        obtain ⟨hindec, hpos, hfull⟩ := hΛ σ hσ
        have hloc := (occurs_directSum_iff m u v σ
          hubound hvpositive hindec hpos hfull).mp hocc
        rcases hloc with h | h
        · exact hu.2.2.2 σ hσ h
        · exact hv.2.2.2 σ hσ h
  let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
  have hΛ : ∀ σ ∈ Λ, sumIndecomposable σ ∧
      (∀ a ∈ σ, 1 ≤ a) ∧
      (∀ i, 1 ≤ i → i ≤ NonnestingDefs.letters σ → i ∈ σ) := by
    intro σ hσ
    simp only [Λ, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with hσ | hσ | hσ | hσ <;> subst σ
    all_goals
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        fin_cases k
        · simp at hk
        all_goals decide
      · intro a ha
        simp at ha
        omega
      · intro i hi hle
        have hcase : i = 1 ∨ i = 2 ∨ i = 3 := by
          simp [NonnestingDefs.letters] at hle
          omega
        rcases hcase with rfl | rfl | rfl <;> simp
  have hpositive (v : increasingWords n) : ∀ x ∈ v.1, 1 ≤ x := by
    intro x hx
    have hxbase : x ∈ (List.range' 1 n).flatMap (fun i => [i, i]) :=
      v.2.1.1.mem_iff.mp hx
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
    have heq : x = i := by simpa using hxi
    subst x
    rw [List.mem_range'_1] at hi
    omega
  have hhead (v : increasingWords n) : v.1 = 1 :: v.1.tail := by
    have hlen : v.1.length = 2 * n := by
      simpa [Nat.mul_comm] using v.2.1.1.length_eq
    cases hv : v.1 with
    | nil => simp [hv] at hlen; omega
    | cons x r =>
      have hxb : 1 ≤ x ∧ x ≤ n := by
        have hxbase : x ∈ (List.range' 1 n).flatMap (fun i => [i, i]) :=
          v.2.1.1.mem_iff.mp (by rw [hv]; simp)
        obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hxbase
        have heq : x = i := by simpa using hxi
        subst x
        rw [List.mem_range'_1] at hi
        omega
      have hx : x = 1 := by
        by_contra hnot
        have hlt := v.2.2 1 x (by omega) (by omega) hxb.2
        rw [hv] at hlt
        have hf : ((x :: r)).idxOf x = 0 := by simp []
        omega
      simp [hx]
  let f : Bool × increasingWords n → increasingWords (n + 1) := by
    intro t
    rcases t with ⟨b, v⟩
    cases b with
    | false =>
      refine ⟨directSum 1 [1, 1] v.1, ?_⟩
      constructor
      · have hiff := sumAvoiders Λ 1 n [1, 1] v.1 hΛ
          (by simp) v.2.1.1
        have hsmall : [1, 1] ∈ NonnestingDefs.avoiders 1 Λ := by
          have hno (σ : List ℕ) (hlen : σ.length = 4) :
              ¬ NonnestingDefs.Occurs σ [1, 1] := by
            intro hocc
            obtain ⟨x, _, _, hsub, _⟩ := hocc
            have hle := hsub.length_le
            simp [hlen] at hle
          refine ⟨by simp, hno _ (by decide), hno _ (by decide), ?_⟩
          intro σ hσ
          simp only [Λ, List.mem_cons, List.not_mem_nil, or_false] at hσ
          rcases hσ with hσ | hσ | hσ | hσ <;> subst σ <;> exact hno _ (by decide)
        simpa [Λ, Nat.add_comm] using hiff.mpr ⟨hsmall, v.2.1⟩
      · change ∀ a b, 1 ≤ a → a < b → b ≤ n + 1 →
          ((1 :: 1 :: shift 1 v.1)).idxOf a <
            ((1 :: 1 :: shift 1 v.1)).idxOf b
        exact cut_insert_first_order v.1 n v.2.2
    | true =>
      let r := v.1.tail
      have hvhead : v.1 = 1 :: r := hhead v
      refine ⟨1 :: 2 :: 1 :: shift 1 r, ?_⟩
      constructor
      · exact crossing_insert r n (hvhead ▸ v.2.1)
      · exact crossing_insert_first_order r n (hvhead ▸ v.2.2)
  have hdelete (t : Bool × increasingWords n) :
      (((f t).1.filter (fun x => decide (1 < x))).map (fun x => x - 1)) =
        t.2.1 := by
    obtain ⟨b, v⟩ := t
    have hshiftPos : ∀ x ∈ shift 1 v.1, 1 < x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have := hpositive v y hy
      omega
    have hshiftFilter : (shift 1 v.1).filter (fun x => decide (1 < x)) =
        shift 1 v.1 := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [hshiftPos x hx]
    have hrestore : (shift 1 v.1).map (fun x => x - 1) = v.1 := by
      simp [shift, List.map_map, Function.comp_def]
    cases b with
    | false =>
      change ((1 :: 1 :: shift 1 v.1).filter
        (fun x => decide (1 < x))).map (fun x => x - 1) = v.1
      simp [hshiftFilter, hrestore]
    | true =>
      have hvhead := hhead v
      have htailPos : ∀ x ∈ v.1.tail, 1 ≤ x := by
        intro x hx
        apply hpositive v x
        rw [hvhead]
        simp [hx]
      have htailFilter : (shift 1 v.1.tail).filter
          (fun x => decide (1 < x)) = shift 1 v.1.tail := by
        apply List.filter_eq_self.mpr
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        have := htailPos y hy
        simp [shift]
        omega
      have htailRestore : (shift 1 v.1.tail).map (fun x => x - 1) =
          v.1.tail := by
        simp [shift, List.map_map, Function.comp_def]
      change ((1 :: 2 :: 1 :: shift 1 v.1.tail).filter
        (fun x => decide (1 < x))).map (fun x => x - 1) = v.1
      rw [hvhead]
      simp [htailFilter, htailRestore]
  apply Equiv.ofBijective f
  constructor
  · intro t t' heq
    have hwords : (f t).1 = (f t').1 := congrArg Subtype.val heq
    rcases t with ⟨b, v⟩
    rcases t' with ⟨b', v'⟩
    cases b <;> cases b'
    · have hv : v.1 = v'.1 := by
        have h1 := hdelete (false, v)
        have h2 := hdelete (false, v')
        rw [hwords] at h1
        exact h1.symm.trans h2
      have : v = v' := Subtype.ext hv
      subst v'
      rfl
    · have hmark := congrArg (fun l : List ℕ => l[1]?) hwords
      simp [f, directSum, shift] at hmark
    · have hmark := congrArg (fun l : List ℕ => l[1]?) hwords
      simp [f, directSum, shift] at hmark
    · have hv : v.1 = v'.1 := by
        have h1 := hdelete (true, v)
        have h2 := hdelete (true, v')
        rw [hwords] at h1
        exact h1.symm.trans h2
      have : v = v' := Subtype.ext hv
      subst v'
      rfl
  · intro w
    let vword := (w.1.filter (fun x => decide (1 < x))).map (fun x => x - 1)
    have hvdata := increasing_delete_lowest w.1 n w.2.1 w.2.2
    let v : increasingWords n := ⟨vword, hvdata⟩
    have hrec := increasing_reconstruct w.1 n w.2.1 hn w.2.2
    rcases hrec with hcut | ⟨r, hvhead, hcross⟩
    · refine ⟨(false, v), ?_⟩
      apply Subtype.ext
      simpa [f, vword, v] using hcut.symm
    · refine ⟨(true, v), ?_⟩
      apply Subtype.ext
      simpa [f, vword, v, hvhead] using hcross.symm

theorem increasingWords_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (increasingWords n) = 2 ^ (n - 1) := by
  classical
  let Λ := [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]]
  have hfinite (j : ℕ) :
      {w : List ℕ | w ∈ NonnestingDefs.avoiders j Λ ∧
        ∀ a b, 1 ≤ a → a < b → b ≤ j → (w).idxOf a < (w).idxOf b}.Finite := by
    let base : List ℕ := (List.range' 1 j).flatMap (fun i => [i, i])
    have hbase : {w : List ℕ | w ∈ base.permutations}.Finite := by
      simpa using (Set.finite_mem_finset base.permutations.toFinset)
    apply hbase.subset
    intro w hw
    have hperm : w ∈ base.permutations := by
      simpa [base, List.mem_permutations] using hw.1.1
    exact hperm
  have hsingle (v : increasingWords 1) : v.1 = [1, 1] := by
    have hlen : v.1.length = 2 := by
      have h := v.2.1.1.length_eq
      simpa using h
    obtain ⟨a, b, heq⟩ := List.length_eq_two.mp hlen
    have hvalue (x : ℕ) (hx : x ∈ v.1) : x = 1 := by
      have hbase := v.2.1.1.mem_iff.mp hx
      simpa using hbase
    have ha : a = 1 := hvalue a (by rw [heq]; simp)
    have hb : b = 1 := hvalue b (by rw [heq]; simp)
    simp [heq, ha, hb]
  have hsmall : [1, 1] ∈ NonnestingDefs.avoiders 1 Λ := by
    have hno (σ : List ℕ) (hlen : σ.length = 4) :
        ¬ NonnestingDefs.Occurs σ [1, 1] := by
      intro hocc
      obtain ⟨x, _, _, hsub, _⟩ := hocc
      have hle := hsub.length_le
      simp [hlen] at hle
    refine ⟨by simp, hno _ (by decide), hno _ (by decide), ?_⟩
    intro σ hσ
    simp only [Λ, List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with hσ | hσ | hσ | hσ <;> subst σ <;> exact hno _ (by decide)
  let one : increasingWords 1 := ⟨[1, 1], hsmall, by
    intro a b ha hab hble
    omega⟩
  haveI : Unique (increasingWords 1) := {
    default := one
    uniq := by
      intro x
      apply Subtype.ext
      exact hsingle x
  }
  induction n, hn using Nat.le_induction with
  | base =>
    letI : Fintype (increasingWords 1) := by
      unfold increasingWords
      exact (hfinite 1).fintype
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.card_unique : Fintype.card (increasingWords 1) = 1)
  | succ j hj ih =>
    letI : Fintype (increasingWords j) := by
      unfold increasingWords
      exact (hfinite j).fintype
    letI : Fintype (increasingWords (j + 1)) := by
      unfold increasingWords
      exact (hfinite (j + 1)).fintype
    have hstep : Nat.card (increasingWords (j + 1)) =
        2 * Nat.card (increasingWords j) := by
      simp only [Nat.card_eq_fintype_card]
      calc
        Fintype.card (increasingWords (j + 1)) =
            Fintype.card (Bool × increasingWords j) :=
          (Fintype.card_congr (increasingStep j hj)).symm
        _ = 2 * Fintype.card (increasingWords j) := by simp
    rw [hstep, ih]
    have hpow : 2 * 2 ^ (j - 1) = 2 ^ j := by
      calc
        2 * 2 ^ (j - 1) = 2 ^ (j - 1 + 1) := by
          rw [pow_succ]
          omega
        _ = 2 ^ j := by rw [Nat.sub_add_cancel hj]
    simpa using hpow

end D5.S3.Combinatorics.Nonnesting.NonnestingFourIncCount

#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourIncCount.increasingStep
#print axioms D5.S3.Combinatorics.Nonnesting.NonnestingFourIncCount.increasingWords_card

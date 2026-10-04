/- GID: D5/S3/Combinatorics/QGrammar/SecGrammarWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/QGrammar/SecGrammarWords
   mirror-E: none(waiver:sec-grammar-normal-forms)
   anchors: [mathlib/module/Mathlib.Data.List.GetD]
   utility: none
   digest: Canonical two-block words have a unique family and integer tuple encoding. -/

import D5.S3.Combinatorics.QGrammar.SecGrammarSupport
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.QGrammar.SecGrammar

open SecGrammarDefs

/-- `true` encodes family A and `false` encodes family B from the support classification. -/
def encode (f : Bool) (j a b : ℕ) : List Var :=
  if f then List.replicate a (false, j + 1) ++ List.replicate b (false, j) ++ [(true, j)]
  else List.replicate a (false, j) ++ [(true, j)] ++ List.replicate b (false, j - 1)


/-- A sorted word with one y and strip width one has a unique admissible tuple.
The high-letter test constructs its family; letter counts give the inverse encoding. -/
theorem normal_form (w : List Var) (j : ℕ) (hw : w.Pairwise dioLe)
    (hy : w.filter (fun v => v.1) = [(true, j)])
    (hx : ∀ v ∈ w, j - 1 ≤ v.2 ∧ v.2 ≤ j + 1)
    (hwidth : ∀ v ∈ w, ∀ u ∈ w, v.2 ≤ u.2 + 1)
    (hzero : 1 ≤ j ∨ (false, j + 1) ∈ w) :
    ∃! q : Bool × ℕ × ℕ,
      (if q.1 then 1 ≤ q.2.1 else 1 ≤ j) ∧ encode q.1 j q.2.1 q.2.2 = w := by
  have : Std.Antisymm dioLe := ⟨by
    rintro ⟨x, i⟩ ⟨y, k⟩ h h'
    cases x <;> cases y <;> simp_all [dioLe, Prod.ext_iff] <;> omega⟩
  have sorted (f : Bool) (i a b : ℕ) (hi : if f then True else 1 ≤ i) :
      (encode f i a b).Pairwise dioLe := by
    cases f <;> simp_all [encode, List.pairwise_append, List.pairwise_replicate,
      List.mem_replicate, dioLe] <;> omega
  have cy (i : ℕ) : w.count (true, i) = if i = j then 1 else 0 := by
    rw [← List.count_filter (p := fun v : Var => v.1) (a := (true, i)) rfl, hy]
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij, Ne.symm hij]
  have unique (f g : Bool) (j k a b c d : ℕ)
      (hf : if f then 1 ≤ a else 1 ≤ j) (hg : if g then 1 ≤ c else 1 ≤ k)
      (h : encode f j a b = encode g k c d) :
      f = g ∧ j = k ∧ a = c ∧ b = d := by
    have hy (e : Bool) (i u v : ℕ) :
        (encode e i u v).filter (fun x => x.1) = [(true, i)] := by
      cases e <;> simp [encode, List.filter_append]
    have hj : j = k := by
      have := congrArg (List.filter (fun x : Var => x.1)) h
      rw [hy, hy] at this
      simpa using this
    subst k
    have hc (v : Var) := congrArg (List.count v) h
    cases f <;> cases g
    · simp only [Bool.false_eq_true, ↓reduceIte] at hf hg
      have hn : j - 1 ≠ j := by omega
      have ha : a = c := by
        simpa [encode, List.count_append, List.count_replicate, hn] using hc (false, j)
      have hb : b = d := by
        simpa [encode, List.count_append, List.count_replicate, Ne.symm hn] using
          hc (false, j - 1)
      exact ⟨rfl, rfl, ha, hb⟩
    · simp only [Bool.false_eq_true, ↓reduceIte] at hf hg
      have hn : j - 1 ≠ j + 1 := by omega
      have := hc (false, j + 1)
      simp [encode, List.count_append, List.count_replicate, hn] at this
      omega
    · simp only [Bool.false_eq_true, ↓reduceIte] at hf hg
      have hn : j - 1 ≠ j + 1 := by omega
      have := hc (false, j + 1)
      simp [encode, List.count_append, List.count_replicate, hn] at this
      omega
    · have ha : a = c := by
        simpa [encode, List.count_append, List.count_replicate] using hc (false, j + 1)
      have hb : b = d := by
        simpa [encode, List.count_append, List.count_replicate] using hc (false, j)
      exact ⟨rfl, rfl, ha, hb⟩
  have finish (f : Bool) (a b : ℕ) (hf : if f then 1 ≤ a else 1 ≤ j)
      (he : encode f j a b = w) :
      ∃! q : Bool × ℕ × ℕ,
        (if q.1 then 1 ≤ q.2.1 else 1 ≤ j) ∧ encode q.1 j q.2.1 q.2.2 = w := by
    refine ⟨(f, a, b), ⟨hf, he⟩, ?_⟩
    rintro ⟨g, c, d⟩ ⟨hg, hge⟩
    obtain ⟨rfl, _, rfl, rfl⟩ := unique g f j j c d a b hg hf (hge.trans he.symm)
    rfl
  by_cases high : (false, j + 1) ∈ w
  · have ha : 1 ≤ w.count (false, j + 1) := List.count_pos_iff.mpr high
    have ix (i : ℕ) (hi : (false, i) ∈ w) : i = j ∨ i = j + 1 := by
      have h₁ := hx (false, i) hi
      have h₂ := hwidth (false, j + 1) high (false, i) hi
      dsimp at h₁ h₂
      omega
    apply finish true (w.count (false, j + 1)) (w.count (false, j)) ha
    symm
    apply List.Perm.eq_of_pairwise' hw (sorted true _ _ _ trivial)
    apply List.perm_iff_count.mpr
    rintro ⟨v, i⟩
    cases v
    · by_cases h₁ : i = j + 1
      · subst i
        simp [encode, List.count_append, List.count_replicate]
      · by_cases h₂ : i = j
        · subst i
          simp [encode, List.count_append, List.count_replicate]
        · have hi : (false, i) ∉ w := fun h => (ix i h).elim h₂ h₁
          simp [encode, List.count_append, List.count_replicate,
            List.count_eq_zero.mpr hi, Ne.symm h₁, Ne.symm h₂]
    · by_cases hij : i = j
      · subst i
        simp [encode, List.count_append, List.count_replicate, cy]
      · simp [encode, List.count_append, List.count_replicate,
          cy, hij, Ne.symm hij]
  · have hj : 1 ≤ j := hzero.resolve_right high
    have ix (i : ℕ) (hi : (false, i) ∈ w) : i = j ∨ i = j - 1 := by
      have h₁ := hx (false, i) hi
      have hn : i ≠ j + 1 := by
        rintro rfl
        exact high hi
      dsimp at h₁
      omega
    apply finish false (w.count (false, j)) (w.count (false, j - 1)) hj
    symm
    apply List.Perm.eq_of_pairwise' hw (sorted false _ _ _ hj)
    apply List.perm_iff_count.mpr
    have hn : j - 1 ≠ j := by omega
    rintro ⟨v, i⟩
    cases v
    · by_cases h₁ : i = j
      · subst i
        simp [encode, List.count_append, List.count_replicate, hn]
      · by_cases h₂ : i = j - 1
        · subst i
          simp [encode, List.count_append, List.count_replicate, Ne.symm hn]
        · have hi : (false, i) ∉ w := fun h => (ix i h).elim h₁ h₂
          simp [encode, List.count_append, List.count_replicate,
            List.count_eq_zero.mpr hi, Ne.symm h₁, Ne.symm h₂]
    · by_cases hij : i = j
      · subst i
        simp [encode, List.count_append, List.count_replicate, cy]
      · simp [encode, List.count_append, List.count_replicate,
          cy, hij, Ne.symm hij]

/-- Every support word has one y and width at most one. After a positive number of
steps, a y at index zero is accompanied by an x at index one. -/
theorem word_invariants (n : ℕ) :
    ∀ w ∈ (deriv^[n] (Finsupp.single [(true, 0)] 1)).support,
      w.Pairwise dioLe ∧ w.countP (fun v => v.1) = 1 ∧
      (∀ v ∈ w, ∀ u ∈ w, v.2 ≤ u.2 + 1) ∧
      (1 ≤ n → ∀ v ∈ w, v.1 = true → 1 ≤ v.2 ∨ (false, v.2 + 1) ∈ w) := by
  classical
  have : Std.Total dioLe := ⟨by
    rintro ⟨x, i⟩ ⟨y, j⟩
    cases x <;> cases y <;> simp [dioLe] <;> omega⟩
  have : IsTrans Var dioLe := ⟨by
    rintro ⟨x, i⟩ ⟨y, j⟩ ⟨z, k⟩ h h'
    cases x <;> cases y <;> cases z <;> simp_all [dioLe] <;> omega⟩
  have step (w : List Var) (hs : w.Pairwise dioLe)
      (hc : w.countP (fun v => v.1) = 1)
      (hd : ∀ v ∈ w, ∀ u ∈ w, v.2 ≤ u.2 + 1)
      (p : ℕ) (hp : p < w.length) (t : List Var)
      (ht : t ∈ (rule (w.getD p (false, 0))).support) :
      let z := dio (w.take p ++ t ++ up (w.drop (p + 1)))
      z.Pairwise dioLe ∧ z.countP (fun v => v.1) = 1 ∧
      (∀ v ∈ z, ∀ u ∈ z, v.2 ≤ u.2 + 1) ∧
      (∀ v ∈ z, v.1 = true → 1 ≤ v.2 ∨ (false, v.2 + 1) ∈ z) := by
    let v := w.getD p (false, 0)
    let L := w.take p
    let R := w.drop (p + 1)
    have hw : L ++ [v] ++ R = w := by
      dsimp [L, v, R]
      rw [List.getD_eq_getElem w (false, 0) hp, List.take_append_getElem hp, List.take_append_drop]
    have hv : v ∈ w := hw ▸ (by simp)
    have hmL (u : Var) (hu : u ∈ L) : u ∈ w := hw ▸ (by simp [hu])
    have hmR (u : Var) (hu : u ∈ R) : u ∈ w := hw ▸ (by simp [hu])
    have hs' : (L ++ [v] ++ R).Pairwise dioLe := hw.symm ▸ hs
    have hL (u : Var) (hu : u ∈ L) : dioLe u v :=
      (List.pairwise_append.mp (List.pairwise_append.mp hs').1).2.2 u hu v (by simp)
    have hR (u : Var) (hu : u ∈ R) : dioLe v u :=
      (List.pairwise_append.mp hs').2.2 v (by simp) u hu
    have counts : L.countP (fun v => v.1) + (if v.1 then 1 else 0) +
        R.countP (fun v => v.1) = 1 := by
      have hh := congrArg (List.countP (fun v : Var => v.1)) hw
      simpa only [List.countP_append, List.countP_singleton, hc] using hh
    have shape : t = [v, (false, v.2 + 1)] ∨ (v.1 = false ∧ t = []) := by
      change t ∈ (rule v).support at ht
      cases he : v.1
      · simp only [rule, he, Bool.false_eq_true, ↓reduceIte] at ht
        have ht' := Finsupp.support_add ht
        simp only [Finset.mem_union, Finsupp.mem_support_single] at ht'
        rcases ht' with ⟨h, _⟩ | ⟨h, _⟩
        · exact Or.inr ⟨rfl, h⟩
        · exact Or.inl h
      · simp only [rule, he, ↓reduceIte, Finsupp.mem_support_single] at ht
        exact Or.inl ht.1
    have boundsL (u : Var) (hu : u ∈ L) : v.2 ≤ u.2 ∧ u.2 ≤ v.2 + 1 := by
      have ho := hL u hu
      have hd' := hd u (hmL u hu) v hv
      unfold dioLe at ho
      omega
    have boundsR (u : Var) (hu : u ∈ R) : v.2 ≤ u.2 + 1 ∧ u.2 + 1 ≤ v.2 + 1 := by
      have ho := hR u hu
      have hd' := hd v hv u (hmR u hu)
      unfold dioLe at ho
      omega
    have bounds (u : Var) (hu : u ∈ L ++ t ++ up R) :
        v.2 ≤ u.2 ∧ u.2 ≤ v.2 + 1 := by
      simp only [List.mem_append] at hu
      rcases hu with (hu | hu) | hu
      · exact boundsL u hu
      · rcases shape with rfl | ⟨_, rfl⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> simp
        · simp at hu
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hu
        exact boundsR s hs
    have perm : (dio (L ++ t ++ up R)).Perm (L ++ t ++ up R) :=
      List.perm_insertionSort dioLe _
    refine ⟨List.pairwise_insertionSort dioLe _, ?_, ?_, ?_⟩
    · rw [perm.countP_eq]
      have hup : (up R).countP (fun v => v.1) = R.countP (fun v => v.1) := by
        simp [up, List.countP_map, Function.comp_def]
      rcases shape with rfl | ⟨he, rfl⟩
      · simp only [List.countP_append, List.countP_cons, List.countP_nil, Bool.false_eq_true,
          ite_false, add_zero, hup]
        omega
      · simpa [List.countP_append, hup, he] using counts
    · intro u hu s hs
      have bu := bounds u (perm.mem_iff.mp hu)
      have bs := bounds s (perm.mem_iff.mp hs)
      omega
    · intro u hu huy
      by_cases huj : 1 ≤ u.2
      · exact Or.inl huj
      · have hu0 : u.2 = 0 := by omega
        have huraw := perm.mem_iff.mp hu
        simp only [List.mem_append] at huraw
        rcases huraw with (huL | hut) | huR
        · have ho := hL u huL
          have hup : 1 ≤ L.countP (fun v => v.1) :=
            List.countP_pos_iff.mpr ⟨u, huL, huy⟩
          have hvy : v.1 = true := by
            unfold dioLe at ho
            simp only [hu0, huy, Nat.not_lt_zero, Bool.true_eq_false, false_or] at ho
            exact ho.2
          simp [hvy] at counts
          omega
        · rcases shape with rfl | ⟨_, rfl⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hut
            rcases hut with rfl | h
            · exact Or.inr (perm.mem_iff.mpr (by simp))
            · subst u
              simp at huy
          · simp at hut
        · obtain ⟨s, _, he⟩ := List.mem_map.mp huR
          have := congrArg Prod.snd he
          dsimp at this
          omega
  induction n with
  | zero =>
    intro w hw
    simp only [Function.iterate_zero, id_eq, Finsupp.mem_support_single] at hw
    rcases hw with ⟨rfl, _⟩
    simp
  | succ n ih =>
    intro z hz
    obtain ⟨w, hw, p, hp, t, ht, rfl⟩ := (support_reduction n).2 z |>.mp hz
    obtain ⟨hs, hc, hd, _⟩ := ih w hw
    obtain ⟨hs', hc', hd', hzero⟩ := step w hs hc hd p hp t ht
    exact ⟨hs', hc', hd', fun _ => hzero⟩

end D5.S3.Combinatorics.QGrammar.SecGrammar

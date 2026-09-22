/- GID: D5/S3/Combinatorics/BalancedCompositionPaths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BalancedCompositionPaths
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Balanced compositions and nonnegative walks starting at height two. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.BalancedCompositionPaths

open scoped BigOperators

/-- The cardinality of the height sequences of length `n + 1` that start at two
and change by one at each step. Nonnegativity is automatic from the codomain
`ℕ`. Every such height is at most `n + 2`, so the finite box loses no walks. -/
def walkCount (n : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (n + 3))).filter
    (fun v => v 0 = 2 ∧ ∀ i : Fin n,
      v i.succ + 1 = v i.castSucc ∨ v i.castSucc + 1 = v i.succ)).card

/-- The cardinality of the compositions whose even parts occur equally often
at odd and even positions. Indices are zero-based: index `i` is position `i+1`,
so an even index is an odd position. Thus `[2,1,2]` is not balanced, whereas
`[1,2,2]` is. Compositions with no even parts are included. -/
def balancedCompositionCount (m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Composition m)).filter (fun c =>
    (Finset.univ.filter (fun i : Fin c.blocks.length =>
      c.blocks[i.val] % 2 = 0 ∧ i.val % 2 = 0)).card =
    (Finset.univ.filter (fun i : Fin c.blocks.length =>
      c.blocks[i.val] % 2 = 0 ∧ i.val % 2 = 1)).card)).card

/-- The balanced-composition interpretation of OEIS A026010, for every index. -/
def claim : Prop := ∀ n : ℕ, walkCount n = balancedCompositionCount (n + 2)

theorem result : claim := by
  classical
  -- The height bound follows from the step condition.
  let W (n h : ℕ) : Finset (Fin (n + 1) → ℕ) :=
    (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (h + n + 1))).filter
      (fun v => v 0 = h ∧ ∀ i : Fin n,
        v i.succ + 1 = v i.castSucc ∨ v i.castSucc + 1 = v i.succ)
  have walk_bound (n h : ℕ) (v : Fin (n + 1) → ℕ)
      (hv : v 0 = h ∧ ∀ i : Fin n,
        v i.succ + 1 = v i.castSucc ∨ v i.castSucc + 1 = v i.succ) :
      ∀ (k : ℕ) (hk : k < n + 1), v ⟨k, hk⟩ ≤ h + k := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa only [Nat.add_zero] using (show v ⟨0, hk⟩ = h from hv.1).le
    | succ k ih =>
        intro hk
        have hk' : k < n := by omega
        have hk0 : k < n + 1 := by omega
        have hb : v ⟨k, hk0⟩ ≤ h + k := ih hk0
        have hs : v ⟨k + 1, hk⟩ + 1 = v ⟨k, hk0⟩ ∨
            v ⟨k, hk0⟩ + 1 = v ⟨k + 1, hk⟩ := hv.2 ⟨k, hk'⟩
        omega
  have Wmem (n h : ℕ) (v : Fin (n + 1) → ℕ) :
      v ∈ W n h ↔ v 0 = h ∧ ∀ i : Fin n,
        v i.succ + 1 = v i.castSucc ∨ v i.castSucc + 1 = v i.succ := by
    simp only [W, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · exact And.right
    · intro hv
      refine ⟨?_, hv⟩
      intro i
      have hb := walk_bound n h v hv i.val i.isLt
      have hvi : v ⟨i.val, i.isLt⟩ = v i := congrArg v (Fin.ext rfl)
      rw [hvi] at hb
      have hi := i.isLt
      omega
  have Wtail (n h : ℕ) (v : Fin (n + 2) → ℕ) (hv : v ∈ W (n + 1) h) :
      Fin.tail v ∈ W n (v 1) := by
    apply (Wmem _ _ _).2
    refine ⟨rfl, ?_⟩
    intro i
    exact ((Wmem _ _ _).1 hv).2 i.succ
  have Wcons (n h a : ℕ) (v : Fin (n + 1) → ℕ) (hv : v ∈ W n a)
      (ha : a + 1 = h ∨ h + 1 = a) : Fin.cons h v ∈ W (n + 1) h := by
    have hv' := (Wmem _ _ _).1 hv
    apply (Wmem _ _ _).2
    refine ⟨Fin.cons_zero _ _, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hv'.1] using ha
    · simpa only [Fin.castSucc_succ, Fin.cons_succ] using hv'.2 j
  have Wzero (h : ℕ) : (W 0 h).card = 1 := by
    have heq : W 0 h = {fun _ => h} := by
      ext v
      rw [Wmem, Finset.mem_singleton]
      constructor
      · intro hv
        funext i
        have hi : i = 0 := Fin.fin_one_eq_zero i
        simpa only [hi] using hv.1
      · rintro rfl
        exact ⟨rfl, fun i => Fin.elim0 i⟩
    rw [heq, Finset.card_singleton]
  have Wr0 (n : ℕ) : (W (n + 1) 0).card = (W n 1).card := by
    have heq : W (n + 1) 0 = (W n 1).image (Fin.cons 0) := by
      ext v
      constructor
      · intro hv
        have hv' := (Wmem _ _ _).1 hv
        have hs : v 1 + 1 = v 0 ∨ v 0 + 1 = v 1 := hv'.2 0
        have hfirst : v 1 = 1 := by omega
        refine Finset.mem_image.2 ⟨Fin.tail v, ?_, ?_⟩
        · simpa only [hfirst] using Wtail n 0 v hv
        · simpa only [hv'.1] using Fin.cons_self_tail v
      · intro hv
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
        exact Wcons n 0 1 u hu (Or.inr rfl)
    rw [heq, Finset.card_image_of_injective _ (Fin.cons_right_injective 0)]
  have Wr (n h : ℕ) :
      (W (n + 1) (h + 1)).card = (W n h).card + (W n (h + 2)).card := by
    have heq : W (n + 1) (h + 1) =
        (W n h).image (Fin.cons (h + 1)) ∪
          (W n (h + 2)).image (Fin.cons (h + 1)) := by
      ext v
      constructor
      · intro hv
        have hv' := (Wmem _ _ _).1 hv
        have hs : v 1 + 1 = v 0 ∨ v 0 + 1 = v 1 := hv'.2 0
        have hfirst : v 1 = h ∨ v 1 = h + 2 := by omega
        have hcons : Fin.cons (h + 1) (Fin.tail v) = v := by
          simpa only [hv'.1] using Fin.cons_self_tail v
        rcases hfirst with hfirst | hfirst
        · apply Finset.mem_union_left
          exact Finset.mem_image.2 ⟨Fin.tail v,
            by simpa only [hfirst] using Wtail n (h + 1) v hv, hcons⟩
        · apply Finset.mem_union_right
          exact Finset.mem_image.2 ⟨Fin.tail v,
            by simpa only [hfirst] using Wtail n (h + 1) v hv, hcons⟩
      · intro hv
        rcases Finset.mem_union.1 hv with hv | hv
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
          exact Wcons n (h + 1) h u hu (Or.inl rfl)
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
          exact Wcons n (h + 1) (h + 2) u hu (Or.inr rfl)
    have hcons_inj : Function.Injective
        (Fin.cons (n := n + 1) (α := fun _ => ℕ) (h + 1)) := by
      intro u₁ u₂ huv
      have htail := congrArg Fin.tail huv
      simpa only [Fin.tail_cons] using htail
    have hd : Disjoint
        ((W n h).image (Fin.cons (n := n + 1) (α := fun _ => ℕ) (h + 1)))
        ((W n (h + 2)).image (Fin.cons (n := n + 1) (α := fun _ => ℕ) (h + 1))) := by
      apply Finset.disjoint_left.2
      intro v hv₁ hv₂
      obtain ⟨u₁, hu₁, he₁⟩ := Finset.mem_image.1 hv₁
      obtain ⟨u₂, hu₂, he₂⟩ := Finset.mem_image.1 hv₂
      have hu : u₁ = u₂ := hcons_inj (he₁.trans he₂.symm)
      have h₁ : u₁ 0 = h := ((Wmem _ _ _).1 hu₁).1
      have h₂ : u₂ 0 = h + 2 := ((Wmem _ _ _).1 hu₂).1
      have he := congrFun hu 0
      omega
    rw [heq, Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective _ hcons_inj,
      Finset.card_image_of_injective _ hcons_inj]

  let pathCount : ℕ → ℕ → ℕ := fun n =>
    Nat.rec (fun _ : ℕ => 1)
      (fun _ f h => match h with
        | 0 => f 1
        | h + 1 => f h + f (h + 2)) n
  have walk_bridge : ∀ n h : ℕ, (W n h).card = pathCount n h := by
    intro n
    induction n with
    | zero => intro h; exact Wzero h
    | succ n ih =>
        intro h
        cases h with
        | zero =>
            change (W (n + 1) 0).card = pathCount n 1
            rw [Wr0, ih]
        | succ h =>
            change (W (n + 1) (h + 1)).card = pathCount n h + pathCount n (h + 2)
            rw [Wr, ih, ih]
  have literal_walk_bridge (n : ℕ) : walkCount n = pathCount n 2 := by
    simpa only [walkCount, W, show 2 + n + 1 = n + 3 by omega] using walk_bridge n 2

  -- Positive lists are used only as the blocks-image of the pinned Composition fintype.
  let balance : List ℕ → ℤ :=
    List.foldr (fun a z => (if a % 2 = 0 then 1 else 0) - z) 0
  have bcons (a : ℕ) (l : List ℕ) :
      balance (a :: l) = (if a % 2 = 0 then 1 else 0) - balance l := rfl
  let C (m : ℕ) (b : ℤ) : Finset (Composition m) :=
    Finset.univ.filter (fun c => balance c.blocks = b)
  let U (m : ℕ) : Finset (List ℕ) :=
    (Finset.univ : Finset (Composition m)).image Composition.blocks
  let L (m : ℕ) (b : ℤ) : Finset (List ℕ) :=
    (U m).filter (fun l => balance l = b)
  have memU (m : ℕ) (l : List ℕ) :
      l ∈ U m ↔ (∀ a ∈ l, 0 < a) ∧ l.sum = m := by
    constructor
    · intro h
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨fun a ha => c.blocks_pos ha, c.blocks_sum⟩
    · rintro ⟨hp, hs⟩
      exact Finset.mem_image.mpr
        ⟨⟨l, fun {a} ha => hp a ha, hs⟩, Finset.mem_univ _, rfl⟩
  have memL (m : ℕ) (b : ℤ) (l : List ℕ) :
      l ∈ L m b ↔ (∀ a ∈ l, 0 < a) ∧ l.sum = m ∧ balance l = b := by
    simp only [L, Finset.mem_filter, memU, and_assoc]
  have Lcard (m : ℕ) (b : ℤ) : (L m b).card = (C m b).card := by
    dsimp only [L, U, C]
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _ (fun c d h => Composition.ext h)
  have positive_zero (l : List ℕ) (hp : ∀ a ∈ l, 0 < a)
      (hs : l.sum = 0) : l = [] := by
    cases l with
    | nil => rfl
    | cons a l =>
        have ha := hp a (by simp)
        simp only [List.sum_cons] at hs
        omega
  have positive_one (l : List ℕ) (hp : ∀ a ∈ l, 0 < a)
      (hs : l.sum = 1) : l = [1] := by
    cases l with
    | nil => simp at hs
    | cons a l =>
        have ha := hp a (by simp)
        have ht : ∀ x ∈ l, 0 < x := fun x hx => hp x (List.mem_cons_of_mem a hx)
        have hs' : a + l.sum = 1 := by simpa only [List.sum_cons] using hs
        have he := positive_zero l ht (by omega)
        subst l
        have he : a = 1 := by simpa using hs'
        subst a
        rfl
  have positive_two (l : List ℕ) (hp : ∀ a ∈ l, 0 < a)
      (hs : l.sum = 2) : l = [1, 1] ∨ l = [2] := by
    cases l with
    | nil => simp at hs
    | cons a l =>
        have ha := hp a (by simp)
        have ht : ∀ x ∈ l, 0 < x := fun x hx => hp x (List.mem_cons_of_mem a hx)
        have hs' : a + l.sum = 2 := by simpa only [List.sum_cons] using hs
        by_cases h : a = 1
        · subst a
          have he := positive_one l ht (by omega)
          subst l
          exact Or.inl rfl
        · have h2 : a = 2 := by omega
          subst a
          have he := positive_zero l ht (by omega)
          subst l
          exact Or.inr rfl
  have Uzero : U 0 = {[]} := by
    ext l
    rw [memU]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hs⟩
      exact positive_zero l hp hs
    · rintro rfl
      simp
  have Uone : U 1 = {[1]} := by
    ext l
    rw [memU]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hs⟩
      exact positive_one l hp hs
    · rintro rfl
      simp
  have Utwo : U 2 = {[1, 1], [2]} := by
    ext l
    rw [memU]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hs⟩
      exact positive_two l hp hs
    · rintro (rfl | rfl) <;> simp
  have Czero (b : ℤ) : (C 0 b).card = (if b = 0 then 1 else 0) := by
    rw [← Lcard]
    by_cases hb : b = 0 <;>
      simp [L, Uzero, Finset.filter_singleton, balance, hb, eq_comm]
  have Cone (b : ℤ) : (C 1 b).card = (if b = 0 then 1 else 0) := by
    rw [← Lcard]
    by_cases hb : b = 0 <;>
      simp [L, Uone, Finset.filter_singleton, balance, hb, eq_comm]
  have Ctwo (b : ℤ) :
      (C 2 b).card = (if b = 0 then 1 else 0) + (if b = 1 then 1 else 0) := by
    rw [← Lcard]
    by_cases h0 : b = 0
    · subst b
      norm_num [L, Utwo, Finset.filter_insert, Finset.filter_singleton, balance]
    by_cases h1 : b = 1
    · subst b
      norm_num [L, Utwo, Finset.filter_insert, Finset.filter_singleton, balance]
    simp [L, Utwo, Finset.filter_insert, Finset.filter_singleton, balance, h0, h1, eq_comm]
  let bump : List ℕ → List ℕ := fun l =>
    match l with
    | [] => []
    | a :: t => (a + 2) :: t
  have bump_injective : Function.Injective bump := by
    intro l t h
    cases l with
    | nil =>
        cases t with
        | nil => rfl
        | cons a t => simp [bump] at h
    | cons a l =>
        cases t with
        | nil => simp [bump] at h
        | cons c t =>
            simp only [bump, List.cons.injEq] at h
            have hac : a = c := by omega
            rw [hac, h.2]
  have Lsplit (m : ℕ) (b : ℤ) :
      L (m + 3) b =
        ((L (m + 1) b).image bump ∪ (L (m + 2) (-b)).image (List.cons 1)) ∪
          (L (m + 1) (1 - b)).image (List.cons 2) := by
    ext l
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · intro hl
      obtain ⟨hp, hs, hb⟩ := (memL _ _ _).mp hl
      cases l with
      | nil => simp at hs
      | cons a l =>
          have ha := hp a (by simp)
          have ht : ∀ x ∈ l, 0 < x := fun x hx => hp x (List.mem_cons_of_mem a hx)
          have hs' : a + l.sum = m + 3 := by simpa only [List.sum_cons] using hs
          by_cases h1 : a = 1
          · subst a
            apply Or.inl
            apply Or.inr
            refine ⟨l, (memL _ _ _).mpr ⟨ht, by omega, ?_⟩, rfl⟩
            norm_num [bcons] at hb
            omega
          by_cases h2 : a = 2
          · subst a
            apply Or.inr
            refine ⟨l, (memL _ _ _).mpr ⟨ht, by omega, ?_⟩, rfl⟩
            norm_num [bcons] at hb
            omega
          · apply Or.inl
            apply Or.inl
            have ha3 : 3 ≤ a := by omega
            have hpar : (a - 2) % 2 = a % 2 := by omega
            refine ⟨(a - 2) :: l, (memL _ _ _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · omega
              · exact ht x hx
            · simp only [List.sum_cons]
              omega
            · simpa only [bcons, hpar] using hb
            · dsimp only [bump]
              congr 1
              omega
    · rintro ((⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩)
      · obtain ⟨hp, hs, hb⟩ := (memL _ _ _).mp hl
        cases l with
        | nil => simp at hs
        | cons a l =>
            apply (memL _ _ _).mpr
            have hpar : (a + 2) % 2 = a % 2 := by omega
            refine ⟨?_, ?_, ?_⟩
            · intro x hx
              change x ∈ (a + 2) :: l at hx
              rcases List.mem_cons.mp hx with rfl | hx
              · omega
              · exact hp x (List.mem_cons_of_mem a hx)
            · change (a + 2) + l.sum = m + 3
              simp only [List.sum_cons] at hs
              omega
            · simpa only [bump, bcons, hpar] using hb
      · obtain ⟨hp, hs, hb⟩ := (memL _ _ _).mp hl
        apply (memL _ _ _).mpr
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · omega
          · exact hp x hx
        · simp only [List.sum_cons]
          omega
        · norm_num [bcons]
          omega
      · obtain ⟨hp, hs, hb⟩ := (memL _ _ _).mp hl
        apply (memL _ _ _).mpr
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · omega
          · exact hp x hx
        · simp only [List.sum_cons]
          omega
        · norm_num [bcons]
          omega
  have bump_disjoint_cons (m : ℕ) (b : ℤ) (S : Finset (List ℕ))
      (k : ℕ) (hk : k ≤ 2) :
      Disjoint ((L (m + 1) b).image bump) (S.image (List.cons k)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, _, he⟩ := Finset.mem_image.mp hx'
    obtain ⟨hp, hs, _⟩ := (memL _ _ _).mp hl
    cases l with
    | nil => simp at hs
    | cons a l =>
        have ha := hp a (by simp)
        change k :: t = (a + 2) :: l at he
        have hh := (List.cons.inj he).1
        omega
  have cons_disjoint (S T : Finset (List ℕ)) :
      Disjoint (S.image (List.cons 1)) (T.image (List.cons 2)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, _, he⟩ := Finset.mem_image.mp hx'
    have hh := (List.cons.inj he).1
    omega
  have Cr (m : ℕ) (b : ℤ) :
      (C (m + 3) b).card =
        (C (m + 1) b).card + (C (m + 2) (-b)).card + (C (m + 1) (1 - b)).card := by
    simp only [← Lcard]
    rw [Lsplit]
    have hAB := bump_disjoint_cons m b (L (m + 2) (-b)) 1 (by omega)
    have hAD := bump_disjoint_cons m b (L (m + 1) (1 - b)) 2 (by omega)
    have hBD := cons_disjoint (L (m + 2) (-b)) (L (m + 1) (1 - b))
    have hABD := Finset.disjoint_union_left.mpr ⟨hAD, hBD⟩
    rw [Finset.card_union_of_disjoint hABD, Finset.card_union_of_disjoint hAB,
      Finset.card_image_of_injective _ bump_injective,
      Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective]

  -- Index zero is position one, so its contribution has positive sign.
  have balance_indices : ∀ L : List ℕ,
      balance L =
        ((Finset.univ.filter (fun i : Fin L.length =>
          L[i.val] % 2 = 0 ∧ i.val % 2 = 0)).card : ℤ) -
        ((Finset.univ.filter (fun i : Fin L.length =>
          L[i.val] % 2 = 0 ∧ i.val % 2 = 1)).card : ℤ) := by
    intro L
    simp only [Finset.natCast_card_filter]
    induction L with
    | nil => simp [balance]
    | cons a L ih =>
        have heven (i : Fin L.length) :
            (i.val + 1) % 2 = 0 ↔ i.val % 2 = 1 := by omega
        have hodd (i : Fin L.length) :
            (i.val + 1) % 2 = 1 ↔ i.val % 2 = 0 := by omega
        change (if a % 2 = 0 then (1 : ℤ) else 0) - balance L = _
        rw [ih]
        simp only [List.length_cons, Fin.sum_univ_succ,
          Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
          List.getElem_cons_succ, heven, hodd]
        norm_num <;> ring
  -- Three consecutive states make the original recursion a single Nat.rec.
  -- In particular, no truncated subtraction is used at the small totals.
  let compositionCount : ℕ → ℤ → ℕ := fun m =>
    (Nat.rec (motive := fun _ => (ℤ → ℕ) × (ℤ → ℕ) × (ℤ → ℕ))
      ((fun b : ℤ => if b = 0 then (1 : ℕ) else 0),
        (fun b : ℤ => if b = 0 then (1 : ℕ) else 0),
        (fun b : ℤ => (if b = 0 then (1 : ℕ) else 0) + (if b = 1 then 1 else 0)))
      (fun _ (f : (ℤ → ℕ) × (ℤ → ℕ) × (ℤ → ℕ)) =>
        (f.2.1, f.2.2, fun b => f.2.1 b + f.2.2 (-b) + f.2.1 (1 - b))) m).1
  have composition_rec (m : ℕ) (b : ℤ) :
      compositionCount (m + 3) b = compositionCount (m + 1) b +
        compositionCount (m + 2) (-b) + compositionCount (m + 1) (1 - b) := rfl
  have composition_two (b : ℤ) :
      compositionCount 2 b = (if b = 0 then (1 : ℕ) else 0) + (if b = 1 then 1 else 0) := rfl
  have composition_three (b : ℤ) :
      compositionCount 3 b = (if b = 0 then (1 : ℕ) else 0)
        + ((if -b = 0 then (1 : ℕ) else 0) + (if -b = 1 then 1 else 0))
        + (if 1 - b = 0 then (1 : ℕ) else 0) := rfl
  have composition_bridge : ∀ (m : ℕ) (b : ℤ),
      (C m b).card = compositionCount m b := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro b
        rcases m with _ | _ | _ | m
        · exact Czero b
        · exact Cone b
        · exact Ctwo b
        · change (C (m + 3) b).card = compositionCount (m + 3) b
          rw [Cr, composition_rec, ih (m + 1) (by omega) b,
            ih (m + 2) (by omega) (-b), ih (m + 1) (by omega) (1 - b)]
  -- This bridge is uniform in the signed, literal index-count balance.
  have literal_composition_bridge (m : ℕ) (b : ℤ) :
      ((Finset.univ : Finset (Composition m)).filter (fun c =>
        ((Finset.univ.filter (fun i : Fin c.blocks.length =>
          c.blocks[i.val] % 2 = 0 ∧ i.val % 2 = 0)).card : ℤ) -
        ((Finset.univ.filter (fun i : Fin c.blocks.length =>
          c.blocks[i.val] % 2 = 0 ∧ i.val % 2 = 1)).card : ℤ) = b)).card =
          compositionCount m b := by
    simpa only [C, balance_indices] using composition_bridge m b
  have balanced_bridge (m : ℕ) : balancedCompositionCount m = compositionCount m 0 := by
    simpa only [balancedCompositionCount, sub_eq_zero, Int.natCast_inj] using
      literal_composition_bridge m 0

  -- The unrestricted walk kernel is Pascal's array in displacement coordinates.
  let w : ℕ → ℤ → ℕ := fun n =>
    Nat.rec (fun z : ℤ => if z = 0 then 1 else 0)
      (fun _ f z => f (z - 1) + f (z + 1)) n
  have wz (z : ℤ) : w 0 z = (if z = 0 then 1 else 0) := rfl
  have ws (n : ℕ) (z : ℤ) : w (n + 1) z = w n (z - 1) + w n (z + 1) := rfl
  have wn : ∀ (n : ℕ) (z : ℤ), w n (-z) = w n z := by
    intro n
    induction n with
    | zero => intro z; simp only [wz, neg_eq_zero]
    | succ n ih =>
        intro z
        rw [ws, ws, show -z - 1 = -(z + 1) by omega,
          show -z + 1 = -(z - 1) by omega, ih, ih, Nat.add_comm]

  -- Reflection followed by telescoping: the interval [-h-1,h], folded at zero.
  let s : ℕ → ℕ → ℕ := fun n h =>
    ∑ k ∈ Finset.range (h + 1), (w n (k : ℤ) + w n ((k : ℤ) + 1))
  have s0 (n : ℕ) : s n 0 = w n 0 + w n 1 := by simp [s]
  have ss (n h : ℕ) :
      s n (h + 1) = s n h + (w n ((h : ℤ) + 1) + w n ((h : ℤ) + 2)) := by
    simp only [s, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, add_assoc]
    norm_num
  have szero : ∀ h : ℕ, s 0 h = 1 := by
    intro h
    induction h with
    | zero => norm_num [s0, wz]
    | succ h ih =>
        simp (disch := omega) only [ss, ih, wz, if_neg, add_zero, zero_add]
  have sr0 (n : ℕ) : s (n + 1) 0 = s n 1 := by
    have hsym := wn n 1
    simp only [ss, s0, ws]
    ring_nf (config := { ifUnchanged := .silent }) at hsym ⊢
    omega
  have sr (n : ℕ) : ∀ h : ℕ, s (n + 1) (h + 1) = s n h + s n (h + 2) := by
    intro h
    induction h with
    | zero =>
        have hsym := wn n 1
        simp only [ss, s0, ws]
        ring_nf (config := { ifUnchanged := .silent }) at hsym ⊢
        omega
    | succ h ih =>
        simp only [ss, ws, Nat.cast_add, Nat.cast_one] at ih ⊢
        ring_nf (config := { ifUnchanged := .silent }) at ih ⊢
        omega
  have paths : ∀ n h : ℕ, pathCount n h = s n h := by
    intro n
    induction n with
    | zero => intro h; exact (szero h).symm
    | succ n ih =>
        intro h
        cases h with
        | zero =>
            change pathCount n 1 = s (n + 1) 0
            rw [ih 1, sr0]
        | succ h =>
            change pathCount n h + pathCount n (h + 2) = s (n + 1) (h + 1)
            rw [ih h, ih (h + 2), sr]

  -- Three of these six consecutive displacements have the required parity.
  -- This is the full-balance invariant, not just the balance-zero specialization.
  let q : ℕ → ℤ → ℕ := fun n b =>
    w n (3 * b - 3) + w n (3 * b - 2) + w n (3 * b - 1) +
      w n (3 * b) + w n (3 * b + 1) + w n (3 * b + 2)
  have qr (n : ℕ) (b : ℤ) :
      q (n + 2) b = q n b + q (n + 1) (-b) + q n (1 - b) := by
    have h0 := wn n (3 * b - 5)
    have h1 := wn n (3 * b - 4)
    have h2 := wn n (3 * b - 3)
    have h3 := wn n (3 * b - 2)
    have h4 := wn n (3 * b - 1)
    have h5 := wn n (3 * b)
    have h6 := wn n (3 * b + 1)
    have h7 := wn n (3 * b + 2)
    have h8 := wn n (3 * b + 3)
    have h9 := wn n (3 * b + 4)
    simp only [q, ws]
    ring_nf (config := { ifUnchanged := .silent }) at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
    omega
  have compositions : ∀ (n : ℕ) (b : ℤ), compositionCount (n + 2) b = q n b := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
        intro b
        simp only [composition_two, q, wz]
        by_cases h0 : b = 0
        · subst b; norm_num
        by_cases h1 : b = 1
        · subst b; norm_num
        have e1 : (3 * b - 3 : ℤ) ≠ 0 := by omega
        have e2 : (3 * b - 2 : ℤ) ≠ 0 := by omega
        have e3 : (3 * b - 1 : ℤ) ≠ 0 := by omega
        have e4 : (3 * b : ℤ) ≠ 0 := by omega
        have e5 : (3 * b + 1 : ℤ) ≠ 0 := by omega
        have e6 : (3 * b + 2 : ℤ) ≠ 0 := by omega
        simp only [if_neg h0, if_neg h1, if_neg e1, if_neg e2, if_neg e3, if_neg e4,
          if_neg e5, if_neg e6, Nat.add_zero, Nat.zero_add]
    | one =>
        intro b
        simp only [composition_three, q, ws, wz]
        by_cases h0 : b = 0
        · subst b; norm_num
        by_cases h1 : b = 1
        · subst b; norm_num
        by_cases hm1 : b = -1
        · subst b; norm_num
        -- the kernel at length one splits each displacement into two, so the conditions
        -- appear in the literal shapes below; b is none of 0, 1, -1 and the rest are
        -- congruences three never satisfies
        have hnb : (-b : ℤ) ≠ 0 := by omega
        have hnb1 : (-b : ℤ) ≠ 1 := by omega
        have h1b : (1 - b : ℤ) ≠ 0 := by omega
        have a1 : (3 * b - 3 - 1 : ℤ) ≠ 0 := by omega
        have a2 : (3 * b - 3 + 1 : ℤ) ≠ 0 := by omega
        have a3 : (3 * b - 2 - 1 : ℤ) ≠ 0 := by omega
        have a4 : (3 * b - 2 + 1 : ℤ) ≠ 0 := by omega
        have a5 : (3 * b - 1 - 1 : ℤ) ≠ 0 := by omega
        have a6 : (3 * b - 1 + 1 : ℤ) ≠ 0 := by omega
        have a7 : (3 * b - 1 : ℤ) ≠ 0 := by omega
        have a8 : (3 * b + 1 : ℤ) ≠ 0 := by omega
        have a9 : (3 * b + 1 - 1 : ℤ) ≠ 0 := by omega
        have a10 : (3 * b + 1 + 1 : ℤ) ≠ 0 := by omega
        have a11 : (3 * b + 2 - 1 : ℤ) ≠ 0 := by omega
        have a12 : (3 * b + 2 + 1 : ℤ) ≠ 0 := by omega
        simp only [if_neg h0, if_neg hnb, if_neg hnb1, if_neg h1b,
          if_neg a1, if_neg a2, if_neg a3, if_neg a4, if_neg a5, if_neg a6,
          if_neg a7, if_neg a8, if_neg a9, if_neg a10, if_neg a11, if_neg a12,
          Nat.add_zero, Nat.zero_add]
    | more n ih0 ih1 =>
        intro b
        change compositionCount (n + 2) b + compositionCount (n + 3) (-b) +
          compositionCount (n + 2) (1 - b) = q (n + 2) b
        rw [ih0 b, ih1 (-b), ih0 (1 - b)]
        exact (qr n b).symm

  intro n
  rw [literal_walk_bridge, balanced_bridge, paths n 2, compositions n 0]
  have h1 := wn n 1
  have h2 := wn n 2
  have h3 := wn n 3
  simp only [ss, s0, q]
  ring_nf (config := { ifUnchanged := .silent }) at h1 h2 h3 ⊢
  omega

end D5.S3.Combinatorics.BalancedCompositionPaths

/- GID: D5/S3/Observer/Separation/BooleanRankFour
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/BooleanRankFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A six-by-five Boolean task of cycle rank four forces the exact uniform ordered budget region. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Separation.BooleanRankFour

/-- `none` denotes an illegal pair, and `some c` a legal pair with output `c`. -/
def Task (X Y : Type) := X → Y → Option Bool

def leftConflict {X Y : Type} (T : Task X Y) : SimpleGraph X where
  Adj x x' := ∃ y c c', T x y = some c ∧ T x' y = some c' ∧ c ≠ c'
  symm := ⟨by
    rintro x x' ⟨y, c, c', h, h', hn⟩
    exact ⟨y, c', c, h', h, hn.symm⟩⟩
  loopless := ⟨by
    rintro x ⟨y, c, c', h, h', hn⟩
    exact hn (Option.some.inj (h.symm.trans h'))⟩

def rightConflict {X Y : Type} (T : Task X Y) : SimpleGraph Y :=
  leftConflict (fun y x => T x y)

def support {X Y : Type} (T : Task X Y) : SimpleGraph (X ⊕ Y) where
  Adj v w := match v, w with
    | .inl x, .inr y => (T x y).isSome = true
    | .inr y, .inl x => (T x y).isSome = true
    | _, _ => False
  symm := ⟨by intro v w; cases v <;> cases w <;> exact id⟩
  loopless := ⟨by intro v; cases v <;> exact id⟩

/-- Inputs are precisely active inputs; support is nonempty and connected. -/
def ActiveConnected {X Y : Type} (T : Task X Y) : Prop :=
  (∃ x y c, T x y = some c) ∧
  (∀ x, ∃ y c, T x y = some c) ∧
  (∀ y, ∃ x c, T x y = some c) ∧ (support T).Connected

/-- The connected cyclomatic number, computed in the integers. -/
noncomputable def cycleRank {X Y : Type} (T : Task X Y) : ℤ :=
  (Nat.card {e : X × Y // (T e.1 e.2).isSome = true} : ℤ) -
    (Nat.card X : ℤ) - (Nat.card Y : ℤ) + 1

/-- Arbitrary ambient message alphabets, with only their reachable images charged. -/
def Admits {X Y : Type} (T : Task X Y) (p q : ℕ) : Prop :=
  ∃ (A B : Type) (a : X → A) (b : Y → B) (d : A → B → Bool),
    Nat.card (Set.range a) ≤ p ∧ Nat.card (Set.range b) ≤ q ∧
    ∀ x y c, T x y = some c → d (a x) (b y) = c

def Region (p q : ℕ) : Prop := 2 ≤ p ∧ 2 ≤ q ∧ 4 ≤ max p q

/-- A protocol may be chosen separately for each member of the entire class. -/
def Uniform (s : ℤ) (p q : ℕ) : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (T : Task X Y),
    ActiveConnected T → cycleRank T ≤ s →
    (leftConflict T).chromaticNumber ≤ 2 →
    (rightConflict T).chromaticNumber ≤ 2 → Admits T p q

/-- The fourteen legal pairs of the six by five obstruction. -/
def F4 : Task (Fin 6) (Fin 5) :=
  ![![some true, none, some false, none, none],
    ![none, some false, none, some true, some true],
    ![some true, none, none, some true, none],
    ![some false, none, none, some false, none],
    ![none, some true, some false, some false, none],
    ![some false, none, none, none, some true]]

/-- Rank four already forces the exact uniform ordered budget region for every
higher rank bound, with arbitrary alphabets and legal-pair correctness. -/
theorem result :
    ActiveConnected F4 ∧ cycleRank F4 = 4 ∧
    (leftConflict F4).chromaticNumber = 2 ∧
    (rightConflict F4).chromaticNumber = 2 ∧
    (∀ p q, Admits F4 p q ↔ Region p q) ∧
    (∀ s : ℤ, 4 ≤ s → ∀ p q, Uniform s p q ↔ Region p q) := by
  classical
  -- Relabel only the actual reachable image. Ambient alphabets need not be finite.
  have relabel {X A : Type} [Fintype X] (a : X → A) (k : ℕ)
      (h : Nat.card (Set.range a) ≤ k) :
      ∃ a' : X → Fin k, ∀ x x', a' x = a' x' ↔ a x = a x' := by
    let : Fintype (Set.range a) := Fintype.ofFinite _
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card (Set.range a) ≤ Fintype.card (Fin k) by
        simpa [Nat.card_eq_fintype_card] using h)
    refine ⟨fun x => e ⟨a x, ⟨x, rfl⟩⟩, ?_⟩
    intro x x'
    constructor
    · intro h; exact congrArg Subtype.val (e.injective h)
    · intro h; exact congrArg e (Subtype.ext h)
  -- Response words give the two endpoints on every task, including empty color classes.
  have endpoint {X Y : Type} [Fintype X] [Fintype Y] (T : Task X Y)
      (hc : (leftConflict T).Colorable 2) : Admits T 2 4 := by
    obtain ⟨a⟩ := hc
    let b : Y → (Fin 2 → Bool) := fun y i =>
      if h : ∃ x c, a x = i ∧ T x y = some c then h.choose_spec.choose else false
    have hb (x : X) (y : Y) (c : Bool) (h : T x y = some c) : b y (a x) = c := by
      have hex : ∃ x' c', a x' = a x ∧ T x' y = some c' := ⟨x, c, rfl, h⟩
      dsimp [b]
      rw [dif_pos hex]
      have hh := hex.choose_spec.choose_spec
      by_contra hn
      exact a.valid ⟨y, _, c, hh.2, h, hn⟩ hh.1
    refine ⟨Fin 2, Fin 2 → Bool, a, b, fun i t => t i, ?_, ?_, ?_⟩
    · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
        (by simp)
    · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
        (by simp)
    · exact hb
  have upper {X Y : Type} [Fintype X] [Fintype Y] (T : Task X Y)
      (ha : (leftConflict T).chromaticNumber ≤ 2)
      (hb : (rightConflict T).chromaticNumber ≤ 2)
      (p q : ℕ) (hr : Region p q) : Admits T p q := by
    obtain ⟨hp, hq, hm⟩ := hr
    rcases le_max_iff.mp hm with hp4 | hq4
    · obtain ⟨A, B, a, b, d, ha', hb', hd⟩ :=
        endpoint (fun y x => T x y) (SimpleGraph.chromaticNumber_le_iff_colorable.mp hb)
      exact ⟨B, A, b, a, fun j i => d i j, hb'.trans hp4, ha'.trans hq,
        fun x y c h => hd y x c h⟩
    · obtain ⟨A, B, a, b, d, ha', hb', hd⟩ :=
        endpoint T (SimpleGraph.chromaticNumber_le_iff_colorable.mp ha)
      exact ⟨A, B, a, b, d, ha'.trans hp, hb'.trans hq4, hd⟩
  have active : ActiveConnected F4 := by
    refine ⟨⟨0, 0, true, rfl⟩, ?_, ?_, ?_⟩
    · decide
    · decide
    · apply (support F4).connected_iff_exists_forall_reachable.mpr
      refine ⟨Sum.inr 0, ?_⟩
      have edge (i : Fin 6) (j : Fin 5) (h : (F4 i j).isSome = true) :
          (support F4).Reachable (.inl i) (.inr j) :=
        SimpleGraph.Adj.reachable h
      have h0 := (edge 0 0 (by decide)).symm
      have h2 := (edge 2 0 (by decide)).symm
      have h3 := (edge 3 0 (by decide)).symm
      have h5 := (edge 5 0 (by decide)).symm
      have h13 := h2.trans (edge 2 3 (by decide))
      have h1 := h13.trans (edge 1 3 (by decide)).symm
      have h4 := h13.trans (edge 4 3 (by decide)).symm
      intro v
      rcases v with i | j
      · fin_cases i <;> assumption
      · fin_cases j
        · exact SimpleGraph.Reachable.refl _
        · exact h1.trans (edge 1 1 (by decide))
        · exact h0.trans (edge 0 2 (by decide))
        · exact h13
        · exact h1.trans (edge 1 4 (by decide))
  have rank : cycleRank F4 = 4 := by
    unfold cycleRank
    simp only [Nat.card_eq_fintype_card]
    decide
  have ca : (leftConflict F4).Colorable 2 := by
    refine ⟨⟨![0, 0, 0, 1, 1, 1], ?_⟩⟩
    change ∀ i j, (leftConflict F4).Adj i j → _
    simp only [leftConflict, SimpleGraph.top_adj]
    decide
  have cb : (rightConflict F4).Colorable 2 := by
    refine ⟨⟨![0, 0, 1, 1, 1], ?_⟩⟩
    change ∀ i j, (rightConflict F4).Adj i j → _
    simp only [rightConflict, leftConflict, SimpleGraph.top_adj]
    decide
  have chiA : (leftConflict F4).chromaticNumber = 2 := by
    apply le_antisymm ca.chromaticNumber_le
    refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (f := ![0, 3]) (by simp) ?_
    simp only [Pairwise, leftConflict]
    decide
  have chiB : (rightConflict F4).chromaticNumber = 2 := by
    apply le_antisymm cb.chromaticNumber_le
    refine SimpleGraph.le_chromaticNumber_of_pairwise_adj (f := ![0, 2]) (by simp) ?_
    simp only [Pairwise, rightConflict, leftConflict]
    decide
  have lower (p q : ℕ) (h : Admits F4 p q) : Region p q := by
    obtain ⟨A, B, a, b, d, ha, hb, hd⟩ := h
    have ac : ∀ i j, (leftConflict F4).Adj i j → a i ≠ a j := by
      rintro i j ⟨y, c, c', hi, hj, hn⟩ he
      exact hn ((hd i y c hi).symm.trans (he ▸ hd j y c' hj))
    have bc : ∀ i j, (rightConflict F4).Adj i j → b i ≠ b j := by
      rintro i j ⟨x, c, c', hi, hj, hn⟩ he
      exact hn ((hd x i c hi).symm.trans (he ▸ hd x j c' hj))
    obtain ⟨a', ea⟩ := relabel a p ha
    obtain ⟨b', eb⟩ := relabel b q hb
    have hp : 2 ≤ p := by
      have hc : (leftConflict F4).Colorable p :=
        ⟨⟨a', fun {i j} h he => ac i j h ((ea i j).mp he)⟩⟩
      have := hc.chromaticNumber_le
      simpa [chiA] using this
    have hq : 2 ≤ q := by
      have hc : (rightConflict F4).Colorable q :=
        ⟨⟨b', fun {i j} h he => bc i j h ((eb i j).mp he)⟩⟩
      have := hc.chromaticNumber_le
      simpa [chiB] using this
    refine ⟨hp, hq, ?_⟩
    by_contra hn
    have hp3 : p ≤ 3 := by omega
    have hq3 : q ≤ 3 := by omega
    obtain ⟨a3, ea3⟩ := relabel a 3 (ha.trans hp3)
    obtain ⟨b3, eb3⟩ := relabel b 3 (hb.trans hq3)
    have ac3 : ∀ i j, (leftConflict F4).Adj i j → a3 i ≠ a3 j := by
      intro i j hc he
      exact ac i j hc ((ea3 i j).mp he)
    let parts : Fin 9 → Fin 6 → Fin 3 :=
      ![![0, 0, 0, 1, 1, 1], ![0, 0, 0, 1, 1, 2],
        ![0, 0, 0, 1, 2, 1], ![0, 0, 0, 1, 2, 2],
        ![0, 0, 1, 2, 2, 2], ![0, 1, 0, 2, 2, 2],
        ![0, 1, 1, 2, 2, 2], ![0, 1, 0, 2, 2, 1],
        ![0, 1, 1, 2, 0, 2]]
    have enumeration : ∀ (a0 a1 a2 a3 a4 a5 : Fin 3),
        let a : Fin 6 → Fin 3 := ![a0, a1, a2, a3, a4, a5]
        a 0 ≠ a 3 → a 0 ≠ a 5 → a 1 ≠ a 3 → a 1 ≠ a 4 →
        a 2 ≠ a 3 → a 2 ≠ a 4 → a 2 ≠ a 5 →
        ∃ k : Fin 9, ∀ i j, a i = a j ↔ parts k i = parts k j := by
      decide
    have hc (i j : Fin 6)
        (h : ∃ y c c', F4 i y = some c ∧ F4 j y = some c' ∧ c ≠ c') :
        a3 i ≠ a3 j := ac3 i j h
    obtain ⟨k, hk⟩ := enumeration (a3 0) (a3 1) (a3 2) (a3 3) (a3 4) (a3 5)
      (hc 0 3 (by decide)) (hc 0 5 (by decide))
      (hc 1 3 (by decide)) (hc 1 4 (by decide))
      (hc 2 3 (by decide)) (hc 2 4 (by decide)) (hc 2 5 (by decide))
    have ha3 : (![a3 0, a3 1, a3 2, a3 3, a3 4, a3 5] : Fin 6 → Fin 3) = a3 := by
      funext i
      fin_cases i <;> rfl
    simp only [ha3] at hk
    let cols : Fin 9 → Fin 4 → Fin 5 :=
      ![![0, 1, 2, 4], ![0, 1, 2, 4], ![0, 1, 2, 4],
        ![0, 1, 2, 4], ![0, 1, 2, 4], ![0, 1, 2, 4],
        ![0, 1, 2, 4], ![0, 1, 2, 3], ![0, 1, 3, 4]]
    have witnesses : ∀ k (j l : Fin 4), j ≠ l →
        ∃ (i t : Fin 6) (c c' : Bool),
          parts k i = parts k t ∧ F4 i (cols k j) = some c ∧
          F4 t (cols k l) = some c' ∧ c ≠ c' := by
      decide
    have hinj : Function.Injective (fun j : Fin 4 => b3 (cols k j)) := by
      intro j l he
      by_contra hjl
      obtain ⟨i, t, c, c', hit, hi, ht, hn⟩ := witnesses k j l hjl
      have hae := (ea3 i t).mp ((hk i t).mpr hit)
      have hbe := (eb3 (cols k j) (cols k l)).mp he
      apply hn
      calc
        c = d (a i) (b (cols k j)) := (hd i _ c hi).symm
        _ = d (a t) (b (cols k l)) := by rw [hae, hbe]
        _ = c' := hd t _ c' ht
    have bad := Fintype.card_le_of_injective _ hinj
    norm_num at bad
  refine ⟨active, rank, chiA, chiB, ?_, ?_⟩
  · intro p q
    exact ⟨lower p q, upper F4 chiA.le chiB.le p q⟩
  · intro s hs p q
    constructor
    · intro hu
      exact lower p q (hu (Fin 6) (Fin 5) F4 active (rank ▸ hs) chiA.le chiB.le)
    · intro hr X Y _ _ T _ _ ha hb
      exact upper T ha hb p q hr

end D5.S3.Observer.Separation.BooleanRankFour

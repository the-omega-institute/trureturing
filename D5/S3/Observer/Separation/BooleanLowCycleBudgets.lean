/- GID: D5/S3/Observer/Separation/BooleanLowCycleBudgets
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/BooleanLowCycleBudgets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Connected partial Boolean tasks of cycle rank at most two have exact uniform ordered message budgets. -/

import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SimpleGraph
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

namespace D5.S3.Observer.Separation.BooleanLowCycleBudgets

/-- A partial Boolean table; `none` is an illegal pair, never an output. -/
abbrev Task (X Y : Type) := X → Y → Option (ZMod 2)

def support {X Y : Type} (t : Task X Y) : SimpleGraph (X ⊕ Y) where
  Adj a b := match a, b with
    | .inl x, .inr y => t x y ≠ none
    | .inr y, .inl x => t x y ≠ none
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> exact not_false⟩

def conflictLeft {X Y : Type} (t : Task X Y) : SimpleGraph X where
  Adj x x' := ∃ y a b, t x y = some a ∧ t x' y = some b ∧ a ≠ b
  symm := ⟨by rintro x x' ⟨y,a,b,ha,hb,hab⟩; exact ⟨y,b,a,hb,ha,hab.symm⟩⟩
  loopless := ⟨by rintro x ⟨y,a,b,ha,hb,hab⟩; exact hab (Option.some.inj (ha.symm.trans hb))⟩

def conflictRight {X Y : Type} (t : Task X Y) : SimpleGraph Y :=
  conflictLeft (fun y x => t x y)

/-- Deterministic simultaneous messages, measured by reachable images only. -/
def HasBudget {X Y : Type} (t : Task X Y) (p q : ℕ) : Prop :=
  ∃ (A B : Type) (α : X → A) (β : Y → B) (δ : A → B → ZMod 2),
    Nat.card (Set.range α) ≤ p ∧ Nat.card (Set.range β) ≤ q ∧
    ∀ x y b, t x y = some b → δ (α x) (β y) = b

/-- All active connected finite tasks, with the original conflict chromatic bounds.
The cyclomatic expression is in integers, so no sequential subtraction truncates. -/
def InClass {X Y : Type} [Fintype X] [Fintype Y] (t : Task X Y) (s : ℕ) : Prop :=
  (∀ x, ∃ y b, t x y = some b) ∧
  (∀ y, ∃ x b, t x y = some b) ∧
  (∃ x y b, t x y = some b) ∧
  (support t).Connected ∧
  (conflictLeft t).chromaticNumber ≤ 2 ∧
  (conflictRight t).chromaticNumber ≤ 2 ∧
  (Nat.card {xy : X × Y // t xy.1 xy.2 ≠ none} : ℤ) + 1 -
    (Fintype.card X : ℤ) - (Fintype.card Y : ℤ) ≤ (s : ℤ)

def UniformBudget (s p q : ℕ) : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (t : Task X Y),
    InClass t s → HasBudget t p q

/-- The symmetric extension is only used on support edges. -/
def edgeValue {X Y : Type} (t : Task X Y) (e : Sym2 (X ⊕ Y)) : ZMod 2 :=
  Sym2.lift ⟨(fun a b => match a, b with
    | .inl x, .inr y => (t x y).getD 0
    | .inr y, .inl x => (t x y).getD 0
    | _, _ => 0), by intro a b; cases a <;> cases b <;> rfl⟩ e

/-- Exact class-wide classification, with an independently chosen protocol for each task. -/
theorem result (s p q : ℕ) (hs : s ≤ 2) (hp : 0 < p) (hq : 0 < q) :
    UniformBudget s p q ↔ 2 ≤ p ∧ 2 ≤ q ∧ s + 4 ≤ p + q := by
  classical
  have compress {X Y : Type} [Fintype X] [Fintype Y] (t : Task X Y) (p q : ℕ) :
      HasBudget t p q ↔ ∃ (α : X → Fin p) (β : Y → Fin q)
        (δ : Fin p → Fin q → ZMod 2),
        ∀ x y b, t x y = some b → δ (α x) (β y) = b := by
    constructor
    · rintro ⟨A,B,α,β,δ,ha,hb,hδ⟩
      letI : Fintype (Set.range α) := Fintype.ofFinite _
      letI : Fintype (Set.range β) := Fintype.ofFinite _
      let ea : Set.range α ↪ Fin p :=
        (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (by simpa using ha))
      let eb : Set.range β ↪ Fin q :=
        (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (by simpa using hb))
      let a := fun x => ea ⟨α x, ⟨x,rfl⟩⟩
      let b := fun y => eb ⟨β y, ⟨y,rfl⟩⟩
      let d := fun i j => if h : ∃ x y, a x = i ∧ b y = j then
        δ (α h.choose) (β h.choose_spec.choose) else 0
      refine ⟨a,b,d,?_⟩
      intro x y c hc
      have hex : ∃ x' y', a x' = a x ∧ b y' = b y := ⟨x,y,rfl,rfl⟩
      dsimp [d]
      rw [dif_pos hex]
      have ax : α hex.choose = α x :=
        congrArg Subtype.val (ea.injective hex.choose_spec.choose_spec.1)
      have by' : β hex.choose_spec.choose = β y :=
        congrArg Subtype.val (eb.injective hex.choose_spec.choose_spec.2)
      rw [ax,by']
      exact hδ x y c hc
    · rintro ⟨α,β,δ,hδ⟩
      refine ⟨Fin p,Fin q,α,β,δ,?_,?_,hδ⟩
      · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (by simp)
      · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (by simp)
  have mono {X Y : Type} (t : Task X Y) {a b c d : ℕ}
      (h : HasBudget t a b) (hac : a ≤ c) (hbd : b ≤ d) : HasBudget t c d := by
    obtain ⟨A,B,α,β,δ,ha,hb,hδ⟩ := h
    exact ⟨A,B,α,β,δ,ha.trans hac,hb.trans hbd,hδ⟩
  have graphFacts {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
      (∀ y : G.edgeSet → ZMod 2,
        (∃ x, edgeDifferential G x = y) ↔
          ∀ v (w : G.Walk v v), w.IsCycle → walkParity y w = 0) ∧
      (Module.finrank (ZMod 2) (simpleCycleSpace G) : ℤ) =
        (Nat.card G.edgeSet : ℤ) - (Fintype.card V : ℤ) +
          (Nat.card G.ConnectedComponent : ℤ) := by
    letI : Fintype G.edgeSet := Fintype.ofFinite _
    letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
    letI : MeasurableSpace (ZMod 2) := ⊤
    letI : MeasurableSingletonClass (ZMod 2) := ⟨fun _ => trivial⟩
    obtain ⟨⟨_,_,_,criterion⟩,⟨T,hle,hacyc,hreach⟩,basis⟩ := finite_graph_cycle_space G
    obtain ⟨cycles,_,_,_,basis,_,_,_,_,_,hcard,hdim,_⟩ := basis T hle hacyc hreach
    refine ⟨fun y => (criterion y).1,?_⟩
    rw [hdim]
    simpa only [Nat.card_eq_fintype_card] using hcard
  have upper {X Y : Type} [Fintype X] [Fintype Y] (t : Task X Y)
      (ht : InClass t s) (hnums : 2 ≤ p ∧ 2 ≤ q ∧ s + 4 ≤ p + q) : HasBudget t p q := by
    obtain ⟨hactX,hactY,hne,hconn,hcolX,hcolY,hrank⟩ := ht
    let G := support t
    let V := X ⊕ Y
    letI : Fintype G.edgeSet := Fintype.ofFinite _
    let legalEdge : {xy : X × Y // t xy.1 xy.2 ≠ none} → G.edgeSet :=
      fun xy => ⟨s(Sum.inl xy.val.1, Sum.inr xy.val.2),xy.property⟩
    have legalBij : Function.Bijective legalEdge := by
      constructor
      · intro a b hab
        have he := congrArg Subtype.val hab
        have he' : a.val.1 = b.val.1 ∧ a.val.2 = b.val.2 := by
          simpa only [legalEdge, Sym2.eq_iff, Prod.mk.injEq, Sum.inl.injEq,
            Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, and_self, or_false] using he
        exact Subtype.ext (Prod.ext he'.1 he'.2)
      · rintro ⟨e,he⟩
        induction e using Sym2.inductionOn with | _ a b =>
          cases a with
          | inl x =>
            cases b with
            | inl x' => exact False.elim he
            | inr y => exact ⟨⟨(x,y),he⟩,rfl⟩
          | inr y =>
            cases b with
            | inl x => exact ⟨⟨(x,y),he⟩,Subtype.ext Sym2.eq_swap⟩
            | inr y' => exact False.elim he
    have edgeCard : Nat.card G.edgeSet = Nat.card {xy : X × Y // t xy.1 xy.2 ≠ none} :=
      (Nat.card_congr (Equiv.ofBijective legalEdge legalBij)).symm
    letI : Nonempty V := ⟨Sum.inl hne.choose⟩
    letI : Subsingleton G.ConnectedComponent := hconn.preconnected.subsingleton_connectedComponent
    have rankG : Module.finrank (ZMod 2) (simpleCycleSpace G) ≤ s := by
      have hdim := (graphFacts G).2
      have cc : Nat.card G.ConnectedComponent = 1 := Nat.card_unique
      rw [edgeCard,cc] at hdim
      simp only [Fintype.card_sum,Nat.cast_add,Nat.cast_one] at hdim
      omega
    let cx : (conflictLeft t).Coloring (ZMod 2) :=
      (chromaticNumber_le_iff_colorable.mp hcolX).toColoring (by simp [ZMod.card])
    let cy : (conflictRight t).Coloring (ZMod 2) :=
      (chromaticNumber_le_iff_colorable.mp hcolY).toColoring (by simp [ZMod.card])
    have sameX (x x' : X) (y : Y) (a b : ZMod 2)
        (ha : t x y = some a) (hb : t x' y = some b) (hc : cx x = cx x') : a = b := by
      by_contra hab
      exact cx.valid ⟨y,a,b,ha,hb,hab⟩ hc
    have sameY (x : X) (y y' : Y) (a b : ZMod 2)
        (ha : t x y = some a) (hb : t x y' = some b) (hc : cy y = cy y') : a = b := by
      by_contra hab
      exact cy.valid ⟨x,a,b,ha,hb,hab⟩ hc
    have responses {A B : Type} (t' : Task A B) (color : B → ZMod 2)
        (consistent : ∀ a b b' c d, t' a b = some c → t' a b' = some d →
          color b = color b' → c = d) :
        ∃ r : A → ZMod 2 → ZMod 2, ∀ a b c, t' a b = some c → r a (color b) = c := by
      let r := fun a i => if h : ∃ b c, t' a b = some c ∧ color b = i then
        h.choose_spec.choose else 0
      refine ⟨r,?_⟩
      intro a b c hc
      have hex : ∃ b' c', t' a b' = some c' ∧ color b' = color b := ⟨b,c,hc,rfl⟩
      dsimp [r]
      rw [dif_pos hex]
      exact consistent a hex.choose b _ c hex.choose_spec.choose_spec.1 hc
        hex.choose_spec.choose_spec.2
    obtain ⟨rx,hrx⟩ := responses t cy sameY
    obtain ⟨ry,hry⟩ := responses (fun y x => t x y) cx (fun y x x' => sameX x x' y)
    have endpointX : HasBudget t 2 4 := by
      refine ⟨ZMod 2,(ZMod 2 → ZMod 2),cx,ry,(fun i r => r i),?_,?_,?_⟩
      · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (by simp [ZMod.card])
      · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (by norm_num [Nat.card_eq_fintype_card, ZMod.card])
      · intro x y b hb; exact hry y x b hb
    have endpointY : HasBudget t 4 2 := by
      refine ⟨(ZMod 2 → ZMod 2),ZMod 2,rx,cy,(fun r j => r j),?_,?_,?_⟩
      · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (by norm_num [Nat.card_eq_fintype_card, ZMod.card])
      · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (by simp [ZMod.card])
      · intro x y b hb; exact hrx x y b hb
    by_cases hp4 : 4 ≤ p
    · exact mono t endpointY hp4 hnums.2.1
    by_cases hq4 : 4 ≤ q
    · exact mono t endpointX hnums.1 hq4
    have boolWord : ∀ r : ZMod 2 → ZMod 2,
        (∀ j, r j = r 0) ∨ (∀ j, r j = r 0 + j) := by decide
    let mx : X → Prop := fun x => ∀ j, rx x j = rx x 0
    let my : Y → Prop := fun y => ∀ i, ry y i = ry y 0
    have offsetX (x : X) (hx : ¬ mx x) : ∀ y b, t x y = some b → b = rx x 0 + cy y := by
      have hx' := (boolWord (rx x)).resolve_left hx
      intro y b hb
      rw [← hrx x y b hb, hx']
    have offsetY (y : Y) (hy : ¬ my y) : ∀ x b, t x y = some b → b = cx x + ry y 0 := by
      have hy' := (boolWord (ry y)).resolve_left hy
      intro x b hb
      rw [← hry y x b hb, hy', add_comm]
    have monoX (x : X) (hx : mx x) : ∀ y b, t x y = some b → b = rx x 0 := by
      intro y b hb; rw [← hrx x y b hb]; exact hx _
    have monoY (y : Y) (hy : my y) : ∀ x b, t x y = some b → b = ry y 0 := by
      intro x b hb; rw [← hry y x b hb]; exact hy _
    let K := fun H : SimpleGraph V => Submodule.span (ZMod 2)
      {z : G.edgeSet → ZMod 2 | ∃ (v : V) (w : H.Walk v v), w.IsCycle ∧
        z = fun e => if e.val ∈ w.edges then 1 else 0}
    change Module.finrank (ZMod 2) (K G) ≤ s at rankG
    have kle (H J : SimpleGraph V) (hle : H ≤ J) : K H ≤ K J := by
      apply Submodule.span_le.mpr
      rintro z ⟨v,w,hw,rfl⟩
      apply Submodule.subset_span
      exact ⟨v,w.mapLe hle,hw.mapLe hle,by simp only [Walk.edges_mapLe_eq_edges]⟩
    have kzero (H : SimpleGraph V) (hle : H ≤ G)
        (hdim : Module.finrank (ZMod 2) (K H) = 0) : H.IsAcyclic := by
      intro v w hw
      have hn : w.edges ≠ [] := fun h => hw.not_nil (Walk.edges_eq_nil.mp h)
      obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil w.edges hn
      have heg : e ∈ G.edgeSet := (edgeSet_mono hle) (w.edges_subset_edgeSet he)
      let z : K H := ⟨(fun e => if e.val ∈ w.edges then 1 else 0),
        Submodule.subset_span ⟨v,w,hw,rfl⟩⟩
      have zzero : z = 0 := (Module.finrank_zero_iff.mp hdim).elim z 0
      have atEdge := congrArg (fun z : K H => z.val ⟨e,heg⟩) zzero
      exact (one_ne_zero : (1 : ZMod 2) ≠ 0) (by simpa [z, he] using atEdge)
    let cut := fun (H : SimpleGraph V) (v : V) =>
      ({ Adj a b := H.Adj a b ∧ a ≠ v ∧ b ≠ v
         symm := ⟨by rintro a b ⟨hab,ha,hb⟩; exact ⟨hab.symm,hb,ha⟩⟩
         loopless := ⟨by intro a ha; exact H.irrefl ha.1⟩ } : SimpleGraph V)
    have cutle (H : SimpleGraph V) (v : V) : cut H v ≤ H := fun _ _ h => h.1
    have drop (H : SimpleGraph V) (hle : H ≤ G) (a b : V)
        (v : V) (w : H.Walk v v) (hw : w.IsCycle) (he : s(a,b) ∈ w.edges) :
        Module.finrank (ZMod 2) (K (cut H a)) < Module.finrank (ZMod 2) (K H) := by
      have heg : s(a,b) ∈ G.edgeSet := (edgeSet_mono hle) (w.edges_subset_edgeSet he)
      have hz : ∀ z ∈ K (cut H a), z ⟨s(a,b),heg⟩ = 0 := by
        intro z hz
        refine Submodule.span_induction (fun z hz => ?_) ?_ ?_ ?_ hz
        · obtain ⟨v',w',hw',rfl⟩ := hz
          have hn : s(a,b) ∉ w'.edges := by
            intro hh
            have hh' : (cut H a).Adj a b := w'.edges_subset_edgeSet hh
            exact hh'.2.1 rfl
          change (if s(a,b) ∈ w'.edges then (1 : ZMod 2) else 0) = 0
          exact if_neg hn
        · rfl
        · intro x y _ _ hx hy; simp only [Pi.add_apply,hx,hy,add_zero]
        · intro r x _ hx; simp only [Pi.smul_apply,hx,smul_zero]
      apply Submodule.finrank_lt_finrank_of_lt
      refine lt_of_le_of_ne (kle _ _ (cutle H a)) ?_
      intro hEq
      have hm : (fun e : G.edgeSet => if e.val ∈ w.edges then (1 : ZMod 2) else 0) ∈ K H :=
        Submodule.subset_span ⟨v,w,hw,rfl⟩
      rw [← hEq] at hm
      have bad := hz _ hm
      change (if s(a,b) ∈ w.edges then (1 : ZMod 2) else 0) = 0 at bad
      rw [if_pos he] at bad
      exact one_ne_zero bad
    have oddEdge (H : SimpleGraph V) (pot : V → ZMod 2)
        (v : V) (w : H.Walk v v)
        (hw : w.IsCycle) (hodd : walkParity (fun e : H.edgeSet => edgeValue t e.val) w ≠ 0) :
        ∃ e : H.edgeSet, e.val ∈ w.edges ∧
          edgeValue t e.val ≠ edgeDifferential H pot e := by
      by_contra hn
      push Not at hn
      have hp0 := ((graphFacts H).1 (edgeDifferential H pot)).mp ⟨pot,rfl⟩ v w hw
      apply hodd
      rw [← hp0]
      unfold walkParity
      congr 1
      apply List.map_congr_left
      intro e he
      have he' := w.edges_subset_edgeSet he
      simp only [dif_pos he']
      exact hn ⟨e,he'⟩ he
    have hitsX (H : SimpleGraph V) (hle : H ≤ G) (v : V) (w : H.Walk v v)
        (hw : w.IsCycle) (hodd : walkParity (fun e : H.edgeSet => edgeValue t e.val) w ≠ 0) :
        ∃ x y, s(Sum.inl x,Sum.inr y) ∈ w.edges ∧ mx x := by
      obtain ⟨e,hem,hed⟩ := oddEdge H (Sum.elim (fun x => rx x 0) cy) v w hw hodd
      obtain ⟨xy,hxy⟩ := legalBij.2 ⟨e.val,(edgeSet_mono hle) e.property⟩
      have heq := congrArg Subtype.val hxy
      change s(Sum.inl xy.val.1,Sum.inr xy.val.2) = e.val at heq
      refine ⟨xy.val.1,xy.val.2,heq ▸ hem,?_⟩
      by_contra hnm
      obtain ⟨b,hb⟩ := Option.ne_none_iff_exists.mp xy.property
      have hoff := offsetX xy.val.1 hnm xy.val.2 b hb.symm
      apply hed
      have eval : edgeDifferential H (Sum.elim (fun x => rx x 0) cy) e =
          rx xy.val.1 0 + cy xy.val.2 := by
        change (endpointCharacters H e) _ = _
        unfold endpointCharacters
        rw [← heq]
        rfl
      rw [eval,← heq]
      simpa only [edgeValue,Sym2.lift_mk,hb.symm,Option.getD_some] using hoff
    have hitsY (H : SimpleGraph V) (hle : H ≤ G) (v : V) (w : H.Walk v v)
        (hw : w.IsCycle) (hodd : walkParity (fun e : H.edgeSet => edgeValue t e.val) w ≠ 0) :
        ∃ x y, s(Sum.inl x,Sum.inr y) ∈ w.edges ∧ my y := by
      obtain ⟨e,hem,hed⟩ := oddEdge H (Sum.elim cx (fun y => ry y 0)) v w hw hodd
      obtain ⟨xy,hxy⟩ := legalBij.2 ⟨e.val,(edgeSet_mono hle) e.property⟩
      have heq := congrArg Subtype.val hxy
      change s(Sum.inl xy.val.1,Sum.inr xy.val.2) = e.val at heq
      refine ⟨xy.val.1,xy.val.2,heq ▸ hem,?_⟩
      by_contra hnm
      obtain ⟨b,hb⟩ := Option.ne_none_iff_exists.mp xy.property
      have hoff := offsetY xy.val.2 hnm xy.val.1 b hb.symm
      apply hed
      have eval : edgeDifferential H (Sum.elim cx (fun y => ry y 0)) e =
          cx xy.val.1 + ry xy.val.2 0 := by
        change (endpointCharacters H e) _ = _
        unfold endpointCharacters
        rw [← heq]
        rfl
      rw [eval,← heq]
      simpa only [edgeValue,Sym2.lift_mk,hb.symm,Option.getD_some] using hoff
    have protocol (ax : Option X) (ay : Option Y) (H : SimpleGraph V)
        (hax : ∀ x, ax = some x → mx x) (hay : ∀ y, ay = some y → my y)
        (survive : ∀ x y b, t x y = some b → ax ≠ some x → ay ≠ some y →
          H.Adj (Sum.inl x) (Sum.inr y))
        (balanced : ∀ v (w : H.Walk v v), w.IsCycle →
          walkParity (fun e : H.edgeSet => edgeValue t e.val) w = 0) :
        HasBudget t (2 + (if ax.isSome then 1 else 0)) (2 + (if ay.isSome then 1 else 0)) := by
      obtain ⟨pot,hpot⟩ := ((graphFacts H).1 _).mpr balanced
      let A := ZMod 2 ⊕ {x : X // ax = some x}
      let B := ZMod 2 ⊕ {y : Y // ay = some y}
      let a : X → A := fun x => if hx : ax = some x then .inr ⟨x,hx⟩ else .inl (pot (.inl x))
      let b : Y → B := fun y => if hy : ay = some y then .inr ⟨y,hy⟩ else .inl (pot (.inr y))
      let d : A → B → ZMod 2 := fun i j => match i,j with
        | .inr x, _ => rx x.val 0
        | .inl _, .inr y => ry y.val 0
        | .inl i, .inl j => i + j
      have cardSel {Z : Type} [Fintype Z] (az : Option Z) :
          Nat.card {z : Z // az = some z} = if az.isSome then 1 else 0 := by
        cases az with
        | none => simp
        | some z => simp
      refine ⟨A,B,a,b,d,?_,?_,?_⟩
      · apply (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
        have hc : Nat.card A = 2 + (if ax.isSome then 1 else 0) := by
          change Nat.card (ZMod 2 ⊕ {x : X // ax = some x}) = _
          rw [Nat.card_sum,cardSel]
          simp only [Nat.card_eq_fintype_card,ZMod.card]
        exact hc.le
      · apply (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
        have hc : Nat.card B = 2 + (if ay.isSome then 1 else 0) := by
          change Nat.card (ZMod 2 ⊕ {y : Y // ay = some y}) = _
          rw [Nat.card_sum,cardSel]
          simp only [Nat.card_eq_fintype_card,ZMod.card]
        exact hc.le
      · intro x y c hc
        by_cases hx : ax = some x
        · by_cases hy : ay = some y
          · have equalBits : rx x 0 = ry y 0 :=
              (monoX x (hax x hx) y c hc).symm.trans (monoY y (hay y hy) x c hc)
            have hd : rx x 0 = c := equalBits.trans (monoY y (hay y hy) x c hc).symm
            simpa only [a,dif_pos hx,d] using hd
          · simpa only [a,dif_pos hx,d] using (monoX x (hax x hx) y c hc).symm
        · by_cases hy : ay = some y
          · simpa only [a,dif_neg hx,b,dif_pos hy,d] using (monoY y (hay y hy) x c hc).symm
          · have hadj := survive x y c hc hx hy
            have he := congrFun hpot ⟨s(Sum.inl x,Sum.inr y),hadj⟩
            change pot (.inl x) + pot (.inr y) = edgeValue t s(Sum.inl x,Sum.inr y) at he
            simpa only [a,dif_neg hx,b,dif_neg hy,d,edgeValue,Sym2.lift_mk,hc,Option.getD_some] using he
    let balanced := fun H : SimpleGraph V => ∀ v (w : H.Walk v v), w.IsCycle →
      walkParity (fun e : H.edgeSet => edgeValue t e.val) w = 0
    have acyclicBalanced (H : SimpleGraph V) (h : H.IsAcyclic) : balanced H := by
      intro v w hw; exact False.elim (h w hw)
    by_cases hbal : balanced G
    · have hb := protocol none none G (by simp) (by simp)
        (by intro x y b hb _ _; exact fun hn => by simpa [hn] using hb) hbal
      exact mono t hb (by simpa using hnums.1) (by simpa using hnums.2.1)
    have hcyc : ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧
        walkParity (fun e : G.edgeSet => edgeValue t e.val) w ≠ 0 := by
      by_contra hn
      apply hbal
      intro v w hw
      by_contra ho
      exact hn ⟨v,w,hw,ho⟩
    obtain ⟨v,w,hw,hodd⟩ := hcyc
    have rankpos : 0 < Module.finrank (ZMod 2) (K G) := by
      by_contra hn
      exact (kzero G le_rfl (by omega)) w hw
    by_cases hp2 : p = 2
    · have hs1 : s ≤ 1 := by omega
      obtain ⟨x,y,he,hy⟩ := hitsY G le_rfl v w hw hodd
      have he' : s(Sum.inr y,Sum.inl x) ∈ w.edges := by simpa only [Sym2.eq_swap] using he
      have hd := drop G le_rfl (Sum.inr y) (Sum.inl x) v w hw he'
      have hb : balanced (cut G (.inr y)) :=
        acyclicBalanced _ (kzero _ (cutle G (.inr y)) (by change Module.finrank (ZMod 2) (K G) ≤ s at rankG; omega))
      have hprot := protocol none (some y) (cut G (.inr y)) (by simp)
        (by intro y' hh; cases Option.some.inj hh; exact hy)
        (by
          intro x' y' b hb _ hy'
          refine ⟨?_,Sum.inl_ne_inr,?_⟩
          · exact fun hn => by simpa [hn] using hb
          · intro hh; apply hy'; exact congrArg some (Sum.inr.inj hh).symm) hb
      exact mono t hprot (by simp; omega) (by simp; omega)
    obtain ⟨x,y,he,hx⟩ := hitsX G le_rfl v w hw hodd
    have hd := drop G le_rfl (Sum.inl x) (Sum.inr y) v w hw he
    let H := cut G (.inl x)
    have hHG : H ≤ G := cutle G (.inl x)
    by_cases hbalH : balanced H
    · have hprot := protocol (some x) none H
        (by intro x' hh; cases Option.some.inj hh; exact hx) (by simp)
        (by
          intro x' y' b hb hx' _
          refine ⟨?_,?_,Sum.inr_ne_inl⟩
          · exact fun hn => by simpa [hn] using hb
          · intro hh; apply hx'; exact congrArg some (Sum.inl.inj hh).symm) hbalH
      exact mono t hprot (by simp; omega) (by simp; omega)
    have hcycH : ∃ (v' : V) (w' : H.Walk v' v'), w'.IsCycle ∧
        walkParity (fun e : H.edgeSet => edgeValue t e.val) w' ≠ 0 := by
      by_contra hn
      apply hbalH
      intro v w hw
      by_contra ho
      exact hn ⟨v,w,hw,ho⟩
    obtain ⟨v',w',hw',hodd'⟩ := hcycH
    obtain ⟨x',y',he',hy'⟩ := hitsY H hHG v' w' hw' hodd'
    have he'' : s(Sum.inr y',Sum.inl x') ∈ w'.edges := by simpa only [Sym2.eq_swap] using he'
    have hd' := drop H hHG (.inr y') (.inl x') v' w' hw' he''
    have rankHpos : 0 < Module.finrank (ZMod 2) (K H) := by
      by_contra hn; exact (kzero H hHG (by omega)) w' hw'
    have hfin : balanced (cut H (.inr y')) :=
      acyclicBalanced _ (kzero _ ((cutle H (.inr y')).trans hHG) (by
        change Module.finrank (ZMod 2) (K G) ≤ s at rankG
        change Module.finrank (ZMod 2) (K H) < Module.finrank (ZMod 2) (K G) at hd
        omega))
    have hprot := protocol (some x) (some y') (cut H (.inr y'))
      (by intro x'' hh; cases Option.some.inj hh; exact hx)
      (by intro y'' hh; cases Option.some.inj hh; exact hy')
      (by
        intro x'' y'' b hb hx'' hy''
        refine ⟨⟨?_,?_,Sum.inr_ne_inl⟩,Sum.inl_ne_inr,?_⟩
        · exact fun hn => by simpa [hn] using hb
        · intro hh; apply hx''; exact congrArg some (Sum.inl.inj hh).symm
        · intro hh; apply hy''; exact congrArg some (Sum.inr.inj hh).symm) hfin
    exact mono t hprot (by simp; omega) (by
      simp
      change Module.finrank (ZMod 2) (K G) ≤ s at rankG
      change Module.finrank (ZMod 2) (K H) < Module.finrank (ZMod 2) (K G) at hd
      omega)
  constructor
  · intro h
    let F0 : Task (Fin 2) (Fin 2) := ![![some 0,none],![some 1,some 0]]
    let F1 : Task (Fin 3) (Fin 3) :=
      ![![none,none,some 0],![some 0,some 1,some 1],![some 1,some 1,none]]
    let F2 : Task (Fin 5) (Fin 4) :=
      ![![some 0,some 0,none,none],![some 0,some 1,none,none],
        ![none,none,some 0,some 1],![none,none,some 1,some 1],
        ![none,some 0,some 1,none]]
    have edgeReach {A B : Type} (t : Task A B) (x : A) (y : B)
        (hb : t x y ≠ none) : (support t).Reachable (.inl x) (.inr y) :=
      (show (support t).Adj (.inl x) (.inr y) from hb).reachable
    have m0 : InClass F0 s := by
      refine ⟨by decide,by decide,⟨0,0,0,rfl⟩,?_,?_,?_,?_⟩
      · apply (connected_iff_exists_forall_reachable _).mpr
        have e00 := edgeReach F0 0 0 (by decide)
        have e10 := edgeReach F0 1 0 (by decide)
        have e11 := edgeReach F0 1 1 (by decide)
        refine ⟨.inl 1,?_⟩
        intro v
        cases v with
        | inl x => fin_cases x; exact e10.trans e00.symm; exact Reachable.refl _
        | inr y => fin_cases y; exact e10; exact e11
      · apply chromaticNumber_le_iff_colorable.mpr
        refine ⟨Coloring.mk (fun x : Fin 2 => x) ?_⟩
        dsimp only [conflictLeft,conflictRight]
        decide
      · apply chromaticNumber_le_iff_colorable.mpr
        refine ⟨Coloring.mk (fun y : Fin 2 => y) ?_⟩
        dsimp only [conflictLeft,conflictRight]
        decide
      · have hc : Nat.card {xy : Fin 2 × Fin 2 // F0 xy.1 xy.2 ≠ none} = 3 := by
          rw [Nat.card_eq_fintype_card]; decide
        rw [hc]; norm_num <;> omega
    obtain ⟨a0,b0,d0,hd0⟩ := (compress F0 p q).mp (h _ _ F0 m0)
    have a01 : a0 0 ≠ a0 1 := by
      intro he
      have h00 := hd0 0 0 0 rfl
      have h10 := hd0 1 0 1 rfl
      rw [he] at h00
      exact zero_ne_one (h00.symm.trans h10)
    have b01 : b0 0 ≠ b0 1 := by
      intro he
      have h10 := hd0 1 0 1 rfl
      have h11 := hd0 1 1 0 rfl
      rw [he] at h10
      exact one_ne_zero (h10.symm.trans h11)
    have hp2 : 2 ≤ p := by
      have := (a0 0).isLt
      have := (a0 1).isLt
      omega
    have hq2 : 2 ≤ q := by
      have := (b0 0).isLt
      have := (b0 1).isLt
      omega
    refine ⟨hp2,hq2,?_⟩
    by_contra hsum
    have sPos : 1 ≤ s := by omega
    have m1 : InClass F1 s := by
      refine ⟨by decide,by decide,⟨0,2,0,rfl⟩,?_,?_,?_,?_⟩
      · apply (connected_iff_exists_forall_reachable _).mpr
        have e02 := edgeReach F1 0 2 (by decide)
        have e10 := edgeReach F1 1 0 (by decide)
        have e11 := edgeReach F1 1 1 (by decide)
        have e12 := edgeReach F1 1 2 (by decide)
        have e20 := edgeReach F1 2 0 (by decide)
        refine ⟨.inl 1,?_⟩
        intro v
        cases v with
        | inl x => fin_cases x; exact e12.trans e02.symm; exact Reachable.refl _; exact e10.trans e20.symm
        | inr y => fin_cases y; exact e10; exact e11; exact e12
      · apply chromaticNumber_le_iff_colorable.mpr
        refine ⟨Coloring.mk (![0,1,0] : Fin 3 → Fin 2) ?_⟩
        dsimp only [conflictLeft,conflictRight]
        decide
      · apply chromaticNumber_le_iff_colorable.mpr
        refine ⟨Coloring.mk (![0,1,1] : Fin 3 → Fin 2) ?_⟩
        dsimp only [conflictLeft,conflictRight]
        decide
      · have hc : Nat.card {xy : Fin 3 × Fin 3 // F1 xy.1 xy.2 ≠ none} = 6 := by
          rw [Nat.card_eq_fintype_card]; decide
        rw [hc]; norm_num <;> omega
    have no22 : ¬ HasBudget F1 2 2 := by
      intro hh
      obtain ⟨a,b,d,hd⟩ := (compress F1 2 2).mp hh
      have neA01 : a 0 ≠ a 1 := by
        intro he
        have h0 := hd 0 2 0 rfl
        have h1 := hd 1 2 1 rfl
        rw [he] at h0
        exact zero_ne_one (h0.symm.trans h1)
      have neA12 : a 1 ≠ a 2 := by
        intro he
        have h0 := hd 1 0 0 rfl
        have h1 := hd 2 0 1 rfl
        rw [he] at h0
        exact zero_ne_one (h0.symm.trans h1)
      have neB01 : b 0 ≠ b 1 := by
        intro he
        have h0 := hd 1 0 0 rfl
        have h1 := hd 1 1 1 rfl
        rw [he] at h0
        exact zero_ne_one (h0.symm.trans h1)
      have neB02 : b 0 ≠ b 2 := by
        intro he
        have h0 := hd 1 0 0 rfl
        have h1 := hd 1 2 1 rfl
        rw [he] at h0
        exact zero_ne_one (h0.symm.trans h1)
      have ha : a 0 = a 2 := by omega
      have hb : b 1 = b 2 := by omega
      have h0 := hd 0 2 0 rfl
      have h1 := hd 2 1 1 rfl
      rw [ha,← hb] at h0
      exact zero_ne_one (h0.symm.trans h1)
    by_cases hs1 : s = 1
    · exact no22 (mono F1 (h _ _ F1 m1) (by omega) (by omega))
    have hs2 : s = 2 := by omega
    have m2 : InClass F2 s := by
      refine ⟨by decide,by decide,⟨0,0,0,rfl⟩,?_,?_,?_,?_⟩
      · apply (connected_iff_exists_forall_reachable _).mpr
        have e00 := edgeReach F2 0 0 (by decide)
        have e01 := edgeReach F2 0 1 (by decide)
        have e11 := edgeReach F2 1 1 (by decide)
        have e22 := edgeReach F2 2 2 (by decide)
        have e23 := edgeReach F2 2 3 (by decide)
        have e32 := edgeReach F2 3 2 (by decide)
        have e41 := edgeReach F2 4 1 (by decide)
        have e42 := edgeReach F2 4 2 (by decide)
        have r2 := e41.symm.trans e42
        refine ⟨.inr 1,?_⟩
        intro v
        cases v with
        | inl x =>
          fin_cases x
          · exact e01.symm
          · exact e11.symm
          · exact r2.trans e22.symm
          · exact r2.trans e32.symm
          · exact e41.symm
        | inr y =>
          fin_cases y
          · exact e01.symm.trans e00
          · exact Reachable.refl _
          · exact r2
          · exact r2.trans (e22.symm.trans e23)
      · apply chromaticNumber_le_iff_colorable.mpr
        refine ⟨Coloring.mk (![0,1,1,0,0] : Fin 5 → Fin 2) ?_⟩
        dsimp only [conflictLeft,conflictRight]
        decide
      · apply chromaticNumber_le_iff_colorable.mpr
        refine ⟨Coloring.mk (![0,1,0,1] : Fin 4 → Fin 2) ?_⟩
        dsimp only [conflictLeft,conflictRight]
        decide
      · have hc : Nat.card {xy : Fin 5 × Fin 4 // F2 xy.1 xy.2 ≠ none} = 10 := by
          rw [Nat.card_eq_fintype_card]; decide
        rw [hc]; norm_num <;> omega
    have collision {A B : Type} (a : Fin 5 → A) (b : Fin 4 → B)
        (d : A → B → ZMod 2)
        (hd : ∀ x y c, F2 x y = some c → d (a x) (b y) = c)
        (x x' : Fin 5) (y y' : Fin 4) (c c' : ZMod 2)
        (h0 : F2 x y = some c) (h1 : F2 x' y' = some c')
        (ha : a x = a x') (hb : b y = b y') : c = c' := by
      have hh := hd x y c h0
      rw [ha,hb] at hh
      exact hh.symm.trans (hd x' y' c' h1)
    have no23 : ¬ HasBudget F2 2 3 := by
      intro hh
      obtain ⟨a,b,d,hd⟩ := (compress F2 2 3).mp hh
      have a01 : a 0 ≠ a 1 := fun he => zero_ne_one (collision a b d hd 0 1 1 1 0 1 rfl rfl he rfl)
      have a14 : a 1 ≠ a 4 := fun he => one_ne_zero (collision a b d hd 1 4 1 1 1 0 rfl rfl he rfl)
      have a42 : a 4 ≠ a 2 := fun he => one_ne_zero (collision a b d hd 4 2 2 2 1 0 rfl rfl he rfl)
      have a23 : a 2 ≠ a 3 := fun he => zero_ne_one (collision a b d hd 2 3 2 2 0 1 rfl rfl he rfl)
      have a04 : a 0 = a 4 := by omega
      have a03 : a 0 = a 3 := by omega
      have b01 : b 0 ≠ b 1 := fun he => zero_ne_one (collision a b d hd 1 1 0 1 0 1 rfl rfl rfl he)
      have b02 : b 0 ≠ b 2 := fun he => zero_ne_one (collision a b d hd 0 4 0 2 0 1 rfl rfl a04 he)
      have b03 : b 0 ≠ b 3 := fun he => zero_ne_one (collision a b d hd 0 3 0 3 0 1 rfl rfl a03 he)
      have b12 : b 1 ≠ b 2 := fun he => zero_ne_one (collision a b d hd 0 4 1 2 0 1 rfl rfl a04 he)
      have b13 : b 1 ≠ b 3 := fun he => zero_ne_one (collision a b d hd 0 3 1 3 0 1 rfl rfl a03 he)
      have b23 : b 2 ≠ b 3 := fun he => zero_ne_one (collision a b d hd 2 2 2 3 0 1 rfl rfl rfl he)
      omega
    have no32 : ¬ HasBudget F2 3 2 := by
      intro hh
      obtain ⟨a,b,d,hd⟩ := (compress F2 3 2).mp hh
      have b01 : b 0 ≠ b 1 := fun he => zero_ne_one (collision a b d hd 1 1 0 1 0 1 rfl rfl rfl he)
      have b12 : b 1 ≠ b 2 := fun he => zero_ne_one (collision a b d hd 4 4 1 2 0 1 rfl rfl rfl he)
      have b23 : b 2 ≠ b 3 := fun he => zero_ne_one (collision a b d hd 2 2 2 3 0 1 rfl rfl rfl he)
      have b02 : b 0 = b 2 := by omega
      have b13 : b 1 = b 3 := by omega
      have a01 : a 0 ≠ a 1 := fun he => zero_ne_one (collision a b d hd 0 1 1 1 0 1 rfl rfl he rfl)
      have a03 : a 0 ≠ a 3 := fun he => zero_ne_one (collision a b d hd 0 3 0 2 0 1 rfl rfl he b02)
      have a04 : a 0 ≠ a 4 := fun he => zero_ne_one (collision a b d hd 0 4 0 2 0 1 rfl rfl he b02)
      have a13 : a 1 ≠ a 3 := fun he => zero_ne_one (collision a b d hd 1 3 0 2 0 1 rfl rfl he b02)
      have a14 : a 1 ≠ a 4 := fun he => one_ne_zero (collision a b d hd 1 4 1 1 1 0 rfl rfl he rfl)
      have a34 : a 3 ≠ a 4 := fun he => one_ne_zero (collision a b d hd 3 4 3 1 1 0 rfl rfl he b13.symm)
      omega
    by_cases hpEq : p = 2
    · exact no23 (mono F2 (h _ _ F2 m2) (by omega) (by omega))
    · exact no32 (mono F2 (h _ _ F2 m2) (by omega) (by omega))
  · intro h
    intro X Y _ _ t ht
    exact upper t ht h

end D5.S3.Observer.Separation.BooleanLowCycleBudgets

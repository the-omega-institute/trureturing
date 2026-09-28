/- GID: D5/S3/Observer/Separation/BooleanRankThreeFiber
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/BooleanRankThreeFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Whole original bit-class deletion forces the complete rank-three odd cycle fiber. -/

import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SimpleGraph
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
open D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality

namespace D5.S3.Observer.Separation.BooleanRankThreeFiber

/-- A partial Boolean table. `none` denotes an illegal pair. -/
structure Task (X Y : Type) where
  table : X → Y → Option (ZMod 2)

variable {X Y : Type}

/-- The original bipartite support; the vertex type includes both input sides. -/
def support (T : Task X Y) : SimpleGraph (X ⊕ Y) where
  Adj a b := match a, b with
    | .inl x, .inr y => ∃ c, T.table x y = some c
    | .inr y, .inl x => ∃ c, T.table x y = some c
    | _, _ => False
  symm := ⟨by rintro (x | y) (x' | y') h <;> exact h⟩
  loopless := ⟨by rintro (x | y) <;> exact id⟩

/-- Alice's conflict graph formed using the original legal table entries. -/
def conflictLeft (T : Task X Y) : SimpleGraph X where
  Adj x x' := ∃ y a b, T.table x y = some a ∧ T.table x' y = some b ∧ a ≠ b
  symm := ⟨by rintro x x' ⟨y,a,b,ha,hb,h⟩; exact ⟨y,b,a,hb,ha,h.symm⟩⟩
  loopless := ⟨by rintro x ⟨y,a,b,ha,hb,h⟩; exact h (Option.some.inj (ha.symm.trans hb))⟩

/-- Bob's conflict graph formed using the original legal table entries. -/
def conflictRight (T : Task X Y) : SimpleGraph Y where
  Adj y y' := ∃ x a b, T.table x y = some a ∧ T.table x y' = some b ∧ a ≠ b
  symm := ⟨by rintro y y' ⟨x,a,b,ha,hb,h⟩; exact ⟨x,b,a,hb,ha,h.symm⟩⟩
  loopless := ⟨by rintro y ⟨x,a,b,ha,hb,h⟩; exact h (Option.some.inj (ha.symm.trans hb))⟩

/-- Monochromaticity is tested on every original incident legal edge. -/
def monoLeft (T : Task X Y) (c : ZMod 2) (x : X) : Prop :=
  ∀ y b, T.table x y = some b → b = c

def monoRight (T : Task X Y) (d : ZMod 2) (y : Y) : Prop :=
  ∀ x b, T.table x y = some b → b = d

/-- Whole-class deletion, represented on the original carrier with deleted vertices isolated. -/
def residual (T : Task X Y) (c d : ZMod 2) : SimpleGraph (X ⊕ Y) where
  Adj a b := (support T).Adj a b ∧
    (match a with | .inl x => ¬ monoLeft T c x | .inr y => ¬ monoRight T d y) ∧
    (match b with | .inl x => ¬ monoLeft T c x | .inr y => ¬ monoRight T d y)
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro a h; exact (support T).loopless.irrefl a h.1⟩

/-- Edge labels, whose values off the support are immaterial. -/
def label (T : Task X Y) : Sym2 (X ⊕ Y) → ZMod 2 :=
  Sym2.lift ⟨(fun a b => match a, b with
    | .inl x, .inr y => (T.table x y).getD 0
    | .inr y, .inl x => (T.table x y).getD 0
    | _, _ => 0), by rintro (x | y) (x' | y') <;> rfl⟩

/-- Balance refers to label parity on all simple cycles. -/
def Balanced (T : Task X Y) (H : SimpleGraph (X ⊕ Y)) : Prop :=
  ∀ v (p : H.Walk v v), p.IsCycle → walkParity (fun e => label T e.val) p = 0

/-- Arbitrary ambient alphabets; only reachable images incur cost. -/
def HasBudget (T : Task X Y) (p q : ℕ) : Prop :=
  ∃ (A B : Type) (α : X → A) (β : Y → B) (δ : A → B → ZMod 2),
    Nat.card (Set.range α) ≤ p ∧ Nat.card (Set.range β) ≤ q ∧
    ∀ x y c, T.table x y = some c → δ (α x) (β y) = c

/-- The integer cyclomatic number of the actual legal-pair support. -/
noncomputable def rank [Fintype X] [Fintype Y] (T : Task X Y) : ℤ :=
  Nat.card {p : X × Y // ∃ c, T.table p.1 p.2 = some c} -
    (Fintype.card X : ℤ) - (Fintype.card Y : ℤ) + 1

/-- The source hypotheses, without any cycle-space or realization assumptions. -/
def Admissible (T : Task X Y) : Prop :=
  (∀ x, ∃ y c, T.table x y = some c) ∧
  (∀ y, ∃ x c, T.table x y = some c) ∧
  (∃ x y c, T.table x y = some c) ∧
  (support T).Connected ∧
  (conflictLeft T).chromaticNumber ≤ 2 ∧ (conflictRight T).chromaticNumber ≤ 2

/-- Actual simple cycles; equality of cycles in the conclusion uses their edge indicators. -/
def Cycle (T : Task X Y) := {p : Σ v, (support T).Walk v v // p.2.IsCycle}

noncomputable def indicator [DecidableEq X] [DecidableEq Y] (T : Task X Y)
    (p : Cycle T) : simpleCycleSpace (support T) := by
  classical
  exact ⟨(fun e => if e.val ∈ p.val.2.edges then 1 else 0),
    Submodule.subset_span ⟨p.val.1, p.val.2, p.property, rfl⟩⟩

/-- The actual linear sum of labels weighted by edge coordinates. -/
noncomputable def parity [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (T : Task X Y) : simpleCycleSpace (support T) →ₗ[ZMod 2] ZMod 2 := by
  classical
  letI := Fintype.ofFinite (support T).edgeSet
  exact ((standardCoordinatePairing (ZMod 2) (support T).edgeSet)
    (fun e => label T e.val)).comp (simpleCycleSpace (support T)).subtype

/-- All of the original odd fiber, with original globally monochromatic vertices on both sides. -/
def RankThreeShape [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (T : Task X Y) : Prop :=
  ∃ C : ZMod 2 × ZMod 2 → Cycle T,
    Function.Injective (fun ij => indicator T (C ij)) ∧
    (∀ z : simpleCycleSpace (support T), parity T z = 1 ↔
      ∃ ij, indicator T (C ij) = z) ∧
    (∀ ij,
      (∃ x, Sum.inl x ∈ (C ij).val.2.support ∧ monoLeft T ij.1 x) ∧
      (∃ y, Sum.inr y ∈ (C ij).val.2.support ∧ monoRight T ij.2 y) ∧
      (∀ x c, Sum.inl x ∈ (C ij).val.2.support → monoLeft T c x → c = ij.1) ∧
      (∀ y d, Sum.inr y ∈ (C ij).val.2.support → monoRight T d y → d = ij.2)) ∧
    indicator T (C (0,0)) + indicator T (C (0,1)) +
      indicator T (C (1,0)) + indicator T (C (1,1)) = 0 ∧
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun ij => indicator T (C ij)))) = 3

/-- Whole original bit-class deletion gives a three-message protocol when balanced.
Four unbalanced residuals force rank at least three; at rank three they exhaust
one affine odd fiber by four distinct simple-cycle indicators. The concrete
four-path table shows that this necessary shape does not imply infeasibility. -/
theorem result :
    (∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (T : Task X Y), Admissible T →
      ((∃ c d, Balanced T (residual T c d)) → HasBudget T 3 3) ∧
      ((∀ c d, ¬ Balanced T (residual T c d)) →
        3 ≤ rank T ∧ (rank T = 3 → RankThreeShape T)) ∧
      (¬ HasBudget T 3 3 → 3 ≤ rank T ∧ (rank T = 3 → RankThreeShape T))) ∧
    (∃ T : Task (Fin 8) (Fin 6), Admissible T ∧ rank T = 3 ∧
      (∀ c d, ¬ Balanced T (residual T c d)) ∧ RankThreeShape T ∧ HasBudget T 3 3) := by
  classical
  have bits (b : ZMod 2) : b = 0 ∨ b = 1 := by
    have hb := ZMod.val_lt b
    have hc : b.val = 0 ∨ b.val = 1 := by omega
    rcases hc with hc | hc
    · left; apply ZMod.val_injective 2; simpa only [ZMod.val_zero] using hc
    · right; apply ZMod.val_injective 2; simpa only [ZMod.val_one] using hc
  have core : ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (T : Task X Y), Admissible T →
      ((∃ c d, Balanced T (residual T c d)) → HasBudget T 3 3) ∧
      ((∀ c d, ¬ Balanced T (residual T c d)) →
        3 ≤ rank T ∧ (rank T = 3 → RankThreeShape T)) ∧
      (¬ HasBudget T 3 3 → 3 ≤ rank T ∧ (rank T = 3 → RankThreeShape T)) := by
    intro X Y _ _ _ _ T hT
    have protocol : (∃ c d, Balanced T (residual T c d)) → HasBudget T 3 3 := by
      classical
      let : MeasurableSpace (ZMod 2) := ⊤
      let : MeasurableSingletonClass (ZMod 2) := ⟨fun _ => trivial⟩
      rintro ⟨c,d,hbal⟩
      let H := residual T c d
      let := Fintype.ofFinite H.edgeSet
      let := Fintype.ofFinite H.ConnectedComponent
      obtain ⟨hpot, _⟩ := (finite_graph_cycle_space H).1.2.2.2 (fun e => label T e.val)
      obtain ⟨h,hh⟩ := hpot.mpr hbal
      let α : X → Option (ZMod 2) := fun x => if monoLeft T c x then none else some (h (.inl x))
      let β : Y → Option (ZMod 2) := fun y => if monoRight T d y then none else some (h (.inr y))
      let δ : Option (ZMod 2) → Option (ZMod 2) → ZMod 2 := fun a b =>
        match a,b with
        | none, _ => c
        | some _, none => d
        | some i, some j => i+j
      refine ⟨Option (ZMod 2), Option (ZMod 2), α, β, δ, ?_, ?_, ?_⟩
      · have hc := Nat.card_le_card_of_injective (fun z : Set.range α => z.val) Subtype.val_injective
        simpa using hc
      · have hc := Nat.card_le_card_of_injective (fun z : Set.range β => z.val) Subtype.val_injective
        simpa using hc
      · intro x y b hb
        by_cases hx : monoLeft T c x
        · simp only [α, if_pos hx, δ]
          exact (hx y b hb).symm
        · by_cases hy : monoRight T d y
          · simp only [α, if_neg hx, β, if_pos hy, δ]
            exact (hy x b hb).symm
          · have he : H.Adj (.inl x) (.inr y) := ⟨⟨b,hb⟩,hx,hy⟩
            have hv := congrFun hh ⟨s(Sum.inl x, Sum.inr y), H.mem_edgeSet.mpr he⟩
            change h (.inl x) + h (.inr y) = (T.table x y).getD 0 at hv
            simpa only [α, if_neg hx, β, if_neg hy, δ, hb, Option.getD_some] using hv
    rcases hT with ⟨hactiveX,hactiveY,hne,hconn,hcl,hcr⟩
    let G := support T
    let := Fintype.ofFinite G.edgeSet
    let := Fintype.ofFinite G.ConnectedComponent
    have response {U V : Type} (F : Task U V) (η : V → ZMod 2)
        (proper : ∀ u v w a b, F.table u v = some a → F.table u w = some b →
          a ≠ b → η v ≠ η w) :
        ∃ u : U → ZMod 2, ∀ x, (¬ ∃ c, monoLeft F c x) →
          ∀ y b, F.table x y = some b → b = u x + η y := by
      let r : U → ZMod 2 → ZMod 2 := fun x j =>
        if h : ∃ b y, F.table x y = some b ∧ η y = j then h.choose else 0
      have hr (x : U) (y : V) (b : ZMod 2) (hb : F.table x y = some b) :
          r x (η y) = b := by
        have hex : ∃ b' y', F.table x y' = some b' ∧ η y' = η y := ⟨b,y,hb,rfl⟩
        dsimp only [r]
        rw [dif_pos hex]
        obtain ⟨y',hy',hc⟩ := hex.choose_spec
        by_contra hne
        exact proper x y' y _ b hy' hb hne hc
      refine ⟨fun x => r x 0, ?_⟩
      intro x hn y b hb
      have hdiff : r x 0 ≠ r x 1 := by
        intro he
        apply hn
        refine ⟨r x 0, fun y' b' hb' => ?_⟩
        have hv := hr x y' b' hb'
        rcases bits (η y') with hj | hj
        · rw [hj] at hv; exact hv.symm
        · rw [hj] at hv; exact hv.symm.trans he.symm
      have hstep : r x 1 = r x 0 + 1 := by
        rcases bits (r x 0) with ha | ha <;> rcases bits (r x 1) with hb | hb <;>
          simp only [ha, hb, ne_eq, not_true_eq_false, zero_add, ZModModule.add_self] at hdiff ⊢
      have hv := hr x y b hb
      rcases bits (η y) with hj | hj
      · rw [hj] at hv ⊢; simpa only [add_zero] using hv.symm
      · rw [hj] at hv ⊢; exact hv.symm.trans hstep
    let colX : (conflictLeft T).Coloring (Fin 2) :=
      (SimpleGraph.chromaticNumber_le_iff_colorable.mp hcl).some
    let colY : (conflictRight T).Coloring (Fin 2) :=
      (SimpleGraph.chromaticNumber_le_iff_colorable.mp hcr).some
    let η : Y → ZMod 2 := fun y => colY y
    let ξ : X → ZMod 2 := fun x => colX x
    obtain ⟨u,hu⟩ := response T η (by
      intro x y y' a b ha hb hn
      exact colY.valid ⟨x,a,b,ha,hb,hn⟩)
    obtain ⟨v,hv⟩ := response (Task.mk (fun y x => T.table x y)) ξ (by
      intro y x x' a b ha hb hn
      exact colX.valid ⟨y,a,b,ha,hb,hn⟩)
    have rawParity (H : SimpleGraph (X ⊕ Y)) {a b : X ⊕ Y} (p : H.Walk a b) :
        walkParity (fun e => label T e.val) p = (p.edges.map (label T)).sum := by
      unfold walkParity
      congr 1
      apply List.map_congr_left
      intro e he
      simp only [dif_pos (p.edges_subset_edgeSet he)]
    have telescopes (H : SimpleGraph (X ⊕ Y)) (h : X ⊕ Y → ZMod 2)
        {a b : X ⊕ Y} (p : H.Walk a b)
        (he : ∀ w z, s(w,z) ∈ p.edges → label T s(w,z) = h w + h z) :
        walkParity (fun e => label T e.val) p = h a + h b := by
      rw [rawParity]
      induction p with
      | nil => simp [ZModModule.add_self]
      | @cons a b c hab p ih =>
        simp only [Walk.edges_cons, List.map_cons, List.sum_cons]
        rw [he a b (by simp),
          ih (fun w z hwz => he w z (by simp only [Walk.edges_cons, List.mem_cons]; exact Or.inr hwz))]
        simp only [add_assoc, ← add_assoc (h b) (h b), ZModModule.add_self, zero_add]
    have hits (p : Cycle T) (hodd : walkParity (fun e => label T e.val) p.val.2 = 1) :
        (∃ x c, Sum.inl x ∈ p.val.2.support ∧ monoLeft T c x) ∧
        (∃ y d, Sum.inr y ∈ p.val.2.support ∧ monoRight T d y) := by
      constructor
      · by_contra hn
        have ht := telescopes G (Sum.elim u η) p.val.2 (by
          intro a b he
          have hab := p.val.2.adj_of_mem_edges he
          cases a with
          | inl x =>
            cases b with
            | inl x' => exact hab.elim
            | inr y =>
              obtain ⟨c,hc⟩ := hab
              have hx : ¬ ∃ c, monoLeft T c x := by
                rintro ⟨c,hc⟩; exact hn ⟨x,c,p.val.2.fst_mem_support_of_mem_edges he,hc⟩
              change (T.table x y).getD 0 = u x + η y
              rw [hc]; exact hu x hx y c hc
          | inr y =>
            cases b with
            | inr y' => exact hab.elim
            | inl x =>
              obtain ⟨c,hc⟩ := hab
              have hx : ¬ ∃ c, monoLeft T c x := by
                rintro ⟨c,hc⟩; exact hn ⟨x,c,p.val.2.snd_mem_support_of_mem_edges he,hc⟩
              change (T.table x y).getD 0 = η y + u x
              rw [hc, add_comm]; exact hu x hx y c hc)
        rw [hodd, ZModModule.add_self] at ht
        exact one_ne_zero ht
      · by_contra hn
        have ht := telescopes G (Sum.elim ξ v) p.val.2 (by
          intro a b he
          have hab := p.val.2.adj_of_mem_edges he
          cases a with
          | inl x =>
            cases b with
            | inl x' => exact hab.elim
            | inr y =>
              obtain ⟨c,hc⟩ := hab
              have hy : ¬ ∃ d, monoLeft (Task.mk (fun y x => T.table x y)) d y := by
                rintro ⟨d,hd⟩; exact hn ⟨y,d,p.val.2.snd_mem_support_of_mem_edges he,hd⟩
              change (T.table x y).getD 0 = ξ x + v y
              rw [hc, add_comm]; exact hv y hy x c hc
          | inr y =>
            cases b with
            | inr y' => exact hab.elim
            | inl x =>
              obtain ⟨c,hc⟩ := hab
              have hy : ¬ ∃ d, monoLeft (Task.mk (fun y x => T.table x y)) d y := by
                rintro ⟨d,hd⟩; exact hn ⟨y,d,p.val.2.fst_mem_support_of_mem_edges he,hd⟩
              change (T.table x y).getD 0 = v y + ξ x
              rw [hc]; exact hv y hy x c hc)
        rw [hodd, ZModModule.add_self] at ht
        exact one_ne_zero ht
    have indicatorParity (p : Cycle T) :
        parity T (indicator T p) = walkParity (fun e => label T e.val) p.val.2 := by
      rw [rawParity, ← List.sum_toFinset (label T) p.property.isTrail.edges_nodup]
      change (∑ e : G.edgeSet, label T e.val *
        (if e.val ∈ p.val.2.edges then 1 else 0)) = _
      simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
      apply Finset.sum_bij (fun e _ => e.val)
      · intro e he
        exact List.mem_toFinset.mpr (Finset.mem_filter.mp he).2
      · intro e he e' he' heq
        exact Subtype.ext heq
      · intro e he
        have hp := List.mem_toFinset.mp he
        exact ⟨⟨e,p.val.2.edges_subset_edgeSet hp⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩, rfl⟩
      · intros; rfl
    have indicatorSupport (p q : Cycle T) (heq : indicator T p = indicator T q) :
        ∀ w, w ∈ p.val.2.support ↔ w ∈ q.val.2.support := by
      have hedges : ∀ e, e ∈ p.val.2.edges ↔ e ∈ q.val.2.edges := by
        intro e
        by_cases hG : e ∈ G.edgeSet
        · have h := congrArg (fun z : simpleCycleSpace G => z.val ⟨e,hG⟩) heq
          change (if e ∈ p.val.2.edges then (1 : ZMod 2) else 0) =
            (if e ∈ q.val.2.edges then 1 else 0) at h
          by_cases hp : e ∈ p.val.2.edges <;> by_cases hq : e ∈ q.val.2.edges <;>
            simp only [hp, hq, if_true, if_false, one_ne_zero, zero_ne_one] at h ⊢
        · exact iff_of_false (fun hp => hG (p.val.2.edges_subset_edgeSet hp))
            (fun hq => hG (q.val.2.edges_subset_edgeSet hq))
      intro w
      rw [Walk.mem_support_iff_exists_mem_edges_of_not_nil p.property.not_nil,
        Walk.mem_support_iff_exists_mem_edges_of_not_nil q.property.not_nil]
      simp only [hedges]
    have dimension : (Module.finrank (ZMod 2) (simpleCycleSpace G) : ℤ) = rank T := by
      let : MeasurableSpace (ZMod 2) := ⊤
      let : MeasurableSingletonClass (ZMod 2) := ⟨fun _ => trivial⟩
      let : Subsingleton G.ConnectedComponent := hconn.preconnected.subsingleton_connectedComponent
      let : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk (Sum.inl hne.choose)⟩
      have hcomp : Fintype.card G.ConnectedComponent = 1 := by simp only [Fintype.card_eq_one_iff]; exact ⟨Classical.choice inferInstance, fun _ => Subsingleton.elim _ _⟩
      let edge : {p : X × Y // ∃ c, T.table p.1 p.2 = some c} → G.edgeSet :=
        fun p => ⟨s(Sum.inl p.val.1, Sum.inr p.val.2), p.property⟩
      have bij : Function.Bijective edge := by
        constructor
        · intro p q he
          have hs := congrArg Subtype.val he
          change s(Sum.inl p.val.1, Sum.inr p.val.2) =
            s(Sum.inl q.val.1, Sum.inr q.val.2) at hs
          have hpq : p.val = q.val := by
            apply Prod.ext_iff.mpr
            simpa only [Sym2.eq_iff, Prod.mk.injEq,
            Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
            false_and, or_false] using hs
          exact Subtype.ext hpq
        · rintro ⟨e,he⟩
          induction e using Sym2.inductionOn with
          | hf a b =>
            cases a with
            | inl x =>
              cases b with
              | inl x' => exact he.elim
              | inr y => exact ⟨⟨(x,y),he⟩, rfl⟩
            | inr y =>
              cases b with
              | inr y' => exact he.elim
              | inl x =>
                refine ⟨⟨(x,y),he⟩, ?_⟩
                apply Subtype.ext
                exact Sym2.eq_swap
      have hcard := Nat.card_eq_of_bijective edge bij
      obtain ⟨_,⟨S,hle,hacyc,hreach⟩,hb⟩ := finite_graph_cycle_space G
      obtain ⟨cs,_,_,_,bs,_,_,_,_,_,hr,hdim,_⟩ := hb S hle hacyc hreach
      rw [hdim]
      rw [hr, hcomp]
      simp only [rank, Fintype.card_sum, Nat.cast_add, Nat.cast_one]
      rw [← Nat.card_eq_fintype_card, ← hcard]
      ring
    have obstruction (hn : ∀ c d, ¬ Balanced T (residual T c d)) :
        3 ≤ rank T ∧ (rank T = 3 → RankThreeShape T) := by
      have four (ij : ZMod 2 × ZMod 2) : ∃ p : Cycle T,
          parity T (indicator T p) = 1 ∧
          (∃ x, Sum.inl x ∈ p.val.2.support ∧ monoLeft T ij.1 x) ∧
          (∃ y, Sum.inr y ∈ p.val.2.support ∧ monoRight T ij.2 y) ∧
          (∀ x c, Sum.inl x ∈ p.val.2.support → monoLeft T c x → c = ij.1) ∧
          (∀ y d, Sum.inr y ∈ p.val.2.support → monoRight T d y → d = ij.2) := by
        let H := residual T (1-ij.1) (1-ij.2)
        have hle : H ≤ G := fun _ _ h => h.1
        obtain ⟨a,p,hp,hodd⟩ : ∃ (a : X ⊕ Y) (p : H.Walk a a), p.IsCycle ∧
            walkParity (fun e => label T e.val) p ≠ 0 := by
          by_contra he
          apply hn (1-ij.1) (1-ij.2)
          intro a p hp
          by_contra ho
          exact he ⟨a,p,hp,ho⟩
        have ho : walkParity (fun e => label T e.val) p = 1 :=
          (bits _).resolve_left hodd
        let q : Cycle T := ⟨⟨a,p.mapLe hle⟩,hp.mapLe hle⟩
        have hq : walkParity (fun e => label T e.val) q.val.2 = 1 := by
          simpa only [rawParity, q, Walk.edges_mapLe_eq_edges] using ho
        have survives (w : X ⊕ Y) (hw : w ∈ p.support) :
            match w with
            | .inl x => ¬ monoLeft T (1-ij.1) x
            | .inr y => ¬ monoRight T (1-ij.2) y := by
          obtain ⟨e,he,hwe⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil).mp hw
          induction e using Sym2.inductionOn with
          | hf a b =>
            have hab := p.adj_of_mem_edges he
            rcases Sym2.mem_iff.mp hwe with rfl | rfl
            · cases w <;> exact hab.2.1
            · cases w <;> exact hab.2.2
        have other (i c : ZMod 2) : c ≠ i → c = 1-i := by
          rcases bits i with hi | hi <;> rcases bits c with hc | hc <;>
            simp only [hi, hc, ne_eq, not_true_eq_false, sub_zero, sub_self,
              zero_ne_one, one_ne_zero, false_implies, implies_true]
        have allX (x : X) (c : ZMod 2) (hx : Sum.inl x ∈ q.val.2.support)
            (hc : monoLeft T c x) : c = ij.1 := by
          by_contra he
          have hs := survives (.inl x) (by simpa only [q, Walk.support_mapLe_eq_support] using hx)
          exact hs (other ij.1 c he ▸ hc)
        have allY (y : Y) (d : ZMod 2) (hy : Sum.inr y ∈ q.val.2.support)
            (hd : monoRight T d y) : d = ij.2 := by
          by_contra he
          have hs := survives (.inr y) (by simpa only [q, Walk.support_mapLe_eq_support] using hy)
          exact hs (other ij.2 d he ▸ hd)
        obtain ⟨⟨x,c,hx,hxc⟩,⟨y,d,hy,hyd⟩⟩ := hits q hq
        refine ⟨q, (indicatorParity q).trans hq,
          ⟨x,hx,?_⟩, ⟨y,hy,?_⟩, allX, allY⟩
        · exact allX x c hx hxc ▸ hxc
        · exact allY y d hy hyd ▸ hyd
      choose C hC using four
      let z : ZMod 2 × ZMod 2 → simpleCycleSpace G := fun ij => indicator T (C ij)
      have inject : Function.Injective z := by
        intro ij kl he
        obtain ⟨x,hx,hxc⟩ := (hC ij).2.1
        obtain ⟨y,hy,hyd⟩ := (hC ij).2.2.1
        have hsupport := indicatorSupport (C ij) (C kl) he
        apply Prod.ext
        · exact (hC kl).2.2.2.1 x ij.1 ((hsupport _).mp hx) hxc
        · exact (hC kl).2.2.2.2 y ij.2 ((hsupport _).mp hy) hyd
      let L := parity T
      have odd (ij) : L (z ij) = 1 := (hC ij).1
      have hL : L ≠ 0 := by
        intro he
        have hh := odd (0,0)
        rw [he, LinearMap.zero_apply] at hh
        exact zero_ne_one hh
      have kerDim := Module.Dual.finrank_ker_add_one_of_ne_zero hL
      change Module.finrank (ZMod 2) (LinearMap.ker L) + 1 =
        Module.finrank (ZMod 2) (simpleCycleSpace G) at kerDim
      have cardFiber : Nat.card {a : simpleCycleSpace G // L a = 1} =
          2 ^ Module.finrank (ZMod 2) (LinearMap.ker L) := by
        have he := L.toAddMonoidHom.fiberEquivKer (z (0,0))
        have hc := Nat.card_congr he
        change Nat.card {a : simpleCycleSpace G // L a = L (z (0,0))} =
          Nat.card (LinearMap.ker L) at hc
        rw [odd] at hc
        rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      let intoFiber : ZMod 2 × ZMod 2 → {a : simpleCycleSpace G // L a = 1} :=
        fun ij => ⟨z ij,odd ij⟩
      have fi : Function.Injective intoFiber := fun ij kl h => inject (congrArg Subtype.val h)
      have count : 4 ≤ 2 ^ Module.finrank (ZMod 2) (LinearMap.ker L) := by
        have hc := Nat.card_le_card_of_injective intoFiber fi
        simpa only [Nat.card_prod, Nat.card_zmod, cardFiber] using hc
      have dimlo : 3 ≤ Module.finrank (ZMod 2) (simpleCycleSpace G) := by
        have hker : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker L) := by
          by_contra h
          have hle : Module.finrank (ZMod 2) (LinearMap.ker L) ≤ 1 := by omega
          have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hle
          norm_num at hp
          omega
        omega
      refine ⟨?_, ?_⟩
      · rw [← dimension]; exact_mod_cast dimlo
      · intro hrank
        have hd : Module.finrank (ZMod 2) (simpleCycleSpace G) = 3 := by omega
        have hk : Module.finrank (ZMod 2) (LinearMap.ker L) = 2 := by omega
        have cardeq : Nat.card (ZMod 2 × ZMod 2) = Nat.card {a : simpleCycleSpace G // L a = 1} := by
          simp only [cardFiber, hk, Nat.card_prod, Nat.card_zmod]
          norm_num
        have surj : Function.Surjective intoFiber :=
          ((Nat.bijective_iff_injective_and_card intoFiber).mpr ⟨fi,cardeq⟩).2
        have exhaust (a : simpleCycleSpace G) : L a = 1 ↔ ∃ ij, z ij = a := by
          constructor
          · intro ha
            obtain ⟨ij,hij⟩ := surj ⟨a,ha⟩
            exact ⟨ij,congrArg Subtype.val hij⟩
          · rintro ⟨ij,rfl⟩; exact odd ij
        have hsumOdd : L (z (0,0) + z (0,1) + z (1,0)) = 1 := by
          rw [map_add, map_add, odd, odd, odd, ZModModule.add_self, zero_add]
        obtain ⟨ij,hij⟩ := (exhaust _).mp hsumOdd
        have he01 : z (0,0) ≠ z (0,1) := fun h => by
          have hh := congrArg Prod.snd (inject h)
          exact zero_ne_one hh
        have he02 : z (0,0) ≠ z (1,0) := fun h => by
          have hh := congrArg Prod.fst (inject h)
          exact zero_ne_one hh
        have he12 : z (0,1) ≠ z (1,0) := fun h => by
          have hh := congrArg Prod.fst (inject h)
          exact zero_ne_one hh
        have hidx : ij = (1,1) := by
          rcases ij with ⟨i,j⟩
          rcases bits i with hi | hi <;> rcases bits j with hj | hj <;> subst i <;> subst j
          · exfalso; apply he12
            have hh : z (0,1) + z (1,0) = 0 := by
              calc
                _ = z (0,0) + (z (0,0) + z (0,1) + z (1,0)) := by
                  calc
                    _ = (z (0,0) + z (0,0)) + (z (0,1) + z (1,0)) := by
                      rw [ZModModule.add_self, zero_add]
                    _ = _ := by abel
                _ = 0 := by rw [← hij, ZModModule.add_self]
            exact (eq_neg_iff_add_eq_zero.mpr hh).trans (ZModModule.neg_eq_self _)
          · exfalso; apply he02
            have hh : z (0,0) + z (1,0) = 0 := by
              calc
                _ = z (0,1) + (z (0,0) + z (0,1) + z (1,0)) := by
                  calc
                    _ = (z (0,1) + z (0,1)) + (z (0,0) + z (1,0)) := by
                      rw [ZModModule.add_self, zero_add]
                    _ = _ := by abel
                _ = 0 := by rw [← hij, ZModModule.add_self]
            exact (eq_neg_iff_add_eq_zero.mpr hh).trans (ZModModule.neg_eq_self _)
          · exfalso; apply he01
            have hh : z (0,0) + z (0,1) = 0 := by
              calc
                _ = (z (0,0) + z (0,1) + z (1,0)) + z (1,0) := by
                  simp only [add_assoc, ZModModule.add_self, add_zero]
                _ = 0 := by rw [← hij, ZModModule.add_self]
            exact (eq_neg_iff_add_eq_zero.mpr hh).trans (ZModModule.neg_eq_self _)
          · rfl
        have hx : z (0,0) + z (0,1) + z (1,0) + z (1,1) = 0 := by
          rw [hidx] at hij
          rw [← hij, ZModModule.add_self]
        have hspan : Submodule.span (ZMod 2) (Set.range z) = ⊤ := by
          have hset : Set.range z = L ⁻¹' ({1} : Set (ZMod 2)) := by
            ext a
            exact (exhaust a).symm
          rw [hset, Submodule.span_preimage_eq (Set.singleton_nonempty _) (by
            rintro a (rfl : a = 1); exact ⟨z (0,0),odd _⟩)]
          have htop : Submodule.span (ZMod 2) ({1} : Set (ZMod 2)) = ⊤ := by
            apply top_unique
            intro a _
            simpa only [smul_eq_mul, mul_one] using
              (Submodule.span (ZMod 2) ({1} : Set (ZMod 2))).smul_mem a
                (Submodule.subset_span (Set.mem_singleton 1))
          rw [htop, Submodule.comap_top]
        refine ⟨C,inject,exhaust,?_,hx,?_⟩
        · intro ij; exact (hC ij).2
        · change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range z)) = 3
          rw [hspan, finrank_top, hd]
    exact ⟨protocol,obstruction,fun hn => obstruction (fun c d hb => hn (protocol ⟨c,d,hb⟩))⟩
  refine ⟨core, ?_⟩
  let θ : Task (Fin 8) (Fin 6) := ⟨![
    ![some 0, some 0, none, none, none, none],
    ![some 1, some 1, none, none, none, none],
    ![some 1, none, some 0, none, none, none],
    ![none, none, some 0, some 1, none, none],
    ![none, some 1, none, some 0, none, none],
    ![some 0, none, none, none, some 1, none],
    ![none, none, none, none, some 1, some 0],
    ![none, some 0, none, none, none, some 1]]⟩
  have hax : ∀ x, ∃ y c, θ.table x y = some c := by decide +kernel
  have hay : ∀ y, ∃ x c, θ.table x y = some c := by decide +kernel
  have hn : ∃ x y c, θ.table x y = some c := ⟨0,0,0,rfl⟩
  let Acol : Fin 8 → Fin 2 := ![0,1,1,0,1,0,1,0]
  let Bcol : Fin 6 → Fin 2 := ![0,1,1,0,1,0]
  have hAc : ∀ x x' y a b, θ.table x y = some a → θ.table x' y = some b →
      a ≠ b → Acol x ≠ Acol x' := by decide +kernel
  have hBc : ∀ y y' x a b, θ.table x y = some a → θ.table x y' = some b →
      a ≠ b → Bcol y ≠ Bcol y' := by decide +kernel
  have hcl : (conflictLeft θ).chromaticNumber ≤ 2 := by
    apply SimpleGraph.chromaticNumber_le_iff_colorable.mpr
    exact ⟨⟨Acol, fun {_ _} ⟨y,a,b,ha,hb,hn⟩ => hAc _ _ y a b ha hb hn⟩⟩
  have hcr : (conflictRight θ).chromaticNumber ≤ 2 := by
    apply SimpleGraph.chromaticNumber_le_iff_colorable.mpr
    exact ⟨⟨Bcol, fun {_ _} ⟨x,a,b,ha,hb,hn⟩ => hBc _ _ x a b ha hb hn⟩⟩
  let Gθ := support θ
  have edge {x : Fin 8} {y : Fin 6} {b : ZMod 2} (hb : θ.table x y = some b) :
      Gθ.Reachable (Sum.inl x) (Sum.inr y) :=
    (show Gθ.Adj (Sum.inl x) (Sum.inr y) from ⟨b,hb⟩).reachable
  have rx0 : Gθ.Reachable (Sum.inr 0) (Sum.inl 0) := (edge (b:=0) rfl).symm
  have rx1 : Gθ.Reachable (Sum.inr 0) (Sum.inl 1) := (edge (b:=1) rfl).symm
  have rx2 : Gθ.Reachable (Sum.inr 0) (Sum.inl 2) := (edge (b:=1) rfl).symm
  have ry1 : Gθ.Reachable (Sum.inr 0) (Sum.inr 1) := rx0.trans (edge (b:=0) rfl)
  have ry2 : Gθ.Reachable (Sum.inr 0) (Sum.inr 2) := rx2.trans (edge (b:=0) rfl)
  have rx3 : Gθ.Reachable (Sum.inr 0) (Sum.inl 3) := ry2.trans (edge (b:=0) rfl).symm
  have ry3 : Gθ.Reachable (Sum.inr 0) (Sum.inr 3) := rx3.trans (edge (b:=1) rfl)
  have rx4 : Gθ.Reachable (Sum.inr 0) (Sum.inl 4) := ry3.trans (edge (b:=0) rfl).symm
  have rx5 : Gθ.Reachable (Sum.inr 0) (Sum.inl 5) := (edge (b:=0) rfl).symm
  have ry4 : Gθ.Reachable (Sum.inr 0) (Sum.inr 4) := rx5.trans (edge (b:=1) rfl)
  have rx6 : Gθ.Reachable (Sum.inr 0) (Sum.inl 6) := ry4.trans (edge (b:=1) rfl).symm
  have ry5 : Gθ.Reachable (Sum.inr 0) (Sum.inr 5) := rx6.trans (edge (b:=0) rfl)
  have rx7 : Gθ.Reachable (Sum.inr 0) (Sum.inl 7) := ry5.trans (edge (b:=1) rfl).symm
  have connected : Gθ.Connected := by
    apply (Gθ.connected_iff_exists_forall_reachable).mpr
    refine ⟨Sum.inr 0, ?_⟩
    rintro (x | y)
    · fin_cases x
      · exact rx0
      · exact rx1
      · exact rx2
      · exact rx3
      · exact rx4
      · exact rx5
      · exact rx6
      · exact rx7
    · fin_cases y
      · exact SimpleGraph.Reachable.refl _
      · exact ry1
      · exact ry2
      · exact ry3
      · exact ry4
      · exact ry5
  have admissible : Admissible θ := ⟨hax,hay,hn,connected,hcl,hcr⟩
  have hcard : Nat.card {p : Fin 8 × Fin 6 // ∃ c, θ.table p.1 p.2 = some c} = 16 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hrank : rank θ = 3 := by
    simp only [rank, hcard, Fintype.card_fin]
    norm_num
  let α : Fin 8 → Fin 3 := ![0,1,1,0,1,0,0,2]
  let β : Fin 6 → Fin 3 := ![0,0,1,2,2,1]
  let δ : Fin 3 → Fin 3 → ZMod 2 := ![![0,0,1],![1,0,0],![0,1,0]]
  have correct : ∀ x y b, θ.table x y = some b → δ (α x) (β y) = b := by decide +kernel
  have feasible : HasBudget θ 3 3 := by
    refine ⟨Fin 3,Fin 3,α,β,δ,?_,?_,correct⟩
    · simpa only [Nat.card_fin] using
        Nat.card_le_card_of_injective (fun z : Set.range α => z.val) Subtype.val_injective
    · simpa only [Nat.card_fin] using
        Nat.card_le_card_of_injective (fun z : Set.range β => z.val) Subtype.val_injective
  have mx : ∀ c x, monoLeft θ c x ↔ (x = 0 ∧ c = 0) ∨ (x = 1 ∧ c = 1) := by
    unfold monoLeft
    decide +kernel
  have my : ∀ d y, monoRight θ d y ↔ (y = 2 ∧ d = 0) ∨ (y = 4 ∧ d = 1) := by
    unfold monoRight
    decide +kernel
  have unbalanced : ∀ c d, ¬ Balanced θ (residual θ c d) := by
    intro c d hb
    let H := residual θ c d
    let : MeasurableSpace (ZMod 2) := ⊤
    let : MeasurableSingletonClass (ZMod 2) := ⟨fun _ => trivial⟩
    let := Fintype.ofFinite H.edgeSet
    let := Fintype.ofFinite H.ConnectedComponent
    obtain ⟨h,hh⟩ := ((finite_graph_cycle_space H).1.2.2.2 (fun e => label θ e.val)).1.mpr hb
    have eqn (x : Fin 8) (y : Fin 6) (b : ZMod 2) (ht : θ.table x y = some b)
        (he : H.Adj (Sum.inl x) (Sum.inr y)) : h (Sum.inl x) + h (Sum.inr y) = b := by
      have heq := congrFun hh ⟨s(Sum.inl x,Sum.inr y),H.mem_edgeSet.mpr he⟩
      change h (Sum.inl x) + h (Sum.inr y) = (θ.table x y).getD 0 at heq
      simpa only [ht,Option.getD_some] using heq
    rcases bits c with hc | hc <;> rcases bits d with hd | hd <;> subst c <;> subst d
    · have e0 := eqn 1 0 1 rfl (by
          change (∃ a, θ.table 1 0 = some a) ∧ ¬ monoLeft θ 0 1 ∧ ¬ monoRight θ 0 0
          rw [mx,my]
          decide +kernel)
      have e1 := eqn 1 1 1 rfl (by
          change (∃ a, θ.table 1 1 = some a) ∧ ¬ monoLeft θ 0 1 ∧ ¬ monoRight θ 0 1
          rw [mx,my]
          decide +kernel)
      have e2 := eqn 5 0 0 rfl (by
          change (∃ a, θ.table 5 0 = some a) ∧ ¬ monoLeft θ 0 5 ∧ ¬ monoRight θ 0 0
          rw [mx,my]
          decide +kernel)
      have e3 := eqn 5 4 1 rfl (by
          change (∃ a, θ.table 5 4 = some a) ∧ ¬ monoLeft θ 0 5 ∧ ¬ monoRight θ 0 4
          rw [mx,my]
          decide +kernel)
      have e4 := eqn 6 4 1 rfl (by
          change (∃ a, θ.table 6 4 = some a) ∧ ¬ monoLeft θ 0 6 ∧ ¬ monoRight θ 0 4
          rw [mx,my]
          decide +kernel)
      have e5 := eqn 6 5 0 rfl (by
          change (∃ a, θ.table 6 5 = some a) ∧ ¬ monoLeft θ 0 6 ∧ ¬ monoRight θ 0 5
          rw [mx,my]
          decide +kernel)
      have e6 := eqn 7 5 1 rfl (by
          change (∃ a, θ.table 7 5 = some a) ∧ ¬ monoLeft θ 0 7 ∧ ¬ monoRight θ 0 5
          rw [mx,my]
          decide +kernel)
      have e7 := eqn 7 1 0 rfl (by
          change (∃ a, θ.table 7 1 = some a) ∧ ¬ monoLeft θ 0 7 ∧ ¬ monoRight θ 0 1
          rw [mx,my]
          decide +kernel)
      have bad : (0 : ZMod 2) = 1 := by
        linear_combination (norm := (ring_nf; simp only [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, mul_zero, sub_zero]))
          e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7
      exact zero_ne_one bad
    · have e0 := eqn 1 0 1 rfl (by
          change (∃ a, θ.table 1 0 = some a) ∧ ¬ monoLeft θ 0 1 ∧ ¬ monoRight θ 1 0
          rw [mx,my]
          decide +kernel)
      have e1 := eqn 1 1 1 rfl (by
          change (∃ a, θ.table 1 1 = some a) ∧ ¬ monoLeft θ 0 1 ∧ ¬ monoRight θ 1 1
          rw [mx,my]
          decide +kernel)
      have e2 := eqn 2 0 1 rfl (by
          change (∃ a, θ.table 2 0 = some a) ∧ ¬ monoLeft θ 0 2 ∧ ¬ monoRight θ 1 0
          rw [mx,my]
          decide +kernel)
      have e3 := eqn 2 2 0 rfl (by
          change (∃ a, θ.table 2 2 = some a) ∧ ¬ monoLeft θ 0 2 ∧ ¬ monoRight θ 1 2
          rw [mx,my]
          decide +kernel)
      have e4 := eqn 3 2 0 rfl (by
          change (∃ a, θ.table 3 2 = some a) ∧ ¬ monoLeft θ 0 3 ∧ ¬ monoRight θ 1 2
          rw [mx,my]
          decide +kernel)
      have e5 := eqn 3 3 1 rfl (by
          change (∃ a, θ.table 3 3 = some a) ∧ ¬ monoLeft θ 0 3 ∧ ¬ monoRight θ 1 3
          rw [mx,my]
          decide +kernel)
      have e6 := eqn 4 3 0 rfl (by
          change (∃ a, θ.table 4 3 = some a) ∧ ¬ monoLeft θ 0 4 ∧ ¬ monoRight θ 1 3
          rw [mx,my]
          decide +kernel)
      have e7 := eqn 4 1 1 rfl (by
          change (∃ a, θ.table 4 1 = some a) ∧ ¬ monoLeft θ 0 4 ∧ ¬ monoRight θ 1 1
          rw [mx,my]
          decide +kernel)
      have bad : (0 : ZMod 2) = 1 := by
        linear_combination (norm := (ring_nf; simp only [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide, mul_zero, sub_zero]))
          e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7
      exact zero_ne_one bad
    · have e0 := eqn 0 0 0 rfl (by
          change (∃ a, θ.table 0 0 = some a) ∧ ¬ monoLeft θ 1 0 ∧ ¬ monoRight θ 0 0
          rw [mx,my]
          decide +kernel)
      have e1 := eqn 0 1 0 rfl (by
          change (∃ a, θ.table 0 1 = some a) ∧ ¬ monoLeft θ 1 0 ∧ ¬ monoRight θ 0 1
          rw [mx,my]
          decide +kernel)
      have e2 := eqn 5 0 0 rfl (by
          change (∃ a, θ.table 5 0 = some a) ∧ ¬ monoLeft θ 1 5 ∧ ¬ monoRight θ 0 0
          rw [mx,my]
          decide +kernel)
      have e3 := eqn 5 4 1 rfl (by
          change (∃ a, θ.table 5 4 = some a) ∧ ¬ monoLeft θ 1 5 ∧ ¬ monoRight θ 0 4
          rw [mx,my]
          decide +kernel)
      have e4 := eqn 6 4 1 rfl (by
          change (∃ a, θ.table 6 4 = some a) ∧ ¬ monoLeft θ 1 6 ∧ ¬ monoRight θ 0 4
          rw [mx,my]
          decide +kernel)
      have e5 := eqn 6 5 0 rfl (by
          change (∃ a, θ.table 6 5 = some a) ∧ ¬ monoLeft θ 1 6 ∧ ¬ monoRight θ 0 5
          rw [mx,my]
          decide +kernel)
      have e6 := eqn 7 5 1 rfl (by
          change (∃ a, θ.table 7 5 = some a) ∧ ¬ monoLeft θ 1 7 ∧ ¬ monoRight θ 0 5
          rw [mx,my]
          decide +kernel)
      have e7 := eqn 7 1 0 rfl (by
          change (∃ a, θ.table 7 1 = some a) ∧ ¬ monoLeft θ 1 7 ∧ ¬ monoRight θ 0 1
          rw [mx,my]
          decide +kernel)
      have bad : (0 : ZMod 2) = 1 := by
        linear_combination (norm := (ring_nf; simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, sub_zero]))
          e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7
      exact zero_ne_one bad
    · have e0 := eqn 0 0 0 rfl (by
          change (∃ a, θ.table 0 0 = some a) ∧ ¬ monoLeft θ 1 0 ∧ ¬ monoRight θ 1 0
          rw [mx,my]
          decide +kernel)
      have e1 := eqn 0 1 0 rfl (by
          change (∃ a, θ.table 0 1 = some a) ∧ ¬ monoLeft θ 1 0 ∧ ¬ monoRight θ 1 1
          rw [mx,my]
          decide +kernel)
      have e2 := eqn 2 0 1 rfl (by
          change (∃ a, θ.table 2 0 = some a) ∧ ¬ monoLeft θ 1 2 ∧ ¬ monoRight θ 1 0
          rw [mx,my]
          decide +kernel)
      have e3 := eqn 2 2 0 rfl (by
          change (∃ a, θ.table 2 2 = some a) ∧ ¬ monoLeft θ 1 2 ∧ ¬ monoRight θ 1 2
          rw [mx,my]
          decide +kernel)
      have e4 := eqn 3 2 0 rfl (by
          change (∃ a, θ.table 3 2 = some a) ∧ ¬ monoLeft θ 1 3 ∧ ¬ monoRight θ 1 2
          rw [mx,my]
          decide +kernel)
      have e5 := eqn 3 3 1 rfl (by
          change (∃ a, θ.table 3 3 = some a) ∧ ¬ monoLeft θ 1 3 ∧ ¬ monoRight θ 1 3
          rw [mx,my]
          decide +kernel)
      have e6 := eqn 4 3 0 rfl (by
          change (∃ a, θ.table 4 3 = some a) ∧ ¬ monoLeft θ 1 4 ∧ ¬ monoRight θ 1 3
          rw [mx,my]
          decide +kernel)
      have e7 := eqn 4 1 1 rfl (by
          change (∃ a, θ.table 4 1 = some a) ∧ ¬ monoLeft θ 1 4 ∧ ¬ monoRight θ 1 1
          rw [mx,my]
          decide +kernel)
      have bad : (0 : ZMod 2) = 1 := by
        linear_combination (norm := (ring_nf; simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, sub_zero]))
          e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7
      exact zero_ne_one bad
  exact ⟨θ,admissible,hrank,unbalanced,(core _ _ θ admissible).2.1 unbalanced |>.2 hrank,feasible⟩



end D5.S3.Observer.Separation.BooleanRankThreeFiber

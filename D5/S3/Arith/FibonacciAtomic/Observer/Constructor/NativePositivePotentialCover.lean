/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositivePotentialCover
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Signed source occurrence cycles and minimum natural block bases. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativePositiveBranchReduction
import D5.S3.Combinatorics.Graph.LayeredCirculation.SupplierDual

/-! Integer consistency and minimum natural ranks on the actual source graph. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePositivePotentialCover

open NativePositiveBranchReduction NativePositiveImageCover NativeTermUnification
open NativeGroundSolutionSpace Maths Maths.MaxPlusPotential
open Lambda Strata.Util

variable {X : Type} [DecidableEq X]

/-- Select one residual sort without identifying repeated or parallel edges. -/
def sortEdges (B : List (BranchEquation X)) (s : X → Term X) (j : X) :=
  (sourceOffsetEdges B s).filter (fun e => e.1.1.2.2 == j)

abbrev Edge (B : List (BranchEquation X)) (s : X → Term X) (j : X) :=
  Fin (sortEdges B s j).length × Bool

def signedGraph (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    EdgeGraph (Occurrence X) (Edge B s j) where
  source e := if e.2 then ((sortEdges B s j).get e.1).1.1
    else ((sortEdges B s j).get e.1).1.2
  target e := if e.2 then ((sortEdges B s j).get e.1).1.2
    else ((sortEdges B s j).get e.1).1.1

def signedWeight (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    (e : Edge B s j) : Int :=
  if e.2 then -((sortEdges B s j).get e.1).2 else ((sortEdges B s j).get e.1).2

def ZeroCycles (B : List (BranchEquation X)) (s : X → Term X) (j : X) : Prop :=
  ∀ (v : Occurrence X) (c : (signedGraph B s j).Walk v v),
    walkWeight (signedWeight B s j) c = 0

def Potential (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    (δ : Occurrence X → Int) : Prop :=
  ∀ e ∈ sortEdges B s j, δ e.1.1 = δ e.1.2 + e.2

/-- The leaf carrier is arbitrary; nonemptiness is needed only to detect
inconsistent cycles. No shape or rank bound is imposed. -/
def BlockSolution (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    {L : Type} (u : Occurrence X → L → Nat) : Prop :=
  ∀ e ∈ sortEdges B s j, ∀ l, (u e.1.1 l : Int) = (u e.1.2 l : Int) + e.2

private theorem potential_iff (B : List (BranchEquation X)) (s : X → Term X) (j : X)
    (δ : Occurrence X → Int) :
    Potential B s j δ ↔ IsPotential (signedGraph B s j) (signedWeight B s j) δ := by
  constructor
  · intro h e
    have eq := h _ (List.get_mem (sortEdges B s j) e.1)
    cases e with | mk i b => cases b <;> simp_all [signedGraph, signedWeight] <;> omega
  · intro h e he
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp he
    have hf := h (i, false)
    have hb := h (i, true)
    simp only [signedGraph, signedWeight, Bool.false_eq_true, ↓reduceIte] at hf hb
    omega

private theorem walk_exact {B : List (BranchEquation X)} {s : X → Term X} {j : X}
    {δ : Occurrence X → Int} (h : Potential B s j δ)
    {v w : Occurrence X} (c : (signedGraph B s j).Walk v w) :
    walkWeight (signedWeight B s j) c = δ w - δ v := by
  induction c with
  | nil => simp [walkWeight]
  | concat c e legal ih =>
      have eq := h _ (List.get_mem (sortEdges B s j) e.1)
      rw [walkWeight_concat, ih]
      subst legal
      cases e with | mk i b => cases b <;> simp_all [signedGraph, signedWeight] <;> omega

private theorem zeroCycles_iff (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    ZeroCycles B s j ↔ ∃ δ, Potential B s j δ := by
  constructor
  · intro h
    obtain ⟨δ, hδ⟩ :=
      (exists_isPotential_iff_forall_closedWalk_nonpos
        (G := signedGraph B s j) (signedWeight B s j)).mpr (fun v c => (h v c).le)
    exact ⟨δ, (potential_iff B s j δ).mpr hδ⟩
  · rintro ⟨δ, hδ⟩ v c
    simpa using walk_exact hδ c

/-- Enumerate the two signed orientations of every actual source edge.
The list retains separate indices for repeated and parallel comparisons. -/
def signedEdges (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    List (Edge B s j) :=
  (List.finRange (sortEdges B s j).length).flatMap fun i => [(i, false), (i, true)]

private theorem signedEdges_complete (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (e : Edge B s j) : e ∈ signedEdges B s j := by
  rcases e with ⟨i, b⟩
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  cases b <;> simp

/-- Finite max-plus relaxation on the original source occurrence graph.
Zero is a lower bound at every vertex, including isolated occurrences. -/
def sourceRelaxation (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    Nat → Occurrence X → Int
  | 0, _ => 0
  | t + 1, v =>
      ((signedEdges B s j).map fun e =>
        if (signedGraph B s j).target e = v then
          sourceRelaxation B s j t ((signedGraph B s j).source e) + signedWeight B s j e
        else 0).foldr max 0

/-- An executable integer potential candidate, with no solution, potential,
path, cycle decision or classical choice supplied as input. The number of
rounds is the number of signed indexed source edges. -/
def computedSourcePotential (B : List (BranchEquation X)) (s : X → Term X) (j : X) :
    Occurrence X → Int :=
  sourceRelaxation B s j (2 * (sortEdges B s j).length)

private theorem fold_max_base (l : List Int) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact ih.trans (le_max_right _ _)

private theorem fold_max_witness {P : Int → Prop} (l : List Int)
    (hb : P 0) (hl : ∀ a ∈ l, P a) : P (l.foldr max 0) := by
  induction l with
  | nil => exact hb
  | cons a l ih =>
      simp only [List.foldr_cons]
      rcases le_total a (l.foldr max 0) with h | h
      · rw [max_eq_right h]
        exact ih (fun x hx => hl x (List.mem_cons_of_mem a hx))
      · rw [max_eq_left h]
        exact hl a (List.mem_cons_self)

private theorem sourceRelaxation_nonneg (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (t : Nat) (v : Occurrence X) :
    0 ≤ sourceRelaxation B s j t v := by
  cases t with
  | zero => exact le_rfl
  | succ t => exact fold_max_base _

private theorem sourceRelaxation_edge (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (t : Nat) (e : Edge B s j) :
    sourceRelaxation B s j t ((signedGraph B s j).source e) + signedWeight B s j e ≤
      sourceRelaxation B s j (t + 1) ((signedGraph B s j).target e) := by
  apply List.le_max_of_le' (0 : Int)
  · exact List.mem_map.mpr ⟨e, signedEdges_complete B s j e, rfl⟩
  · simp only [ite_true]
    exact le_rfl

private theorem source_walk_le_relaxation (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (t : Nat) {v w : Occurrence X}
    (c : (signedGraph B s j).Walk v w) (hlen : c.length ≤ t) :
    walkWeight (signedWeight B s j) c ≤ sourceRelaxation B s j t w := by
  induction t generalizing v w with
  | zero =>
      cases c with
      | nil => simp [walkWeight, EdgeGraph.Walk.edges, sourceRelaxation]
      | concat c e legal => simp at hlen
  | succ t ih =>
      cases c with
      | nil => simpa [walkWeight, EdgeGraph.Walk.edges] using
          sourceRelaxation_nonneg B s j (t + 1) v
      | concat c e legal =>
          have hp := ih c (by simpa using Nat.le_of_succ_le_succ hlen)
          have he := sourceRelaxation_edge B s j t e
          rw [legal] at he
          rw [walkWeight_concat]
          omega

private theorem sourceRelaxation_attained (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (t : Nat) (v : Occurrence X) :
    ∃ (start : Occurrence X) (c : (signedGraph B s j).Walk start v),
      c.length ≤ t ∧ sourceRelaxation B s j t v = walkWeight (signedWeight B s j) c := by
  induction t generalizing v with
  | zero => exact ⟨v, .nil, le_rfl, by simp [sourceRelaxation, walkWeight, EdgeGraph.Walk.edges]⟩
  | succ t ih =>
      apply fold_max_witness
        (P := fun z => ∃ (start : Occurrence X) (c : (signedGraph B s j).Walk start v),
          c.length ≤ t + 1 ∧ z = walkWeight (signedWeight B s j) c)
      · exact ⟨v, .nil, Nat.zero_le _, by simp [walkWeight, EdgeGraph.Walk.edges]⟩
      · intro z hz
        obtain ⟨e, _, rfl⟩ := List.mem_map.mp hz
        by_cases he : (signedGraph B s j).target e = v
        · simp only [if_pos he]
          obtain ⟨start, c, hlen, hvalue⟩ := ih ((signedGraph B s j).source e)
          refine ⟨start, (c.concat e rfl).castFinish he, ?_, ?_⟩
          · simpa using Nat.add_le_add_right hlen 1
          · rw [walkWeight_castFinish, walkWeight_concat, hvalue]
        · simp only [if_neg he]
          exact ⟨v, .nil, Nat.zero_le _, by simp [walkWeight, EdgeGraph.Walk.edges]⟩

private theorem computed_source_potential (B : List (BranchEquation X))
    (s : X → Term X) (j : X) (good : ZeroCycles B s j) :
    Potential B s j (computedSourcePotential B s j) := by
  apply (potential_iff B s j _).mpr
  intro e
  obtain ⟨start, c, _, hvalue⟩ := sourceRelaxation_attained B s j
    (2 * (sortEdges B s j).length) ((signedGraph B s j).source e)
  obtain ⟨pruned, hnodup, hweight⟩ := exists_nodup_visited_walkWeight_le
    (fun v c => (good v c).le) (c.concat e rfl).length (c.concat e rfl) le_rfl
  have hcard : pruned.length ≤ 2 * (sortEdges B s j).length := by
    simpa only [EdgeGraph.Walk.edges_length, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Nat.mul_comm] using
      pruned.edges_nodup_of_visited_nodup hnodup |>.length_le_card
  have hbound := source_walk_le_relaxation B s j _ pruned hcard
  rw [walkWeight_concat] at hweight
  change sourceRelaxation B s j _ ((signedGraph B s j).source e) + signedWeight B s j e ≤
    sourceRelaxation B s j _ ((signedGraph B s j).target e)
  omega

private theorem edge_spec (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    {e : (Occurrence X × Occurrence X) × Int}
    (he : e ∈ sourceOffsetEdges B (action p S)) :
    e.1.1 ∈ occurrenceVertices p (action p S) ∧
    e.1.2 ∈ occurrenceVertices p (action p S) ∧ e.1.1.2.2 = e.1.2.2.2 := by
  apply (mgu_occurrence_graph_exact p (shapeEquations B) S hok).2.1
  rw [← source_comparison_graph_identification]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

private theorem connected_sort (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    {v w : Occurrence X} (h : sourceConnected B (action p S) v w) :
    v.2.2 = w.2.2 := by
  induction h with
  | rel a b he =>
      obtain ⟨e, he, eq⟩ := List.mem_map.mp he
      have hs := (edge_spec p B S hok he).2.2
      simpa only [eq] using hs
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

private theorem common_difference (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (j : X) {f g : Occurrence X → Int}
    (hf : Potential B (action p S) j f) (hg : Potential B (action p S) j g)
    {v w : Occurrence X} (h : sourceConnected B (action p S) v w) :
    v.2.2 = j → f v - g v = f w - g w := by
  induction h with
  | rel v w he =>
      intro hv
      obtain ⟨e, he, eq⟩ := List.mem_map.mp he
      have pair : e.1 = (v,w) := eq
      have mem : e ∈ sortEdges B (action p S) j := by
        simp only [sortEdges, List.mem_filter, beq_iff_eq]
        exact ⟨he, by simpa only [pair] using hv⟩
      have h1 := hf e mem
      have h2 := hg e mem
      simp only [pair] at h1 h2
      omega
  | refl v => intro _; rfl
  | symm v w h ih =>
      intro hw
      have hv : v.2.2 = j := (connected_sort p B S hok h).trans hw
      exact (ih hv).symm
  | trans v w z h1 h2 ih1 ih2 =>
      intro hv
      have hw : w.2.2 = j := (connected_sort p B S hok h1).symm.trans hv
      exact (ih1 hv).trans (ih2 hw)

/-- The actual source comparison graph admits one minimum natural base per
occurring sort. Nonzero cycles exclude solutions on every inhabited leaf
carrier; zero cycles classify all natural solutions, including a singleton
isolated occurrence. The theorem does not assert native code reconstruction. -/
theorem source_sort_minimum_base (p : Presentation X) (B : List (BranchEquation X))
    (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (j : X) (occurs : ∃ v ∈ occurrenceVertices p (action p S), v.2.2 = j) :
    (¬ ZeroCycles B (action p S) j →
      ∀ (L : Type) [Nonempty L] (u : Occurrence X → L → Nat),
        ¬ BlockSolution B (action p S) j u) ∧
    (ZeroCycles B (action p S) j →
      ∃ (δ : Occurrence X → Int) (b : Occurrence X) (a : Occurrence X → Nat),
        δ = computedSourcePotential B (action p S) j ∧
        Potential B (action p S) j δ ∧
        b ∈ occurrenceVertices p (action p S) ∧ b.2.2 = j ∧ a b = 0 ∧
        (∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
          δ b ≤ δ v ∧ (a v : Int) = δ v - δ b) ∧
        (∀ (L : Type) (u : Occurrence X → L → Nat),
          BlockSolution B (action p S) j u ↔
          ∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
            ∀ l, u v l = u b l + a v)) := by
  classical
  constructor
  · intro bad L _ u hu
    let l : L := Classical.choice (inferInstance : Nonempty L)
    apply bad
    exact (zeroCycles_iff B (action p S) j).mpr ⟨fun v => (u v l : Int), fun e he => hu e he l⟩
  · intro good
    let δ := computedSourcePotential B (action p S) j
    have hδ : Potential B (action p S) j δ := computed_source_potential B (action p S) j good
    let V := (occurrenceVertices p (action p S)).toFinset.filter (fun v => v.2.2 = j)
    have hV : V.Nonempty := by
      obtain ⟨v, hv, hj⟩ := occurs
      exact ⟨v, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, hj⟩⟩
    obtain ⟨b, hb, hmin⟩ := V.exists_min_image δ hV
    have hb' := Finset.mem_filter.mp hb
    let a : Occurrence X → Nat := fun v => (δ v - δ b).toNat
    have ha : ∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
        δ b ≤ δ v ∧ (a v : Int) = δ v - δ b := by
      intro v hv hj
      have hm := hmin v (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, hj⟩)
      exact ⟨hm, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨δ, b, a, rfl, hδ, List.mem_toFinset.mp hb'.1, hb'.2, ?_, ha, ?_⟩
    · simp [a]
    · intro L u
      constructor
      · intro hu v hv hj l
        have conn := (source_connected_iff_sort p B S hok b v
          (List.mem_toFinset.mp hb'.1) hv).mpr (hb'.2.trans hj.symm)
        have hd := common_difference p B S hok j
          (f := fun w => (u w l : Int)) (g := δ)
          (fun e he => hu e he l) hδ conn hb'.2
        have hav := (ha v hv hj).2
        omega
      · intro hu e he l
        have he' := (List.mem_filter.mp he).1
        have hj : e.1.1.2.2 = j := by
          simpa only [beq_iff_eq] using (List.mem_filter.mp he).2
        have spec := edge_spec p B S hok he'
        have hu1 := hu e.1.1 spec.1 hj l
        have hu2 := hu e.1.2 spec.2.1 (spec.2.2.symm.trans hj) l
        have ha1 := (ha e.1.1 spec.1 hj).2
        have ha2 := (ha e.1.2 spec.2.1 (spec.2.2.symm.trans hj)).2
        have hed := hδ e he
        omega

/-- Leaves retain their ordered positions even when all ranks coincide. -/
def Leaves : FreeMagma Unit → Type
  | .of _ => Unit
  | .mul A B => Leaves A ⊕ Leaves B

instance leavesFinite : (T : FreeMagma Unit) → Finite (Leaves T)
  | .of _ => inferInstanceAs (Finite Unit)
  | .mul A B =>
      letI := leavesFinite A
      letI := leavesFinite B
      inferInstanceAs (Finite (Leaves A ⊕ Leaves B))

instance leavesNonempty : (T : FreeMagma Unit) → Nonempty (Leaves T)
  | .of _ => inferInstanceAs (Nonempty Unit)
  | .mul A B =>
      letI := leavesNonempty A
      inferInstanceAs (Nonempty (Leaves A ⊕ Leaves B))

def fill : (T : FreeMagma Unit) → (Leaves T → Nat) → NativeFiniteNormalInversion.Code
  | .of _, r => .of (r ())
  | .mul A B, r => .mul (fill A (fun l => r (.inl l))) (fill B (fun l => r (.inr l)))

private theorem fill_shift (T : FreeMagma Unit) (r : Leaves T → Nat) (a : Nat) :
    fill T (fun l => r l + a) = NativeFiniteNormalInversion.shiftCode a (fill T r) := by
  induction T using FreeMagma.rec with
  | of => rfl
  | mul A B ihA ihB =>
      exact congrArg₂ FreeMagma.mul (ihA _) (ihB _)

private theorem normal_subtree (C : NativeFiniteNormalInversion.Code) (q : List Bool)
    (D : NativeFiniteNormalInversion.Code) (hC : NativeFiniteNormalInversion.Normal C)
    (h : subtree C q = some D) : NativeFiniteNormalInversion.Normal D := by
  induction q generalizing C with
  | nil =>
      simp only [subtree, Option.some.injEq] at h
      exact h ▸ hC
  | cons b q ih =>
      cases C with
      | of n => cases h
      | mul A B =>
          cases b
          · exact ih A hC.1 h
          · exact ih B hC.2.1 h

/-- Actual occurrence subtrees turn the minimum rank base into a normal
native block. Rank inverses and expansion recover the identical blocks. -/
theorem source_canonical_block_recovery (p : Presentation X)
    (B : List (BranchEquation X)) (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (j : X) (occurs : ∃ v ∈ occurrenceVertices p (action p S), v.2.2 = j)
    (good : ZeroCycles B (action p S) j) :
    ∃ (b : Occurrence X) (a : Occurrence X → Nat),
      b ∈ occurrenceVertices p (action p S) ∧ b.2.2 = j ∧ a b = 0 ∧
      ∀ (T : FreeMagma Unit) (u : Occurrence X → Leaves T → Nat)
        (C : X → NativeFiniteNormalInversion.Code),
        BlockSolution B (action p S) j u →
        (∀ x, NativeFiniteNormalInversion.Normal (C x)) →
        (∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
          subtree (C v.1) v.2.1 = some (fill T (u v))) →
        NativeFiniteNormalInversion.Normal (fill T (u b)) ∧
        ∀ v ∈ occurrenceVertices p (action p S), v.2.2 = j →
          fill T (u v) = NativeFiniteNormalInversion.shiftCode (a v) (fill T (u b)) ∧
          NativeFiniteNormalInversion.expand (fill T (u v)) =
            GenealogicalFiberTransport.substitution^[a v]
              (NativeFiniteNormalInversion.expand (fill T (u b))) ∧
          (∀ l, NativeFiniteNormalInversion.rankInverse (a v) (u v l) = some (u b l)) := by
  obtain ⟨δ, b, a, _, hδ, hb, hj, hab, hmin, law⟩ :=
    (source_sort_minimum_base p B S hok j occurs).2 good
  refine ⟨b, a, hb, hj, hab, ?_⟩
  intro T u C hu hC actual
  have ranks := (law (Leaves T) u).mp hu
  refine ⟨normal_subtree (C b.1) b.2.1 _ (hC b.1) (actual b hb hj), ?_⟩
  intro v hv hvj
  have heq : u v = fun l => u b l + a v := funext (ranks v hv hvj)
  have code : fill T (u v) = NativeFiniteNormalInversion.shiftCode (a v) (fill T (u b)) := by
    rw [heq]
    exact fill_shift T (u b) (a v)
  refine ⟨code, ?_, ?_⟩
  · rw [code]
    exact NativeFiniteNormalInversion.shift_expand (a v) (fill T (u b))
  · intro l
    exact ((NativeFiniteNormalInversion.exact_natural_rank_inverse (a v) (u v l)).1
      (u b l)).mpr (ranks v hv hvj l).symm

/-- The actual code at an occurrence address. Invalid addresses have a
fixed default; all results below prove validity before using a block. -/
def occurrenceCode (C : X → NativeFiniteNormalInversion.Code) (v : Occurrence X) :
    NativeFiniteNormalInversion.Code :=
  (subtree (C v.1) v.2.1).getD (.of 0)

private def Fits (C : X → NativeFiniteNormalInversion.Code) :
    Term (Occurrence X) → NativeFiniteNormalInversion.Code → Prop
  | .of (.inl _), .of _ => True
  | .of (.inl _), .mul _ _ => False
  | .of (.inr v), D => D = occurrenceCode C v
  | .mul A B, .mul D E => Fits C A D ∧ Fits C B E
  | .mul _ _, .of _ => False

private theorem subtree_child {A : Type} (C : FreeMagma A) (q : List Bool)
    (D E : FreeMagma A) (h : subtree C q = some (.mul D E)) :
    subtree C (q ++ [false]) = some D ∧ subtree C (q ++ [true]) = some E := by
  induction q generalizing C with
  | nil => simpa only [subtree, List.nil_append, Option.some.injEq] using h ▸
      (show subtree (.mul D E) [false] = some D ∧
        subtree (.mul D E) [true] = some E from ⟨rfl, rfl⟩)
  | cons b q ih =>
      cases C with
      | of a => cases h
      | mul A B => cases b <;> exact ih _ h

private theorem fits_decorate (C : X → NativeFiniteNormalInversion.Code)
    (w : X → NativeGroundSolutionSpace.Source) (x : X) (t : Term X)
    (q : List Bool) (D : NativeFiniteNormalInversion.Code)
    (actual : subtree (C x) q = some D)
    (sh : shape D = evaluate w t) : Fits C (decorateFrom x q t) D := by
  induction t generalizing q D with
  | of a =>
      cases a with
      | inl b => cases D <;> simp_all [shape, evaluate, Fits, decorateFrom]
      | inr j =>
          change D = (subtree (C x) q).getD (.of 0)
          rw [actual]
          rfl
  | mul A B ihA ihB =>
      cases D with
      | of n => cases sh
      | mul D E =>
          have hs : shape D = evaluate w A ∧ shape E = evaluate w B := by
            exact FreeMagma.mul.inj sh
          have hc := subtree_child (C x) q D E actual
          exact ⟨ihA _ _ hc.1 hs.1, ihB _ _ hc.2 hs.2⟩

private theorem fits_offsets (C : X → NativeFiniteNormalInversion.Code)
    (A B : Term (Occurrence X)) (D E : NativeFiniteNormalInversion.Code)
    (a : Nat) (hA : Fits C A D) (hB : Fits C B E)
    (eq : D = NativeFiniteNormalInversion.shiftCode a E) :
    ∀ e ∈ offsetComparisonEdges (a : Int) A B,
      e.2 = (a : Int) ∧ occurrenceCode C e.1.1 =
        NativeFiniteNormalInversion.shiftCode a (occurrenceCode C e.1.2) := by
  induction A generalizing B D E with
  | of b =>
      cases B with
      | of c =>
          cases b <;> cases c <;> simp only [offsetComparisonEdges,
            List.mem_singleton, List.not_mem_nil, false_implies, forall_eq]
          exact ⟨rfl, by simpa only [Fits] at hA hB; simpa [hA, hB] using eq⟩
      | mul l r => simp [offsetComparisonEdges]
  | mul A B ihA ihB =>
      cases B_1 : B with
      | of c => simp [offsetComparisonEdges]
      | mul U V =>
          cases E with
          | of n => cases hB
          | mul E F =>
              subst D
              rcases hA with ⟨hD, hE⟩
              rcases hB with ⟨hU, hV⟩
              intro e he
              rcases List.mem_append.mp he with he | he
              · exact ihA _ _ _ hD hU rfl e he
              · exact ihB _ _ _ hE hV rfl e he

private theorem actual_source_offsets (B : List (BranchEquation X))
    (s : X → Term X) (C : X → NativeFiniteNormalInversion.Code)
    (factor : ∀ x, evaluate (fun y => shape (C y)) (s x) = shape (C x))
    (sat : ∀ b ∈ B, b.Holds C) :
    ∀ e ∈ sourceOffsetEdges B s, ∃ a : Nat, e.2 = (a : Int) ∧
      occurrenceCode C e.1.1 = NativeFiniteNormalInversion.shiftCode a
        (occurrenceCode C e.1.2) := by
  have fit (x : X) : Fits C (decorate s x) (C x) :=
    fits_decorate C (fun y => shape (C y)) x (s x) [] (C x) rfl (factor x).symm
  intro e he
  obtain ⟨b, hb, he⟩ := List.mem_flatMap.mp he
  have hs := sat b hb
  cases b with
  | primitive z n => cases he
  | collapse z x y => cases he
  | shift z a x => exact ⟨a, fits_offsets C _ _ _ _ a (fit z) (fit x) hs e he⟩
  | ordinary z x y =>
      refine ⟨0, fits_offsets C _ _ _ _ 0 (fit z) ?_ ?_ e he⟩
      · exact ⟨fit x, fit y⟩
      · simpa only [NativeFiniteNormalInversion.shiftCode] using hs
  | same x y =>
      refine ⟨0, fits_offsets C _ _ _ _ 0 (fit x) (fit y) ?_ e he⟩
      simpa only [NativeFiniteNormalInversion.shiftCode] using hs

#print axioms source_sort_minimum_base
#print axioms source_canonical_block_recovery

end D5.S3.Arith.FibonacciAtomic.Observer.NativePositivePotentialCover

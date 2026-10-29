/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveBranchReduction
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite native constructor-collapse branching and total free-shape reduction. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativePositiveImageCover
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion

/-! Canonical native constructor cases precede free-shape unification. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveBranchReduction

open NativeFiniteNormalInversion (Code Normal expand encode smart shiftCode)
open NativeTermUnification (Term Presentation evaluate)
open NativeGroundSolutionSpace (Sol action encodeEquations)
open NativePositiveImageCover (Occurrence occurrenceVertices Connected occurrenceEdges comparisonEdges
  comparisonTerm mgu_occurrence_graph_exact)
open GenealogicalFiberTransport (substitution)
open Lambda Strata.Util

abbrev Source := GenealogicalFiberTransport.Source

variable {X : Type}

/-- Finite named native equations. Every declared name remains in X. -/
inductive Equation (X : Type) where
  | primitive : X → Nat → Equation X
  | shift : X → Nat → X → Equation X
  | pair : X → X → X → Equation X
  | same : X → X → Equation X

def Equation.Holds (v : X → Source) : Equation X → Prop
  | .primitive z n => v z = expand (.of n)
  | .shift z a x => v z = substitution^[a] (v x)
  | .pair z x y => v z = .mul (v x) (v y)
  | .same x y => v x = v y

/-- A collapse introduces an unrestricted natural rank, rather than
enumerating ranks or bounding the underlying source trees. -/
inductive BranchEquation (X : Type) where
  | primitive : X → Nat → BranchEquation X
  | shift : X → Nat → X → BranchEquation X
  | ordinary : X → X → X → BranchEquation X
  | collapse : X → X → X → BranchEquation X
  | same : X → X → BranchEquation X

def BranchEquation.origin : BranchEquation X → Equation X
  | .primitive z n => .primitive z n
  | .shift z a x => .shift z a x
  | .ordinary z x y | .collapse z x y => .pair z x y
  | .same x y => .same x y

def BranchEquation.Holds (u : X → Code) : BranchEquation X → Prop
  | .primitive z n => u z = .of n
  | .shift z a x => u z = shiftCode a (u x)
  | .ordinary z x y => u z = .mul (u x) (u y)
  | .collapse z x y => ∃ r : Nat,
      u x = .of (r + 1) ∧ u y = .of r ∧ u z = .of (r + 2)
  | .same x y => u x = u y

def choices : Equation X → List (BranchEquation X)
  | .primitive z n => [.primitive z n]
  | .shift z a x => [.shift z a x]
  | .pair z x y => [.ordinary z x y, .collapse z x y]
  | .same x y => [.same x y]

/-- Executable finite branching depends only on the input equations. -/
def branches : List (Equation X) → List (List (BranchEquation X))
  | [] => [[]]
  | e :: E => (choices e).flatMap fun b => (branches E).map (b :: ·)

/-- Erase only ranks, after choosing the native constructor cases. -/
def shape : Code → Source
  | .of _ => .of true
  | .mul l r => .mul (shape l) (shape r)

private def name (x : X) : Term X := .of (.inr x)
private def shapeLeaf : Term X := .of (.inl true)

def BranchEquation.shapeEquations : BranchEquation X → NativeGroundSolutionSpace.Equations X
  | .primitive z _ => [(name z, shapeLeaf)]
  | .shift z _ x => [(name z, name x)]
  | .ordinary z x y => [(name z, .mul (name x) (name y))]
  | .collapse z x y => [(name x, shapeLeaf), (name y, shapeLeaf), (name z, shapeLeaf)]
  | .same x y => [(name x, name y)]

def shapeEquations (B : List (BranchEquation X)) : NativeGroundSolutionSpace.Equations X :=
  B.flatMap BranchEquation.shapeEquations

/-! The source-side comparison carrier keeps the rank information that is
discarded by `shape`.  A shift contributes its actual natural offset, while
ordinary and equality comparisons contribute zero offset.  Primitive and
collapse cases retain their scalar constraints in `B` but contribute no
residual block edge. -/

private def offsetComparisonEdges (d : Int) : Term (Occurrence X) → Term (Occurrence X) →
    List ((Occurrence X × Occurrence X) × Int)
  | .of (.inr a), .of (.inr b) => [((a, b), d)]
  | .mul l r, .mul u v => offsetComparisonEdges d l u ++ offsetComparisonEdges d r v
  | _, _ => []

private theorem offsetComparisonEdges_projection (d : Int)
    (A B : Term (Occurrence X)) :
    (offsetComparisonEdges d A B).map (fun e => e.1) = comparisonEdges A B := by
  induction A generalizing B with
  | of a =>
      cases B with
      | of b => cases a <;> cases b <;> rfl
      | mul l r => simp [offsetComparisonEdges, comparisonEdges]
  | mul l r hl hr =>
      cases B with
      | of a => rfl
      | mul u v =>
          simp only [offsetComparisonEdges, comparisonEdges, List.map_append, hl, hr]

def sourceOffsetEdges (B : List (BranchEquation X)) (s : X → Term X) :
    List ((Occurrence X × Occurrence X) × Int) :=
  B.flatMap fun b => match b with
  | .primitive _ _ => []
  | .shift z a x =>
      offsetComparisonEdges (Int.ofNat a)
        (comparisonTerm s (name z)) (comparisonTerm s (name x))
  | .ordinary z x y =>
      offsetComparisonEdges 0
        (comparisonTerm s (name z))
        (comparisonTerm s (.mul (name x) (name y)))
  | .collapse _ _ _ => []
  | .same x y =>
      offsetComparisonEdges 0
        (comparisonTerm s (name x)) (comparisonTerm s (name y))

def sourceOccurrenceEdges (B : List (BranchEquation X)) (s : X → Term X) :
    List (Occurrence X × Occurrence X) :=
  (sourceOffsetEdges B s).map (fun e => e.1)

def sourceConnected (B : List (BranchEquation X)) (s : X → Term X) :
    Occurrence X → Occurrence X → Prop :=
  Relation.EqvGen (fun a b => (a, b) ∈ sourceOccurrenceEdges B s)

private theorem comparisonTerm_primitive_leaf (s : X → Term X) :
    comparisonTerm s (.of (.inl true) : Term X) =
      (.of (.inl true) : Term (Occurrence X)) := by
  rfl

private theorem comparisonEdges_primitive_right (A : Term (Occurrence X)) (b : Bool) :
    comparisonEdges A (.of (.inl b)) = [] := by
  cases A with
  | of a => cases a <;> rfl
  | mul l r => rfl

theorem source_comparison_graph_identification (B : List (BranchEquation X))
    (s : X → Term X) :
    sourceOccurrenceEdges B s = occurrenceEdges (shapeEquations B) s := by
  induction B with
  | nil => rfl
  | cons b B ih =>
      have head :
          (sourceOffsetEdges [b] s).map (fun e => e.1) =
            occurrenceEdges (BranchEquation.shapeEquations b) s := by
        cases b <;>
          simp [sourceOffsetEdges, occurrenceEdges, BranchEquation.shapeEquations,
            offsetComparisonEdges_projection, comparisonEdges,
            name, shapeLeaf]
        all_goals
          simp [comparisonTerm_primitive_leaf, comparisonEdges_primitive_right]
      calc
        sourceOccurrenceEdges (b :: B) s =
            (sourceOffsetEdges [b] s).map (fun e => e.1) ++
              sourceOccurrenceEdges B s := by
                change (sourceOffsetEdges (b :: B) s).map (fun e => e.1) =
                  (sourceOffsetEdges [b] s).map (fun e => e.1) ++
                    (sourceOffsetEdges B s).map (fun e => e.1)
                simp [sourceOffsetEdges, List.flatMap_cons, List.map_append,
                  List.flatMap_singleton]
        _ = occurrenceEdges (BranchEquation.shapeEquations b) s ++
              occurrenceEdges (shapeEquations B) s := by rw [head, ih]
        _ = occurrenceEdges (shapeEquations (b :: B)) s := by
              simp only [shapeEquations, List.flatMap_cons, occurrenceEdges,
                List.flatMap_append]

theorem source_connected_iff_sort (p : Presentation X)
    (B : List (BranchEquation X)) (S : SubstInfo)
    (hok : (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S)
    (a b : Occurrence X)
    (ha : a ∈ occurrenceVertices p (action p S))
    (hb : b ∈ occurrenceVertices p (action p S)) :
    (sourceConnected B (action p S) a b ↔ a.2.2 = b.2.2) := by
  unfold sourceConnected
  rw [source_comparison_graph_identification]
  exact (mgu_occurrence_graph_exact p (shapeEquations B) S hok).2.2 a b ha hb

private theorem shift_smart (a : Nat) (A B : Code) :
    smart (shiftCode a A) (shiftCode a B) = shiftCode a (smart A B) := by
  cases A with
  | of n =>
      cases B with
      | of m =>
          have eq : n + a = m + a + 1 ↔ n = m + 1 := by omega
          simp only [shiftCode, smart, eq]
          split_ifs <;> congr 1 <;> omega
      | mul l r => rfl
  | mul l r => cases B <;> rfl

private theorem encode_substitution (g : Source) :
    encode (substitution g) = shiftCode 1 (encode g) := by
  induction g with
  | of b => cases b <;> rfl
  | mul l r hl hr =>
      change smart (encode (substitution l)) (encode (substitution r)) = _
      rw [hl, hr]
      exact shift_smart 1 (encode l) (encode r)

private theorem shift_zero (C : Code) : shiftCode 0 C = C := by
  induction C with
  | of n => rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

private theorem shift_add (a b : Nat) (C : Code) :
    shiftCode a (shiftCode b C) = shiftCode (a + b) C := by
  induction C with
  | of n => simp only [shiftCode, Nat.add_assoc, Nat.add_comm b a]
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

private theorem encode_shift (a : Nat) (g : Source) :
    encode (substitution^[a] g) = shiftCode a (encode g) := by
  induction a with
  | zero => exact (shift_zero _).symm
  | succ a ih =>
      rw [Function.iterate_succ_apply', encode_substitution, ih, shift_add]
      congr 1
      omega

private theorem encode_primitive (n : Nat) : encode (expand (.of n)) = .of n := by
  change encode (substitution^[n] (.of true)) = .of n
  rw [encode_shift]
  simp only [encode, shiftCode, Nat.zero_add]

private theorem choice_complete (e : Equation X) (v : X → Source) (h : e.Holds v) :
    ∃ b ∈ choices e, b.Holds (fun x => encode (v x)) := by
  cases e with
  | primitive z n =>
      refine ⟨.primitive z n, List.mem_singleton_self _, ?_⟩
      change encode (v z) = .of n
      rw [h, encode_primitive]
  | shift z a x =>
      refine ⟨.shift z a x, List.mem_singleton_self _, ?_⟩
      change encode (v z) = shiftCode a (encode (v x))
      rw [h, encode_shift]
  | same x y =>
      exact ⟨.same x y, List.mem_singleton_self _, congrArg encode h⟩
  | pair z x y =>
      have hz : encode (v z) = smart (encode (v x)) (encode (v y)) := by
        rw [h]
        rfl
      cases hx : encode (v x) with
      | of n =>
          cases hy : encode (v y) with
          | of m =>
              by_cases eq : n = m + 1
              · refine ⟨.collapse z x y, by simp [choices], m, ?_, hy, ?_⟩
                · simpa only [eq] using hx
                · simpa only [hx, hy, smart, eq, ite_true] using hz
              · refine ⟨.ordinary z x y, by simp [choices], ?_⟩
                simpa only [BranchEquation.Holds, hx, hy, smart, eq, ite_false] using hz
          | mul l r =>
              refine ⟨.ordinary z x y, by simp [choices], ?_⟩
              simpa only [BranchEquation.Holds, hx, hy, smart] using hz
      | mul l r =>
          refine ⟨.ordinary z x y, by simp [choices], ?_⟩
          cases hy : encode (v y) <;> simpa only [BranchEquation.Holds, hx, hy, smart] using hz

private theorem branch_sound (u : X → Code) (b : BranchEquation X) (h : b.Holds u) :
    b.origin.Holds (fun x => expand (u x)) := by
  cases b with
  | primitive z n => exact congrArg expand h
  | shift z a x =>
      change expand (u z) = substitution^[a] (expand (u x))
      rw [h, NativeFiniteNormalInversion.shift_expand]
  | ordinary z x y => exact congrArg expand h
  | same x y => exact congrArg expand h
  | collapse z x y =>
      obtain ⟨r,hx,hy,hz⟩ := h
      change expand (u z) = .mul (expand (u x)) (expand (u y))
      rw [hx, hy, hz]
      exact NativeRankedEqualityCompiler.atomic_pair r

private theorem choices_origin (e : Equation X) (b : BranchEquation X) (h : b ∈ choices e) :
    b.origin = e := by
  cases e <;> simp only [choices, List.mem_cons, List.not_mem_nil, or_false] at h
  all_goals first
    | subst b; rfl
    | rcases h with rfl | rfl <;> rfl

private theorem branches_exact (E : List (Equation X)) (v : X → Source) :
    (∀ e ∈ E, e.Holds v) ↔
      ∃ B ∈ branches E, ∀ b ∈ B, b.Holds (fun x => encode (v x)) := by
  induction E with
  | nil => simp [branches]
  | cons e E ih =>
      constructor
      · intro h
        obtain ⟨b,hb,satb⟩ := choice_complete e v (h e (List.mem_cons_self))
        obtain ⟨B,hB,satB⟩ := ih.mp (fun c hc => h c (List.mem_cons_of_mem e hc))
        refine ⟨b :: B, List.mem_flatMap.mpr ⟨b,hb,List.mem_map.mpr ⟨B,hB,rfl⟩⟩, ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact satb
        · exact satB c hc
      · rintro ⟨whole,hwhole,sat⟩
        obtain ⟨b,hb,rest⟩ := List.mem_flatMap.mp hwhole
        obtain ⟨B,hB,eq⟩ := List.mem_map.mp rest
        subst whole
        have head := branch_sound _ b (sat b (List.mem_cons_self))
        have origin := choices_origin e b hb
        have head : e.Holds v := by
          simpa only [origin, NativeFiniteNormalInversion.encode_law] using head
        have tail := ih.mpr ⟨B,hB,fun c hc => sat c (List.mem_cons_of_mem b hc)⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact head
        · exact tail c hc

private theorem shape_shift (a : Nat) (C : Code) : shape (shiftCode a C) = shape C := by
  induction C with
  | of n => rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

private theorem branch_shape (u : X → Code) (b : BranchEquation X) (h : b.Holds u) :
    Sol b.shapeEquations (fun x => shape (u x)) := by
  cases b with
  | primitive z n =>
      intro c hc
      simp only [BranchEquation.shapeEquations, List.mem_singleton] at hc
      subst c
      change shape (u z) = .of true
      rw [h]
      rfl
  | shift z a x =>
      intro c hc
      simp only [BranchEquation.shapeEquations, List.mem_singleton] at hc
      subst c
      change shape (u z) = shape (u x)
      rw [h, shape_shift]
  | ordinary z x y =>
      intro c hc
      simp only [BranchEquation.shapeEquations, List.mem_singleton] at hc
      subst c
      change shape (u z) = .mul (shape (u x)) (shape (u y))
      rw [h]
      rfl
  | same x y =>
      intro c hc
      simp only [BranchEquation.shapeEquations, List.mem_singleton] at hc
      subst c
      exact congrArg shape h
  | collapse z x y =>
      obtain ⟨r,hx,hy,hz⟩ := h
      intro c hc
      simp only [BranchEquation.shapeEquations, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · change shape (u x) = .of true
        rw [hx]; rfl
      · change shape (u y) = .of true
        rw [hy]; rfl
      · change shape (u z) = .of true
        rw [hz]; rfl

/-- Every actual solution selects a member of the executable finite branch
list. Its full named shape assignment solves that branch's free equations. -/
theorem native_branch_reduction (p : Presentation X) (E : List (Equation X)) (v : X → Source) :
    (∀ e ∈ E, e.Holds v) ↔
      ∃ B ∈ branches E,
        (∀ x, Normal (encode (v x))) ∧
        (∀ b ∈ B, b.Holds (fun x => encode (v x))) ∧
        ∃ S : SubstInfo, (encodeEquations p (shapeEquations B)).unify SubstInfo.empty = .ok S ∧
          (∀ x, evaluate (fun y => shape (encode (v y))) (action p S x) = shape (encode (v x))) ∧
          (∀ a b, a ∈ occurrenceVertices p (action p S) →
            b ∈ occurrenceVertices p (action p S) →
            (Connected (shapeEquations B) (action p S) a b ↔ a.2.2 = b.2.2)) ∧
          (∀ a b, a ∈ occurrenceVertices p (action p S) →
            b ∈ occurrenceVertices p (action p S) →
            (sourceConnected B (action p S) a b ↔ a.2.2 = b.2.2)) := by
  constructor
  · intro hv
    obtain ⟨B,hB,sat⟩ := (branches_exact E v).mp hv
    have shapes : Sol (shapeEquations B) (fun x => shape (encode (v x))) := by
      intro c hc
      obtain ⟨b,hb,hc⟩ := List.mem_flatMap.mp hc
      exact branch_shape _ b (sat b hb) c hc
    obtain ⟨S,hok⟩ := NativeGroundSolutionSpace.native_complete p _ _ shapes
    refine ⟨B,hB,fun x => (NativeFiniteNormalInversion.encode_law (v x)).1,sat,S,hok,?_,?_,?_⟩
    · intro x
      have eq := congrFun (NativeGroundSolutionSpace.Ext_restriction p _ S hok _ shapes) x
      simpa only [NativeGroundSolutionSpace.Ext, NativeGroundSolutionSpace.sigma,
        NativeGroundSolutionSpace.evaluate_restrictTerm] using eq
    · exact (NativePositiveImageCover.mgu_occurrence_graph_exact p _ S hok).2.2
    · exact source_connected_iff_sort p B S hok
  · rintro ⟨B,hB,_,sat,S,hok,_,_,_⟩
    exact (branches_exact E v).mpr ⟨B,hB,sat⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveBranchReduction

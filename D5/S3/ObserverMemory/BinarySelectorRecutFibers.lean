/- GID: D5/S3/ObserverMemory/BinarySelectorRecutFibers
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/BinarySelectorRecutFibers
   mirror-E: none(waiver:symbolic-finite-relation-family)
   anchors: []
   utility: none
   digest: Selector recuts have exact fibers, optimal supplements and short legal separators. -/

import D5.S3.ObserverMemory.StrictAnchoredBoundary
import D5.S0.History.Coding.MinimumRollbackAlphabet
import D5.S3.ConceptDynamics.Reversibility.ExactRollbackInjectivityCriterion
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
namespace D5.S3.ObserverMemory.BinarySelectorRecutFibers
open StrictAnchoredBoundary
open D5.S0.Automata.TypedPartialDFAOOverBase

abbrev Word (m : Nat) := List.Vector Bool m
abbrev Point (m : Nat) := (Word m × Word m) × Bool

def selected {m : Nat} (p : Point m) : Word m := if p.2 then p.1.2 else p.1.1
def unused {m : Nat} (p : Point m) : Word m := if p.2 then p.1.1 else p.1.2
def anchor {m : Nat} (p : Point m) : List Bool := p.1.1.val ++ p.1.2.val
def selectorPrefix {m : Nat} (p : Point m) : List Bool := anchor p ++ [p.2]
def code {m : Nat} (p : Point m) : List Bool := anchor p ++ p.2 :: (selected p).val
def relation (m : Nat) : Set (List Bool) := Set.range (@code m)
def predecessor {m : Nat} (i j : Word m) : Set (List Bool) := {false :: i.val, true :: j.val}
def fine {m : Nat} (p : Point m) : Set (List Bool) × List Bool :=
  (predecessor p.1.1 p.1.2, [p.2])
def state {m : Nat} (p : Point m) : List Bool × List Bool := (anchor p,[p.2])
def rebuild {m : Nat} (x : Word m) (b : Bool) (y : Word m) : Point m :=
  if b then ((y,x),true) else ((x,y),false)
def label {m : Nat} (p : Point m) : Bool × Word m := (p.2,unused p)

def binaryLabel {m : Nat} (p : Point m) : Word (m+1) := List.Vector.cons p.2 (unused p)
def binaryRecover {m : Nat} (x : Word m) (w : Word (m+1)) : Point m := rebuild x w.head w.tail

def currentFiber (m : Nat) (x : Word m) : Set (Set (List Bool) × List Bool) :=
  {z | z ∈ image (relation m) (2 * m + 1, 1) ∧ {f | z.2 ++ f ∈ z.1} = {x.val}}
def fixedBitFiber (m : Nat) (x : Word m) (b : Bool) : Set (Set (List Bool) × List Bool) :=
  {z | z ∈ currentFiber m x ∧ z.2 = [b]}

private theorem word_card (m : Nat) : Nat.card (Word m) = 2 ^ m := by
  rw [Nat.card_eq_fintype_card, card_vector, Fintype.card_bool]

private theorem anchor_length {m : Nat} (p : Point m) : (anchor p).length = 2 * m := by
  simp [anchor, p.1.1.property, p.1.2.property]; omega
private theorem selector_prefix_length {m : Nat} (p : Point m) : (selectorPrefix p).length = 2 * m + 1 := by
  simp [selectorPrefix,anchor_length]
private theorem code_length {m : Nat} (p : Point m) : (code p).length = 3 * m + 1 := by
  simp [code,anchor_length,(selected p).property]; omega
private theorem code_split {m : Nat} (p : Point m) : code p = selectorPrefix p ++ (selected p).val := by
  simp [code,selectorPrefix,List.append_assoc]
private theorem anchor_inj {m : Nat} {p q : Point m} (h : anchor p = anchor q) : p.1 = q.1 := by
  have he := List.append_inj h (p.1.1.property.trans q.1.1.property.symm)
  exact Prod.ext (Subtype.ext he.1) (Subtype.ext he.2)
private theorem selector_prefix_injective (m : Nat) : Function.Injective (@selectorPrefix m) := by
  intro p q h
  have he := List.append_inj h ((anchor_length p).trans (anchor_length q).symm)
  exact Prod.ext (anchor_inj he.1) (by simpa using he.2)
private theorem code_injective (m : Nat) : Function.Injective (@code m) := by
  intro p q h
  have he := List.append_inj h ((anchor_length p).trans (anchor_length q).symm)
  exact Prod.ext (anchor_inj he.1) (List.cons.inj he.2).1
private theorem fixed_length (m : Nat) : ∀ f ∈ relation m, f.length = 3 * m + 1 := by
  rintro f ⟨p,rfl⟩; exact code_length p
private theorem nonempty_relation (m : Nat) : (relation m).Nonempty :=
  ⟨code (default : Point m),⟨default,rfl⟩⟩
private theorem state_actual {m : Nat} (p : Point m) : actual (relation m) (state p) := by
  exact ⟨(selected p).val,⟨p,code_split p⟩⟩
private theorem state_type {m : Nat} (p : Point m) : publicType (state p) = (2 * m + 1, 1) := by
  simp [publicType,state,anchor_length]

private theorem residual_anchor {m : Nat} (i j : Word m) :
    residual (relation m) (i.val ++ j.val) = predecessor i j := by
  ext f
  constructor
  · rintro ⟨p,hp⟩
    have h := List.append_inj hp (by simp [anchor,i.property,j.property, Nat.two_mul])
    have ha : ((i,j) : Word m × Word m) = p.1 :=
      anchor_inj (p := ((i,j),false)) (q := p) h.1.symm
    rcases p with ⟨⟨a,b⟩,c⟩
    simp only [Prod.mk.injEq] at ha
    rcases ha with ⟨rfl,rfl⟩
    cases c <;> simp_all [code,selected,predecessor]
  · intro hf
    simp only [predecessor,Set.mem_insert_iff,Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact ⟨((i,j),false),rfl⟩
    · exact ⟨((i,j),true),rfl⟩

private theorem derivative_predecessor {m : Nat} (i j : Word m) (b : Bool) :
    {f | [b] ++ f ∈ predecessor i j} = {(selected ((i,j),b)).val} := by
  cases b <;> ext f <;> simp [predecessor,selected]
private theorem predecessor_injective (m : Nat) :
    Function.Injective (fun ij : Word m × Word m => predecessor ij.1 ij.2) := by
  intro ij kl h
  have h0 := congrArg (fun S : Set (List Bool) => {f | [false] ++ f ∈ S}) h
  have h1 := congrArg (fun S : Set (List Bool) => {f | [true] ++ f ∈ S}) h
  rw [derivative_predecessor,derivative_predecessor] at h0 h1
  apply Prod.ext <;> apply Subtype.ext
  · simpa [selected] using h0
  · simpa [selected] using h1
private theorem fine_injective (m : Nat) : Function.Injective (@fine m) := by
  intro p q h
  exact Prod.ext (predecessor_injective m (congrArg Prod.fst h))
    (by simpa [fine] using congrArg Prod.snd h)
private theorem residual_selector_prefix {m : Nat} (p : Point m) :
    residual (relation m) (selectorPrefix p) = {(selected p).val} := by
  ext f
  constructor
  · rintro ⟨q,hq⟩
    rw [code_split] at hq
    have h := List.append_inj hq ((selector_prefix_length q).trans (selector_prefix_length p).symm)
    have he := selector_prefix_injective m h.1
    subst q
    exact h.2.symm
  · intro hf
    have : f = (selected p).val := hf
    subst f
    exact ⟨p,code_split p⟩

private theorem selector_prefix_complete {m : Nat} {u : List Bool}
    (hu : u.length = 2 * m + 1) (ha : ∃ f, u ++ f ∈ relation m) :
    ∃ p : Point m, u = selectorPrefix p := by
  rcases ha with ⟨f,p,hp⟩
  rw [code_split] at hp
  exact ⟨p,(List.append_inj hp ((selector_prefix_length p).trans hu.symm)).1.symm⟩
private theorem anchor_complete {m : Nat} {u : List Bool}
    (hu : u.length = 2 * m) (ha : ∃ f, u ++ f ∈ relation m) :
    ∃ i j : Word m, u = i.val ++ j.val := by
  rcases ha with ⟨f,p,hp⟩
  exact ⟨p.1.1,p.1.2,(List.append_inj hp ((anchor_length p).trans hu.symm)).1.symm⟩
private theorem typed_one_complete {m : Nat} (s : typedState (relation m) (2 * m + 1, 1)) :
    ∃ p : Point m, s.val = state p := by
  have ht := congrArg Prod.snd s.property.1
  have hk := congrArg Prod.fst s.property.1
  simp only [publicType] at ht hk
  obtain ⟨p,hp⟩ := selector_prefix_complete (by simpa [List.length_append] using hk) s.property.2
  have hv : s.val.1.length = (anchor p).length := by rw [anchor_length]; omega
  have he := List.append_inj hp hv
  exact ⟨p,Prod.ext he.1 he.2⟩
private theorem boundary_state {m : Nat} (p : Point m) : boundary (relation m) (state p) = fine p := by
  simp [boundary,state,fine,anchor,residual_anchor]
private theorem image_one (m : Nat) : image (relation m) (2 * m + 1, 1) = Set.range (@fine m) := by
  ext z
  constructor
  · rintro ⟨s,rfl⟩
    obtain ⟨p,hp⟩ := typed_one_complete s
    exact ⟨p,by change fine p = boundary (relation m) s.val; rw [hp,boundary_state]⟩
  · rintro ⟨p,rfl⟩
    exact ⟨⟨state p,state_type p,state_actual p⟩,boundary_state p⟩
private theorem image_zero (m : Nat) : image (relation m) (2 * m + 1, 0) =
    Set.range (fun x : Word m => ({x.val},([] : List Bool))) := by
  ext z
  constructor
  · rintro ⟨s,rfl⟩
    have ht : s.val.2 = [] := List.length_eq_zero_iff.mp (congrArg Prod.snd s.property.1)
    have hk := congrArg Prod.fst s.property.1
    have hv : s.val.1.length = 2 * m + 1 := by simpa [publicType,ht] using hk
    obtain ⟨p,hp⟩ := selector_prefix_complete hv (by simpa [actual,ht] using s.property.2)
    exact ⟨selected p,by simp [boundary,ht,hp,residual_selector_prefix]⟩
  · rintro ⟨x,rfl⟩
    let p : Point m := ((x,x),false)
    have hx : selected p = x := rfl
    refine ⟨⟨(selectorPrefix p,[]),?_,?_⟩,?_⟩
    · simp [publicType,selector_prefix_length]
    · exact ⟨x.val,⟨p,by simpa [hx] using code_split p⟩⟩
    · simp [boundary,residual_selector_prefix,hx]

private theorem relation_original (m : Nat) (w : List Bool) :
    w ∈ relation m ↔ ∃ i j : Word m,
      w = (i.val ++ j.val) ++ false :: i.val ∨ w = (i.val ++ j.val) ++ true :: j.val := by
  constructor
  · rintro ⟨⟨⟨i,j⟩,b⟩,rfl⟩
    refine ⟨i,j,?_⟩
    cases b <;> simp [code,anchor,selected]
  · rintro ⟨i,j,h | h⟩
    · exact ⟨((i,j),false),h.symm⟩
    · exact ⟨((i,j),true),h.symm⟩
private theorem residuals_previous (m : Nat) : residualSet (relation m) (2*m) =
    Set.range (fun ij : Word m × Word m => predecessor ij.1 ij.2) := by
  ext S; constructor
  · rintro ⟨v,hv,ha,rfl⟩
    obtain ⟨i,j,rfl⟩ := anchor_complete hv ha
    exact ⟨(i,j),(residual_anchor i j).symm⟩
  · rintro ⟨⟨i,j⟩,rfl⟩
    exact ⟨i.val ++ j.val,by simp; omega,⟨false :: i.val,⟨((i,j),false),rfl⟩⟩,
      residual_anchor i j⟩
private theorem residuals_current (m : Nat) : residualSet (relation m) (2*m+1) =
    Set.range (fun x : Word m => ({x.val} : Set (List Bool))) := by
  ext S; constructor
  · rintro ⟨v,hv,ha,rfl⟩
    obtain ⟨p,rfl⟩ := selector_prefix_complete hv ha
    exact ⟨selected p,(residual_selector_prefix p).symm⟩
  · rintro ⟨x,rfl⟩
    let p : Point m := ((x,x),false)
    exact ⟨selectorPrefix p,selector_prefix_length p,
      ⟨x.val,⟨p,code_split p⟩⟩,residual_selector_prefix p⟩

/-- The two relevant cuts exhaust actual selectorPrefixes and their residuals in the same binary relation. -/
theorem selector_residual_classification (m : Nat) :
    (∀ w : List Bool, w ∈ relation m ↔ ∃ i j : Word m,
      w = (i.val ++ j.val) ++ false :: i.val ∨ w = (i.val ++ j.val) ++ true :: j.val) ∧
    (relation m).Nonempty ∧ (∀ f ∈ relation m, f.length = 3 * m + 1) ∧
    Nat.card (relation m) = 2 * (2 ^ m)^2 ∧
    (∀ u : List Bool, u.length = 2 * m →
      ((∃ f, u ++ f ∈ relation m) ↔ ∃ i j : Word m, u = i.val ++ j.val)) ∧
    (∀ u : List Bool, u.length = 2 * m + 1 →
      ((∃ f, u ++ f ∈ relation m) ↔ ∃ p : Point m, u = selectorPrefix p)) ∧
    (∀ i j : Word m, residual (relation m) (i.val ++ j.val) = predecessor i j ∧
      (∀ b : Bool, {f | [b] ++ f ∈ predecessor i j} = {(selected ((i,j),b)).val})) ∧
    Function.Injective (fun ij : Word m × Word m => predecessor ij.1 ij.2) ∧
    (∀ p : Point m, actual (relation m) (state p) ∧
      residual (relation m) (selectorPrefix p) = {(selected p).val} ∧
      boundary (relation m) (state p) = fine p) ∧
    residualSet (relation m) (2*m) = Set.range (fun ij : Word m × Word m => predecessor ij.1 ij.2) ∧
    Nat.card (residualSet (relation m) (2*m)) = (2^m)^2 ∧
    residualSet (relation m) (2*m+1) = Set.range (fun x : Word m => ({x.val} : Set (List Bool))) ∧
    image (relation m) (2 * m + 1, 0) = Set.range (fun x : Word m => ({x.val},([] : List Bool))) ∧
    image (relation m) (2 * m + 1, 1) = Set.range (@fine m) := by
  classical
  refine ⟨relation_original m,nonempty_relation m,fixed_length m,?_,?_,?_,?_,
    predecessor_injective m,?_,residuals_previous m,?_,residuals_current m,image_zero m,image_one m⟩
  · rw [relation,Nat.card_range_of_injective (code_injective m),Nat.card_prod,Nat.card_prod,
      word_card,Nat.card_eq_fintype_card,Fintype.card_bool]
    ring
  · intro u hu; constructor
    · exact anchor_complete hu
    · rintro ⟨i,j,rfl⟩
      exact ⟨false :: i.val,⟨((i,j),false),rfl⟩⟩
  · intro u hu; constructor
    · exact selector_prefix_complete hu
    · rintro ⟨p,rfl⟩; exact ⟨(selected p).val,⟨p,code_split p⟩⟩
  · intro i j; exact ⟨residual_anchor i j,derivative_predecessor i j⟩
  · intro p; exact ⟨state_actual p,residual_selector_prefix p,boundary_state p⟩
  · rw [residuals_previous,Nat.card_range_of_injective (predecessor_injective m),
      Nat.card_prod,word_card]
    ring


private theorem rebuild_selected {m : Nat} (x : Word m) (b : Bool) (y : Word m) :
    selected (rebuild x b y) = x := by cases b <;> rfl
private theorem rebuild_label {m : Nat} (x : Word m) (b : Bool) (y : Word m) :
    label (rebuild x b y) = (b,y) := by cases b <;> rfl
private theorem rebuild_self {m : Nat} (p : Point m) :
    rebuild (selected p) p.2 (unused p) = p := by
  rcases p with ⟨⟨i,j⟩,b⟩; cases b <;> rfl
private theorem derivative_fine {m : Nat} (p : Point m) :
    {f | (fine p).2 ++ f ∈ (fine p).1} = {(selected p).val} :=
  derivative_predecessor _ _ _
private theorem singleton_injective (m : Nat) :
    Function.Injective (fun x : Word m => ({x.val} : Set (List Bool))) := by
  intro x y h; apply Subtype.ext; simpa using h
private theorem current_fiber_image {m : Nat} (x : Word m) :
    currentFiber m x = Set.range (fun byPair : Bool × Word m => fine (rebuild x byPair.1 byPair.2)) := by
  ext z
  constructor
  · rintro ⟨hz,hx⟩
    rw [image_one] at hz
    rcases hz with ⟨p,rfl⟩
    rw [derivative_fine] at hx
    have he := singleton_injective m hx
    refine ⟨label p,?_⟩
    change fine (rebuild x p.2 (unused p)) = fine p
    rw [← he,rebuild_self]
  · rintro ⟨⟨b,y⟩,rfl⟩
    exact ⟨by rw [image_one]; exact ⟨rebuild x b y,rfl⟩,
      by rw [derivative_fine,rebuild_selected]⟩
private theorem fixed_fiber_image {m : Nat} (x : Word m) (b : Bool) :
    fixedBitFiber m x b = Set.range (fun y : Word m => fine (rebuild x b y)) := by
  ext z
  constructor
  · rintro ⟨hz,hb⟩
    rw [current_fiber_image] at hz
    rcases hz with ⟨⟨c,y⟩,rfl⟩
    have h : c = b := by
      have he : (rebuild x c y).2 = c := congrArg Prod.fst (rebuild_label x c y)
      simpa only [fine,he,List.singleton_inj] using hb
    subst c
    exact ⟨y,rfl⟩
  · rintro ⟨y,rfl⟩
    refine ⟨?_,?_⟩
    · rw [current_fiber_image]; exact ⟨(b,y),rfl⟩
    · have h := congrArg Prod.fst (rebuild_label x b y)
      simpa [fine,label] using congrArg (fun c => [c]) h
private theorem fiber_map_injective {m : Nat} (x : Word m) :
    Function.Injective (fun byPair : Bool × Word m => fine (rebuild x byPair.1 byPair.2)) := by
  intro a b h
  have he := fine_injective m h
  simpa only [rebuild_label] using congrArg label he
private theorem current_fiber_card {m : Nat} (x : Word m) :
    Nat.card (currentFiber m x) = 2 * 2 ^ m := by
  rw [current_fiber_image,Nat.card_range_of_injective (fiber_map_injective x),Nat.card_prod,
    word_card,Nat.card_eq_fintype_card,Fintype.card_bool]
private theorem fixed_fiber_card {m : Nat} (x : Word m) (b : Bool) :
    Nat.card (fixedBitFiber m x b) = 2 ^ m := by
  rw [fixed_fiber_image,Nat.card_range_of_injective,word_card]
  intro y z h
  have he := @fiber_map_injective m x (b,y) (b,z) h
  exact congrArg Prod.snd he
private theorem width_zero (m : Nat) : Nat.card (image (relation m) (2*m+1,0)) = 2^m := by
  rw [image_zero,Nat.card_range_of_injective,word_card]
  intro x y h
  exact singleton_injective m (congrArg Prod.fst h)
private theorem width_one (m : Nat) : Nat.card (image (relation m) (2*m+1,1)) = 2*(2^m)^2 := by
  rw [image_one,Nat.card_range_of_injective (fine_injective m),Nat.card_prod,Nat.card_prod,
    word_card,Nat.card_eq_fintype_card,Fintype.card_bool]
  ring

/-- Counts are taken on the original actual boundary image, including every current and fixed-bit fiber. -/
theorem selector_widths_and_fibers (m : Nat) (hm : 1 ≤ m) :
    Nat.card (image (relation m) (2*m+1,0)) = 2^m ∧
    Nat.card (image (relation m) (2*m+1,1)) = 2*(2^m)^2 ∧
    (Nat.card (image (relation m) (2*m+1,1)) : ℚ) /
      Nat.card (image (relation m) (2*m+1,0)) = 2 * (2^m : Nat) ∧
    (∀ x : Word m, currentFiber m x =
      Set.range (fun byPair : Bool × Word m => fine (rebuild x byPair.1 byPair.2)) ∧
      Nat.card (currentFiber m x) = 2*2^m ∧
      (∀ b : Bool, fixedBitFiber m x b = Set.range (fun y : Word m => fine (rebuild x b y)) ∧
        Nat.card (fixedBitFiber m x b) = 2^m)) ∧
    (∀ s s', actual (relation m) s → actual (relation m) s' → publicType s = publicType s' →
      (legal (3*m+1) (relation m) s = legal (3*m+1) (relation m) s' ↔
        boundary (relation m) s = boundary (relation m) s')) ∧
    (∀ (X : Type) (a : List Bool × List Bool → X), Exact (3*m+1) (relation m) a →
      ∃! factor : Set.range (fun s : typedState (relation m) (2*m+1,1) => a s.val) →
        image (relation m) (2*m+1,1),
        (Set.rangeFactorization (fun s : typedState (relation m) (2*m+1,1) => boundary (relation m) s.val) =
          factor ∘ Set.rangeFactorization (fun s : typedState (relation m) (2*m+1,1) => a s.val)) ∧
        Function.Surjective factor ∧
        2*(2^m)^2 ≤ Nat.card (Set.range (fun s : typedState (relation m) (2*m+1,1) => a s.val))) ∧
    (∀ s a, actual (relation m) s →
      Option.map (fun r => (publicType r,boundary (relation m) r)) (step (3*m+1) (relation m) s a) =
        boundaryStep (3*m+1) (publicType s) (boundary (relation m) s) a) ∧
    (∀ (X : Type) (a : List Bool × List Bool → X), Exact (3*m+1) (relation m) a →
      2^m ≤ Nat.card (Set.range (fun s : typedState (relation m) (2*m+1,0) => a s.val))) := by
  have supplier := strict_anchored_specialization (3*m+1) (relation m) (fixed_length m)
    (nonempty_relation m) (2*m+1) 1 (by omega) (by omega)
  refine ⟨width_zero m,width_one m,?_,?_,supplier.2.1,?_,supplier.1,?_⟩
  · rw [width_zero,width_one]
    have hpos : (2^m : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  · intro x
    exact ⟨current_fiber_image x,current_fiber_card x,
      fun b => ⟨fixed_fiber_image x b,fixed_fiber_card x b⟩⟩
  · intro X a ha
    simpa only [width_one] using supplier.2.2.2.2 X a ha
  · intro X a ha
    have supplier0 := strict_anchored_specialization (3*m+1) (relation m) (fixed_length m)
      (nonempty_relation m) (2*m+1) 0 (by omega) (by omega)
    obtain ⟨g,hg,_⟩ := supplier0.2.2.2.2 X a ha
    simpa only [width_zero] using hg.2.2

private def selectFiberEquiv {m : Nat} (x : Word m) :
    {p : Point m // selected p = x} ≃ Bool × Word m where
  toFun p := label p.val
  invFun byPair := ⟨rebuild x byPair.1 byPair.2,rebuild_selected _ _ _⟩
  left_inv := by intro p; apply Subtype.ext; change rebuild x p.val.2 (unused p.val) = p.val
                 simpa only [p.property] using rebuild_self p.val
  right_inv := by intro byPair; exact rebuild_label _ _ _
private def fixedFiberEquiv {m : Nat} (x : Word m) (b : Bool) :
    {p : Point m // (selected p,p.2) = (x,b)} ≃ Word m where
  toFun p := unused p.val
  invFun y := ⟨rebuild x b y,Prod.ext (rebuild_selected _ _ _) (congrArg Prod.fst (rebuild_label _ _ _))⟩
  left_inv := by
    intro p; apply Subtype.ext
    have hx : selected p.val = x := congrArg Prod.fst p.property
    have hb : p.val.2 = b := congrArg Prod.snd p.property
    change rebuild x b (unused p.val) = p.val
    simpa only [hx,hb] using rebuild_self p.val
  right_inv := by
    intro y; exact congrArg Prod.snd (rebuild_label _ _ _)
private theorem selected_fiber_card {m : Nat} (x : Word m) :
    Nat.card {p : Point m // selected p = x} = 2*2^m := by
  rw [Nat.card_congr (selectFiberEquiv x),Nat.card_prod,word_card,
    Nat.card_eq_fintype_card,Fintype.card_bool]
private theorem selected_bit_fiber_card {m : Nat} (xb : Word m × Bool) :
    Nat.card {p : Point m // (selected p,p.2) = xb} = 2^m := by
  rw [Nat.card_congr (fixedFiberEquiv xb.1 xb.2),word_card]

/-- Arbitrary finite supplements obey sharp fiber bounds; the unused component gives actual reconstruction. -/
theorem selector_optimal_supplements (m : Nat) :
    (∀ (Z : Type) [Finite Z] (L : Point m → Z),
      (∃ R : Word m × Z → Point m, ∀ p, R (selected p,L p) = p) → 2*2^m ≤ Nat.card Z) ∧
    (∀ (Z : Type) [Finite Z] (L : Point m → Z),
      (∃ R : (Word m × Bool) × Z → Point m, ∀ p, R ((selected p,p.2),L p) = p) → 2^m ≤ Nat.card Z) ∧
    (∀ p : Point m, rebuild (selected p) (label p).1 (label p).2 = p ∧
      rebuild (selected p) p.2 (unused p) = p ∧
      binaryRecover (selected p) (binaryLabel p) = p ∧
      fine (rebuild (selected p) (label p).1 (label p).2) = boundary (relation m) (state p)) ∧
    (∀ i j : Word m, label ((i,j),false) = (false,j) ∧ label ((i,j),true) = (true,i)) ∧
    Nat.card (Bool × Word m) = 2*2^m ∧ Nat.card (Word m) = 2^m ∧
    (∀ ℓ : Nat,
      (∃ L : Point m → Word ℓ, Function.Injective (fun p => (selected p,L p))) ↔ m+1 ≤ ℓ) ∧
    (∀ ℓ : Nat,
      (∃ L : Point m → Word ℓ, Function.Injective (fun p => ((selected p,p.2),L p))) ↔ m ≤ ℓ) ∧
    Nat.clog 2 (2*2^m) = m+1 ∧ Nat.clog 2 (2^m) = m := by
  classical
  have max1 : Finset.univ.sup (fun x : Word m => Nat.card {p : Point m // selected p = x}) = 2*2^m := by
    simp only [selected_fiber_card,Finset.sup_const,Finset.univ_nonempty,ite_true]
  have max0 : Finset.univ.sup (fun xb : Word m × Bool =>
      Nat.card {p : Point m // (selected p,p.2) = xb}) = 2^m := by
    simp only [selected_bit_fiber_card,Finset.sup_const,Finset.univ_nonempty,ite_true]
  have min1 := D5.S0.History.Coding.MinimumRollbackAlphabet.minimum_rollback_alphabet (@selected m)
  have min0 := D5.S0.History.Coding.MinimumRollbackAlphabet.minimum_rollback_alphabet
    (fun p : Point m => (selected p,p.2))
  dsimp only at min1 min0
  rw [max1] at min1
  rw [max0] at min0
  have bound1 : ∀ (Z : Type) [Finite Z] (L : Point m → Z),
      Function.Injective (fun p => (selected p,L p)) → 2*2^m ≤ Nat.card Z := min1.1
  have bound0 : ∀ (Z : Type) [Finite Z] (L : Point m → Z),
      Function.Injective (fun p => ((selected p,p.2),L p)) → 2^m ≤ Nat.card Z := min0.1
  refine ⟨?_,?_,?_,?_,?_,word_card m,?_,?_,?_,Nat.clog_pow 2 m (by decide)⟩
  · intro Z _ L hR
    exact bound1 Z L ((D5.S3.ConceptDynamics.Reversibility.ExactRollbackInjectivityCriterion.exact_rollback_iff_joint_record_injective
      (@selected m) L).mp hR)
  · intro Z _ L hR
    exact bound0 Z L ((D5.S3.ConceptDynamics.Reversibility.ExactRollbackInjectivityCriterion.exact_rollback_iff_joint_record_injective
      (fun p : Point m => (selected p,p.2)) L).mp hR)
  · intro p
    exact ⟨rebuild_self p,rebuild_self p,by
      simpa [binaryRecover,binaryLabel] using rebuild_self p,by change fine (rebuild (selected p) p.2 (unused p)) = boundary (relation m) (state p); rw [rebuild_self,boundary_state]⟩
  · intro i j; exact ⟨rfl,rfl⟩
  · rw [Nat.card_prod,word_card,Nat.card_eq_fintype_card,Fintype.card_bool]
  · intro ℓ; constructor
    · rintro ⟨L,hL⟩
      have hb := bound1 (Word ℓ) L hL
      rw [word_card,← Nat.pow_succ'] at hb
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
    · intro hℓ
      obtain ⟨L,hL⟩ := min1.2
      have hc : 2*2^m ≤ Nat.card (Word ℓ) := by
        rw [word_card,← Nat.pow_succ']
        exact Nat.pow_le_pow_right (by decide) hℓ
      let e : Fin (2*2^m) ↪ Word ℓ :=
        (Fin.castLEEmb hc).trans (Finite.equivFin (Word ℓ)).symm.toEmbedding
      refine ⟨fun p => e (L p),?_⟩
      intro p q hpq
      have hfirst := congrArg (fun z => z.1) hpq
      have hsecond := congrArg (fun z => z.2) hpq
      apply hL
      exact Prod.ext hfirst (e.injective hsecond)
  · intro ℓ; constructor
    · rintro ⟨L,hL⟩
      have hb := bound0 (Word ℓ) L hL
      rw [word_card] at hb
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
    · intro hℓ
      obtain ⟨L,hL⟩ := min0.2
      have hc : 2^m ≤ Nat.card (Word ℓ) := by
        rw [word_card]; exact Nat.pow_le_pow_right (by decide) hℓ
      let e : Fin (2^m) ↪ Word ℓ :=
        (Fin.castLEEmb hc).trans (Finite.equivFin (Word ℓ)).symm.toEmbedding
      refine ⟨fun p => e (L p),?_⟩
      intro p q hpq
      have hfirst := congrArg (fun z => z.1) hpq
      have hsecond := congrArg (fun z => z.2) hpq
      apply hL
      exact Prod.ext hfirst (e.injective hsecond)
  · rw [← Nat.pow_succ']; exact Nat.clog_pow 2 (m+1) (by decide)


/-- A branch experiment spends the one credit before supplying a new selector and full component. -/
def experiment {m : Nat} (p : Point m) (b : Bool) (x : Word m) : List (Action Bool) :=
  .delete p.2 :: (b :: x.val).map Action.append
noncomputable def separator {m : Nat} (p q : Point m) : List (Action Bool) :=
  if p.2 ≠ q.2 then [.delete p.2]
  else if p.1.1 ≠ q.1.1 then experiment p false p.1.1
  else experiment p true p.1.2

private theorem append_run (m : Nat) (f v : List Bool) (hv : ∃ g, v ++ g ∈ relation m) :
    runTransition (step (3*m+1) (relation m)) (v,[]) (f.map Action.append) =
      if (∃ g, (v ++ f) ++ g ∈ relation m) then some (v ++ f,[]) else none := by
  classical
  induction f generalizing v with
  | nil => simp [runTransition,hv]
  | cons a f ih =>
    have hguard : (∃ g, (v ++ (a :: f)) ++ g ∈ relation m) →
        v.length < 3*m+1 ∧ actual (relation m) (v,[a]) := by
      rintro ⟨g,hg⟩
      constructor
      · have h := fixed_length m _ hg
        simp only [List.length_append,List.length_cons] at h
        omega
      · exact ⟨f ++ g,by simpa [List.append_assoc] using hg⟩
    by_cases hg : v.length < 3*m+1 ∧ actual (relation m) (v,[a])
    · have hn : ∃ g, (v ++ [a]) ++ g ∈ relation m := by simpa [actual] using hg.2
      simpa [runTransition,step,hg,List.append_assoc] using ih (v ++ [a]) hn
    · have hn : ¬ ∃ g, (v ++ (a :: f)) ++ g ∈ relation m := fun h => hg (hguard h)
      simp only [List.map_cons,runTransition,step,Prod.fst,Prod.snd,List.length_nil,
        Nat.add_zero,List.nil_append,if_neg hg,if_neg hn]
private theorem full_extendable {m : Nat} (w : List Bool) (hw : w.length = 3*m+1) :
    (∃ f, w ++ f ∈ relation m) ↔ w ∈ relation m := by
  constructor
  · rintro ⟨f,hf⟩
    have h := fixed_length m _ hf
    have hz : f = [] := List.length_eq_zero_iff.mp (by simp only [List.length_append,hw] at h; omega)
    simpa [hz] using hf
  · intro h; exact ⟨[],by simpa using h⟩
private theorem experiment_run {m : Nat} (p : Point m) (b : Bool) (x : Word m) :
    runTransition (step (3*m+1) (relation m)) (state p) (experiment p b x) =
      if x = selected (p.1,b) then some (anchor p ++ b :: x.val,[]) else none := by
  classical
  have hv : ∃ g, anchor p ++ g ∈ relation m := ⟨p.2 :: (selected p).val,⟨p,rfl⟩⟩
  simp only [experiment,runTransition,state,step,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.reverse_reverse,if_pos rfl,if_true]
  rw [append_run m (b :: x.val) (anchor p) hv,
    full_extendable _ (by simp [anchor_length,x.property]; omega)]
  have he : anchor p ++ b :: x.val ∈ relation m ↔ x = selected (p.1,b) := by
    change (b :: x.val) ∈ residual (relation m) (anchor p) ↔ _
    rw [show anchor p = p.1.1.val ++ p.1.2.val from rfl,residual_anchor]
    cases b <;> simp [predecessor,selected] <;>
      exact ⟨Subtype.ext,fun h => congrArg Subtype.val h⟩
  simp only [he]
private theorem experiment_legal {m : Nat} (p : Point m) (b : Bool) (x : Word m) :
    experiment p b x ∈ legal (3*m+1) (relation m) (state p) ↔ x = selected (p.1,b) := by
  change (runTransition _ _ _).isSome = true ↔ _
  rw [experiment_run]
  by_cases h : x = selected (p.1,b) <;> simp [h]
private theorem separator_spec {m : Nat} (p q : Point m) (hne : fine p ≠ fine q) :
    (separator p q).length ≤ m+2 ∧
    separator p q ∈ legal (3*m+1) (relation m) (state p) ∧
    separator p q ∉ legal (3*m+1) (relation m) (state q) := by
  classical
  by_cases hb : p.2 = q.2
  · by_cases hi : p.1.1 = q.1.1
    · have hj : p.1.2 ≠ q.1.2 := by
        intro hj
        apply hne
        have hpq : p = q := Prod.ext (Prod.ext hi hj) hb
        rw [hpq]
      have hex : experiment p true p.1.2 = experiment q true p.1.2 := by simp [experiment,hb]
      simp only [separator,ne_eq,hb,not_true_eq_false,if_false,hi]
      refine ⟨?_,(experiment_legal _ _ _).mpr rfl,?_⟩
      · simp [experiment,p.1.2.property]
      · rw [hex,experiment_legal]; exact hj
    · have hex : experiment p false p.1.1 = experiment q false p.1.1 := by simp [experiment,hb]
      simp only [separator,ne_eq,hb,not_true_eq_false,if_false,hi,not_false_eq_true,if_true]
      refine ⟨?_,(experiment_legal _ _ _).mpr rfl,?_⟩
      · simp [experiment,p.1.1.property]
      · rw [hex,experiment_legal]; exact hi
  · simp only [separator,hb,ne_eq,not_false_eq_true,if_true]
    refine ⟨by simp,?_,?_⟩ <;>
      simp [legal,runTransition,state,step,hb]

/-- These are original strict supplied actions, with an explicit separator of at most m+2 requests. -/
theorem selector_legal_separators (m : Nat) :
    (∀ p : Point m, ∀ b : Bool, ∀ x : Word m,
      experiment p b x ∈ legal (3*m+1) (relation m) (state p) ↔ x = selected (p.1,b)) ∧
    (∀ p q : Point m, fine p ≠ fine q →
      (separator p q).length ≤ m+2 ∧
      separator p q ∈ legal (3*m+1) (relation m) (state p) ∧
      separator p q ∉ legal (3*m+1) (relation m) (state q)) ∧
    (∀ s t : typedState (relation m) (2*m+1,1), boundary (relation m) s.val ≠ boundary (relation m) t.val →
      ∃ w : List (Action Bool), w.length ≤ m+2 ∧
        w ∈ legal (3*m+1) (relation m) s.val ∧ w ∉ legal (3*m+1) (relation m) t.val) := by
  refine ⟨experiment_legal,separator_spec,?_⟩
  intro s t hne
  obtain ⟨p,hp⟩ := typed_one_complete s
  obtain ⟨q,hq⟩ := typed_one_complete t
  rw [hp,hq,boundary_state,boundary_state] at hne
  exact ⟨separator p q,by simpa [hp,hq] using separator_spec p q hne⟩


/-- An alphabet-only comparison at the same selector cut would impose a uniform factor two. -/
def AlphabetOnlyTwoBound : Prop := ∀ m : Nat, 1 ≤ m →
  Nat.card (image (relation m) (2*m+1,1)) ≤ 2 * Nat.card (image (relation m) (2*m+1,0))

/-- The selector family refutes the alphabet-only bound while each individual relation remains finite. -/
theorem result : ¬ AlphabetOnlyTwoBound := by
  intro h
  have hx := h 1 (by decide)
  rw [width_one,width_zero] at hx
  norm_num at hx

/-- The full branching count is attained and the same-cut amplification is unbounded across finite relations. -/
theorem selector_full_branching_sharpness :
    (∀ m : Nat, Nat.card (image (relation m) (2*m+1,1)) =
      2 * Nat.card (image (relation m) (2*m+1,0)) ^ 2 ∧ (relation m).Finite) ∧
    (∀ m : Nat, ∀ x : Word m, Function.Injective (fun j : Word m => predecessor x j) ∧
      ∀ j : Word m, {f | [false] ++ f ∈ predecessor x j} = {x.val}) ∧
    (∀ K : Nat, ∃ m : Nat, 1 ≤ m ∧
      K * Nat.card (image (relation m) (2*m+1,0)) < Nat.card (image (relation m) (2*m+1,1))) := by
  refine ⟨?_,?_,?_⟩
  · intro m
    exact ⟨by rw [width_zero,width_one],Set.finite_range (@code m)⟩
  · intro m x
    refine ⟨?_,fun j => derivative_predecessor x j false⟩
    intro i j h
    exact congrArg Prod.snd (@predecessor_injective m (x,i) (x,j) h)
  · intro K
    refine ⟨K+1,by omega,?_⟩
    rw [width_zero,width_one]
    have hk : K+1 < 2^(K+1) := Nat.lt_two_pow_self
    have hp : 0 < 2^(K+1) := by positivity
    have hlt : K < 2 * 2^(K+1) := by omega
    have hmul := Nat.mul_lt_mul_of_pos_right hlt hp
    nlinarith

#print axioms selector_residual_classification
#print axioms selector_widths_and_fibers
#print axioms selector_optimal_supplements
#print axioms selector_legal_separators
#print axioms selector_full_branching_sharpness
#print axioms result
end D5.S3.ObserverMemory.BinarySelectorRecutFibers

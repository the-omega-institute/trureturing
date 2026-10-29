/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Occurrence connectivity of the actual total native free-term MGU. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeGroundSolutionSpace
import Mathlib.Logic.Relation

/-! The free-shape prerequisite for positive native image covers. The unifier
is applied only to free Boolean constructor terms. Interpreted native powers,
rank offsets and the entire image-cover construction are separate obligations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveImageCover

open Lambda Strata.Util NativeTermUnification
open NativeGroundSolutionSpace

variable {X : Type}

/-- A residual occurrence retains its declared output name, ordered address
and residual sort. Validity is checked against that total output. -/
abbrev Occurrence (X : Type) := X × List Bool × X

def subtree {A : Type} : FreeMagma A → List Bool → Option (FreeMagma A)
  | t, [] => some t
  | .of _, _ :: _ => none
  | .mul l _, false :: q => subtree l q
  | .mul _ r, true :: q => subtree r q

def IsOccurrence (s : X → Term X) (o : Occurrence X) : Prop :=
  subtree (s o.1) o.2.1 = some (.of (.inr o.2.2))

/-- Each use of a declared name receives the same occurrence labels. -/
def decorateFrom (x : X) (p : List Bool) : Term X → Term (Occurrence X)
  | .of (.inl b) => .of (.inl b)
  | .of (.inr y) => .of (.inr (x, p, y))
  | .mul l r => .mul (decorateFrom x (p ++ [false]) l)
      (decorateFrom x (p ++ [true]) r)

def decorate (s : X → Term X) (x : X) : Term (Occurrence X) :=
  decorateFrom x [] (s x)

private def erase : Term (Occurrence X) → Term X
  | .of (.inl b) => .of (.inl b)
  | .of (.inr o) => .of (.inr o.2.2)
  | .mul l r => .mul (erase l) (erase r)

private def instantiate {A B : Type} (s : A → Term B) : Term A → Term B :=
  FreeMagma.lift (Sum.elim (fun b => .of (.inl b)) s)

/-- Expand all names before matching positive comparisons. -/
def comparisonTerm (s : X → Term X) (t : Term X) : Term (Occurrence X) :=
  instantiate (decorate s) t

/-- Match only corresponding residual leaves. Ordinary constructors and
explicit primitive leaves contribute no block edge. -/
def comparisonEdges : Term (Occurrence X) → Term (Occurrence X) →
    List (Occurrence X × Occurrence X)
  | .of (.inr a), .of (.inr b) => [(a,b)]
  | .mul l r, .mul u v => comparisonEdges l u ++ comparisonEdges r v
  | _, _ => []

def occurrenceEdges (C : Equations X) (s : X → Term X) :
    List (Occurrence X × Occurrence X) :=
  C.flatMap fun c => comparisonEdges (comparisonTerm s c.1) (comparisonTerm s c.2)

/-- Every declared output is included, even when its name is absent from C.
Repeated occurrences remain distinct vertices. -/
def occurrenceVertices (p : Presentation X) (s : X → Term X) : List (Occurrence X) :=
  p.enumeration.flatMap fun x => termVars (decorate s x)

def Connected (C : Equations X) (s : X → Term X) :
    Occurrence X → Occurrence X → Prop :=
  Relation.EqvGen (fun a b => (a,b) ∈ occurrenceEdges C s)

private theorem erase_decorateFrom (x : X) (p : List Bool) (t : Term X) :
    erase (decorateFrom x p t) = t := by
  induction t generalizing p with
  | of a => cases a <;> rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul (hl _) (hr _)

private theorem erase_comparison (s : X → Term X) (t : Term X) :
    erase (comparisonTerm s t) = substitute s t := by
  induction t with
  | of a => cases a with
    | inl b => rfl
    | inr x => exact erase_decorateFrom x [] (s x)
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

private theorem instantiate_evaluate {A B : Type} (s : A → Term B)
    (v : B → Source) (t : Term A) :
    evaluate v (instantiate s t) = evaluate (fun x => evaluate v (s x)) t := by
  induction t with
  | of a => cases a <;> rfl
  | mul l r hl hr => exact congrArg₂ FreeMagma.mul hl hr

private theorem decorate_subtree (x : X) (p q : List Bool) (t : Term X) (y : X)
    (h : subtree t q = some (.of (.inr y))) :
    subtree (decorateFrom x p t) q = some (.of (.inr (x,p ++ q,y))) := by
  induction q generalizing p t with
  | nil =>
      simp only [subtree, Option.some.injEq] at h
      subst t
      simp only [decorateFrom, subtree, List.append_nil]
  | cons b q ih =>
      cases t with
      | of a => cases h
      | mul l r =>
          cases b
          · simpa only [decorateFrom, subtree, List.append_assoc, List.cons_append,
              List.nil_append] using ih (p ++ [false]) l h
          · simpa only [decorateFrom, subtree, List.append_assoc, List.cons_append,
              List.nil_append] using ih (p ++ [true]) r h

private theorem evaluate_subtree {A : Type} (v : A → Source)
    (t : Term A) (q : List Bool) (y : A)
    (h : subtree t q = some (.of (.inr y))) :
    subtree (evaluate v t) q = some (v y) := by
  induction q generalizing t with
  | nil =>
      simp only [subtree, Option.some.injEq] at h
      subst t
      rfl
  | cons b q ih =>
      cases t with
      | of a => cases h
      | mul l r => cases b <;> exact ih _ h

private theorem comparison_edge_at (A B : Term (Occurrence X)) (q : List Bool)
    (a b : Occurrence X)
    (ha : subtree A q = some (.of (.inr a)))
    (hb : subtree B q = some (.of (.inr b))) :
    (a,b) ∈ comparisonEdges A B := by
  induction q generalizing A B with
  | nil =>
      simp only [subtree, Option.some.injEq] at ha hb
      subst A; subst B
      exact List.mem_singleton_self _
  | cons d q ih =>
      cases A with
      | of c => cases ha
      | mul l r =>
          cases B with
          | of c => cases hb
          | mul u v =>
              cases d
              · exact List.mem_append_left _ (ih l u ha hb)
              · exact List.mem_append_right _ (ih r v ha hb)

private theorem comparison_evaluate (A B : Term (Occurrence X))
    (v : Occurrence X → Source) (he : erase A = erase B)
    (hv : ∀ q a b, subtree A q = some (.of (.inr a)) →
      subtree B q = some (.of (.inr b)) → v a = v b) :
    evaluate v A = evaluate v B := by
  induction A generalizing B with
  | of a =>
      cases B with
      | of b =>
          cases a with
          | inl c =>
              cases b with
              | inl d =>
                  have cd : c = d := by injection he with h; exact Sum.inl.inj h
                  subst d; rfl
              | inr o => cases he
          | inr o =>
              cases b with
              | inl d => cases he
              | inr u => exact hv [] o u rfl rfl
      | mul l r => cases he
  | mul l r hl hr =>
      cases B with
      | of b => cases he
      | mul u w =>
          have parts : erase l = erase u ∧ erase r = erase w := by
            injection he with h1 h2; exact ⟨h1,h2⟩
          exact congrArg₂ FreeMagma.mul
            (hl u parts.1 (fun q a b ha hb => hv (false :: q) a b ha hb))
            (hr w parts.2 (fun q a b ha hb => hv (true :: q) a b ha hb))

/-- In the actual total MGU of any finite free constructor problem, any two
occurrences of the same residual sort are connected by positive comparisons.
There is no assertion about an empty, unused residual sort. -/
theorem mgu_occurrence_connected (p : Presentation X) (C : Equations X)
    (S : SubstInfo) (hok : (encodeEquations p C).unify SubstInfo.empty = .ok S)
    (a b : Occurrence X) (ha : IsOccurrence (action p S) a)
    (hb : IsOccurrence (action p S) b) (hsort : a.2.2 = b.2.2) :
    Connected C (action p S) a b := by
  classical
  let s := action p S
  let color : Occurrence X → Source := fun o =>
    .of (decide (Connected C s a o))
  have edge_color (o u : Occurrence X) (edge : (o,u) ∈ occurrenceEdges C s) :
      color o = color u := by
    have eqv : Connected C s a o ↔ Connected C s a u := by
      constructor
      · intro h
        exact .trans _ _ _ h (.rel _ _ edge)
      · intro h
        exact .trans _ _ _ h (.symm _ _ (.rel _ _ edge))
    simp only [color, eqv]
  let v : X → Source := fun x => evaluate color (decorate s x)
  have sat : Sol C v := by
    intro c hc
    have native := Constraints.unify_sound (encodeEquations p C) SubstInfo.empty S hok
      (encode p c.1, encode p c.2) (List.mem_map.mpr ⟨c,hc,rfl⟩)
    have eqs : substitute s c.1 = substitute s c.2 := by
      apply encode_injective p
      simpa only [s, action_substitute_encode p C S hok] using native
    have erased : erase (comparisonTerm s c.1) = erase (comparisonTerm s c.2) := by
      rw [erase_comparison, erase_comparison, eqs]
    have same := comparison_evaluate (comparisonTerm s c.1) (comparisonTerm s c.2)
      color erased (by
        intro q o u ho hu
        apply edge_color
        exact List.mem_flatMap.mpr ⟨c,hc,comparison_edge_at _ _ q o u ho hu⟩)
    simpa only [comparisonTerm, instantiate_evaluate, v] using same
  have factor : ∀ x, evaluate v (s x) = v x := by
    intro x
    have eq := congrFun (Ext_restriction p C S hok v sat) x
    simpa only [Ext, sigma, evaluate_restrictTerm, s] using eq
  have at_color (o : Occurrence X) (ho : IsOccurrence s o) : color o = v o.2.2 := by
    have hd : subtree (decorate s o.1) o.2.1 = some (.of (.inr o)) := by
      simpa only [decorate, List.nil_append] using
        decorate_subtree o.1 [] o.2.1 (s o.1) o.2.2 ho
    have hc := evaluate_subtree color (decorate s o.1) o.2.1 o hd
    have ht := evaluate_subtree v (s o.1) o.2.1 o.2.2 ho
    rw [factor] at ht
    exact Option.some.inj (hc.symm.trans ht)
  have colors : color a = color b := by rw [at_color a ha, at_color b hb, hsort]
  have ca : color a = .of true := by
    simp only [color, show Connected C s a a from .refl _, decide_true]
  rw [ca] at colors
  have truth : decide (Connected C s a b) = true := by
    exact (FreeMagma.of.inj colors.symm)
  exact of_decide_eq_true truth

end D5.S3.Arith.FibonacciAtomic.Observer.NativePositiveImageCover

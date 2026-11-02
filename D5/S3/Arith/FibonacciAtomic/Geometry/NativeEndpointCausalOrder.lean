/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointCausalOrder
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact local and creating-split edges generate the native endpoint order. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals

/-! Exact source-local edges for the endpoint-labelled causal order. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointCausalOrder

open GenealogicalFiberTransport (Source)
open NativeGuardedLeafRepair (Call)
open Observer.OriginalVector.NativePostClockInverse (address)
open NativeEndpointEventIdeals

/-- The first local event, if present, is promotion for alpha birth and split
for beta birth. Membership excludes an inactive terminal position. -/
def First (b : Bool) (t : Source) (e : Call) : Prop :=
  e = (if b then .promote [] else .split []) ∧ e ∈ events b t

/-- AA17.2 edges: local promotion before split, parent creating split before
the first child-local event, and the same edges within either child. -/
def Edge : Bool → Source → Call → Call → Prop
  | _, .of _, _, _ => False
  | b, .mul l r, c, d =>
      (b = true ∧ c = .promote [] ∧ d = .split []) ∨
      (∃ e, First false l e ∧ c = .split [] ∧ d = e.shift [false]) ∨
      (∃ e, First true r e ∧ c = .split [] ∧ d = e.shift [true]) ∨
      (∃ e f, c = e.shift [false] ∧ d = f.shift [false] ∧ Edge false l e f) ∨
      (∃ e f, c = e.shift [true] ∧ d = f.shift [true] ∧ Edge true r e f)

private theorem first_le (b : Bool) (t : Source) (e : Call) (he : e ∈ events b t) :
    First b t (if b then .promote [] else .split []) ∧
      (if b then Call.promote [] else .split []) ≤ e := by
  cases t with
  | of a =>
      cases b <;> cases a <;> simp_all [events, First]
  | mul l r =>
      refine ⟨⟨rfl, ?_⟩, ?_⟩
      · cases b <;> simp
      · cases e with
        | promote p => cases p with
          | nil =>
              have hb : b = true := (by simpa using he : b = true)
              subst b
              exact le_rfl
          | cons a p =>
              change EventLe _ _
              cases b <;> simp [EventLe, address, phase]
        | split p => cases p with
          | nil =>
              change EventLe _ _
              cases b <;> simp [EventLe, address, phase]
          | cons a p =>
              change EventLe _ _
              cases b <;> simp [EventLe, address, phase]

private theorem edge_lt (b : Bool) (t : Source) (c d : Call) (h : Edge b t c d) : c < d := by
  induction t generalizing b c d with
  | of a => exact h.elim
  | mul l r il ir =>
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨e, _, rfl, rfl⟩ | ⟨e, _, rfl, rfl⟩ |
        ⟨e, f, rfl, rfl, h⟩ | ⟨e, f, rfl, rfl, h⟩
      · change EventLe _ _ ∧ ¬ EventLe _ _
        simp [EventLe, address, phase]
      · exact root_before false e
      · exact root_before true e
      · exact (shift_lt false e f).mpr (il false e f h)
      · exact (shift_lt true e f).mpr (ir true e f h)

private theorem lift_left (b : Bool) (l r : Source) {c d : Call}
    (h : Relation.TransGen (Edge false l) c d) :
    Relation.TransGen (Edge b (.mul l r)) (c.shift [false]) (d.shift [false]) := by
  exact Relation.TransGen.lift (Call.shift [false])
    (fun e f hef => Or.inr (Or.inr (Or.inr (Or.inl ⟨e, f, rfl, rfl, hef⟩)))) c d h

private theorem lift_right (b : Bool) (l r : Source) {c d : Call}
    (h : Relation.TransGen (Edge true r) c d) :
    Relation.TransGen (Edge b (.mul l r)) (c.shift [true]) (d.shift [true]) := by
  exact Relation.TransGen.lift (Call.shift [true])
    (fun e f hef => Or.inr (Or.inr (Or.inr (Or.inr ⟨e, f, rfl, rfl, hef⟩)))) c d h

private theorem complete (b : Bool) (t : Source) (c d : Call)
    (hc : c ∈ events b t) (hd : d ∈ events b t) (hcd : c < d) :
    Relation.TransGen (Edge b t) c d := by
  induction t generalizing b c d with
  | of a =>
      cases a <;> cases b <;> simp_all [events]
  | mul l r il ir =>
      have left_path : ∀ e ∈ events false l,
          Relation.TransGen (Edge b (.mul l r)) (.split []) (e.shift [false]) := by
        intro e he
        obtain ⟨hf, hle⟩ := first_le false l e he
        have hstart : Edge b (.mul l r) (.split []) ((Call.split []).shift [false]) :=
          Or.inr (Or.inl ⟨_, hf, rfl, rfl⟩)
        by_cases h : Call.split [] = e
        · simpa only [h] using Relation.TransGen.single hstart
        · exact (Relation.TransGen.single hstart).trans
            (lift_left b l r (il false _ e hf.2 he (lt_of_le_of_ne hle h)))
      have right_path : ∀ e ∈ events true r,
          Relation.TransGen (Edge b (.mul l r)) (.split []) (e.shift [true]) := by
        intro e he
        obtain ⟨hf, hle⟩ := first_le true r e he
        have hstart : Edge b (.mul l r) (.split []) ((Call.promote []).shift [true]) :=
          Or.inr (Or.inr (Or.inl ⟨_, hf, rfl, rfl⟩))
        by_cases h : Call.promote [] = e
        · simpa only [h] using Relation.TransGen.single hstart
        · exact (Relation.TransGen.single hstart).trans
            (lift_right b l r (ir true _ e hf.2 he (lt_of_le_of_ne hle h)))
      have shifted : ∀ (a : Bool) (e : Call), d = e.shift [a] →
          Relation.TransGen (Edge b (.mul l r)) c d := by
        intro a e hed
        subst d
        rcases (lt_shift a e c).mp hcd with h | h | ⟨f, rfl, hfe⟩
        · subst c
          have hb : b = true := by simpa using hc
          have hs : Edge b (.mul l r) (.promote []) (.split []) :=
            Or.inl ⟨hb, rfl, rfl⟩
          apply (Relation.TransGen.single hs).trans
          cases a
          · exact left_path e ((shift_mem b false l r e).mp hd)
          · exact right_path e ((shift_mem b true l r e).mp hd)
        · subst c
          cases a
          · exact left_path e ((shift_mem b false l r e).mp hd)
          · exact right_path e ((shift_mem b true l r e).mp hd)
        · cases a
          · exact lift_left b l r (il false f e ((shift_mem b false l r f).mp hc) ((shift_mem b false l r e).mp hd) hfe)
          · exact lift_right b l r (ir true f e ((shift_mem b true l r f).mp hc) ((shift_mem b true l r e).mp hd) hfe)
      cases d with
      | promote p => cases p with
        | nil => exact (lt_promote_root c hcd).elim
        | cons a p => exact shifted a (.promote p) rfl
      | split p => cases p with
        | nil =>
            have he : c = .promote [] := (lt_split_root c).mp hcd
            subst c
            exact .single (Or.inl ⟨by simpa using hc, rfl, rfl⟩)
        | cons a p => exact shifted a (.split p) rfl

/-- The finite endpoint's strict prefix/phase order is exactly the transitive
closure of AA17.2's local and immediate creating-split edges. -/
theorem result (b : Bool) (t : Source) (c d : Event b t) :
    Relation.TransGen (Edge b t) c.1 d.1 ↔ c < d := by
  constructor
  · intro h
    have all : ∀ {e f : Call}, Relation.TransGen (Edge b t) e f → e < f := by
      intro e f hp
      induction hp with
      | single he => exact edge_lt b t _ _ he
      | tail _ he ih => exact ih.trans (edge_lt b t _ _ he)
    exact all h
  · exact fun h => complete b t c.1 d.1 c.2 d.2 h

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointCausalOrder

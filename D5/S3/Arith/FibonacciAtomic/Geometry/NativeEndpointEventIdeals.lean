/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Membership cutTerm native endpoints and their actual guarded event transitions. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair
import D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
import Mathlib.Data.List.Infix

/-! Endpoint-labelled causal cuts on the original guarded native tree operations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout)
open ActualLeafHistoryRigidity (subtree)
open ActualImageAddressCertificate (replace)
open NativeMaterialRootRecognition (D)
open NativeGuardedLeafRepair (Call run)

def address : Call → Address
  | .promote p | .split p => p

def phase : Call → ℕ
  | .promote _ => 0
  | .split _ => 1

/-- Ancestor addresses precede descendants; at one address promotion precedes split. -/
def EventLe (c d : Call) : Prop :=
  address c <+: address d ∧ (address c = address d → phase c ≤ phase d)

instance eventPartialOrder : PartialOrder Call where
  le := EventLe
  le_refl c := ⟨List.prefix_rfl, fun _ => le_rfl⟩
  le_trans c d e hcd hde := by
    refine ⟨hcd.1.trans hde.1, ?_⟩
    intro hce
    have hdc : address d <+: address c := by rw [hce]; exact hde.1
    have h : address c = address d :=
      hcd.1.eq_of_length (Nat.le_antisymm hcd.1.length_le hdc.length_le)
    exact (hcd.2 h).trans (hde.2 (h.symm.trans hce))
  le_antisymm c d hcd hdc := by
    have h : address c = address d :=
      hcd.1.eq_of_length (Nat.le_antisymm hcd.1.length_le hdc.1.length_le)
    have hk : phase c = phase d := Nat.le_antisymm (hcd.2 h) (hdc.2 h.symm)
    cases c <;> cases d <;> simp_all [address, phase]

private theorem call_le_iff (c d : Call) : c ≤ d ↔ EventLe c d := Iff.rfl

private theorem shift_injective (p : Address) : Function.Injective (Call.shift p) := by
  intro c d h
  cases c <;> cases d <;> simp_all [Call.shift]

private theorem shift_order (b : Bool) (c d : Call) :
    c.shift [b] ≤ d.shift [b] ↔ c ≤ d := by
  cases c <;> cases d <;> simp [call_le_iff, EventLe, address, phase, Call.shift]

private theorem root_before (b : Bool) (c : Call) :
    Call.split [] < c.shift [b] := by
  cases c <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase, Call.shift]

private theorem shift_lt (b : Bool) (c d : Call) :
    c.shift [b] < d.shift [b] ↔ c < d := by
  simp only [lt_iff_le_not_ge, shift_order]

@[simp] private theorem lt_promote_root (c : Call) : ¬ c < .promote [] := by
  cases c with
  | promote p => cases p <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase]
  | split p => cases p <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase]

@[simp] private theorem lt_split_root (c : Call) : c < .split [] ↔ c = .promote [] := by
  cases c with
  | promote p => cases p <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase]
  | split p => cases p <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase]

private theorem lt_shift (b : Bool) (c d : Call) :
    d < c.shift [b] ↔ d = .promote [] ∨ d = .split [] ∨
      ∃ f, d = f.shift [b] ∧ f < c := by
  cases c <;> cases d with
  | promote p =>
      cases p with
      | nil => simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase, Call.shift]
      | cons a p =>
          cases a <;> cases b <;>
            simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase, Call.shift]
  | split p =>
      cases p with
      | nil => simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase, Call.shift]
      | cons a p =>
          cases a <;> cases b <;>
            simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase, Call.shift]

/-- Alpha is the root/right birth type; a left child is born beta. -/
def birthAt : Bool → Address → Bool
  | b, [] => b
  | _, c :: p => birthAt c p

/-- Pull membership back along the original address shift. -/
def sectionAt (I : Set Call) (p : Address) : Set Call :=
  {c | c.shift p ∈ I}

/-- Exactly the endpoint's split labels and nontrivial born-alpha promotions. -/
def events : Bool → Source → Finset Call
  | b, .of a => if b && !a then {.promote []} else ∅
  | b, .mul l r =>
      (if b then {.promote []} else ∅) ∪ {.split []} ∪
      (events false l).image (Call.shift [false]) ∪
      (events true r).image (Call.shift [true])

@[simp] private theorem shift_ne_promote (b : Bool) (c : Call) :
    c.shift [b] ≠ .promote [] := by cases c <;> simp [Call.shift]

@[simp] private theorem shift_ne_split (b : Bool) (c : Call) :
    c.shift [b] ≠ .split [] := by cases c <;> simp [Call.shift]

@[simp] private theorem shift_same (b : Bool) (c d : Call) :
    c.shift [b] = d.shift [b] ↔ c = d := (shift_injective [b]).eq_iff

@[simp] private theorem shift_different (b : Bool) (c d : Call) :
    c.shift [!b] ≠ d.shift [b] := by cases b <;> cases c <;> cases d <;> simp [Call.shift]

@[simp] private theorem promote_root_mem (b : Bool) (t : Source) :
    .promote [] ∈ events b t ↔ b = true ∧ t ≠ .of true := by
  cases t with
  | of a => cases a <;> cases b <;> simp [events]
  | mul l r => cases b <;> simp [events]

@[simp] private theorem split_root_mem (b : Bool) (t : Source) :
    .split [] ∈ events b t ↔ ∃ l r, t = .mul l r := by
  cases t with
  | of a => cases a <;> cases b <;> simp [events]
  | mul l r => cases b <;> simp [events]

@[simp] private theorem shift_mem (b c : Bool) (l r : Source) (e : Call) :
    e.shift [c] ∈ events b (.mul l r) ↔ e ∈ events c (if c then r else l) := by
  cases b <;> cases c <;>
    simp [events, Finset.mem_image, eq_comm]

/-- The original no-left-alpha domain, including the specified local birth type. -/
def Born (b : Bool) (t : Source) : Prop := D t ∧ (b = false → t ≠ .of true)

/-- A supported lower set in the endpoint's finite labelled ancestor order. -/
def Ideal (b : Bool) (t : Source) (I : Set Call) : Prop :=
  I ⊆ (events b t : Set Call) ∧
    ∀ c ∈ events b t, ∀ d ∈ I, c ≤ d → c ∈ I

private theorem ideal_section (b c : Bool) (l r : Source) (I : Set Call)
    (hI : Ideal b (.mul l r) I) :
    Ideal c (if c then r else l) (sectionAt I [c]) := by
  refine ⟨?_, ?_⟩
  · intro e he
    exact (shift_mem b c l r e).mp (hI.1 he)
  · intro e he d hd hle
    exact hI.2 (e.shift [c]) ((shift_mem b c l r e).mpr he)
      (d.shift [c]) hd ((shift_order c e d).mpr hle)

private theorem ideal_split_promotion (b : Bool) (l r : Source) (I : Set Call)
    (hI : Ideal b (.mul l r) I) (hs : .split [] ∈ I) (hb : b = true) :
    .promote [] ∈ I := by
  apply hI.2 (.promote []) (by simp [hb]) (.split []) hs
  exact ⟨List.prefix_rfl, by simp [phase]⟩

private theorem ideal_child_split (b c : Bool) (l r : Source) (I : Set Call)
    (hI : Ideal b (.mul l r) I) (e : Call) (he : e.shift [c] ∈ I) :
    .split [] ∈ I :=
  hI.2 (.split []) (by simp) (e.shift [c]) he (root_before c e).le

/-- Freshness and all strict predecessors in the exact labelled endpoint order. -/
def Enabled (b : Bool) (t : Source) (I : Set Call) (e : Call) : Prop :=
  e ∉ I ∧ ∀ d ∈ events b t, d < e → d ∈ I

private theorem enabled_promote_root (b : Bool) (t : Source) (I : Set Call) :
    Enabled b t I (.promote []) ↔ .promote [] ∉ I := by
  simp [Enabled]

private theorem enabled_split_root (b : Bool) (l r : Source) (I : Set Call) :
    Enabled b (.mul l r) I (.split []) ↔
      .split [] ∉ I ∧ (b = true → .promote [] ∈ I) := by
  simp [Enabled]

private theorem enabled_shift (b c : Bool) (l r : Source) (I : Set Call)
    (hI : Ideal b (.mul l r) I) (e : Call) :
    Enabled b (.mul l r) I (e.shift [c]) ↔
      .split [] ∈ I ∧ Enabled c (if c then r else l) (sectionAt I [c]) e := by
  constructor
  · rintro ⟨hf, hp⟩
    refine ⟨hp (.split []) (by simp) (root_before c e), hf, ?_⟩
    intro d hd hde
    exact hp (d.shift [c]) ((shift_mem b c l r d).mpr hd) ((shift_lt c d e).mpr hde)
  · rintro ⟨hs, hf, hp⟩
    refine ⟨hf, ?_⟩
    intro d hd hde
    rcases (lt_shift c e d).mp hde with h | h | ⟨f, rfl, hfe⟩
    · subst d
      exact ideal_split_promotion b l r I hI hs ((promote_root_mem b _).mp hd).1
    · simpa [h] using hs
    · exact hp f ((shift_mem b c l r f).mp hd) hfe

/-- A cutTerm endpoint uses membership only, with no execution or chosen order. -/
noncomputable def cutTerm : Bool → Source → Set Call → Source
  | b, .of a, I => if b && !a then
      if .promote [] ∈ I then .of false else .of true
    else .of a
  | b, .mul l r, I => if .split [] ∈ I then
      .mul (cutTerm false l (sectionAt I [false]))
        (cutTerm true r (sectionAt I [true]))
    else if b then if .promote [] ∈ I then .of false else .of true
    else .of false

/-- Every strict ancestor's creating split has occurred. -/
def Created : Set Call → Address → Prop
  | _, [] => True
  | I, b :: p => .split [] ∈ I ∧ Created (sectionAt I [b]) p

/-- The actual leaf guard, on the unchanged native subtree operation. -/
def Guard : Call → Source → Prop
  | .promote p, u => subtree p u = some (.of true)
  | .split p, u => subtree p u = some (.of false)

/-- The original replacement made by a successful single call. -/
def next : Call → Source → Source
  | .promote p, u => replace u p (.of false)
  | .split p, u => replace u p (.mul (.of false) (.of true))

private theorem shift_append (p q : Address) (c : Call) :
    (c.shift q).shift p = c.shift (p ++ q) := by
  cases c <;> simp [Call.shift, List.append_assoc]

private theorem section_cons (I : Set Call) (b : Bool) (p : Address) :
    sectionAt (sectionAt I [b]) p = sectionAt I (b :: p) := by
  ext c
  simp [sectionAt, shift_append]

private theorem partial_leaf (b a : Bool) (I : Set Call) :
    ∃ x : Bool, cutTerm b (.of a) I = .of x := by
  classical
  cases b <;> cases a <;> simp [cutTerm]
  split_ifs <;> exact ⟨_, rfl⟩

/-- The actual addressed subtree exists precisely after all creating splits.
The subtree itself is the membership-defined local cutTerm endpoint. -/
theorem subtree_partial (t : Source) (p : Address) (v : Source)
    (hp : subtree p t = some v) (b : Bool) (I : Set Call) :
    subtree p (cutTerm b t I) =
      if Created I p then some (cutTerm (birthAt b p) v (sectionAt I p)) else none := by
  classical
  induction p generalizing t b I with
  | nil =>
      have ht : t = v := by simpa [subtree] using hp
      subst v
      have hs : sectionAt I [] = I := by
        ext c
        cases c <;> simp [sectionAt, Call.shift]
      simp [subtree, birthAt, Created, hs]
  | cons c p ih =>
      cases t with
      | of a => simp [subtree] at hp
      | mul l r =>
          by_cases hs : Call.split [] ∈ I
          · cases c
            · simpa [cutTerm, hs, subtree, Created, birthAt, section_cons] using
                ih l (by simpa [subtree] using hp) false (sectionAt I [false])
            · simpa [cutTerm, hs, subtree, Created, birthAt, section_cons] using
                ih r (by simpa [subtree] using hp) true (sectionAt I [true])
          · simp only [cutTerm, hs, ↓reduceIte, Created, false_and, birthAt]
            cases b <;> simp [subtree]
            split_ifs <;> rfl

/-- Local beta/alpha leaf recognition in a cutTerm endpoint. This is a
structural fact about actual constructors, rather than a run assumption. -/
private theorem local_guard (b : Bool) (t : Source) (I : Set Call)
    (hn : t ≠ .of true) :
    (cutTerm b t I = .of true ↔
      b = true ∧ .promote [] ∉ I ∧ (∀ l r, t = .mul l r → .split [] ∉ I)) ∧
    (cutTerm b t I = .of false ↔
      (b = false ∨ .promote [] ∈ I) ∧ (∀ l r, t = .mul l r → .split [] ∉ I)) := by
  classical
  cases t with
  | of a => cases a <;> cases b <;> simp_all [cutTerm]
  | mul l r =>
      cases b <;> by_cases hs : Call.split [] ∈ I <;>
        by_cases hp : Call.promote [] ∈ I <;> simp [cutTerm, hs, hp]

/-- Actual guard/ancestor correspondence for every non-alpha target subtree.
All membership tests are on endpoint labels; no execution defines the cut. -/
theorem guard_ancestor (t : Source) (p : Address) (v : Source)
    (hp : subtree p t = some v) (hn : v ≠ .of true) (b : Bool) (I : Set Call) :
    (Guard (.promote p) (cutTerm b t I) ↔
      Created I p ∧ birthAt b p = true ∧ .promote p ∉ I ∧
        (∀ l r, v = .mul l r → .split p ∉ I)) ∧
    (Guard (.split p) (cutTerm b t I) ↔
      Created I p ∧ (birthAt b p = false ∨ .promote p ∈ I) ∧
        (∀ l r, v = .mul l r → .split p ∉ I)) := by
  classical
  have hs := subtree_partial t p v hp b I
  have hg := local_guard (birthAt b p) v (sectionAt I p) hn
  simp only [Guard, hs]
  by_cases hc : Created I p
  · simp only [hc, ↓reduceIte, Option.some.injEq, true_and]
    simpa [sectionAt, Call.shift] using hg
  · simp [hc]


private theorem born_children (b : Bool) (l r : Source) (h : Born b (.mul l r)) :
    Born false l ∧ Born true r := by
  obtain ⟨hl, hr, hn⟩ := (NativeGuardedLeafRepair.D_mul l r).mp h.1
  exact ⟨⟨hl, fun _ he => hn (by simp [he, readout])⟩, ⟨hr, by simp⟩⟩

private theorem partial_empty (b : Bool) (t : Source) (h : Born b t) :
    cutTerm b t ∅ = .of b := by
  classical
  cases t with
  | of a => cases b <;> cases a <;> simp_all [Born, cutTerm]
  | mul l r => cases b <;> simp [cutTerm]

private theorem partial_congr (b : Bool) (t : Source) (I J : Set Call)
    (h : ∀ e ∈ events b t, e ∈ I ↔ e ∈ J) : cutTerm b t I = cutTerm b t J := by
  classical
  induction t generalizing b I J with
  | of a =>
      cases a <;> cases b <;> simp only [cutTerm, Bool.false_and, Bool.true_and,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hp := h (.promote []) (by simp)
      simp only [hp]
  | mul l r il ir =>
      have hs := h (.split []) (by simp)
      simp only [cutTerm, hs]
      split_ifs with hsplit
      · congr 1
        · apply il
          intro e he
          exact h (e.shift [false]) ((shift_mem b false l r e).mpr he)
        · apply ir
          intro e he
          exact h (e.shift [true]) ((shift_mem b true l r e).mpr he)
      · by_cases hb : b = true
        · simp only [hb, ↓reduceIte]
          have hp := h (.promote []) (by simp [hb])
          simp only [hp]
        · simp [hb]

private theorem partial_dormant (b : Bool) (t : Source) (I : Set Call)
    (hb : Born b t) (hI : Ideal b t I) (hs : .split [] ∉ I)
    (hp : b = true → .promote [] ∉ I) : cutTerm b t I = .of b := by
  classical
  cases t with
  | of a => cases b <;> cases a <;> simp_all [Born, cutTerm]
  | mul l r => cases b <;> simp_all [cutTerm]

private theorem child_dormant (b c : Bool) (l r : Source) (I : Set Call)
    (hb : Born b (.mul l r)) (hI : Ideal b (.mul l r) I) (hs : .split [] ∉ I) :
    cutTerm c (if c then r else l) (sectionAt I [c]) = .of c := by
  have hc : sectionAt I [c] = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro e he
    exact hs (ideal_child_split b c l r I hI e he)
  rw [hc]
  apply partial_empty
  cases c
  · exact (born_children b l r hb).1
  · exact (born_children b l r hb).2

@[simp] private theorem section_insert_root (I : Set Call) (b : Bool) (e : Call)
    (he : address e = []) : sectionAt (insert e I) [b] = sectionAt I [b] := by
  ext c
  have hn : c.shift [b] ≠ e := by
    intro h
    cases c <;> cases e <;> simp_all [address, Call.shift]
  simp [sectionAt, hn]

@[simp] private theorem section_insert_same (I : Set Call) (b : Bool) (e : Call) :
    sectionAt (insert (e.shift [b]) I) [b] = insert e (sectionAt I [b]) := by
  ext c
  simp [sectionAt]

@[simp] private theorem section_insert_other (I : Set Call) (b : Bool) (e : Call) :
    sectionAt (insert (e.shift [!b]) I) [b] = sectionAt I [b] := by
  ext c
  have hn := shift_different (!b) c e
  simpa [sectionAt] using (or_iff_right hn :
    (c.shift [b] = e.shift [!b] ∨ c.shift [b] ∈ I) ↔ c.shift [b] ∈ I)

/-- Inserting a guarded endpoint label changes the membership-defined cutTerm
term by precisely the original native replacement. -/
theorem partial_insert (b : Bool) (t : Source) (I : Set Call)
    (hb : Born b t) (hI : Ideal b t I) (e : Call) (he : e ∈ events b t)
    (hg : Guard e (cutTerm b t I)) :
    next e (cutTerm b t I) = cutTerm b t (insert e I) := by
  classical
  induction t generalizing b I e with
  | of a =>
      cases a <;> cases b <;> simp_all [events]
      subst e
      simp [Guard, cutTerm, subtree] at hg
      simp [next, cutTerm, replace, hg]
  | mul l r il ir =>
      have hc := born_children b l r hb
      have rootP : ∀ p, e = .promote p → p = [] →
          next e (cutTerm b (.mul l r) I) = cutTerm b (.mul l r) (insert e I) := by
        intro p heq hp
        subst p
        subst e
        have hb' : b = true := (promote_root_mem b (.mul l r)).mp he |>.1
        subst b
        have hh := (guard_ancestor (.mul l r) [] (.mul l r) rfl (by simp) true I).1.mp hg
        have hs : Call.split [] ∉ I := hh.2.2.2 l r rfl
        simp [next, replace, cutTerm, hs]
      have rootS : e = .split [] →
          next e (cutTerm b (.mul l r) I) = cutTerm b (.mul l r) (insert e I) := by
        intro heq
        subst e
        have hh := (guard_ancestor (.mul l r) [] (.mul l r) rfl (by simp) b I).2.mp hg
        have hs : Call.split [] ∉ I := hh.2.2 l r rfl
        have hl := child_dormant b false l r I hb hI hs
        have hr := child_dormant b true l r I hb hI hs
        have hp : cutTerm b (.mul l r) I = .of false := by
          exact Option.some.inj hg
        simp only [next, hp, replace, cutTerm, Set.mem_insert_iff, true_or, ↓reduceIte]
        rw [section_insert_root I false (.split []) rfl,
          section_insert_root I true (.split []) rfl, hl, hr]
      have shifted : ∀ c d, e = d.shift [c] →
          next e (cutTerm b (.mul l r) I) = cutTerm b (.mul l r) (insert e I) := by
        intro c d hed
        subst e
        have hs : Call.split [] ∈ I := by
          by_contra hn
          have hg' := hg
          cases c <;> cases d <;> cases b <;>
            simp [Guard, Call.shift, cutTerm, hn, subtree] at hg'
          all_goals split_ifs at hg' <;> contradiction
        have hmem := (shift_mem b c l r d).mp he
        have hi := ideal_section b c l r I hI
        cases c
        · have hguard : Guard d (cutTerm false l (sectionAt I [false])) := by
            cases d <;> simpa [Guard, cutTerm, hs, Call.shift, subtree] using hg
          have hi' := il false (sectionAt I [false]) hc.1 hi d hmem hguard
          cases d <;>
            simpa [next, cutTerm, hs, Call.shift, replace,
              section_insert_same, section_insert_other, address] using
              congrArg (fun x => FreeMagma.mul x (cutTerm true r (sectionAt I [true]))) hi'
        · have hguard : Guard d (cutTerm true r (sectionAt I [true])) := by
            cases d <;> simpa [Guard, cutTerm, hs, Call.shift, subtree] using hg
          have hi' := ir true (sectionAt I [true]) hc.2 hi d hmem hguard
          cases d <;>
            simpa [next, cutTerm, hs, Call.shift, replace,
              section_insert_same, section_insert_other, address] using
              congrArg (fun x => FreeMagma.mul (cutTerm false l (sectionAt I [false])) x) hi'
      cases e with
      | promote p =>
          cases p with
          | nil => exact rootP [] rfl rfl
          | cons c p => exact shifted c (.promote p) rfl
      | split p =>
          cases p with
          | nil => exact rootS rfl
          | cons c p => exact shifted c (.split p) rfl

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals

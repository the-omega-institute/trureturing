/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Membership partial native endpoints and their actual guarded event transitions. -/

import D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativePostClockInverse
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
open Observer.OriginalVector.NativePostClockInverse (address kind replacement edited)
open scoped Classical

@[simp] private theorem leaf_eq (a b : Bool) : (FreeMagma.of a : Source) = .of b ↔ a = b := by
  constructor
  · intro h; injection h
  · rintro rfl; rfl

@[simp] private theorem node_leaf (l r : Source) (b : Bool) : l * r ≠ .of b := by
  intro h; cases h

@[simp] private theorem leaf_node (b : Bool) (l r : Source) : (.of b : Source) ≠ l * r := by
  intro h; cases h

@[simp] private theorem node_eq (l r v w : Source) : l * r = v * w ↔ l = v ∧ r = w := by
  constructor
  · intro h; injection h with h₁ h₂; exact ⟨h₁, h₂⟩
  · rintro ⟨rfl, rfl⟩; rfl

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

theorem root_before (b : Bool) (c : Call) :
    Call.split [] < c.shift [b] := by
  cases c <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase, Call.shift]

theorem shift_lt (b : Bool) (c d : Call) :
    c.shift [b] < d.shift [b] ↔ c < d := by
  simp only [lt_iff_le_not_ge, shift_order]

@[simp] theorem lt_promote_root (c : Call) : ¬ c < .promote [] := by
  cases c with
  | promote p => cases p <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase]
  | split p => cases p <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase]

@[simp] theorem lt_split_root (c : Call) : c < .split [] ↔ c = .promote [] := by
  cases c with
  | promote p => cases p <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase]
  | split p => cases p <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase]

theorem lt_shift (b : Bool) (c d : Call) :
    d < c.shift [b] ↔ d = .promote [] ∨ d = .split [] ∨
      ∃ f, d = f.shift [b] ∧ f < c := by
  have shifted : ∀ (a : Bool) (f : Call),
      f.shift [a] < c.shift [b] ↔
        f.shift [a] = .promote [] ∨ f.shift [a] = .split [] ∨
          ∃ g, f.shift [a] = g.shift [b] ∧ g < c := by
    intro a f
    by_cases hab : a = b
    · subst a
      constructor
      · intro h; exact Or.inr (Or.inr ⟨f, rfl, (shift_lt b f c).mp h⟩)
      · rintro (h | h | ⟨g, h, hg⟩)
        · cases f <;> simp [Call.shift] at h
        · cases f <;> simp [Call.shift] at h
        · have hf : f = g := shift_injective [b] h
          subst g
          exact (shift_lt b f c).mpr hg
    · have hn : ¬ f.shift [a] < c.shift [b] := by
        cases f <;> cases c <;>
          simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase, Call.shift, hab]
      have he : ∀ g : Call, f.shift [a] ≠ g.shift [b] := by
        intro g; cases f <;> cases g <;> simp [Call.shift, hab]
      have hp : f.shift [a] ≠ .promote [] := by cases f <;> simp [Call.shift]
      have hs : f.shift [a] ≠ .split [] := by cases f <;> simp [Call.shift]
      simp [hn, he, hp, hs]
  cases d with
  | promote p => cases p with
    | nil =>
        have h : Call.promote [] < c.shift [b] := by
          cases c <;> simp [lt_iff_le_not_ge, call_le_iff, EventLe, address, phase, Call.shift]
        simp [h]
    | cons a p => exact shifted a (.promote p)
  | split p => cases p with
    | nil => simp [root_before b c]
    | cons a p => exact shifted a (.split p)

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

@[simp] private theorem false_true_shift (c d : Call) :
    c.shift [false] ≠ d.shift [true] := by cases c <;> cases d <;> simp [Call.shift]

@[simp] private theorem true_false_shift (c d : Call) :
    c.shift [true] ≠ d.shift [false] := by cases c <;> cases d <;> simp [Call.shift]

@[simp] theorem shift_mem (b c : Bool) (l r : Source) (e : Call) :
    e.shift [c] ∈ events b (.mul l r) ↔ e ∈ events c (if c then r else l) := by
  cases b <;> cases c <;> simp [events, Finset.mem_image]

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
  constructor
  · rintro ⟨hf, hp⟩
    exact ⟨hf, fun hb => hp (.promote []) (by simp [hb]) (by simp)⟩
  · rintro ⟨hf, hp⟩
    refine ⟨hf, ?_⟩
    intro d hd hlt
    have he := (lt_split_root d).mp hlt
    subst d
    exact hp ((promote_root_mem b _).mp hd).1

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

/-- A partial endpoint uses membership only, with no execution or chosen order. -/
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

private theorem shift_append (p q : Address) (c : Call) :
    (c.shift q).shift p = c.shift (p ++ q) := by
  cases c <;> simp [Call.shift, List.append_assoc]

private theorem section_cons (I : Set Call) (b : Bool) (p : Address) :
    sectionAt (sectionAt I [b]) p = sectionAt I (b :: p) := by
  ext c
  simp [sectionAt, shift_append]

/-- The actual addressed subtree exists precisely after all creating splits.
The subtree itself is the membership-defined local partial endpoint. -/
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

/-- Local beta/alpha leaf recognition in a partial endpoint. This is a
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

theorem partial_empty (b : Bool) (t : Source) (h : Born b t) :
    cutTerm b t ∅ = .of b := by
  classical
  cases t with
  | of a => cases b <;> cases a <;> simp_all [Born, cutTerm]
  | mul l r => cases b <;> simp [cutTerm]

private theorem child_dormant (b c : Bool) (l r : Source) (I : Set Call)
    (hb : Born b (.mul l r)) (hI : Ideal b (.mul l r) I) (hs : .split [] ∉ I) :
    cutTerm c (if c then r else l) (sectionAt I [c]) = .of c := by
  have hc : sectionAt I [c] = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
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
  have hn : c.shift [b] ≠ e.shift [!b] := by simpa using shift_different (!b) c e
  simpa [sectionAt] using (or_iff_right hn :
    (c.shift [b] = e.shift [!b] ∨ c.shift [b] ∈ I) ↔ c.shift [b] ∈ I)

/-- Inserting a guarded endpoint label changes the membership-defined cutTerm
term by precisely the original native replacement. -/
theorem partial_insert (b : Bool) (t : Source) (I : Set Call)
    (hb : Born b t) (hI : Ideal b t I) (e : Call) (he : e ∈ events b t)
    (hg : Guard e (cutTerm b t I)) :
    edited (cutTerm b t I) e = cutTerm b t (insert e I) := by
  classical
  induction t generalizing b I e with
  | of a =>
      cases a <;> cases b <;> simp_all [events]
      subst e
      simp [Guard, cutTerm, subtree] at hg
      simp [edited, kind, replacement, address, cutTerm, replace, hg]
  | mul l r il ir =>
      have hc := born_children b l r hb
      have rootP : ∀ p, e = .promote p → p = [] →
          edited (cutTerm b (.mul l r) I) e = cutTerm b (.mul l r) (insert e I) := by
        intro p heq hp
        subst p
        subst e
        have hb' : b = true := (promote_root_mem b (.mul l r)).mp he |>.1
        subst b
        have hh := (guard_ancestor (.mul l r) [] (.mul l r) rfl (by simp) true I).1.mp hg
        have hs : Call.split [] ∉ I := hh.2.2.2 l r rfl
        simp [edited, kind, replacement, address, replace, cutTerm, hs]
      have rootS : e = .split [] →
          edited (cutTerm b (.mul l r) I) e = cutTerm b (.mul l r) (insert e I) := by
        intro heq
        subst e
        have hh := (guard_ancestor (.mul l r) [] (.mul l r) rfl (by simp) b I).2.mp hg
        have hs : Call.split [] ∉ I := hh.2.2 l r rfl
        have hl := child_dormant b false l r I hb hI hs
        have hr := child_dormant b true l r I hb hI hs
        have hp : cutTerm b (.mul l r) I = .of false := by
          exact Option.some.inj hg
        have hx : edited (cutTerm b (.mul l r) I) (.split []) =
            .mul (.of false) (.of true) := by rw [hp]; rfl
        rw [hx, cutTerm, if_pos (show Call.split [] ∈ insert (Call.split []) I from Or.inl rfl),
          section_insert_root I false (.split []) rfl,
          section_insert_root I true (.split []) rfl]
        simpa only [Bool.false_eq_true, ↓reduceIte] using
          (congrArg₂ FreeMagma.mul hl hr).symm
      have shifted : ∀ (c : Bool) (d : Call), e = d.shift [c] →
          edited (cutTerm b (.mul l r) I) e = cutTerm b (.mul l r) (insert e I) := by
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
          have hs' : Call.split [] ∈ insert (d.shift [false]) I := Or.inr hs
          simp only [cutTerm, hs, hs', ↓reduceIte]
          have ho : sectionAt (insert (d.shift [false]) I) [true] = sectionAt I [true] := by
            simpa only [Bool.not_true] using section_insert_other I true d
          rw [section_insert_same, ho]
          cases d <;> simpa [edited, kind, replacement, address, Call.shift, replace] using
            congrArg (fun x => FreeMagma.mul x (cutTerm true r (sectionAt I [true]))) hi'
        · have hguard : Guard d (cutTerm true r (sectionAt I [true])) := by
            cases d <;> simpa [Guard, cutTerm, hs, Call.shift, subtree] using hg
          have hi' := ir true (sectionAt I [true]) hc.2 hi d hmem hguard
          have hs' : Call.split [] ∈ insert (d.shift [true]) I := Or.inr hs
          simp only [cutTerm, hs, hs', ↓reduceIte]
          have ho : sectionAt (insert (d.shift [true]) I) [false] = sectionAt I [false] := by
            simpa only [Bool.not_false] using section_insert_other I false d
          rw [ho, section_insert_same]
          cases d <;> simpa [edited, kind, replacement, address, Call.shift, replace] using
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


/-- Membership conditions for the actual addressed leaf required by a call. -/
private def AncestorReady (b : Bool) (I : Set Call) (v : Source) : Call → Prop
  | .promote p => Created I p ∧ birthAt b p = true ∧ .promote p ∉ I ∧
      (∀ l r, v = .mul l r → .split p ∉ I)
  | .split p => Created I p ∧ (birthAt b p = false ∨ .promote p ∈ I) ∧
      (∀ l r, v = .mul l r → .split p ∉ I)

private theorem event_target (b : Bool) (t : Source) (e : Call) (he : e ∈ events b t) :
    ∃ v, subtree (address e) t = some v ∧ v ≠ .of true := by
  induction t generalizing b e with
  | of a => cases a <;> cases b <;> simp_all [events, address, subtree]
  | mul l r il ir =>
      have shifted : ∀ (c : Bool) (d : Call), e = d.shift [c] →
          ∃ v, subtree (address e) (.mul l r) = some v ∧ v ≠ .of true := by
        intro c d hed
        subst e
        have hm := (shift_mem b c l r d).mp he
        cases c
        · cases d <;> simpa [address, Call.shift, subtree] using il false _ hm
        · cases d <;> simpa [address, Call.shift, subtree] using ir true _ hm
      cases e with
      | promote p => cases p with
        | nil => exact ⟨.mul l r, rfl, by simp⟩
        | cons c p => exact shifted c (.promote p) rfl
      | split p => cases p with
        | nil => exact ⟨.mul l r, rfl, by simp⟩
        | cons c p => exact shifted c (.split p) rfl

private theorem enabled_ancestor (b : Bool) (t : Source) (I : Set Call)
    (hI : Ideal b t I) (e : Call) (he : e ∈ events b t) (v : Source)
    (hv : subtree (address e) t = some v) :
    Enabled b t I e ↔ AncestorReady b I v e := by
  induction t generalizing b I e with
  | of a =>
      cases a <;> cases b <;> simp [events] at he
      subst e
      have hv' : v = .of false := by simpa [address, subtree] using hv.symm
      subst v
      simp [AncestorReady, Created, birthAt, Enabled]
  | mul l r il ir =>
      have shifted : ∀ (c : Bool) (d : Call), e = d.shift [c] →
          (Enabled b (.mul l r) I e ↔ AncestorReady b I v e) := by
        intro c d hed
        subst e
        have hm := (shift_mem b c l r d).mp he
        have hp : subtree (address d) (if c then r else l) = some v := by
          cases c <;> cases d <;> simpa [address, Call.shift, subtree] using hv
        have ih : Enabled c (if c then r else l) (sectionAt I [c]) d ↔
            AncestorReady c (sectionAt I [c]) v d := by
          cases c
          · exact il false _ (ideal_section b false l r I hI) d hm hp
          · exact ir true _ (ideal_section b true l r I hI) d hm hp
        rw [enabled_shift b c l r I hI d]
        cases d <;> simpa [AncestorReady, Created, birthAt, Call.shift, sectionAt,
          and_assoc] using and_congr_right (fun _ : Call.split [] ∈ I => ih)
      cases e with
      | promote p => cases p with
        | nil =>
            have hb : b = true := ((promote_root_mem b (.mul l r)).mp he).1
            have hv' : v = .mul l r := by simpa [address, subtree] using hv.symm
            subst v
            subst b
            rw [enabled_promote_root]
            constructor
            · intro hp
              refine ⟨trivial, rfl, hp, ?_⟩
              intro x y _ hs
              exact hp (ideal_split_promotion true l r I hI hs rfl)
            · exact fun h => h.2.2.1
        | cons c p => exact shifted c (.promote p) rfl
      | split p => cases p with
        | nil =>
            have hv' : v = .mul l r := by simpa [address, subtree] using hv.symm
            subst v
            rw [enabled_split_root]
            cases b <;> simp [AncestorReady, Created, birthAt, and_comm]
        | cons c p => exact shifted c (.split p) rfl

/-- On every supported downclosed membership cut, the actual guard is exactly
freshness plus predecessor enabling. The guard/ancestor witness is applied at
the actual event address, with no native simulation hypothesis. -/
theorem guard_enabled (b : Bool) (t : Source) (I : Set Call)
    (hb : Born b t) (hI : Ideal b t I) (e : Call) (he : e ∈ events b t) :
    Guard e (cutTerm b t I) ↔ Enabled b t I e := by
  obtain ⟨v, hv, hn⟩ := event_target b t e he
  have ha := enabled_ancestor b t I hI e he v hv
  cases e with
  | promote p => exact (guard_ancestor t p v hv hn b I).1.trans ha.symm
  | split p => exact (guard_ancestor t p v hv hn b I).2.trans ha.symm

/-- Reading the event roster of a membership cut gives that very ideal.
This invariant makes the cut independent of any chosen execution. -/
theorem cut_events (b : Bool) (t : Source) (I : Set Call)
    (hb : Born b t) (hI : Ideal b t I) :
    (events b (cutTerm b t I) : Set Call) = I := by
  classical
  induction t generalizing b I with
  | of a =>
      cases b <;> cases a
      · have hi : I = ∅ := Set.eq_empty_iff_forall_notMem.mpr (by
          intro e he
          have := hI.1 he
          simpa [events] using this)
        simp [hi, cutTerm, events]
      · exact (hb.2 rfl rfl).elim
      · by_cases hp : Call.promote [] ∈ I
        · have hi : I = {Call.promote []} := by
            apply Set.Subset.antisymm
            · intro e he
              simpa [events] using hI.1 he
            · simpa using hp
          simp [hi, cutTerm, events]
        · have hi : I = ∅ := Set.eq_empty_iff_forall_notMem.mpr (by
            intro e he
            have he' : e = .promote [] := by simpa [events] using hI.1 he
            exact hp (he' ▸ he))
          simp [hi, cutTerm, events]
      · have hi : I = ∅ := Set.eq_empty_iff_forall_notMem.mpr (by
          intro e he
          have := hI.1 he
          simpa [events] using this)
        simp [hi, cutTerm, events]
  | mul l r il ir =>
      have hc := born_children b l r hb
      have hl := il false (sectionAt I [false]) hc.1 (ideal_section b false l r I hI)
      have hr := ir true (sectionAt I [true]) hc.2 (ideal_section b true l r I hI)
      by_cases hs : Call.split [] ∈ I
      · simp only [cutTerm, hs, ↓reduceIte]
        ext e
        have shifted : ∀ (c : Bool) (d : Call), e = d.shift [c] →
            (e ∈ (events b (.mul (cutTerm false l (sectionAt I [false]))
              (cutTerm true r (sectionAt I [true]))) : Set Call) ↔ e ∈ I) := by
          intro c d he
          subst e
          rw [show (d.shift [c] ∈ (events b (.mul (cutTerm false l (sectionAt I [false]))
              (cutTerm true r (sectionAt I [true]))) : Set Call)) ↔
              d ∈ (events c (if c then cutTerm true r (sectionAt I [true]) else
                cutTerm false l (sectionAt I [false])) : Set Call) from shift_mem ..]
          cases c
          · exact Set.ext_iff.mp hl d
          · exact Set.ext_iff.mp hr d
        cases e with
        | promote p =>
            cases p with
            | nil =>
                simp only [Finset.mem_coe, promote_root_mem, ne_eq,
                  FreeMagma.mul_eq, node_leaf, not_false_eq_true, and_true]
                constructor
                · exact ideal_split_promotion b l r I hI hs
                · exact fun hp => ((promote_root_mem b _).mp (hI.1 hp)).1
            | cons c p => exact shifted c (.promote p) rfl
        | split p =>
            cases p with
            | nil => simp [hs]
            | cons c p => exact shifted c (.split p) rfl
      · have hp0 : b = false → Call.promote [] ∉ I := by
          intro hb hp
          have hm := ((promote_root_mem b (.mul l r)).mp (hI.1 hp)).1
          simp [hb] at hm
        have hchild : ∀ (c : Bool) (d : Call), d.shift [c] ∉ I := by
          intro c d hd
          exact hs (ideal_child_split b c l r I hI d hd)
        ext e
        cases e with
        | promote p =>
            cases p with
            | nil => cases b <;> by_cases hp : Call.promote [] ∈ I <;>
                simp_all [cutTerm, hs, hp, promote_root_mem]
            | cons c p =>
                have hn : Call.promote (c :: p) ∉ I := by
                  simpa [Call.shift] using hchild c (.promote p)
                cases b <;> by_cases hp : Call.promote [] ∈ I <;>
                  simp [cutTerm, hs, hp, events, hn]
        | split p =>
            cases p with
            | nil => cases b <;> by_cases hp : Call.promote [] ∈ I <;>
                simp [cutTerm, hs, hp, events]
            | cons c p =>
                have hn : Call.split (c :: p) ∉ I := by
                  simpa [Call.shift] using hchild c (.split p)
                cases b <;> by_cases hp : Call.promote [] ∈ I <;>
                  simp [cutTerm, hs, hp, events, hn]

private theorem run_cons_guard (e : Call) (u : Source) (w : List Call) (hg : Guard e u) :
    run u (e :: w) = run (edited u e) w := by
  cases e <;> simp only [Guard] at hg <;> simp [run, hg, edited, kind, replacement, address]

theorem cut_full (b : Bool) (t : Source) (hb : Born b t) :
    cutTerm b t (events b t : Set Call) = t := by
  classical
  induction t generalizing b with
  | of a => cases b <;> cases a <;> simp_all [Born, cutTerm]
  | mul l r il ir =>
      have hc := born_children b l r hb
      have hs : Call.split [] ∈ (events b (.mul l r) : Set Call) := by simp
      simp only [cutTerm, hs, ↓reduceIte]
      have section_eq : ∀ c, sectionAt (events b (.mul l r) : Set Call) [c] =
          (events c (if c then r else l) : Set Call) := by
        intro c
        ext e
        exact shift_mem b c l r e
      rw [section_eq false, section_eq true]
      exact congrArg₂ FreeMagma.mul (il false hc.1) (ir true hc.2)

/-- The finite actual labels, ordered by labelled causal ancestry. -/
abbrev Event (b : Bool) (t : Source) := {e : Call // e ∈ events b t}

instance eventFinite (b : Bool) (t : Source) : Finite (Event b t) := by
  classical
  exact Finite.of_fintype (↥(events b t))

/-- Forget subtype proofs but retain precisely the selected labelled events. -/
def raw (b : Bool) (t : Source) (K : Set (Event b t)) : Set Call :=
  {e | ∃ h : e ∈ events b t, (⟨e, h⟩ : Event b t) ∈ K}

private theorem raw_ideal (b : Bool) (t : Source) (K : Set (Event b t))
    (hK : IsLowerSet K) : Ideal b t (raw b t K) := by
  refine ⟨fun e ⟨h, _⟩ => h, ?_⟩
  intro c hc d hd hcd
  obtain ⟨hd, hdK⟩ := hd
  exact ⟨hc, hK (show (⟨c, hc⟩ : Event b t) ≤ ⟨d, hd⟩ from hcd) hdK⟩

@[simp] private theorem raw_mem (b : Bool) (t : Source) (K : Set (Event b t)) (e : Event b t) :
    e.1 ∈ raw b t K ↔ e ∈ K := by simp [raw]

@[simp] private theorem raw_insert (b : Bool) (t : Source) (K : Set (Event b t))
    (e : Event b t) : raw b t (insert e K) = insert e.1 (raw b t K) := by
  ext d
  simp only [raw, Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨hd, he | hK⟩
    · exact Or.inl (congrArg Subtype.val he)
    · exact Or.inr ⟨hd, hK⟩
  · rintro (he | ⟨hd, hK⟩)
    · subst d
      exact ⟨e.2, Or.inl rfl⟩
    · exact ⟨hd, Or.inr hK⟩

private theorem typed_enabled (b : Bool) (t : Source) (K : Set (Event b t))
    (e : Event b t) :
    D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.Enabled K e ↔
      Enabled b t (raw b t K) e.1 := by
  simp only [D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.Enabled,
    Enabled, raw_mem]
  constructor
  · rintro ⟨hf, hp⟩
    exact ⟨hf, fun d hd hde => ⟨hd, hp ⟨d, hd⟩ hde⟩⟩
  · rintro ⟨hf, hp⟩
    exact ⟨hf, fun d hde => (raw_mem b t K d).mp (hp d.1 d.2 hde)⟩

private theorem raw_empty (b : Bool) (t : Source) : raw b t ∅ = ∅ := by
  ext e
  simp [raw]

private theorem raw_univ (b : Bool) (t : Source) :
    raw b t Set.univ = (events b t : Set Call) := by
  ext e
  simp [raw]

private theorem lower_insert (b : Bool) (t : Source) (K : Set (Event b t))
    (hK : IsLowerSet K) (e : Event b t)
    (he : D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.Enabled K e) :
    IsLowerSet (insert e K) := by
  intro d c hcd hd
  rcases hd with hde | hd
  · subst d
    by_cases hce : c = e
    · exact Or.inl hce
    · exact Or.inr (he.2 c (lt_of_le_of_ne hcd hce))
  · exact Or.inr (hK hcd hd)

private theorem cut_injective (b : Bool) (t : Source) (hb : Born b t)
    (K J : Set (Event b t)) (hK : IsLowerSet K) (hJ : IsLowerSet J)
    (he : cutTerm b t (raw b t K) = cutTerm b t (raw b t J)) : K = J := by
  have hr : raw b t K = raw b t J := by
    rw [← cut_events b t (raw b t K) hb (raw_ideal b t K hK), he,
      cut_events b t (raw b t J) hb (raw_ideal b t J hJ)]
  ext e
  rw [← raw_mem b t K e, hr, raw_mem]

private theorem run_head (e : Call) (u v : Source) (w : List Call) :
    run u (e :: w) = some v ↔ Guard e u ∧ run (edited u e) w = some v := by
  cases e with
  | promote p =>
      cases hs : subtree p u with
      | none => simp [run, hs, Guard]
      | some s => cases s with
        | of a => cases a <;> simp [run, hs, Guard, edited, kind, replacement, address]
        | mul l r => simp [run, hs, Guard]
  | split p =>
      cases hs : subtree p u with
      | none => simp [run, hs, Guard]
      | some s => cases s with
        | of a => cases a <;> simp [run, hs, Guard, edited, kind, replacement, address]
        | mul l r => simp [run, hs, Guard]

/-- The actual native run agrees with enabled execution between any two ideals.
The reverse direction tracks the membership ideal at every successful prefix. -/
theorem execution_adequacy (b : Bool) (t : Source) (hb : Born b t)
    (K J : Set (Event b t)) (hK : IsLowerSet K) (hJ : IsLowerSet J)
    (l : List (Event b t)) :
    D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.Exec K l J ↔
      run (cutTerm b t (raw b t K)) (l.map Subtype.val) =
        some (cutTerm b t (raw b t J)) := by
  induction l generalizing K with
  | nil =>
      change K = J ↔ some (cutTerm b t (raw b t K)) = some (cutTerm b t (raw b t J))
      exact ⟨fun h => by rw [h], fun h => cut_injective b t hb K J hK hJ (Option.some.inj h)⟩
  | cons e l ih =>
      change (_ ∧ _) ↔ run _ (e.1 :: l.map Subtype.val) = _
      rw [run_head]
      have hg : Guard e.1 (cutTerm b t (raw b t K)) ↔
          D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.Enabled K e :=
        (guard_enabled b t (raw b t K) hb (raw_ideal b t K hK) e.1 e.2).trans
          (typed_enabled b t K e).symm
      constructor
      · rintro ⟨hen, htail⟩
        have guard := hg.mpr hen
        refine ⟨guard, ?_⟩
        rw [partial_insert b t (raw b t K) hb (raw_ideal b t K hK) e.1 e.2 guard,
          ← raw_insert]
        exact (ih (insert e K) (lower_insert b t K hK e hen)).mp htail
      · rintro ⟨guard, htail⟩
        have hen := hg.mp guard
        refine ⟨hen, ?_⟩
        apply (ih (insert e K) (lower_insert b t K hK e hen)).mpr
        rw [raw_insert]
        rw [partial_insert b t (raw b t K) hb (raw_ideal b t K hK) e.1 e.2 guard] at htail
        exact htail

/-- Actual labelled histories from alpha are exactly linear extensions of the
endpoint's finite causal order; the generic theorem is used after adequacy. -/
theorem linear_extension_histories (t : Source) (ht : D t)
    (l : List (Event true t)) :
    run (.of true) (l.map Subtype.val) = some t ↔
      D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.ExtensionList
        ∅ Set.univ l := by
  have hb : Born true t := ⟨ht, by simp⟩
  have had := execution_adequacy true t hb ∅ Set.univ
    isLowerSet_empty isLowerSet_univ l
  rw [raw_empty, raw_univ, partial_empty true t hb, cut_full true t hb] at had
  exact had.symm.trans
    ((D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.result
      (∅ : Set (Event true t)) Set.univ isLowerSet_empty isLowerSet_univ
        (Set.empty_subset _)).1 l)

private theorem born_next (b : Bool) (u : Source) (e : Call)
    (hb : Born b u) (hg : Guard e u) : Born b (edited u e) := by
  have hr : run u [e] = some (edited u e) := by
    rw [run_cons_guard e u [] hg]
    rfl
  refine ⟨NativeGuardedLeafRepair.run_preserves_D hb.1 hr, ?_⟩
  intro _
  cases e with
  | promote p =>
      cases p with
      | nil => simp [edited, kind, replacement, address, replace]
      | cons c p => cases u with
        | of a => simp [Guard, subtree] at hg
        | mul l r => cases c <;> simp [edited, kind, replacement, address, replace]
  | split p =>
      cases p with
      | nil => simp [edited, kind, replacement, address, replace]
      | cons c p => cases u with
        | of a => simp [Guard, subtree] at hg
        | mul l r => cases c <;> simp [edited, kind, replacement, address, replace]

/-- A successful actual call adds precisely its own fresh endpoint label.
This is the native history-to-ideal inventory step, proved on source operations. -/
private theorem event_step (b : Bool) (u : Source) (e : Call)
    (hb : Born b u) (hg : Guard e u) :
    events b (edited u e) = insert e (events b u) ∧ e ∉ events b u := by
  classical
  induction u generalizing b e with
  | of a =>
      cases e with
      | promote p =>
          cases p with
          | nil =>
              have ha : a = true := by simpa [Guard, subtree] using hg
              subst a
              have hb' : b = true := by cases b <;> simp_all [Born]
              subst b
              simp [edited, kind, replacement, address, replace, events]
          | cons c p => simp [Guard, subtree] at hg
      | split p =>
          cases p with
          | nil =>
              have ha : a = false := by simpa [Guard, subtree] using hg
              subst a
              cases b <;> simp [edited, kind, replacement, address, replace, events, Finset.pair_comm]
          | cons c p => simp [Guard, subtree] at hg
  | mul l r il ir =>
      have hc := born_children b l r hb
      have child : ∀ (c : Bool) (d : Call), e = d.shift [c] →
          events b (edited (.mul l r) e) = insert e (events b (.mul l r)) ∧
            e ∉ events b (.mul l r) := by
        intro c d hed
        subst e
        cases c
        · have hg' : Guard d l := by cases d <;> simpa [Guard, Call.shift, subtree] using hg
          obtain ⟨hi, hf⟩ := il false d hc.1 hg'
          constructor
          · have hed : edited (.mul l r) (d.shift [false]) = .mul (edited l d) r := by
              cases d <;> rfl
            rw [hed, events, hi]
            cases b <;> simp [events, Finset.image_insert, Finset.insert_union,
              Finset.union_insert, Finset.insert_comm]
          · exact fun hm => hf ((shift_mem b false l r d).mp hm)
        · have hg' : Guard d r := by cases d <;> simpa [Guard, Call.shift, subtree] using hg
          obtain ⟨hi, hf⟩ := ir true d hc.2 hg'
          constructor
          · have hed : edited (.mul l r) (d.shift [true]) = .mul l (edited r d) := by
              cases d <;> rfl
            rw [hed, events, hi]
            cases b <;> simp [events, Finset.image_insert, Finset.insert_union,
              Finset.union_insert, Finset.insert_comm]
          · exact fun hm => hf ((shift_mem b true l r d).mp hm)
      cases e with
      | promote p => cases p with
        | nil => simp [Guard, subtree] at hg
        | cons c p => exact child c (.promote p) rfl
      | split p => cases p with
        | nil => simp [Guard, subtree] at hg
        | cons c p => exact child c (.split p) rfl

private theorem history_events (b : Bool) (u v : Source) (hb : Born b u)
    (w : List Call) (h : run u w = some v) :
    events b u ⊆ events b v ∧ ∀ e ∈ w, e ∈ events b v := by
  classical
  induction w generalizing u with
  | nil => cases h; exact ⟨Finset.Subset.rfl, by simp⟩
  | cons e w ih =>
      obtain ⟨hg, hr⟩ := (run_head e u v w).mp h
      obtain ⟨heq, _⟩ := event_step b u e hb hg
      obtain ⟨hsub, hmem⟩ := ih (edited u e) (born_next b u e hb hg) hr
      refine ⟨?_, ?_⟩
      · rw [heq] at hsub
        exact fun d hd => hsub (Finset.mem_insert_of_mem hd)
      · intro d hd
        rcases List.mem_cons.mp hd with hde | hd
        · subst d
          apply hsub
          rw [heq]
          exact Finset.mem_insert_self e _
        · exact hmem d hd

/-- Every raw successful history has the exact labelled linear-extension lift.
No membership, reachability or history-adequacy premise is supplied by the caller. -/
theorem all_histories (t : Source) (ht : D t) (w : List Call) :
    run (.of true) w = some t ↔ ∃ l : List (Event true t),
      l.map Subtype.val = w ∧
      D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity.ExtensionList
        ∅ Set.univ l := by
  constructor
  · intro hw
    have hb : Born true (.of true) := ⟨NativeGuardedLeafRepair.alphaRHistory.domain, by simp⟩
    have hm := (history_events true (.of true) t hb w hw).2
    let l : List (Event true t) := w.attach.map (fun e => ⟨e.1, hm e.1 e.2⟩)
    have hl : l.map Subtype.val = w := by simp [l]
    refine ⟨l, hl, ?_⟩
    apply (linear_extension_histories t ht l).mp
    simpa [hl] using hw
  · rintro ⟨l, rfl, hl⟩
    exact (linear_extension_histories t ht l).mpr hl

end D5.S3.Arith.FibonacciAtomic.Geometry.NativeEndpointEventIdeals

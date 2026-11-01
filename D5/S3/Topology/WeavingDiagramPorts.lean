/- GID: D5/S3/Topology/WeavingDiagramPorts
   generality: G
   mirror-B: D5/B/S3/Topology/WeavingDiagramPorts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Finite closed braid port matchings and uniform smoothing components. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

/-! Actual temporal braid matching and uniform smoothing component classification. -/

set_option autoImplicit false
namespace D5.S3.Topology.WeavingDiagramPorts

inductive Port | tl | tr | bl | br
  deriving DecidableEq, Repr

instance : Fintype Port := ⟨{.tl,.tr,.bl,.br}, by intro a; cases a <;> simp⟩

structure Parameters where
  n : ℕ
  m : ℕ
  hn : 2 ≤ n
  hm : 3 ≤ m

instance (P : Parameters) : NeZero P.m := ⟨by have := P.hm; omega⟩

abbrev Dart (P : Parameters) := ZMod P.m × Fin P.n × Port

def predIndex {n : ℕ} (i : Fin n) (_h : i.val ≠ 0) : Fin n := ⟨i.val - 1, by omega⟩
def succIndex {n : ℕ} (i : Fin n) (h : i.val + 1 < n) : Fin n := ⟨i.val + 1,h⟩

/-- The next input at the same strand position in temporal generator order.
An internal position meets generator p - 1, then p, then p - 1 in the next period.
The two outer positions meet only one generator per period. -/
def external (P : Parameters) : Dart P → Dart P
  | (t,i,.bl) => if h : i.val = 0 then (t + 1,i,.tl)
      else (t + 1,predIndex i h,.tr)
  | (t,i,.br) => if h : i.val + 1 < P.n then (t,succIndex i h,.tl)
      else (t + 1,i,.tr)
  | (t,i,.tl) => if h : i.val = 0 then (t - 1,i,.bl)
      else (t,predIndex i h,.br)
  | (t,i,.tr) => if h : i.val + 1 < P.n then (t - 1,succIndex i h,.bl)
      else (t - 1,i,.br)

/-- Cup - cap is selected by zero - based generator parity p, p=0 for printed odd. -/
def cup (p : ℕ) {P : Parameters} (i : Fin P.n) : Prop := i.val % 2 = p

instance (p : ℕ) {P : Parameters} (i : Fin P.n) : Decidable (cup p i) := inferInstanceAs (Decidable (i.val % 2 = p))

def localMate (P : Parameters) (p : ℕ) : Dart P → Dart P
  | (t,i,a) => (t,i, if cup p i then
      match a with | .tl => .tr | .tr => .tl | .bl => .br | .br => .bl
    else match a with | .tl => .bl | .bl => .tl | .tr => .br | .br => .tr)

/-- Each port has exactly one external neighbour, including both seams. -/
theorem external_involutive (P : Parameters) : Function.Involutive (external P) := by
  rintro ⟨t,i,a⟩
  have hi := i.isLt
  cases a <;> simp only [external] <;> split_ifs <;>
    simp_all [external, predIndex, succIndex, Fin.ext_iff] <;> try omega
  all_goals split_ifs <;> simp_all [Fin.ext_iff] <;> omega

/-- External wires never join a port to itself. -/
theorem external_ne_self (P : Parameters) (x : Dart P) : external P x ≠ x := by
  rcases x with ⟨t,i,a⟩
  cases a <;> simp only [external] <;> split_ifs <;> simp

private theorem local_involutive (P : Parameters) (p : ℕ) :
    Function.Involutive (localMate P p) := by
  rintro ⟨t,i,a⟩
  cases a <;> simp [localMate] <;> split_ifs <;> rfl

private theorem local_ne_self (P : Parameters) (p : ℕ) (x : Dart P) :
    localMate P p x ≠ x := by
  rcases x with ⟨t,i,a⟩
  cases a <;> simp [localMate] <;> split_ifs <;> simp

/-- The actual smoothed port graph. Involution and no - fixed - point proofs
supply its symmetry and looplessness, without removing any arc. -/
def portGraph (P : Parameters) (p : ℕ) : SimpleGraph (Dart P) where
  Adj x y := y = localMate P p x ∨ y = external P x
  symm := ⟨by
    intro x y h
    rcases h with rfl | rfl
    · exact Or.inl (local_involutive P p x).symm
    · exact Or.inr (external_involutive P x).symm⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h
    · exact local_ne_self P p x h.symm
    · exact external_ne_self P x h.symm⟩

/-- Both matching arcs of the actual smoothed port graph. -/
def step (P : Parameters) (p : ℕ) (x y : Dart P) : Prop :=
  (portGraph P p).Adj x y

abbrev Reach (P : Parameters) (p : ℕ) := Relation.EqvGen (step P p)
abbrev Circle (P : Parameters) (p : ℕ) := Quotient (Relation.EqvGen.setoid (step P p))

private theorem reach_local (P : Parameters) (p : ℕ) (x : Dart P) :
    Reach P p x (localMate P p x) := Relation.EqvGen.rel _ _ (Or.inl rfl)
private theorem reach_external (P : Parameters) (p : ℕ) (x : Dart P) :
    Reach P p x (external P x) := Relation.EqvGen.rel _ _ (Or.inr rfl)

/-- Labels include only interval circles and the outer strands actually unpaired. -/
abbrev Label (P : Parameters) (p : ℕ) :=
  ({i : Fin P.n // cup p i} × ZMod P.m) ⊕
    {b : Bool // if b then ¬ cup p (⟨P.n - 1, by have := P.hn; omega⟩ : Fin P.n)
      else ¬ cup p (⟨0, by have := P.hn; omega⟩ : Fin P.n)}

/-- Interval i is coded i + 1; the outer strands are coded 0 and n + 1.
Hub labels have time zero, since the hub runs through every period. -/
def code (P : Parameters) (p : ℕ) : Dart P → ℕ × ZMod P.m
  | (t,i,a) => if cup p i then
      (i.val + 1, match a with | .tl | .tr => t - 1 | .bl | .br => t)
    else match a with
      | .tl | .bl => if i.val = 0 then (0,0) else (i.val,t)
      | .tr | .br => if i.val + 1 < P.n then (i.val + 2,t - 1) else (P.n + 1,0)

private theorem code_local (P : Parameters) (p : ℕ) (x : Dart P) :
    code P p (localMate P p x) = code P p x := by
  rcases x with ⟨t,i,a⟩
  cases a <;> simp [localMate, code] <;> split_ifs <;> rfl

private theorem code_external (P : Parameters) (p : ℕ) (hp : p < 2) (x : Dart P) :
    code P p (external P x) = code P p x := by
  rcases x with ⟨t,i,a⟩
  have hi := i.isLt
  cases a <;> simp only [external] <;> split_ifs <;>
    simp_all [code, cup, predIndex, succIndex] <;>
    split_ifs <;> simp_all <;> try omega
  all_goals split_ifs <;> simp_all [Fin.ext_iff] <;> try omega
  all_goals split_ifs <;> simp_all <;> omega

private theorem code_reach (P : Parameters) (p : ℕ) (hp : p < 2)
    {x y : Dart P} (h : Reach P p x y) : code P p x = code P p y := by
  induction h with
  | rel x y h =>
    rcases h with rfl | rfl
    · exact (code_local P p x).symm
    · exact (code_external P p hp x).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ hab hbc => exact hab.trans hbc

private theorem cup_pred (P : Parameters) (p : ℕ) (hp : p < 2)
    (i : Fin P.n) (hi : i.val ≠ 0) (h : cup p i) :
    ¬ cup p (predIndex i hi) := by unfold cup at *; dsimp [predIndex]; omega

private theorem notcup_pred (P : Parameters) (p : ℕ) (hp : p < 2)
    (i : Fin P.n) (hi : i.val ≠ 0) (h : ¬ cup p i) :
    cup p (predIndex i hi) := by unfold cup at *; dsimp [predIndex]; omega

private theorem notcup_succ (P : Parameters) (p : ℕ) (hp : p < 2)
    (i : Fin P.n) (hi : i.val + 1 < P.n) (h : ¬ cup p i) :
    cup p (succIndex i hi) := by unfold cup at *; dsimp [succIndex]; omega

private theorem cup_top_path (P : Parameters) (p : ℕ) (hp : p < 2)
    (t : ZMod P.m) (i : Fin P.n) (h : cup p i) :
    Reach P p (t,i,.tl) (t - 1,i,.bl) := by
  by_cases hi : i.val = 0
  · simpa [external, hi] using reach_external P p (t,i,.tl)
  · let j := predIndex i hi
    have hj : j.val + 1 < P.n := by dsimp [j,predIndex]; have := i.isLt; omega
    have hv : ¬ cup p j := cup_pred P p hp i hi h
    have he : succIndex j hj = i := by apply Fin.ext; dsimp [succIndex,j,predIndex]; omega
    have a : Reach P p (t,i,.tl) (t,j,.br) := by
      simpa [external,hi,j] using reach_external P p (t,i,.tl)
    have b : Reach P p (t,j,.br) (t,j,.tr) := by
      simpa [localMate,hv] using reach_local P p (t,j,.br)
    have c : Reach P p (t,j,.tr) (t - 1,i,.bl) := by
      simpa [external,hj,he] using reach_external P p (t,j,.tr)
    exact .trans _ _ _ a (.trans _ _ _ b c)

private theorem vertical_left_path (P : Parameters) (p : ℕ)
    (t : ZMod P.m) (i : Fin P.n) (hi : i.val ≠ 0)
    (hprev : cup p (predIndex i hi)) :
    Reach P p (t,i,.tl) (t,predIndex i hi,.bl) := by
  have a : Reach P p (t,i,.tl) (t,predIndex i hi,.br) := by
    simpa [external,hi] using reach_external P p (t,i,.tl)
  have b : Reach P p (t,predIndex i hi,.br) (t,predIndex i hi,.bl) := by
    simpa [localMate,hprev] using reach_local P p (t,predIndex i hi,.br)
  exact .trans _ _ _ a b

private theorem vertical_right_path (P : Parameters) (p : ℕ)
    (t : ZMod P.m) (i : Fin P.n) (hi : i.val + 1 < P.n) :
    Reach P p (t,i,.tr) (t - 1,succIndex i hi,.bl) := by
  simpa [external,hi] using reach_external P p (t,i,.tr)

private def first (P : Parameters) : Fin P.n := ⟨0, by have := P.hn; omega⟩
private def last (P : Parameters) : Fin P.n := ⟨P.n - 1, by have := P.hn; omega⟩

private theorem left_time_step (P : Parameters) (p : ℕ)
    (h : ¬ cup p (first P)) (t : ZMod P.m) :
    Reach P p (t,first P,.tl) (t + 1,first P,.tl) := by
  have a : Reach P p (t,first P,.tl) (t,first P,.bl) := by
    simpa [localMate,h] using reach_local P p (t,first P,.tl)
  have b : Reach P p (t,first P,.bl) (t + 1,first P,.tl) := by
    simpa [external,first] using reach_external P p (t,first P,.bl)
  exact .trans _ _ _ a b

private theorem right_time_step (P : Parameters) (p : ℕ)
    (h : ¬ cup p (last P)) (t : ZMod P.m) :
    Reach P p (t,last P,.tr) (t + 1,last P,.tr) := by
  have hn := P.hn
  have a : Reach P p (t,last P,.tr) (t,last P,.br) := by
    simpa [localMate,h] using reach_local P p (t,last P,.tr)
  have b : Reach P p (t,last P,.br) (t + 1,last P,.tr) := by
    simpa [external,last,show ¬ (P.n - 1 + 1 < P.n) by omega] using
      reach_external P p (t,last P,.br)
  exact .trans _ _ _ a b

private theorem cyclic_path (P : Parameters) (p : ℕ) (f : ZMod P.m → Dart P)
    (h : ∀ t, Reach P p (f t) (f (t + 1))) (t : ZMod P.m) :
    Reach P p (f t) (f 0) := by
  obtain ⟨k,rfl⟩ := ZMod.natCast_zmod_surjective t
  apply Relation.EqvGen.symm
  have go : ∀ k : ℕ, Reach P p (f 0) (f (k : ZMod P.m)) := by
    intro k
    induction k with
    | zero => simpa using (Relation.EqvGen.refl (r := step P p) (f 0))
    | succ k ih => simpa [Nat.cast_add,Nat.cast_one] using
        Relation.EqvGen.trans _ _ _ ih (h (k : ZMod P.m))
  exact go k

private def repCode (P : Parameters) (c : ℕ × ZMod P.m) : Dart P :=
  if h0 : c.1 = 0 then (0,first P,.tl)
  else if h : c.1 ≤ P.n then (c.2,⟨c.1 - 1,by omega⟩,.bl)
  else (0,last P,.tr)

private theorem repCode_interval (P : Parameters) (i : Fin P.n) (t : ZMod P.m) :
    repCode P (i.val + 1,t) = (t,i,.bl) := by
  have hi : i.val + 1 ≤ P.n := by have := i.isLt; omega
  simp [repCode,hi]

private theorem tl_rep (P : Parameters) (p : ℕ) (hp : p < 2)
    (t : ZMod P.m) (i : Fin P.n) :
    Reach P p (t,i,.tl) (repCode P (code P p (t,i,.tl))) := by
  by_cases h : cup p i
  · simpa [code,h,repCode_interval] using cup_top_path P p hp t i h
  · by_cases hi : i.val = 0
    · have he : i = first P := Fin.ext hi
      subst i
      have ec : code P p (t,first P,.tl) = (0,0) := by
        simp only [code,h,↓reduceIte]; rfl
      rw [ec]
      change Reach P p (t,first P,.tl) (0,first P,.tl)
      exact cyclic_path P p (fun t => (t,first P,.tl)) (left_time_step P p h) t
    · have hv := notcup_pred P p hp i hi h
      have e : repCode P (i.val,t) = (t,predIndex i hi,.bl) := by
        have eq : i.val = (predIndex i hi).val + 1 := by dsimp [predIndex]; omega
        conv_lhs => rw [eq]
        exact repCode_interval P (predIndex i hi) t
      simpa [code,h,hi,e] using vertical_left_path P p t i hi hv

private theorem tr_rep (P : Parameters) (p : ℕ) (hp : p < 2)
    (t : ZMod P.m) (i : Fin P.n) :
    Reach P p (t,i,.tr) (repCode P (code P p (t,i,.tr))) := by
  by_cases h : cup p i
  · have a : Reach P p (t,i,.tr) (t,i,.tl) := by
      simpa [localMate,h] using reach_local P p (t,i,.tr)
    have b := tl_rep P p hp t i
    simpa [code,h] using Relation.EqvGen.trans _ _ _ a b
  · by_cases hi : i.val + 1 < P.n
    · have e : repCode P (i.val + 2,t - 1) = (t - 1,succIndex i hi,.bl) := by
        simpa [succIndex,Nat.add_assoc] using repCode_interval P (succIndex i hi) (t - 1)
      simpa [code,h,hi,e] using vertical_right_path P p t i hi
    · have hn := P.hn
      have he : i = last P := by apply Fin.ext; dsimp [last]; have := i.isLt; omega
      subst i
      have hh : ¬ (last P).val + 1 < P.n := by dsimp [last]; omega
      have ec : code P p (t,last P,.tr) = (P.n + 1,0) := by
        simp only [code,h,hh,↓reduceIte]
      rw [ec]
      have er : repCode P (P.n + 1,0) = (0,last P,.tr) := by simp [repCode]
      rw [er]
      exact cyclic_path P p (fun t => (t,last P,.tr)) (right_time_step P p h) t

private theorem reach_rep (P : Parameters) (p : ℕ) (hp : p < 2) (x : Dart P) :
    Reach P p x (repCode P (code P p x)) := by
  rcases x with ⟨t,i,a⟩
  cases a with
  | tl => exact tl_rep P p hp t i
  | tr => exact tr_rep P p hp t i
  | bl =>
    by_cases h : cup p i
    · simpa [code,h,repCode_interval] using (Relation.EqvGen.refl (r := step P p) (t,i,Port.bl))
    · have a : Reach P p (t,i,.bl) (t,i,.tl) := by
        simpa [localMate,h] using reach_local P p (t,i,.bl)
      simpa [code,h] using Relation.EqvGen.trans _ _ _ a (tl_rep P p hp t i)
  | br =>
    by_cases h : cup p i
    · simpa [localMate,code,h,repCode_interval] using reach_local P p (t,i,.br)
    · have a : Reach P p (t,i,.br) (t,i,.tr) := by
        simpa [localMate,h] using reach_local P p (t,i,.br)
      simpa [code,h] using Relation.EqvGen.trans _ _ _ a (tr_rep P p hp t i)

/-- Two actual ports lie on the same smoothed circle exactly when their codes agree. -/
theorem reach_iff_code (P : Parameters) (p : ℕ) (hp : p < 2) (x y : Dart P) :
    Reach P p x y ↔ code P p x = code P p y := by
  constructor
  · exact code_reach P p hp
  · intro h
    have a := reach_rep P p hp x
    have b := reach_rep P p hp y
    rw [← h] at b
    exact .trans _ _ _ a (.symm _ _ b)

private def labelCode (P : Parameters) (p : ℕ) : Label P p → ℕ × ZMod P.m
  | .inl (i,t) => (i.val.val + 1,t)
  | .inr b => (if b.val then P.n + 1 else 0,0)

private def labelRep (P : Parameters) (p : ℕ) : Label P p → Dart P
  | .inl (i,t) => (t,i.val,.bl)
  | .inr b => if b.val then (0,last P,.tr) else (0,first P,.tl)

private theorem labelCode_injective (P : Parameters) (p : ℕ) :
    Function.Injective (labelCode P p) := by
  intro x y h
  rcases x with ⟨⟨i,hi⟩,t⟩ | ⟨b,hb⟩ <;>
    rcases y with ⟨⟨j,hj⟩,u⟩ | ⟨c,hc⟩
  · simp only [labelCode,Prod.mk.injEq,Nat.add_right_cancel_iff] at h
    obtain ⟨hij,rfl⟩ := h
    have : i = j := Fin.ext hij
    subst j
    rfl
  · cases c <;> simp [labelCode] at h <;> have := i.isLt <;> omega
  · cases b <;> simp [labelCode] at h <;> have := j.isLt <;> omega
  · cases b <;> cases c <;> simp_all [labelCode]

private theorem code_labelRep (P : Parameters) (p : ℕ) (z : Label P p) :
    code P p (labelRep P p z) = labelCode P p z := by
  rcases z with ⟨⟨i,hi⟩,t⟩ | ⟨b,hb⟩
  · simp [labelRep,code,hi,labelCode]
  · cases b
    · change ¬ cup p (first P) at hb
      change code P p (0,first P,.tl) = (0,0)
      simp only [code,hb,↓reduceIte]
      rfl
    · have hn := P.hn
      have hh : ¬ (last P).val + 1 < P.n := by dsimp [last]; omega
      change ¬ cup p (last P) at hb
      simp [labelRep,code,labelCode,hb,hh]

private def labelOf (P : Parameters) (p : ℕ) (hp : p < 2) : Dart P → Label P p
  | (t,i,a) => if h : cup p i then .inl (⟨i,h⟩,
      match a with | .tl | .tr => t - 1 | .bl | .br => t)
    else match a with
      | .tl | .bl => if hi : i.val = 0 then .inr ⟨false,by
          have he : i = (⟨0,by have := P.hn; omega⟩ : Fin P.n) := Fin.ext hi
          simpa [he] using h⟩
        else .inl (⟨predIndex i hi,notcup_pred P p hp i hi h⟩,t)
      | .tr | .br => if hi : i.val + 1 < P.n then
          .inl (⟨succIndex i hi,notcup_succ P p hp i hi h⟩,t - 1)
        else .inr ⟨true,by
          have he : i = (⟨P.n - 1,by have := P.hn; omega⟩ : Fin P.n) := by
            apply Fin.ext; change i.val = P.n - 1; have := i.isLt; omega
          simpa [he] using h⟩

private theorem labelOf_code (P : Parameters) (p : ℕ) (hp : p < 2) (x : Dart P) :
    labelCode P p (labelOf P p hp x) = code P p x := by
  rcases x with ⟨t,i,a⟩
  cases a <;> simp only [labelOf,code] <;> split_ifs <;>
    simp_all [labelCode,predIndex,succIndex] <;> omega

/-- Explicit bijection from the actual component quotient to interval and hub labels. -/
noncomputable def circleEquiv (P : Parameters) (p : ℕ) (hp : p < 2) :
    Circle P p ≃ Label P p where
  toFun := Quotient.lift (labelOf P p hp) (by
    intro x y h
    apply labelCode_injective P p
    rw [labelOf_code,labelOf_code]
    exact code_reach P p hp h)
  invFun z := Quotient.mk _ (labelRep P p z)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      apply Quotient.sound
      apply (reach_iff_code P p hp _ _).mpr
      change code P p (labelRep P p (labelOf P p hp x)) = code P p x
      rw [code_labelRep,labelOf_code]
  right_inv := by
    intro z
    apply labelCode_injective P p
    change labelCode P p (labelOf P p hp (labelRep P p z)) = labelCode P p z
    rw [labelOf_code,code_labelRep]

private def parityEquiv (P : Parameters) (p : ℕ) (hp : p < 2) :
    {i : Fin P.n // cup p i} ≃ Fin ((P.n + 1 - p) / 2) where
  toFun i := ⟨i.val.val / 2,by have := i.val.isLt; have := i.property; unfold cup at *; omega⟩
  invFun j := ⟨⟨2 * j.val + p,by have := j.isLt; omega⟩,by unfold cup; dsimp; omega⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; have := i.property; unfold cup at *; dsimp; omega
  right_inv j := by apply Fin.ext; dsimp; omega

private theorem label_card (P : Parameters) (p : ℕ) (hp : p < 2) :
    Fintype.card (Label P p) = ((P.n + 1 - p) / 2) * P.m +
      (if p = 0 then 1 - P.n % 2 else 1 + P.n % 2) := by
  have hi : Fintype.card {i : Fin P.n // cup p i} = (P.n + 1 - p) / 2 :=
    (Fintype.card_congr (parityEquiv P p hp)).trans (Fintype.card_fin _)
  have hb : Fintype.card {b : Bool // if b then
      ¬ cup p (⟨P.n - 1,by have := P.hn; omega⟩ : Fin P.n)
      else ¬ cup p (⟨0,by have := P.hn; omega⟩ : Fin P.n)} =
      (if p = 0 then 1 - P.n % 2 else 1 + P.n % 2) := by
    rw [Fintype.card_subtype]
    rw [Fintype.univ_bool]
    have hn := P.hn
    have hd : P.n % 2 < 2 := Nat.mod_lt _ (by omega)
    have ht : (P.n - 1) % 2 = 1 - P.n % 2 := by omega
    rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;>
      rcases (show P.n % 2 = 0 ∨ P.n % 2 = 1 by omega) with hd | hd <;>
      simp [cup,ht,hd] <;> decide
  simpa [Label,Fintype.card_sum,Fintype.card_prod,hi,hb] using
    congrArg (fun k => ((P.n + 1 - p) / 2) * P.m + k) hb

/-- Exact circle count for cup - caps at printed odd generators. -/
theorem odd_circle_count (P : Parameters) :
    Nat.card (Circle P 0) =
      (((P.n - P.n % 2) / 2) + P.n % 2) * P.m + 1 - P.n % 2 := by
  rw [Nat.card_congr (circleEquiv P 0 (by omega)),Nat.card_eq_fintype_card,
    label_card P 0 (by omega)]
  have hn := P.hn
  have hd : P.n % 2 < 2 := Nat.mod_lt _ (by omega)
  have he : (P.n + 1) / 2 = (P.n - P.n % 2) / 2 + P.n % 2 := by omega
  simp only [Nat.sub_zero,ite_true]
  rw [he]
  omega

/-- Exact circle count for cup - caps at printed even generators. -/
theorem even_circle_count (P : Parameters) :
    Nat.card (Circle P 1) = ((P.n - P.n % 2) / 2) * P.m + 1 + P.n % 2 := by
  rw [Nat.card_congr (circleEquiv P 1 (by omega)),Nat.card_eq_fintype_card,
    label_card P 1 (by omega)]
  have he : P.n / 2 = (P.n - P.n % 2) / 2 := by omega
  simp [he,Nat.add_assoc]

/-- The actual quotient class of a port. -/
def circle (P : Parameters) (p : ℕ) (x : Dart P) : Circle P p := Quotient.mk _ x

private theorem circle_eq_iff (P : Parameters) (p : ℕ) (hp : p < 2) (x y : Dart P) :
    circle P p x = circle P p y ↔ code P p x = code P p y :=
  Quotient.eq.trans (reach_iff_code P p hp x y)

/-- Crossing edges use one port on each of the two actual smoothing arcs. -/
def edgeEnds (P : Parameters) (p : ℕ) (t : ZMod P.m) (i : Fin P.n) :
    Circle P p × Circle P p :=
  if cup p i then (circle P p (t,i,.tl),circle P p (t,i,.bl))
    else (circle P p (t,i,.tl),circle P p (t,i,.tr))

/-- A cup - cap edge joins the preceding interval to the current interval. -/
theorem cup_edge (P : Parameters) (p : ℕ) (hp : p < 2)
    (t : ZMod P.m) (i : Fin P.n) (h : cup p i) :
    edgeEnds P p t i = (circle P p (t - 1,i,.bl),circle P p (t,i,.bl)) := by
  simp only [edgeEnds,h,↓reduceIte,Prod.mk.injEq,and_true]
  apply (circle_eq_iff P p hp _ _).mpr
  simp [code,h]

/-- An internal vertical edge joins its left and right neighbouring intervals. -/
theorem internal_edge (P : Parameters) (p : ℕ) (hp : p < 2)
    (t : ZMod P.m) (i : Fin P.n) (h : ¬ cup p i)
    (hl : i.val ≠ 0) (hr : i.val + 1 < P.n) :
    edgeEnds P p t i =
      (circle P p (t,predIndex i hl,.bl),circle P p (t - 1,succIndex i hr,.bl)) := by
  have hpv := notcup_pred P p hp i hl h
  have hsv := notcup_succ P p hp i hr h
  simp only [edgeEnds,h,↓reduceIte,Prod.mk.injEq]
  constructor <;> apply (circle_eq_iff P p hp _ _).mpr <;>
    simp only [code,h,hpv,hsv,↓reduceIte] <;>
    simp [hl,hr,predIndex,succIndex] <;> omega

/-- The left boundary edge is incident to the actual unpaired left circle. -/
theorem left_edge (P : Parameters) (p : ℕ) (hp : p < 2)
    (t : ZMod P.m) (h : ¬ cup p (first P)) :
    edgeEnds P p t (first P) =
      (circle P p (0,first P,.tl),
       circle P p (t - 1,succIndex (first P) (by dsimp [first]; have := P.hn; omega),.bl)) := by
  have hi : (first P).val + 1 < P.n := by dsimp [first]; have := P.hn; omega
  have hsv := notcup_succ P p hp (first P) hi h
  simp only [edgeEnds,h,↓reduceIte,Prod.mk.injEq]
  constructor <;> apply (circle_eq_iff P p hp _ _).mpr <;>
    simp only [code,h,hsv,↓reduceIte] <;>
    simp [first,succIndex,hi,show 1 < P.n by have := P.hn; omega]

/-- The right boundary edge is incident to the actual unpaired right circle. -/
theorem right_edge (P : Parameters) (p : ℕ) (hp : p < 2)
    (t : ZMod P.m) (h : ¬ cup p (last P)) :
    edgeEnds P p t (last P) =
      (circle P p (t,predIndex (last P) (by dsimp [last]; have := P.hn; omega),.bl),
       circle P p (0,last P,.tr)) := by
  have hl : (last P).val ≠ 0 := by dsimp [last]; have := P.hn; omega
  have hr : ¬ (last P).val + 1 < P.n := by dsimp [last]; have := P.hn; omega
  have hpv := notcup_pred P p hp (last P) hl h
  simp only [edgeEnds,h,↓reduceIte,Prod.mk.injEq]
  constructor <;> apply (circle_eq_iff P p hp _ _).mpr <;>
    simp only [code,h,hpv,↓reduceIte] <;>
    simp [hl,hr,predIndex] <;> have := P.hn <;> dsimp [last] <;> omega

/-- The two actual endpoint classes of every crossing are distinct. -/
theorem edge_endpoints_distinct (P : Parameters) (p : ℕ) (hp : p < 2)
    (t : ZMod P.m) (i : Fin P.n) :
    (edgeEnds P p t i).1 ≠ (edgeEnds P p t i).2 := by
  by_cases h : cup p i
  · simp only [edgeEnds,h,↓reduceIte,ne_eq]
    rw [circle_eq_iff P p hp]
    simp only [code,h,↓reduceIte,Prod.mk.injEq,true_and]
    intro ht
    have he : (1 : ZMod P.m) = 0 := by linear_combination -ht
    have hm := P.hm
    have : P.m ∣ 1 := (ZMod.natCast_eq_zero_iff 1 P.m).mp (by simpa using he)
    have := Nat.le_of_dvd (by omega : 0 < 1) this
    omega
  · simp only [edgeEnds,h,↓reduceIte,ne_eq]
    rw [circle_eq_iff P p hp]
    simp only [code,h,↓reduceIte]
    split_ifs <;> simp only [Prod.mk.injEq] <;> intro hh <;>
      have := i.isLt <;> have := P.hn <;> omega

/-- Periods are ordered first, then the zero - based printed generator order. -/
def before {P : Parameters} (a b : ℕ × Fin P.n) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)

/-- A strand position p meets exactly generators p - 1 and p when present. -/
def incident {n : ℕ} (position : ℕ) (i : Fin n) : Prop :=
  i.val = position ∨ i.val + 1 = position

/-- Successor occurrence before passing to cyclic time. -/
def chronologicalNext (P : Parameters) (q : ℕ) (i : Fin P.n) (right : Bool) :
    ℕ × Fin P.n × Port :=
  if right then
    if h : i.val + 1 < P.n then (q,succIndex i h,.tl) else (q + 1,i,.tr)
  else if h : i.val = 0 then (q + 1,i,.tl) else (q + 1,predIndex i h,.tr)

/-- The external matching is the cyclic reduction of the chronologically next
crossing incident to the same strand position. There is no intervening occurrence. -/
theorem external_chronological (P : Parameters) (q : ℕ) (i : Fin P.n) (right : Bool) :
    let y := chronologicalNext P q i right
    let position := i.val + if right then 1 else 0
    (y.2.2 = .tl ∨ y.2.2 = .tr) ∧
    (y.2.1.val + if y.2.2 = .tr then 1 else 0) = position ∧
    before (P := P) (q,i) (y.1,y.2.1) ∧
    (∀ (s : ℕ) (j : Fin P.n), incident position j →
      before (P := P) (q,i) (s,j) → ¬ before (P := P) (s,j) (y.1,y.2.1)) ∧
    external P ((q : ZMod P.m),i,if right then .br else .bl) =
      ((y.1 : ZMod P.m),y.2.1,y.2.2) := by
  have hi := i.isLt
  cases right <;> simp only [chronologicalNext,Bool.false_eq_true,↓reduceIte] <;>
    split_ifs <;> simp_all [external,before,incident,predIndex,succIndex,Nat.cast_add] <;>
    intros <;> try omega
  all_goals
    constructor
    · omega
    · intro s j hj hbefore
      constructor
      · omega
      · intro hs
        omega

end D5.S3.Topology.WeavingDiagramPorts

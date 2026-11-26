/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonStateActions
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonStateActions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct genuine componentwise signed bouquet charts and exact flag switch actions. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Perm.Cycle.Factors
import D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Function.Basic
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Quotient
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Dimension.Constructions

import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonFlagGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonStateActions
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonFlagGeometry

section RibbonComponents

open Relation Finset
open scoped BigOperators

variable {C : Type*} {X E : C→Type*}

inductive inComponent (r : ∀ c, X c→X c→Prop) : Sigma X→Sigma X→Prop
  | mk (c : C) (x y : X c) (h : r c x y) : inComponent r ⟨c,x⟩ ⟨c,y⟩
def relSetoid {Y : Type*} (r : Y→Y→Prop) : Setoid Y :=
  ⟨EqvGen r, ⟨.refl,fun h=>.symm _ _ h,fun h g=>.trans _ _ _ h g⟩⟩

private def label (r : ∀ c, X c→X c→Prop) (x : Sigma X) :
    Sigma (fun c=>Quotient (relSetoid (r c))) := ⟨x.1,Quotient.mk _ x.2⟩

private theorem lift_component_path (r : ∀ c, X c→X c→Prop)
    (c:C) {x y:X c} (h:EqvGen (r c) x y) :
    EqvGen (inComponent r) ⟨c,x⟩ ⟨c,y⟩ := by
  induction h with
  | rel x y h => exact .rel _ _ (.mk c x y h)
  | refl x => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem component_path_iff (r : ∀ c, X c→X c→Prop) (x y : Sigma X) :
    EqvGen (inComponent r) x y ↔ label r x=label r y := by
  constructor
  · intro h
    induction h with
    | rel x y h =>
      cases h with
      | mk c a b h =>
        exact congrArg (Sigma.mk c) (Quotient.sound (.rel a b h : EqvGen (r c) a b))
    | refl x => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · rcases x with ⟨i,x⟩; rcases y with ⟨j,y⟩
    intro h
    have hij : i=j := congrArg Sigma.fst h
    subst j
    have hc : Quotient.mk (relSetoid (r i)) x=Quotient.mk (relSetoid (r i)) y := by
      injection h
    exact lift_component_path r i (Quotient.exact hc)

/-- Boundary components themselves decompose, before taking cardinalities. -/
noncomputable def quotient_components (r : ∀ c, X c→X c→Prop) :
    Quotient (relSetoid (inComponent r)) ≃ Sigma (fun c=>Quotient (relSetoid (r c))) := by
  let f : Quotient (relSetoid (inComponent r)) → Sigma (fun c=>Quotient (relSetoid (r c))) :=
    Quotient.lift (label r) (fun x y h=>(component_path_iff r x y).mp h)
  apply Equiv.ofBijective f
  constructor
  · intro a b
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        intro h
        exact Quotient.sound ((component_path_iff r a b).mpr h)
  · rintro ⟨c,q⟩
    induction q using Quotient.inductionOn with
    | h z => exact ⟨Quotient.mk _ ⟨c,z⟩,rfl⟩

variable [Fintype C] [∀ c,Fintype (X c)] [∀ c,Fintype (E c)]
variable {R : Type*} [CommSemiring R] [DecidableEq C] [∀ c,DecidableEq (E c)]

end RibbonComponents

section MarkedPorts

open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary

variable {X E : Type*}

def portIndex {G A : X→X} (C : AlternatingFlagChart G A) (x : X) : D C.n :=
  (C.chart.symm x).1

private theorem portIndex_iff {G A : X→X} (C : AlternatingFlagChart G A)
    (hA : Function.Involutive A) (x y:X) :
    portIndex C x = portIndex C y ↔ x=y ∨ A x=y := by
  obtain ⟨⟨i,s⟩,rfl⟩ := C.chart.surjective x
  obtain ⟨⟨j,t⟩,rfl⟩ := C.chart.surjective y
  have h (i:D C.n) : A (C.chart (outFlag i)) = C.chart (inFlag i) := by
    rw [← C.base i,hA]
  constructor
  · intro he
    simp only [portIndex,Equiv.symm_apply_apply] at he
    subst j
    cases s <;> cases t
    · exact .inl rfl
    · exact .inr (C.base i)
    · exact .inr (h i)
    · exact .inl rfl
  · rintro (he|he)
    · simp only [portIndex,Equiv.symm_apply_apply]
      exact congrArg Prod.fst (C.chart.injective he)
    · cases s with
      | false =>
        change A (C.chart (inFlag i))=C.chart (j,t) at he
        rw [C.base] at he
        simp only [portIndex,Equiv.symm_apply_apply]
        exact congrArg Prod.fst (C.chart.injective he)
      | true =>
        change A (C.chart (outFlag i))=C.chart (j,t) at he
        rw [h] at he
        simp only [portIndex,Equiv.symm_apply_apply]
        exact congrArg Prod.fst (C.chart.injective he)

structure OrderedPortLabels (E : Type*) (n : ℕ) where
  a : E→D n
  b : E→D n
  a_inj : Function.Injective a
  b_inj : Function.Injective b
  separate : ∀ e f, a e≠b f
  ordered : ∀ e,(a e).val < (b e).val

/-- Two distinct marked matching ports per edge can be canonically
ordered, with no external endpoint-label table. -/
noncomputable def order_marked_ports {G A : X→X} (C : AlternatingFlagChart G A)
    (hA : Function.Involutive A) (p : E×Bool→X)
    (hdis : ∀ f g : E×Bool, p f=p g ∨ A (p f)=p g → f=g) :
    OrderedPortLabels E C.n := by
  let q (x:E×Bool) := portIndex C (p x)
  have hq : Function.Injective q := fun f g h=>hdis f g ((portIndex_iff C hA _ _).mp h)
  let flip (e:E) : Bool := decide (q (e,true) < q (e,false))
  let a (e:E) := q (e,flip e)
  let b (e:E) := q (e,!(flip e))
  refine ⟨a,b,?_,?_,?_,?_⟩
  · intro e f h
    exact congrArg Prod.fst (hq h)
  · intro e f h
    exact congrArg Prod.fst (hq h)
  · intro e f h
    have he : (e,flip e)=(f,!(flip f)) := hq h
    have hef : e=f := congrArg Prod.fst he
    subst f
    have hc : flip e = !(flip e) := congrArg Prod.snd he
    cases hh : flip e <;> simp [hh] at hc
  · intro e
    change a e < b e
    by_cases h : q (e,true) < q (e,false)
    · simpa [a,b,flip,h] using h
    · have hne : q (e,false)≠q (e,true) := by
        intro he
        have hx := congrArg Prod.snd (hq he)
        contradiction
      have hl := lt_of_le_of_ne (le_of_not_gt h) hne
      simpa [a,b,flip,h] using hl

private theorem signed_chart_of_local_switch [Fintype X] [DecidableEq X] {G A : X→X} (C : AlternatingFlagChart G A)
    (i j : D C.n) (b : X→X) (hb : Function.Involutive b)
    (h1 : portIndex C (b (C.chart (inFlag i)))=j)
    (h2 : portIndex C (b (C.chart (outFlag i)))=j) :
    ∃ t : Bool,
      b (C.chart (inFlag i))=C.chart (if t then inFlag j else outFlag j) ∧
      b (C.chart (outFlag i))=C.chart (if t then outFlag j else inFlag j) := by
  have port (z:X) (hz:portIndex C z=j) :
      z=C.chart (inFlag j) ∨ z=C.chart (outFlag j) := by
    obtain ⟨⟨k,s⟩,rfl⟩ := C.chart.surjective z
    simp only [portIndex,Equiv.symm_apply_apply] at hz
    subst k
    cases s
    · exact .inl rfl
    · exact .inr rfl
  exact signed_alternative_from_chart G A C i j b hb (port _ h1) (port _ h2)

end MarkedPorts

section MarkedSwitchAction

open Relation

variable {E X : Type*} [DecidableEq X]

abbrev BandFlag (E : Type*) := E × Bool × Bool

/-- Indicator false pairs the two flags at the same port; true changes
ports with the prescribed twist. Both choices are literal involutions. -/
def bandCode (τ s : Bool) (q : Bool×Bool) : Bool×Bool :=
  if s then (!q.1,q.2 ^^ τ) else (q.1,!q.2)

private theorem bandCode_inv (τ s : Bool) : Function.Involutive (bandCode τ s) := by
  rintro ⟨a,b⟩
  cases τ <;> cases s <;> cases a <;> cases b <;> rfl

private theorem bandCode_free (τ s : Bool) (q : Bool×Bool) : bandCode τ s q ≠ q := by
  rcases q with ⟨a,b⟩
  cases τ <;> cases s <;> cases a <;> cases b <;> decide
/-- The action of a binary assignment on globally disjoint marked flags.
The gap is independent and the unmarked cap involution is unaltered. -/
noncomputable def markedAction (A : X→X) (mark : BandFlag E→X)
    (t s : E→Bool) (x:X) : X := by
  classical
  exact if h : ∃ q, mark q=x then
    let q:=Classical.choose h
    mark (q.1,bandCode (t q.1) (s q.1) q.2)
  else A x

theorem markedAction_apply_mark (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t s : E→Bool) (q:BandFlag E) :
    markedAction A mark t s (mark q) = mark (q.1,bandCode (t q.1) (s q.1) q.2) := by
  classical
  unfold markedAction
  split
  · rename_i h
    have hh := hm (Classical.choose_spec h)
    rw [hh]
  · rename_i h
    exact (h ⟨q,rfl⟩).elim

theorem markedAction_apply_unmarked (A : X→X) (mark : BandFlag E→X)
    (t s : E→Bool) (x:X) (hx : ¬∃ q,mark q=x) :
    markedAction A mark t s x=A x := by
  classical
  unfold markedAction
  exact dif_neg hx

/-- Any state is an honest matching, including simultaneous switches on
all bands, without any order dependence. -/
theorem markedAction_match (A : X→X) (mark : BandFlag E→X)
    (hA : Function.Involutive A) (hAf : ∀ x,A x≠x) (hm : Function.Injective mark)
    (h0 : ∀ q, A (mark q)=mark (q.1,bandCode false false q.2))
    (t s : E→Bool) :
    Function.Involutive (markedAction A mark t s) ∧
      ∀ x, markedAction A mark t s x≠x := by
  classical
  constructor
  · intro x
    by_cases he : ∃ q,mark q=x
    · obtain ⟨q,rfl⟩ := he
      rw [markedAction_apply_mark _ _ hm,markedAction_apply_mark _ _ hm]
      exact congrArg (fun v=>mark (q.1,v)) (bandCode_inv (t q.1) (s q.1) q.2)
    · have ha : ¬∃ q, mark q=A x := by
        rintro ⟨q,hq⟩
        apply he
        use (q.1,bandCode false false q.2)
        rw [← h0 q,hq,hA]
      rw [markedAction_apply_unmarked _ _ _ _ _ he,markedAction_apply_unmarked _ _ _ _ _ ha,hA]
  · intro x
    by_cases he : ∃ q,mark q=x
    · obtain ⟨q,rfl⟩ := he
      rw [markedAction_apply_mark _ _ hm]
      intro h
      exact bandCode_free (t q.1) (s q.1) q.2 (congrArg Prod.snd (hm h))
    · rw [markedAction_apply_unmarked _ _ _ _ _ he]
      exact hAf x

/-- Post-dual representatives of the two ports of a band. If the base
choice crosses ports, use the two flags on its original left port. -/
def statePortRep (s : E→Bool) (x : E×Bool) : BandFlag E :=
  if s x.1 then (x.1,false,x.2) else (x.1,x.2,false)

private theorem statePortRep_inj (s : E→Bool) : Function.Injective (statePortRep s) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  have hh : e=f := by
    have hx := congrArg Prod.fst h
    simpa [statePortRep,apply_ite] using hx
  subst f
  by_cases hs : s e=true
  · simpa [statePortRep,hs] using h
  · simpa [statePortRep,hs] using h

/-- These chosen representations are globally distinct even as matching
ports, including edges that became loops after taking the forest. -/
private theorem statePortRep_disjoint (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t s : E→Bool) :
    ∀ f g : E×Bool,
      mark (statePortRep s f) = mark (statePortRep s g) ∨
      markedAction A mark t s (mark (statePortRep s f)) = mark (statePortRep s g) → f=g := by
  rintro ⟨e,b⟩ ⟨f,c⟩ (h|h)
  · exact statePortRep_inj s (hm h)
  · rw [markedAction_apply_mark _ _ hm] at h
    have h := hm h
    have he : e=f := by
      have hh := congrArg Prod.fst h
      simpa [statePortRep,apply_ite] using hh
    subst f
    cases ht : t e <;> cases hs : s e <;> cases b <;> cases c <;>
      simp [statePortRep,ht,hs,bandCode] at h

end MarkedSwitchAction

section MarkedForest

open Relation
variable {E X : Type*} [Fintype X] [DecidableEq X] [DecidableEq E]

def bandEnds (mark : BandFlag E→X) (e:E) : X×X :=
  (mark (e,false,false),mark (e,true,false))

private theorem marked_on_onestate (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t s : E→Bool) (e:E) (a b : Bool) :
    markedAction A mark t (Function.update s e true) (mark (e,a,b)) =
      mark (e,!a,b ^^ t e) := by
  rw [markedAction_apply_mark _ _ hm]
  simp [bandCode]

private theorem marked_off_onestate (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t s : E→Bool) (e:E) (h:s e=false) (a b : Bool) :
    markedAction A mark t s (mark (e,a,b)) = mark (e,a,!b) := by
  rw [markedAction_apply_mark _ _ hm]
  simp [bandCode,h]

/-- Switching one not-yet-selected genuine band merges exactly the
classes specified by its physical endpoint flags. -/
private theorem marked_band_join (G A : X→X) (hG : Function.Involutive G)
    (hGf : ∀ x,G x≠x) (hA : Function.Involutive A) (hAf : ∀ x,A x≠x)
    (mark : BandFlag E→X) (hm : Function.Injective mark)
    (h0 : ∀ q, A (mark q)=mark (q.1,bandCode false false q.2))
    (t s : E→Bool) (e:E) (he:s e=false)
    (hsep : ¬wholeConn G (markedAction A mark t s) (bandEnds mark e).1 (bandEnds mark e).2)
    (x y:X) :
    wholeConn G (markedAction A mark t (Function.update s e true)) x y ↔
      addedJoin (wholeConn G (markedAction A mark t s)) (bandEnds mark e).1 (bandEnds mark e).2 x y := by
  let a := (bandEnds mark e).1
  let b := (bandEnds mark e).2
  let L := markedAction A mark t s
  let M := markedAction A mark t (Function.update s e true)
  have hLa : L a=mark (e,false,true) := marked_off_onestate _ _ hm _ _ _ he false false
  have hLb : L b=mark (e,true,true) := marked_off_onestate _ _ hm _ _ _ he true false
  have hL := markedAction_match A mark hA hAf hm h0 t s
  apply match_switch_join G L M hG hL.1 hGf hL.2 a b hsep _ _ _ x y
  · intro z hz
    obtain ⟨q,rfl⟩ | hu := em (∃ q,mark q=z)
    · rcases q with ⟨f,i,j⟩
      have hfe : f≠e := by
        intro h
        subst f
        apply hz
        rw [hLa,hLb]
        cases i <;> cases j
        · exact .inl rfl
        · exact .inr (.inl rfl)
        · exact .inr (.inr (.inl rfl))
        · exact .inr (.inr (.inr rfl))
      dsimp [L,M]
      rw [markedAction_apply_mark _ _ hm,markedAction_apply_mark _ _ hm]
      simp [Function.update_of_ne hfe]
    · dsimp [L,M]
      rw [markedAction_apply_unmarked _ _ _ _ _ hu, markedAction_apply_unmarked _ _ _ _ _ hu]
  · intro z hz
    rw [hLa] at hz
    rw [hLb]
    rcases hz with rfl|rfl
    · change M (mark (e,false,false)) = b ∨ M (mark (e,false,false)) = _
      dsimp only [M]
      rw [marked_on_onestate _ _ hm]
      cases h : t e
      · exact .inl rfl
      · exact .inr rfl
    · change M (mark (e,false,true)) = b ∨ M (mark (e,false,true)) = _
      dsimp only [M]
      rw [marked_on_onestate _ _ hm]
      cases h : t e
      · exact .inr rfl
      · exact .inl rfl
  · intro z hz
    rw [hLb] at hz
    rw [hLa]
    rcases hz with rfl|rfl
    · change M (mark (e,true,false)) = a ∨ M (mark (e,true,false)) = _
      dsimp only [M]
      rw [marked_on_onestate _ _ hm]
      cases h : t e
      · exact .inl rfl
      · exact .inr rfl
    · change M (mark (e,true,true)) = a ∨ M (mark (e,true,true)) = _
      dsimp only [M]
      rw [marked_on_onestate _ _ hm]
      cases h : t e
      · exact .inr rfl
      · exact .inl rfl

/-- Greedy forest realization on the actual binary state function of
the disjoint marked ribbon, not merely on an existential permutation. -/
theorem marked_forest_state (G A : X→X) (hG : Function.Involutive G)
    (hGf : ∀ x,G x≠x) (hA : Function.Involutive A) (hAf : ∀ x,A x≠x)
    (mark : BandFlag E→X) (hm : Function.Injective mark)
    (h0 : ∀ q, A (mark q)=mark (q.1,bandCode false false q.2))
    (t s : E→Bool) (l : List E) (hn:l.Nodup) (hf:∀ e∈l,s e=false) :
    ∃ s' : E→Bool, (∀ e, e∉l → s' e = s e) ∧
      ∀ x y, wholeConn G (markedAction A mark t s') x y ↔
        graphJoin (wholeConn G (markedAction A mark t s)) (l.map (bandEnds mark)) x y := by
  classical
  induction l generalizing s with
  | nil =>
    refine ⟨s,fun _ _=>rfl,fun x y=>⟨fun h=>.rel _ _ (.inl h),?_⟩⟩
    apply eqvGen_transfer _ (eqvGen_is_equivalence _)
    intro i j h
    exact h.elim id (fun hh=>(List.not_mem_nil hh).elim)
  | cons e l ih =>
    let R := wholeConn G (markedAction A mark t s)
    let a := (bandEnds mark e).1
    let b := (bandEnds mark e).2
    have he := (List.nodup_cons.mp hn).1
    have hn' := (List.nodup_cons.mp hn).2
    have hrest : ∀ f∈l,s f=false := fun f h=>hf f (List.mem_cons_of_mem _ h)
    have hg (x y:X) := graphJoin_cons R a b (l.map (bandEnds mark)) x y
    by_cases hc : R a b
    · obtain ⟨s',hs',hw⟩ := ih s hn' hrest
      let eqR : Equivalence R := eqvGen_is_equivalence _
      have hsame (i j:X) : R i j ↔ addedJoin R a b i j := by
        refine ⟨fun h=>.rel _ _ (.inl h),?_⟩
        apply eqvGen_transfer _ eqR
        intro i j h
        rcases h with h|⟨rfl,rfl⟩
        · exact h
        · exact hc
      exact ⟨s',fun f h=>hs' f (fun hm=>h (List.mem_cons_of_mem _ hm)),fun x y=>
        (hw x y).trans ((graphJoin_congr hsame (l.map (bandEnds mark)) x y).trans (hg x y))⟩
    · let S := Function.update s e true
      have hrest' (f:E) (hfl:f∈l) : S f=false := by
        have hne : f≠e := fun h=>he (h ▸ hfl)
        simp [S,Function.update_of_ne hne,hrest f hfl]
      obtain ⟨s',hs',hw⟩ := ih S hn' hrest'
      have hstep (i j:X) : wholeConn G (markedAction A mark t S) i j ↔ addedJoin R a b i j :=
        marked_band_join G A hG hGf hA hAf mark hm h0 t s e (hf e (List.mem_cons_self ..)) hc i j
      refine ⟨s',?_,fun x y=>(hw x y).trans
        ((graphJoin_congr hstep (l.map (bandEnds mark)) x y).trans (hg x y))⟩
      intro f h
      have hne : f≠e := fun he=>h (he ▸ List.mem_cons_self ..)
      have hnmem : f∉l := fun hm=>h (List.mem_cons_of_mem _ hm)
      simp [hs' f hnmem,S,Function.update_of_ne hne]

end MarkedForest

section MarkedBouquet

open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open Relation

variable {E X : Type*} [Fintype X] [DecidableEq X]

def postSlot (t s : Bool) (q:Bool×Bool) : Bool :=
  if s then q.2 ^^ (q.1 && t) else q.1
private theorem postSlot_opposite (t s : Bool) (q:Bool×Bool) :
    postSlot t s (bandCode t (!s) q) = !(postSlot t s q) := by
  rcases q with ⟨a,b⟩
  cases t <;> cases s <;> cases a <;> cases b <;> rfl

private theorem mark_index_from_slot (G A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t s : E→Bool)
    (C : AlternatingFlagChart G (markedAction A mark t s))
    (hA : Function.Involutive (markedAction A mark t s))
    (e:E) (q:Bool×Bool) :
    portIndex C (mark (e,q)) =
      portIndex C (mark (statePortRep s (e,postSlot (t e) (s e) q))) := by
  apply (portIndex_iff C hA _ _).mpr
  rw [markedAction_apply_mark _ _ hm]
  rcases q with ⟨a,b⟩
  cases hs : s e <;> cases ht : t e <;> cases a <;> cases b <;>
    simp [bandCode,postSlot,statePortRep,hs,ht]

private theorem order_marked_ports_witness {G A : X→X} (C : AlternatingFlagChart G A)
    (hA : Function.Involutive A) (p : E×Bool→X)
    (hdis : ∀ f g : E×Bool, p f=p g ∨ A (p f)=p g → f=g) :
    ∀ e, ∃ k : Bool,
       (order_marked_ports C hA p hdis).a e = portIndex C (p (e,k)) ∧
       (order_marked_ports C hA p hdis).b e = portIndex C (p (e,!k)) := by
  intro e
  exact ⟨decide (portIndex C (p (e,true)) < portIndex C (p (e,false))),rfl,rfl⟩

structure SignedMarkedChart (G A : X→X) (alt : X→X) (E : Type*) (support : E→X→Prop) where
  C : AlternatingFlagChart G A
  ports : OrderedPortLabels E C.n
  twist : E → Bool
  membership : ∀ e x, support e x ↔ portIndex C x = ports.a e ∨ portIndex C x = ports.b e
  in_alternative : ∀ e,
    alt (C.chart (inFlag (ports.a e))) =
    C.chart (if twist e then inFlag (ports.b e) else outFlag (ports.b e))
  out_alternative : ∀ e,
    alt (C.chart (outFlag (ports.a e))) =
    C.chart (if twist e then outFlag (ports.b e) else inFlag (ports.b e))

/-- Actual toggling of each band is a canonical signed pairing in the
constructed chart, regardless of original orientations or the forest
edges that were selected. -/
noncomputable def canonical_marked_signed_chart
    (G A : X→X) (hA : Function.Involutive A) (hAf : ∀ x,A x≠x)
    (mark : BandFlag E→X) (hm : Function.Injective mark)
    (h0 : ∀ q, A (mark q)=mark (q.1,bandCode false false q.2))
    (t s : E→Bool) (C : AlternatingFlagChart G (markedAction A mark t s)) :
    SignedMarkedChart G (markedAction A mark t s) (markedAction A mark t (fun e=>!(s e))) E (fun e x=>∃ q:Bool×Bool, x=mark (e,q)) := by
  classical
  let B := markedAction A mark t s
  let B' := markedAction A mark t (fun e=>!(s e))
  have hi : Function.Involutive B := (markedAction_match A mark hA hAf hm h0 t s).1
  have hi' : Function.Involutive B' := (markedAction_match A mark hA hAf hm h0 t _).1
  let p : E×Bool→X := fun f=>mark (statePortRep s f)
  let D := order_marked_ports C hi p (statePortRep_disjoint A mark hm t s)
  have exists_of_port (e:E) (k:Bool) (z:X)
      (hn : portIndex C (p (e,k)) = portIndex C z) :
      ∃ q : Bool×Bool, z=mark (e,q) := by
    have hh := (portIndex_iff C hi _ _).mp hn
    change p (e,k)=z ∨ B (p (e,k))=z at hh
    rcases hh with hh|hh
    · use (statePortRep s (e,k)).2
      have he : (statePortRep s (e,k)).1=e := by simp [statePortRep,apply_ite]
      have hp : p (e,k)=mark (e,(statePortRep s (e,k)).2) := by
        dsimp [p]
        congr 1
        exact Prod.ext he rfl
      exact hh.symm.trans hp
    · dsimp [p,B] at hh
      rw [markedAction_apply_mark _ _ hm] at hh
      have he : (statePortRep s (e,k)).1=e := by simp [statePortRep,apply_ite]
      use bandCode (t (statePortRep s (e,k)).1) (s (statePortRep s (e,k)).1) (statePortRep s (e,k)).2
      exact hh.symm.trans (congrArg mark (Prod.ext he rfl))
  have membership (e:E) (z:X) :
      (∃ q:Bool×Bool,z=mark (e,q)) ↔ portIndex C z=D.a e ∨ portIndex C z=D.b e := by
    obtain ⟨k,ha,hb⟩ := order_marked_ports_witness C hi p (statePortRep_disjoint A mark hm t s) e
    change D.a e = _ at ha
    change D.b e = _ at hb
    rw [ha,hb]
    constructor
    · rintro ⟨q,rfl⟩
      have hq := mark_index_from_slot G A mark hm t s C hi e q
      cases hk : k <;> cases hh : postSlot (t e) (s e) q <;>
        simp only [hh,hk,Bool.not_false,Bool.not_true] at hq ⊢
      · exact .inl hq
      · exact .inr hq
      · exact .inr hq
      · exact .inl hq
    · rintro (hh|hh)
      · exact exists_of_port e k z hh.symm
      · exact exists_of_port e (!k) z hh.symm
  have hiAlt (e:E) (j:Bool) : portIndex C (B' (C.chart (D.a e,j))) = D.b e := by
    obtain ⟨k,hka,hkb⟩ := order_marked_ports_witness C hi p (statePortRep_disjoint A mark hm t s) e
    change D.a e = _ at hka
    change D.b e = _ at hkb
    let z := C.chart (D.a e,j)
    have hz : portIndex C (p (e,k)) = portIndex C z := by
      rw [← hka]
      simp [z,portIndex]
    have hmz := exists_of_port e k z hz
    obtain ⟨q,hq⟩ := hmz
    let u := postSlot (t e) (s e) q
    have hu : u=k := by
      have h1 : portIndex C (p (e,u)) = portIndex C (p (e,k)) := by
        change portIndex C (mark (statePortRep s (e,u))) = _
        rw [← mark_index_from_slot G A mark hm t s C hi e q,← hq]
        exact hz.symm
      have he := statePortRep_disjoint A mark hm t s (e,u) (e,k)
        ((portIndex_iff C hi _ _).mp h1)
      exact congrArg Prod.snd he
    change portIndex C (B' z) = D.b e
    rw [hq, show B' (mark (e,q)) = mark (e,bandCode (t e) (!(s e)) q)
      from markedAction_apply_mark _ _ hm _ _ (e,q)]
    rw [mark_index_from_slot G A mark hm t s C hi,postSlot_opposite]
    change portIndex C (p (e,!u))=D.b e
    rw [hu,← hkb]
  have H (e:E) := signed_chart_of_local_switch C (D.a e) (D.b e) B' hi'
    (hiAlt e false) (hiAlt e true)
  exact ⟨C,D,fun e=>Classical.choose (H e),membership,fun e=>(Classical.choose_spec (H e)).1,
    fun e=>(Classical.choose_spec (H e)).2⟩

end MarkedBouquet

section FlagMatchingEqv

open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open Relation

variable {E X : Type*} [Fintype X] [DecidableEq X]

private theorem cyclicNext_surj (n:ℕ) : Function.Surjective (@cyclicNext n) := by
  intro i
  by_cases h : i.val=0
  · refine ⟨⟨n,Nat.lt_succ_self _⟩,Fin.ext ?_⟩
    change (n+1)%(n+1)=i.val
    simp [h]
  · refine ⟨⟨i.val-1,Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩,Fin.ext ?_⟩
    change (i.val-1+1)%(n+1)=i.val
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h),Nat.mod_eq_of_lt i.isLt]

private theorem map_eqv {Y Z : Type*} {R : Y→Y→Prop} {S : Z→Z→Prop} (f : Y→Z)
    (h : ∀ x y,R x y→EqvGen S (f x) (f y)) {x y:Y} (hxy:EqvGen R x y) :
    EqvGen S (f x) (f y) := by
  induction hxy with
  | rel x y hr => exact h x y hr
  | refl x => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Direct exact action-to-boundary equivalence; every cap, gap or
physical switched band is carried through the actual extraction chart. -/
theorem matching_is_literal_boundary (G B F : X→X) (hG : Function.Involutive G)
    (hF : Function.Involutive F) (C : AlternatingFlagChart G B)
    (a b : E→D C.n) (t:E→Bool)
    (cap : ∀ i, (∀ e,a e≠i) → (∀ e,b e≠i) → F (C.chart (inFlag i))=C.chart (outFlag i))
    (hI : ∀ e,F (C.chart (inFlag (a e)))=C.chart (if t e then inFlag (b e) else outFlag (b e)))
    (hO : ∀ e,F (C.chart (outFlag (a e)))=C.chart (if t e then outFlag (b e) else inFlag (b e)))
    (x y : Flag C.n) :
    wholeConn G F (C.chart x) (C.chart y) ↔ EqvGen (FlagLink a b t) x y := by
  have arc (i:D C.n) : EqvGen (FlagLink a b t) (outFlag i) (inFlag (cyclicNext i)) :=
    .rel _ _ (.arc _)
  have lI (e:E) : EqvGen (FlagLink a b t) (inFlag (a e)) (if t e then inFlag (b e) else outFlag (b e)) := by
    cases h:t e
    · exact .symm _ _ (.rel _ _ (.crossB _ h))
    · exact .rel _ _ (.twistIn _ h)
  have lO (e:E) : EqvGen (FlagLink a b t) (outFlag (a e)) (if t e then outFlag (b e) else inFlag (b e)) := by
    cases h:t e
    · exact .rel _ _ (.crossA _ h)
    · exact .rel _ _ (.twistOut _ h)
  have hg (x:Flag C.n) : EqvGen (FlagLink a b t) x (C.chart.symm (G (C.chart x))) := by
    rcases x with ⟨i,c⟩
    cases c
    · obtain ⟨j,hj⟩ := cyclicNext_surj C.n i
      have he := congrArg G (C.gap j)
      rw [hG,hj] at he
      change EqvGen (FlagLink a b t) (inFlag i) (C.chart.symm (G (C.chart (inFlag i))))
      rw [← he,Equiv.symm_apply_apply,← hj]
      exact .symm _ _ (arc _)
    · change EqvGen (FlagLink a b t) (outFlag i) (C.chart.symm (G (C.chart (outFlag i))))
      rw [C.gap,Equiv.symm_apply_apply]
      exact arc _
  have hf (x:Flag C.n) : EqvGen (FlagLink a b t) x (C.chart.symm (F (C.chart x))) := by
    rcases x with ⟨i,c⟩
    by_cases hL : ∃ e, a e=i
    · obtain ⟨e,rfl⟩ := hL
      cases c
      · change EqvGen (FlagLink a b t) (inFlag (a e)) (C.chart.symm (F (C.chart (inFlag (a e)))))
        rw [hI,Equiv.symm_apply_apply]
        exact lI _
      · change EqvGen (FlagLink a b t) (outFlag (a e)) (C.chart.symm (F (C.chart (outFlag (a e)))))
        rw [hO,Equiv.symm_apply_apply]
        exact lO _
    · by_cases hR : ∃ e, b e=i
      · obtain ⟨e,rfl⟩ := hR
        have qI := congrArg F (hI e)
        have qO := congrArg F (hO e)
        rw [hF] at qI qO
        cases ht : t e <;> simp only [ht, Bool.false_eq_true, if_false, if_true] at qI qO
        · cases c
          · change EqvGen (FlagLink a b t) (inFlag (b e)) (C.chart.symm (F (C.chart (inFlag (b e)))))
            rw [← qO,Equiv.symm_apply_apply]
            exact .symm _ _ (.rel _ _ (.crossA _ ht))
          · change EqvGen (FlagLink a b t) (outFlag (b e)) (C.chart.symm (F (C.chart (outFlag (b e)))))
            rw [← qI,Equiv.symm_apply_apply]
            exact .rel _ _ (.crossB _ ht)
        · cases c
          · change EqvGen (FlagLink a b t) (inFlag (b e)) (C.chart.symm (F (C.chart (inFlag (b e)))))
            rw [← qI,Equiv.symm_apply_apply]
            exact .symm _ _ (.rel _ _ (.twistIn _ ht))
          · change EqvGen (FlagLink a b t) (outFlag (b e)) (C.chart.symm (F (C.chart (outFlag (b e)))))
            rw [← qO,Equiv.symm_apply_apply]
            exact .symm _ _ (.rel _ _ (.twistOut _ ht))
      · have hcap := cap i (fun e h=>hL ⟨e,h⟩) (fun e h=>hR ⟨e,h⟩)
        have forward : EqvGen (FlagLink a b t) (outFlag i) (inFlag i) :=
          .rel _ _ (.cap i (fun e h=>hL ⟨e,h⟩) (fun e h=>hR ⟨e,h⟩))
        cases c
        · change EqvGen (FlagLink a b t) (inFlag i) (C.chart.symm (F (C.chart (inFlag i))))
          rw [hcap,Equiv.symm_apply_apply]
          exact .symm _ _ forward
        · have hrev := congrArg F hcap
          rw [hF] at hrev
          change EqvGen (FlagLink a b t) (outFlag i) (C.chart.symm (F (C.chart (outFlag i))))
          rw [← hrev,Equiv.symm_apply_apply]
          exact forward
  constructor
  · intro h
    have hh := map_eqv C.chart.symm
      (R:=matchStep G F (fun _=>False)) (S:=FlagLink a b t) (fun i j hstep=>by
        obtain ⟨x,rfl⟩ := C.chart.surjective i
        rcases hstep with rfl|⟨_,rfl⟩
        · simpa using hg x
        · simpa using hf x) h
    simpa using hh
  · apply map_eqv C.chart
    intro i j h
    cases h with
    | arc i => exact .rel _ _ (.inl (C.gap i).symm)
    | cap i ha hb => exact .symm _ _ (.rel _ _ (.inr ⟨id,(cap i ha hb).symm⟩))
    | crossA e ht =>
      exact .rel _ _ (.inr ⟨id,by simpa [ht] using (hO e).symm⟩)
    | crossB e ht =>
      exact .symm _ _ (.rel _ _ (.inr ⟨id,by simpa [ht] using (hI e).symm⟩))
    | twistIn e ht =>
      exact .rel _ _ (.inr ⟨id,by simpa [ht] using (hI e).symm⟩)
    | twistOut e ht =>
      exact .rel _ _ (.inr ⟨id,by simpa [ht] using (hO e).symm⟩)

end FlagMatchingEqv

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonStateActions

/- GID: D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonJointMoments
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonJointMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reconstruct every literal marked signed ribbon boundary observable from one global family of quotient-code mixed-state moments. -/

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

import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonStateActions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonJointMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonFlagGeometry
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonStateActions

section MarkedMoments

open Finset Relation
open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction

variable {E X : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]

def matchSetoid (G B:X→X) : Setoid X :=
  ⟨wholeConn G B,eqvGen_is_equivalence _⟩

noncomputable def markedCircleCount (G A:X→X) (mark:BandFlag E→X) (t s:E→Bool) : ℕ :=
  Nat.card (Quotient (matchSetoid G (markedAction A mark t s)))
private theorem marked_xor_action_inactive (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t τ s : E→Bool) (e:E) (h:s e=false) (q:Bool×Bool) :
    markedAction A mark t (switch τ s) (mark (e,q)) =
      markedAction A mark t τ (mark (e,q)) := by
  rw [markedAction_apply_mark _ _ hm,markedAction_apply_mark _ _ hm]
  cases hτ : τ e <;> simp [switch,h,hτ]

private theorem marked_xor_action_active (A : X→X) (mark : BandFlag E→X)
    (hm : Function.Injective mark) (t τ s : E→Bool) (e:E) (h:s e=true) (q:Bool×Bool) :
    markedAction A mark t (switch τ s) (mark (e,q)) =
      markedAction A mark t (fun a=>!(τ a)) (mark (e,q)) := by
  rw [markedAction_apply_mark _ _ hm,markedAction_apply_mark _ _ hm]
  cases hτ : τ e <;> simp [switch,h,hτ]

/-- Actual boundary counts at each state before and after the selected
forest, with the exact input weights subsequently toggled by XOR. -/
private theorem physical_chart_counts (G A:X→X) (hG:Function.Involutive G) (hA:Function.Involutive A)
    (hAf:∀ x,A x≠x) (mark:BandFlag E→X) (hm:Function.Injective mark)
    (h0:∀ q,A (mark q)=mark (q.1,bandCode false false q.2)) (t τ s:E→Bool)
    (C : SignedMarkedChart G (markedAction A mark t τ)
      (markedAction A mark t (fun e=>!(τ e))) E (fun e x=>∃ q:Bool×Bool,x=mark (e,q))) :
    markedCircleCount G A mark t (switch τ s) =
      signedBouquetCircleCount C.ports.a C.ports.b C.twist (selected s) := by
  let P := C.C
  let a := C.ports.a
  let b := C.ports.b
  let F := markedAction A mark t (switch τ s)
  let B := markedAction A mark t τ
  let Calt := markedAction A mark t (fun e=>!(τ e))
  have hF : Function.Involutive F := (markedAction_match A mark hA hAf hm h0 t _).1
  have cap (i:D P.n) (ha:∀ e:selected s,a e≠i) (hb:∀ e:selected s,b e≠i) :
      F (P.chart (inFlag i)) = P.chart (outFlag i) := by
    let x := P.chart (inFlag i)
    have he : portIndex P x=i := by simp [x,portIndex,inFlag]
    have hFB : F x=B x := by
      by_cases hx : ∃ q,mark q=x
      · obtain ⟨⟨e,q⟩,hqx⟩ := hx
        have hmem := (C.membership e x).mp ⟨q,hqx.symm⟩
        change portIndex P x=a e ∨ portIndex P x=b e at hmem
        rw [he] at hmem
        have hstate : s e=false := by
          cases hs : s e
          · rfl
          · have eS : e∈selected s := (mem_selected_iff s e).mpr hs
            exact hmem.elim (fun h=>(ha ⟨e,eS⟩ h.symm).elim) (fun h=>(hb ⟨e,eS⟩ h.symm).elim)
        rw [← hqx]
        exact marked_xor_action_inactive A mark hm t τ s e hstate q
      · exact (markedAction_apply_unmarked _ _ _ _ _ hx).trans (markedAction_apply_unmarked _ _ _ _ _ hx).symm
    exact hFB.trans (P.base i)
  have switchAt (e : selected s) (j:Bool) : F (P.chart (a e,j))=Calt (P.chart (a e,j)) := by
    let x := P.chart (a e,j)
    have he : portIndex P x=a e := by simp [x,portIndex]
    obtain ⟨q,hq⟩ := (C.membership (e:E) x).mpr (.inl he)
    change F x=Calt x
    rw [hq]
    exact marked_xor_action_active A mark hm t τ s e ((mem_selected_iff s e).mp e.prop) q
  have hI (e:selected s) : F (P.chart (inFlag (a e))) =
      P.chart (if C.twist e then inFlag (b e) else outFlag (b e)) :=
    (switchAt e false).trans (C.in_alternative e)
  have hO (e:selected s) : F (P.chart (outFlag (a e))) =
      P.chart (if C.twist e then outFlag (b e) else inFlag (b e)) :=
    (switchAt e true).trans (C.out_alternative e)
  unfold markedCircleCount signedBouquetCircleCount
  symm
  apply Nat.card_congr
  exact Quotient.congr P.chart (fun x y=>(matching_is_literal_boundary G B F hG hF P
    (fun i:selected s=>a i) (fun i:selected s=>b i) (fun i:selected s=>C.twist i) cap hI hO x y).symm)

end MarkedMoments

section MarkedComponents

open Relation Finset
open scoped BigOperators

variable {J : Type*} {X E : J→Type*}
  [Fintype J] [DecidableEq J] [∀ j,Fintype (X j)] [∀ j,DecidableEq (X j)]
  [∀ j,Fintype (E j)] [∀ j,DecidableEq (E j)]

def sigmaAction (f : ∀ j, X j→X j) (x:Sigma X) : Sigma X :=
  ⟨x.1,f x.1 x.2⟩

def sigmaMark (m : ∀ j, BandFlag (E j)→X j) (q : BandFlag (Sigma E)) : Sigma X :=
  ⟨q.1.1,m q.1.1 (q.1.2,q.2)⟩

private theorem sigmaMark_injective (m : ∀ j, BandFlag (E j)→X j)
    (hm : ∀ j,Function.Injective (m j)) : Function.Injective (sigmaMark m) := by
  intro a b h
  rcases a with ⟨⟨i,e⟩,sa⟩; rcases b with ⟨⟨j,f⟩,sb⟩
  have he : i=j := congrArg Sigma.fst h
  subst j
  have hh : m i (e,sa)=m i (f,sb) := by injection h
  have he := hm _ hh
  cases he
  rfl

private theorem sigma_markedAction_apply (A : ∀ j,X j→X j) (m : ∀ j,BandFlag (E j)→X j)
    (hm : ∀ j,Function.Injective (m j)) (t s : Sigma E→Bool) (j:J) (x:X j) :
    markedAction (sigmaAction A) (sigmaMark m) t s ⟨j,x⟩ =
      ⟨j,markedAction (A j) (m j) (fun e=>t ⟨j,e⟩) (fun e=>s ⟨j,e⟩) x⟩ := by
  by_cases he : ∃ q,m j q=x
  · obtain ⟨⟨e,q⟩,rfl⟩ := he
    change markedAction (sigmaAction A) (sigmaMark m) t s (sigmaMark m (⟨j,e⟩,q)) = _
    rw [markedAction_apply_mark _ _ (sigmaMark_injective m hm),markedAction_apply_mark _ _ (hm j)]
    rfl
  · have he' : ¬∃ q,sigmaMark m q = (⟨j,x⟩ : Sigma X) := by
      rintro ⟨⟨⟨i,e⟩,q⟩,h⟩
      have hi : i=j := congrArg Sigma.fst h
      subst i
      apply he
      refine ⟨(e,q),?_⟩
      injection h
    rw [markedAction_apply_unmarked _ _ _ _ _ he',
      markedAction_apply_unmarked _ _ _ _ _ he]
    rfl

private theorem sigma_matchStep (G F : ∀ j, X j→X j) :
    matchStep (sigmaAction G) (sigmaAction F) (fun _=>False) =
      inComponent (fun j=>matchStep (G j) (F j) (fun _=>False)) := by
  funext x y
  apply propext
  constructor
  · rcases x with ⟨j,x⟩
    rintro (rfl|⟨_,rfl⟩)
    · exact .mk _ _ _ (.inl rfl)
    · exact .mk _ _ _ (.inr ⟨id,rfl⟩)
  · intro h
    cases h with
    | mk j x y h =>
      rcases h with rfl|⟨_,rfl⟩
      · exact .inl rfl
      · exact .inr ⟨id,rfl⟩

private theorem markedCircles_disjoint (G A : ∀ j,X j→X j) (m : ∀ j,BandFlag (E j)→X j)
    (hm : ∀ j,Function.Injective (m j)) (t s : Sigma E→Bool) :
    markedCircleCount (sigmaAction G) (sigmaAction A) (sigmaMark m) t s =
      ∑ j, markedCircleCount (G j) (A j) (m j) (fun e=>t ⟨j,e⟩) (fun e=>s ⟨j,e⟩) := by
  classical
  have he : markedAction (sigmaAction A) (sigmaMark m) t s =
      sigmaAction (fun j=>markedAction (A j) (m j) (fun e=>t ⟨j,e⟩) (fun e=>s ⟨j,e⟩)) := by
    funext q
    rcases q with ⟨j,x⟩
    exact sigma_markedAction_apply A m hm t s j x
  unfold markedCircleCount matchSetoid
  rw [he]
  change Nat.card (Quotient (relSetoid (matchStep (sigmaAction G) (sigmaAction _) _))) = _
  rw [sigma_matchStep,Nat.card_congr (quotient_components _),Nat.card_sigma]
  rfl

end MarkedComponents

section ActualComponents

open Finset Relation

section Fibres
variable {Y J : Type*}

abbrev fibre {Y J : Type*} (p : Y → J) (j : J) := {y : Y // p y = j}

noncomputable instance fibreFintype [Fintype Y] (p:Y→J) (j:J) : Fintype (fibre p j) :=
  Fintype.ofFinite _

def fibreEquiv (p : Y → J) : Y ≃ Sigma (fibre p) where
  toFun y := ⟨p y,⟨y,rfl⟩⟩
  invFun y := y.2.val
  left_inv _ := rfl
  right_inv := by rintro ⟨_,⟨y,rfl⟩⟩; rfl

def fibreAction (p:Y→J) (F:Y→Y) (hF:∀ y,p (F y)=p y) (j:J) (x:fibre p j) : fibre p j :=
  ⟨F x.val,(hF _).trans x.prop⟩

private theorem lift_equivalence {Y Z : Type*} {R : Y→Y→Prop} {S : Z→Z→Prop}
    (f:Y→Z) (h:∀ x y,R x y→EqvGen S (f x) (f y)) {x y:Y} (H:EqvGen R x y) :
    EqvGen S (f x) (f y) := by
  induction H with
  | rel x y hh => exact h x y hh
  | refl x => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

private theorem path_label (p:Y→J) {R:Y→Y→Prop}
    (hR:∀ x y,R x y → p x=p y) {x y:Y} (h:EqvGen R x y) : p x=p y := by
  induction h with
  | rel x y h => exact hR x y h
  | refl x => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

private theorem path_restrict (p:Y→J) (R:Y→Y→Prop)
    (hR:∀ x y,R x y → p x=p y) {x y:Y} (h:EqvGen R x y) :
    ∀ (j:J) (hx:p x=j) (hy:p y=j),
      EqvGen (fun a b:fibre p j=>R a.val b.val) ⟨x,hx⟩ ⟨y,hy⟩ := by
  induction h with
  | rel x y h => intro j hx hy; exact .rel _ _ h
  | refl x => intro j hx hy; exact .refl _
  | symm x y h ih => intro j hx hy; exact .symm _ _ (ih _ hy hx)
  | trans x y z h₁ h₂ ih₁ ih₂ =>
    intro j hx hz
    have h' : p x=p y := path_label p hR h₁
    have hy : p y=j := h'.symm.trans hx
    exact .trans _ _ _ (ih₁ j hx hy) (ih₂ j hy hz)

private theorem match_naturality {Z : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (e:Y≃Z) (G A:Y→Y) (G' A':Z→Z)
    (hg:∀ x,e (G x)=G' (e x)) (ha:∀ x,e (A x)=A' (e x)) (x y:Y) :
    wholeConn G A x y ↔ wholeConn G' A' (e x) (e y) := by
  constructor
  · apply lift_equivalence e
    intro a b h
    rcases h with rfl|⟨_,rfl⟩
    · exact .rel _ _ (.inl (hg a))
    · exact .rel _ _ (.inr ⟨id,ha a⟩)
  · intro h
    have Hg (u:Z) : e.symm (G' u)=G (e.symm u) := by
      rw [← (e.apply_symm_apply u),← hg]
      simp
    have Ha (u:Z) : e.symm (A' u)=A (e.symm u) := by
      rw [← (e.apply_symm_apply u),← ha]
      simp
    have h' := lift_equivalence e.symm
      (R:=matchStep G' A' (fun _=>False)) (S:=matchStep G A (fun _=>False))
      (fun a b h=>by
        rcases h with rfl|⟨_,rfl⟩
        · exact .rel _ _ (.inl (Hg a))
        · exact .rel _ _ (.inr ⟨id,Ha a⟩)) h
    change EqvGen (matchStep G A (fun _=>False)) x y
    simpa only [Equiv.symm_apply_apply] using h'

end Fibres

section Literal
variable {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]

def Incidence (G A:X→X) (m:BandFlag E→X) (x y:X) : Prop :=
  matchStep G A (fun _=>False) x y ∨ ∃ e, x=(bandEnds m e).1 ∧ y=(bandEnds m e).2

def componentSetoid (G A:X→X) (m:BandFlag E→X) : Setoid X := relSetoid (Incidence G A m)

abbrev Components (G A:X→X) (m:BandFlag E→X) := Quotient (componentSetoid G A m)
def component (G A:X→X) (m:BandFlag E→X) : X→Components G A m := Quotient.mk _
def edgeComponent (G A:X→X) (m:BandFlag E→X) (e:E) : Components G A m :=
  component G A m (bandEnds m e).1

private theorem comp_eq_step (G A:X→X) (m:BandFlag E→X) {x y:X}
    (h:Incidence G A m x y) : component G A m x=component G A m y :=
  Quotient.sound (.rel _ _ h)

private theorem comp_G (G A:X→X) (m:BandFlag E→X) (x:X) :
    component G A m (G x)=component G A m x :=
  (comp_eq_step G A m (.inl (.inl rfl))).symm

private theorem comp_A (G A:X→X) (m:BandFlag E→X) (x:X) :
    component G A m (A x)=component G A m x :=
  (comp_eq_step G A m (.inl (.inr ⟨id,rfl⟩))).symm

private theorem comp_mark (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2))
    (e:E) (q:Bool×Bool) : component G A m (m (e,q))=edgeComponent G A m e := by
  have hA (b:Bool) : component G A m (m (e,b,true)) = component G A m (m (e,b,false)) := by
    have h := comp_A G A m (m (e,b,false))
    rw [h0] at h
    exact h
  have hB : component G A m (m (e,true,false))=edgeComponent G A m e :=
    (comp_eq_step G A m (.inr ⟨e,rfl,rfl⟩)).symm
  rcases q with ⟨a,b⟩
  cases a <;> cases b
  · rfl
  · exact hA false
  · exact hB
  · exact (hA true).trans hB

def localGap (G A:X→X) (m:BandFlag E→X) :=
  fibreAction (component G A m) G (comp_G G A m)

def localCap (G A:X→X) (m:BandFlag E→X) :=
  fibreAction (component G A m) A (comp_A G A m)

def localMark (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (j:Components G A m)
    (q:BandFlag (fibre (edgeComponent G A m) j)) : fibre (component G A m) j :=
  ⟨m (q.1.val,q.2),(comp_mark G A m h0 q.1.val q.2).trans q.1.prop⟩

private theorem localMark_injective (G A:X→X) (m:BandFlag E→X)
    (hm:Function.Injective m) (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2))
    (j:Components G A m) : Function.Injective (localMark G A m h0 j) := by
  rintro ⟨a,p⟩ ⟨b,q⟩ h
  have h := hm (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext (congrArg (fun x : BandFlag E=>x.1) h))
    (congrArg (fun x : BandFlag E=>x.2) h)

private theorem localGap_involution (G A:X→X) (m:BandFlag E→X) (hG:Function.Involutive G)
    (j:Components G A m) : Function.Involutive (localGap G A m j) :=
  fun x=>Subtype.ext (hG x.val)

private theorem localCap_involution (G A:X→X) (m:BandFlag E→X) (hA:Function.Involutive A)
    (j:Components G A m) : Function.Involutive (localCap G A m j) :=
  fun x=>Subtype.ext (hA x.val)

private theorem localCap_mark (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (j:Components G A m)
    (q:BandFlag (fibre (edgeComponent G A m) j)) :
    localCap G A m j (localMark G A m h0 j q)=
      localMark G A m h0 j (q.1,bandCode false false q.2) :=
  Subtype.ext (h0 (q.1.val,q.2))

private theorem local_step (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (j:Components G A m)
    (x y:fibre (component G A m) j) (h:Incidence G A m x.val y.val) :
    @graphJoin (fibre (component G A m) j)
      (wholeConn (localGap G A m j) (localCap G A m j))
      ((Finset.univ : Finset (fibre (edgeComponent G A m) j)).toList.map
        (bandEnds (localMark G A m h0 j))) x y := by
  rcases h with h|⟨e,he,hf⟩
  · apply EqvGen.rel
    left
    apply EqvGen.rel
    rcases h with hl|⟨_,hr⟩
    · exact .inl (Subtype.ext hl)
    · exact .inr ⟨id,Subtype.ext hr⟩
  · apply EqvGen.rel
    right
    let e' : fibre (edgeComponent G A m) j := ⟨e,by rw [edgeComponent,← he]; exact x.prop⟩
    apply List.mem_map.mpr
    refine ⟨e',by simp,Prod.ext (Subtype.ext he.symm) (Subtype.ext hf.symm)⟩

private theorem actual_component_connected (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (j:Components G A m) :
    ∀ x y:fibre (component G A m) j,
      graphJoin (wholeConn (localGap G A m j) (localCap G A m j))
        ((Finset.univ : Finset (fibre (edgeComponent G A m) j)).toList.map
           (bandEnds (localMark G A m h0 j))) x y := by
  classical
  intro x y
  have h : EqvGen (Incidence G A m) x.val y.val := Quotient.exact (x.prop.trans y.prop.symm)
  apply eqvGen_transfer (local_step G A m h0 j) (eqvGen_is_equivalence _) x y
  exact path_restrict (component G A m) (Incidence G A m)
    (fun _ _ h=>comp_eq_step G A m h) h j x.prop y.prop

private theorem actual_component_nonempty (G A:X→X) (m:BandFlag E→X) (j:Components G A m) :
    Nonempty (fibre (component G A m) j) := by
  induction j using Quotient.inductionOn with
  | h x => exact ⟨⟨x,rfl⟩⟩


noncomputable instance componentFintype (G A:X→X) (m:BandFlag E→X) : Fintype (Components G A m) := by
  classical
  exact Fintype.ofSurjective (component G A m) (fun j => by
    induction j using Quotient.inductionOn with
    | h a => exact ⟨a,rfl⟩)

private theorem fibre_mark_transport (G A:X→X) (m:BandFlag E→X)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (q:BandFlag E) :
    fibreEquiv (component G A m) (m q) =
    sigmaMark (localMark G A m h0) (fibreEquiv (edgeComponent G A m) q.1,q.2) := by
  apply (fibreEquiv (component G A m)).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

/-- Boundary circles split over actual quotient fibres for every literal
state, with arbitrary representative ordering and including empty carriers. -/
private theorem actual_circles_components (G A:X→X) (m:BandFlag E→X)
    (hm:Function.Injective m)
    (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (t s:E→Bool) :
    markedCircleCount G A m t s =
      ∑ j : Components G A m,
        markedCircleCount (localGap G A m j) (localCap G A m j)
          (localMark G A m h0 j) (fun e=>t e.val) (fun e=>s e.val) := by
  classical
  let jX := fibreEquiv (component G A m)
  let jE := fibreEquiv (edgeComponent G A m)
  let G' := sigmaAction (localGap G A m)
  let A' := sigmaAction (localCap G A m)
  let m' := sigmaMark (localMark G A m h0)
  let t' := t ∘ jE.symm
  let s' := s ∘ jE.symm
  let B := markedAction A m t s
  let B' := markedAction A' m' t' s'
  have hG (x:X) : jX (G x)=G' (jX x) := by
    apply jX.symm.injective
    rw [Equiv.symm_apply_apply]
    rfl
  have hA (x:X) : jX (A x)=A' (jX x) := by
    apply jX.symm.injective
    rw [Equiv.symm_apply_apply]
    rfl
  have hB (x:X) : jX (B x)=B' (jX x) := by
    by_cases hx : ∃ q,m q=x
    · obtain ⟨⟨e,q⟩,rfl⟩ := hx
      dsimp only [B,B']
      rw [markedAction_apply_mark _ _ hm,fibre_mark_transport G A m h0,
        fibre_mark_transport G A m h0,
        markedAction_apply_mark _ _ (sigmaMark_injective _ (localMark_injective G A m hm h0))]
      dsimp only [t',s',Function.comp_apply]
      change m' (jE e,bandCode (t e) (s e) q) =
        m' (jE e,bandCode (t (jE.symm (jE e))) (s (jE.symm (jE e))) q)
      rw [Equiv.symm_apply_apply]
    · have hx' : ¬∃ q,m' q=jX x := by
        rintro ⟨⟨e,q⟩,he⟩
        apply hx
        obtain ⟨e,rfl⟩ := jE.surjective e
        apply Exists.intro (e,q)
        apply jX.injective
        exact (fibre_mark_transport G A m h0 (e,q)).trans he
      dsimp only [B,B']
      rw [markedAction_apply_unmarked _ _ _ _ _ hx,
        markedAction_apply_unmarked _ _ _ _ _ hx']
      exact hA x
  have hw : markedCircleCount G A m t s =
      markedCircleCount G' A' m' t' s' := by
    unfold markedCircleCount
    apply Nat.card_congr
    exact Quotient.congr jX (match_naturality jX G B G' B' hG hB)
  rw [hw,markedCircles_disjoint _ _ _ (localMark_injective G A m hm h0)]
  rfl


end Literal

end ActualComponents

section JointColumns

open Finset
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open scoped BigOperators
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction

section Joint
variable {J : Type*} [Fintype J] [DecidableEq J] {E V : J→Type*}
  [∀ j,Fintype (E j)] [∀ j,DecidableEq (E j)]
  [∀ j,AddCommGroup (V j)] [∀ j,Module K (V j)] [∀ j,FiniteDimensional K (V j)]

def jointLabel (ell : ∀ j, E j→V j) (e:Sigma E) : ∀ j,V j :=
  Pi.single e.1 (ell e.1 e.2)

/-- The global code does not use component products as precomputed observables.
Raw columns are summed into disjoint fibres and projection commutes exactly
with selecting physical band states. -/
private theorem project_joint_columns (ell : ∀ j,E j→V j) (s:Sigma E→Bool) (j:J) :
    (columns (F:=K) (jointLabel ell) (selected s)).map (LinearMap.proj j) =
      columns (F:=K) (ell j) (selected (fun e=>s ⟨j,e⟩)) := by
  classical
  unfold columns
  rw [Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨⟨c,e⟩,h,rfl⟩,rfl⟩
    by_cases hc : j=c
    · subst c
      change Pi.single j (ell j e) j ∈ _
      rw [Pi.single_eq_same]
      exact Submodule.subset_span ⟨e,(mem_selected_iff (fun e=>s ⟨j,e⟩) e).2 ((mem_selected_iff s ⟨j,e⟩).1 h),rfl⟩
    · change Pi.single c (ell c e) j ∈ _
      rw [Pi.single_eq_of_ne hc]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨e,h,rfl⟩
    exact Submodule.subset_span ⟨jointLabel ell ⟨j,e⟩,⟨⟨j,e⟩,(mem_selected_iff s ⟨j,e⟩).2 ((mem_selected_iff (fun e=>s ⟨j,e⟩) e).1 h),rfl⟩,by
      change Pi.single j (ell j e) j=ell j e
      exact Pi.single_eq_same _ _⟩

/-- One marginal-moment lattice, for the *global* direct sum (and all its
quotients), simultaneously reconstructs products of arbitrary functions
of the actual selected component-column spans. -/
private theorem joint_moment_reconstruction
    [Fintype (∀ j,V j)]
    [Fintype (Submodule K (∀ j,V j))]
    [∀ L : Submodule K (∀ j,V j),Fintype (Module.Dual K ((∀ j,V j) ⧸ L))]
    (ell : ∀ j,E j→V j) (f : ∀ j,Submodule K (V j) → ℝ) :
    ∃ α : Submodule K (∀ j,V j) → ℝ,
      ∀ s : Sigma E→Bool,
        signedCoeff (jointLabel ell) α (selected s) =
          ∏ j, f j (columns (F:=K) (ell j) (selected (fun e=>s ⟨j,e⟩))) := by
  let F (W : Submodule K (∀ j,V j)) : ℝ := ∏ j, f j (W.map (LinearMap.proj j))
  obtain ⟨α,hα⟩ := physical_lattice_reconstruction (jointLabel ell) F
  refine ⟨α,fun s=>?_⟩
  rw [show signedCoeff (jointLabel ell) α (selected s) =
      F (columns (F:=K) (jointLabel ell) (selected s)) from hα _]
  unfold F
  simp_rw [project_joint_columns]

end Joint

end JointColumns

section AllRibbonMoments

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
open D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.ProjectionMoments
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.SignedBouquetMomentReconstruction

variable {X E : Type*} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
variable (G A:X→X) (m:BandFlag E→X)
  (h0:∀ q,A (m q)=m (q.1,bandCode false false q.2)) (t:E→Bool)

abbrev EdgeFibre (j:Components G A m) := fibre (edgeComponent G A m) j

structure ChartFibre (j:Components G A m) where
  state : EdgeFibre G A m j → Bool
  chart : SignedMarkedChart (localGap G A m j)
    (markedAction (localCap G A m j) (localMark G A m h0 j) (fun e=>t e.val) state)
    (markedAction (localCap G A m j) (localMark G A m h0 j) (fun e=>t e.val) (fun e=>!(state e)))
    (EdgeFibre G A m j) (fun e x=>∃ q:Bool×Bool,x=localMark G A m h0 j (e,q))

variable {G A m h0 t}

abbrev chartSpace {j:Components G A m} (C : ChartFibre G A m h0 t j) :=
  SignedLabelSpace C.chart.ports.a C.chart.ports.b C.chart.twist

private theorem exists_fibre_chart (hG:Function.Involutive G) (hGf:∀ x,G x≠x)
    (hA:Function.Involutive A) (hAf:∀ x,A x≠x) (hm:Function.Injective m)
    (j:Components G A m) : Nonempty (ChartFibre G A m h0 t j) := by
  classical
  obtain ⟨x⟩ := actual_component_nonempty G A m j
  let g := localGap G A m j
  let a := localCap G A m j
  let m' := localMark G A m h0 j
  let t' : EdgeFibre G A m j→Bool := fun e=>t e.val
  have gi := localGap_involution G A m hG j
  have ai := localCap_involution G A m hA j
  have gf (y) : g y≠y := fun h=>hGf y.val (congrArg Subtype.val h)
  have af (y) : a y≠y := fun h=>hAf y.val (congrArg Subtype.val h)
  have mi := localMark_injective G A m hm h0 j
  have hcap := localCap_mark G A m h0 j
  let l := (Finset.univ : Finset (EdgeFibre G A m j)).toList
  obtain ⟨τ,_,hτ⟩ := marked_forest_state g a gi gf ai af m' mi hcap t' (fun _=>false)
      l (Finset.nodup_toList _) (fun _ _=>rfl)
  have hzero : markedAction a m' t' (fun _=>false)=a := by
    funext y
    by_cases h : ∃ q,m' q=y
    · obtain ⟨q,rfl⟩ := h
      rw [markedAction_apply_mark _ _ mi]
      exact (hcap q).symm
    · exact markedAction_apply_unmarked _ _ _ _ _ h
  have hc (y) : wholeConn g (markedAction a m' t' τ) x y := by
    apply (hτ x y).mpr
    rw [hzero]
    exact actual_component_connected G A m h0 j x y
  have hB := markedAction_match a m' ai af mi hcap t' τ
  let P := alternating_flag_chart g (markedAction a m' t' τ) gi hB.1 gf hB.2 x hc
  exact ⟨⟨τ,canonical_marked_signed_chart g a ai af m' mi hcap t' τ P⟩⟩

noncomputable def chartCharge {j:Components G A m} (C : ChartFibre G A m h0 t j)
    (d:ℝ) (W:Submodule K (chartSpace C)) : ℝ :=
  let a := C.chart.ports.a
  let b := C.chart.ports.b
  let B0 := signedBilin a b C.chart.twist
  let hs : B0.flip=B0 := signedBilin_symmetric a b C.chart.twist
    C.chart.ports.a_inj C.chart.ports.b_inj C.chart.ports.separate C.chart.ports.ordered
  (d⁻¹)^Module.finrank K ((radicalForm B0 hs).restrict W).range

private theorem local_charge_counts (hG:Function.Involutive G) (hA:Function.Involutive A)
    (hAf:∀ x,A x≠x) (hm:Function.Injective m) {j:Components G A m}
    (C : ChartFibre G A m h0 t j) (d:ℝ) (hd:d≠0) (s:EdgeFibre G A m j→Bool) :
    (d*d^(selected s).card)*chartCharge C d
      (columns (F:=K) (intrinsicLabel C.chart.ports.a C.chart.ports.b C.chart.twist) (selected s)) =
      d^(markedCircleCount (localGap G A m j) (localCap G A m j)
          (localMark G A m h0 j) (fun e=>t e.val) (switch C.state s)) := by
  classical
  let a := C.chart.ports.a
  let b := C.chart.ports.b
  let B0 := signedBilin a b C.chart.twist
  let hs : B0.flip=B0 := signedBilin_symmetric a b C.chart.twist
    C.chart.ports.a_inj C.chart.ports.b_inj C.chart.ports.separate C.chart.ports.ordered
  let B := radicalForm B0 hs
  let ell := intrinsicLabel a b C.chart.twist
  let W := columns (F:=K) ell (selected s)
  have hc := restriction_euler_from_labels a b C.chart.twist ell B
    C.chart.ports.a_inj C.chart.ports.b_inj C.chart.ports.separate C.chart.ports.ordered
    (fun i j => by
      change B (B0.ker.mkQ (Pi.single j 1)) (B0.ker.mkQ (Pi.single i 1)) = _
      exact (radicalForm_apply B0 hs _ _).trans (signedBilin_port a b C.chart.twist i j)) (selected s)
  have hr := physical_chart_counts (localGap G A m j) (localCap G A m j)
    (localGap_involution G A m hG j) (localCap_involution G A m hA j)
    (fun x h=>hAf x.val (congrArg Subtype.val h))
    (localMark G A m h0 j) (localMark_injective G A m hm h0 j) (localCap_mark G A m h0 j)
    (fun e=>t e.val) C.state s C.chart
  change (d*d^(selected s).card)*(d⁻¹)^Module.finrank K (B.restrict W).range = _
  rw [hr, show d*d^(selected s).card = d^(1+(selected s).card) by rw [pow_add,pow_one],← hc]
  dsimp only [W]
  rw [pow_add,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hd),mul_one]

variable (G A m h0 t)

abbrev AllCharts := ∀ j:Components G A m, ChartFibre G A m h0 t j
abbrev AllEdges := Sigma (EdgeFibre G A m)
abbrev AllSpace (C:AllCharts G A m h0 t) := ∀ j:Components G A m, chartSpace (C j)

noncomputable def allSpaceFinite (C:AllCharts G A m h0 t) : Fintype (AllSpace G A m h0 t C) := by
  classical
  letI : ∀ j:Components G A m, Fintype (chartSpace (C j)) := fun j=>intrinsicFinite (C j).chart.ports.a (C j).chart.ports.b (C j).chart.twist
  infer_instance

noncomputable def allSubspaces (C:AllCharts G A m h0 t) : Fintype (Submodule K (AllSpace G A m h0 t C)) := by
  letI := allSpaceFinite G A m h0 t C
  letI : Finite (Submodule K (AllSpace G A m h0 t C)) :=
    Finite.of_injective (fun W : Submodule K (AllSpace G A m h0 t C) => (W : Set (AllSpace G A m h0 t C)))
      SetLike.coe_injective
  exact Fintype.ofFinite _

noncomputable def allDuals (C:AllCharts G A m h0 t)
    (L : Submodule K (AllSpace G A m h0 t C)) :
    Fintype (Module.Dual K (AllSpace G A m h0 t C ⧸ L)) := by
  letI := allSpaceFinite G A m h0 t C
  letI : Finite (AllSpace G A m h0 t C ⧸ L) := Finite.of_surjective _ L.mkQ_surjective
  letI : Finite (Module.Dual K (AllSpace G A m h0 t C ⧸ L)) :=
    Finite.of_injective (fun f : Module.Dual K (AllSpace G A m h0 t C ⧸ L)=>fun x=>f x)
      (fun {_ _} h=>LinearMap.ext (congrFun h))
  exact Fintype.ofFinite _

noncomputable def allLabel (C:AllCharts G A m h0 t) :
    AllEdges G A m → AllSpace G A m h0 t C := by
  classical
  exact jointLabel (fun j=>intrinsicLabel (C j).chart.ports.a (C j).chart.ports.b (C j).chart.twist)

def globalSwitch (C:AllCharts G A m h0 t) (s:AllEdges G A m→Bool) (e:E) : Bool :=
  let e' := fibreEquiv (edgeComponent G A m) e
  switch (C e'.1).state (fun f=>s ⟨e'.1,f⟩) e'.2

noncomputable def jointReadout (C:AllCharts G A m h0 t)
    (α:Submodule K (AllSpace G A m h0 t C)→ℝ) (s:AllEdges G A m→Bool) : ℝ := by
  classical
  letI := allSubspaces G A m h0 t C
  letI := allDuals G A m h0 t C
  exact signedCoeff (allLabel G A m h0 t C) α (selected s)

/-- One global quotient-code physical moment portfolio for arbitrary marked
ribbons, with no connectedness, chart, forest or component premises. -/
private theorem all_ribbon_joint_moments (hG:Function.Involutive G) (hGf:∀ x,G x≠x)
    (hA:Function.Involutive A) (hAf:∀ x,A x≠x) (hm:Function.Injective m) :
    ∃ C : AllCharts G A m h0 t, ∀ d:ℝ,d≠0 →
      ∃ α:Submodule K (AllSpace G A m h0 t C)→ℝ, ∀ s:AllEdges G A m→Bool,
        (∏ j:Components G A m, d*d^(selected (fun e:EdgeFibre G A m j=>s ⟨j,e⟩)).card)*
          jointReadout G A m h0 t C α s =
        d^(markedCircleCount G A m t (globalSwitch G A m h0 t C s)) := by
  classical
  let C : AllCharts G A m h0 t := fun j=>
    Classical.choice (exists_fibre_chart (h0:=h0) (t:=t) hG hGf hA hAf hm j)
  refine ⟨C,fun d hd=>?_⟩
  letI := allSpaceFinite G A m h0 t C
  letI := allSubspaces G A m h0 t C
  letI := allDuals G A m h0 t C
  obtain ⟨α,ha⟩ := joint_moment_reconstruction
    (fun j=>intrinsicLabel (C j).chart.ports.a (C j).chart.ports.b (C j).chart.twist)
    (fun j=>chartCharge (C j) d)
  refine ⟨α,fun s=>?_⟩
  have eα : jointReadout G A m h0 t C α s = _ := ha s
  rw [eα,← Finset.prod_mul_distrib,actual_circles_components G A m hm h0,← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  have H := local_charge_counts (h0:=h0) (t:=t) hG hA hAf hm (C j) d hd (fun e=>s ⟨j,e⟩)
  have heq : (fun e:EdgeFibre G A m j=>globalSwitch G A m h0 t C s e.val) =
        switch (C j).state (fun e=>s ⟨j,e⟩) := by
    funext e
    obtain ⟨e,he⟩ := e
    change edgeComponent G A m e = j at he
    subst j
    rfl
  rw [heq]
  exact H


def globalSwitchEquiv (C:AllCharts G A m h0 t) : (AllEdges G A m→Bool) ≃ (E→Bool) where
  toFun := globalSwitch G A m h0 t C
  invFun r e := switch (C e.1).state (fun f=>r f.val) e.2
  left_inv s := by
    funext e
    obtain ⟨j,⟨e,he⟩⟩ := e
    change edgeComponent G A m e = j at he
    subst j
    dsimp [globalSwitch,switch,fibreEquiv]
    cases (C (edgeComponent G A m e)).state ⟨e,rfl⟩ <;> simp
  right_inv r := by
    funext e
    dsimp [globalSwitch,switch,fibreEquiv]
    cases (C (edgeComponent G A m e)).state ⟨e,rfl⟩ <;> simp

/-- Exact weighted consequence over the original, unsplit edge carrier.
A general observable of all bits may be included without any factorization
hypothesis; it is not used to select the chart or the moment coefficients. -/
theorem any_observable_joint_moments (hG:Function.Involutive G) (hGf:∀ x,G x≠x)
    (hA:Function.Involutive A) (hAf:∀ x,A x≠x) (hm:Function.Injective m) :
    letI := Classical.decEq (AllEdges G A m)
    ∃ C : AllCharts G A m h0 t, ∀ d:ℝ,d≠0 →
      ∃ α:Submodule K (AllSpace G A m h0 t C)→ℝ, ∀ w:(E→Bool)→ℝ,
        (∑ r:E→Bool, w r * d^(markedCircleCount G A m t r)) =
        ∑ s:AllEdges G A m→Bool,
          w (globalSwitch G A m h0 t C s) *
           ((∏ j:Components G A m, d*d^(selected (fun e:EdgeFibre G A m j=>s ⟨j,e⟩)).card)*
            jointReadout G A m h0 t C α s) := by
  classical
  letI : DecidableEq (AllEdges G A m) := Classical.decEq _
  obtain ⟨C,hC⟩ := all_ribbon_joint_moments G A m h0 t hG hGf hA hAf hm
  refine ⟨C,fun d hd=>?_⟩
  obtain ⟨α,hα⟩ := hC d hd
  refine ⟨α,fun w=>?_⟩
  simp_rw [hα]
  symm
  exact Equiv.sum_comp (globalSwitchEquiv G A m h0 t C)
    (fun r=>w r * d^(markedCircleCount G A m t r))

end AllRibbonMoments

end D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.MarkedRibbonJointMoments

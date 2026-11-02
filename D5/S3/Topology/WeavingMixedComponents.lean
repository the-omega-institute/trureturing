/- GID: D5/S3/Topology/WeavingMixedComponents
   generality: G
   mirror-B: D5/B/S3/Topology/WeavingMixedComponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Actual mixed weaving circles map onto spanning reference components. -/

import D5.S3.Topology.WeavingDiagramPorts
import D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Actual mixed smoothings and spanning reference graphs on the uniform circles.
All cyclic seams and isolated spanning vertices are retained. -/

set_option autoImplicit false

namespace D5.S3.Topology.WeavingMixedComponents

open D5.S3.Topology.WeavingDiagramPorts

abbrev Crossing (P : Parameters) := ZMod P.m × Fin P.n

/-- Change precisely the crossings in S to the complementary local smoothing. -/
def mixedMate (P : Parameters) (p : ℕ) (S : Finset (Crossing P)) : Dart P → Dart P
  | (t,i,a) => if (t,i) ∈ S then localMate P (1-p) (t,i,a)
      else localMate P p (t,i,a)

theorem mixedMate_involutive (P : Parameters) (p : ℕ) (S : Finset (Crossing P)) :
    Function.Involutive (mixedMate P p S) := by
  rintro ⟨t,i,a⟩
  by_cases h : (t,i) ∈ S <;>
    cases a <;> simp [mixedMate, h, localMate] <;> split_ifs <;> rfl

theorem mixedMate_ne_self (P : Parameters) (p : ℕ) (S : Finset (Crossing P))
    (x : Dart P) : mixedMate P p S x ≠ x := by
  rcases x with ⟨t,i,a⟩
  by_cases h : (t,i) ∈ S <;>
    cases a <;> simp [mixedMate, h, localMate] <;> split_ifs <;> simp

def mixedPerm (P : Parameters) (p : ℕ) (S : Finset (Crossing P)) : Equiv.Perm (Dart P) where
  toFun := mixedMate P p S
  invFun := mixedMate P p S
  left_inv := mixedMate_involutive P p S
  right_inv := mixedMate_involutive P p S

def externalPerm (P : Parameters) : Equiv.Perm (Dart P) where
  toFun := external P
  invFun := external P
  left_inv := external_involutive P
  right_inv := external_involutive P

/-- Both colors remain in the generating relation even if their endpoints agree. -/
def mixedStep (P : Parameters) (p : ℕ) (S : Finset (Crossing P)) (x y : Dart P) : Prop :=
  y = mixedMate P p S x ∨ y = external P x

abbrev MixedReach (P : Parameters) (p : ℕ) (S : Finset (Crossing P)) :=
  Relation.EqvGen (mixedStep P p S)

abbrev MixedCircle (P : Parameters) (p : ℕ) (S : Finset (Crossing P)) :=
  Quotient (Relation.EqvGen.setoid (mixedStep P p S))

def mixedCircle (P : Parameters) (p : ℕ) (S : Finset (Crossing P))
    (x : Dart P) : MixedCircle P p S := Quotient.mk _ x

theorem mixedStep_empty (P : Parameters) (p : ℕ) :
    mixedStep P p ∅ = step P p := by
  funext x y
  rcases x with ⟨t,i,a⟩
  simp [mixedStep, mixedMate, step, portGraph]

theorem mixedStep_univ (P : Parameters) (p : ℕ) :
    mixedStep P p Finset.univ = step P (1-p) := by
  funext x y
  rcases x with ⟨t,i,a⟩
  simp [mixedStep, mixedMate, step, portGraph]

theorem mixed_empty_card (P : Parameters) (p : ℕ) :
    Nat.card (MixedCircle P p ∅) = Nat.card (Circle P p) := by
  unfold MixedCircle
  rw [mixedStep_empty]

theorem mixed_univ_card (P : Parameters) (p : ℕ) :
    Nat.card (MixedCircle P p Finset.univ) = Nat.card (Circle P (1-p)) := by
  unfold MixedCircle
  rw [mixedStep_univ]

/-- The supplier's reflexive-transitive connectivity is precisely the actual
mixed equivalence relation, including its symmetric closure. -/
theorem mixedReach_iff_matchingConnected (P : Parameters) (p : ℕ)
    (S : Finset (Crossing P)) (x y : Dart P) :
    MixedReach P p S x y ↔
      D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit.Connected
        (externalPerm P) (mixedPerm P p S) x y := by
  let R := fun u v : Dart P => externalPerm P u = v ∨ mixedPerm P p S u = v
  haveI : Std.Symm R := ⟨by
    intro a b h
    rcases h with h | h
    · left
      rw [← h]
      exact external_involutive P a
    · right
      rw [← h]
      exact mixedMate_involutive P p S a⟩
  change MixedReach P p S x y ↔ Relation.ReflTransGen R x y
  constructor
  · intro h
    induction h with
    | rel a b h =>
      apply Relation.ReflTransGen.single
      exact h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)
    | refl => exact .refl
    | symm _ _ _ ih => exact symm ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    induction h with
    | refl => exact Relation.EqvGen.refl _
    | tail h hbc ih =>
      exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _
        (hbc.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)))

theorem circle_local (P : Parameters) (p : ℕ) (x : Dart P) :
    circle P p (localMate P p x) = circle P p x := by
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inl rfl))

theorem circle_external (P : Parameters) (p : ℕ) (x : Dart P) :
    circle P p (external P x) = circle P p x := by
  apply Quotient.sound
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr rfl))

/-- Spanning subgraph on ALL uniform circles, with exactly the selected
crossing incidences. Injectivity of crossing labels is a separate theorem. -/
def referenceGraph (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) : SimpleGraph (Circle P p) where
  Adj u v := ∃ a ∈ S,
    (u = (edgeEnds P p a.1 a.2).1 ∧ v = (edgeEnds P p a.1 a.2).2) ∨
    (u = (edgeEnds P p a.1 a.2).2 ∧ v = (edgeEnds P p a.1 a.2).1)
  symm := ⟨by
    rintro u v ⟨a,ha,h⟩
    exact ⟨a,ha,h.elim (fun h => Or.inr ⟨h.2,h.1⟩)
      (fun h => Or.inl ⟨h.2,h.1⟩)⟩⟩
  loopless := ⟨by
    rintro u ⟨a,ha,h⟩
    have hn := edge_endpoints_distinct P p hp a.1 a.2
    rcases h with h | h
    · exact hn (h.1.symm.trans h.2)
    · exact hn (h.2.symm.trans h.1)⟩

def dartComponent (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (x : Dart P) :
    (referenceGraph P p hp S).ConnectedComponent :=
  (referenceGraph P p hp S).connectedComponentMk (circle P p x)

/-- In a selected crossing, all four reference port labels lie in the same
spanning component. This proves the needed incidence, rather than assuming it. -/
theorem selected_crossing_component (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (t : ZMod P.m) (i : Fin P.n)
    (hi : (t,i) ∈ S) (a b : Port) :
    dartComponent P p hp S (t,i,a) = dartComponent P p hp S (t,i,b) := by
  let G := referenceGraph P p hp S
  have hedge : G.Adj (edgeEnds P p t i).1 (edgeEnds P p t i).2 :=
    ⟨(t,i),hi,Or.inl ⟨rfl,rfl⟩⟩
  have hc := SimpleGraph.ConnectedComponent.sound hedge.reachable
  by_cases h : cup p i
  · have ht : circle P p (t,i,.tr) = circle P p (t,i,.tl) := by
      simpa [localMate,h] using circle_local P p (t,i,.tl)
    have hb : circle P p (t,i,.br) = circle P p (t,i,.bl) := by
      simpa [localMate,h] using circle_local P p (t,i,.bl)
    have hm : dartComponent P p hp S (t,i,.tl) =
        dartComponent P p hp S (t,i,.bl) := by
      simpa [G,edgeEnds,h,dartComponent] using hc
    cases a <;> cases b <;> simp only [dartComponent, ht, hb] <;>
      first | rfl | exact hm | exact hm.symm
  · have hl : circle P p (t,i,.bl) = circle P p (t,i,.tl) := by
      simpa [localMate,h] using circle_local P p (t,i,.tl)
    have hr : circle P p (t,i,.br) = circle P p (t,i,.tr) := by
      simpa [localMate,h] using circle_local P p (t,i,.tr)
    have hm : dartComponent P p hp S (t,i,.tl) =
        dartComponent P p hp S (t,i,.tr) := by
      simpa [G,edgeEnds,h,dartComponent] using hc
    cases a <;> cases b <;> simp only [dartComponent, hl, hr] <;>
      first | rfl | exact hm | exact hm.symm

theorem mixedMate_component (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (x : Dart P) :
    dartComponent P p hp S (mixedMate P p S x) = dartComponent P p hp S x := by
  rcases x with ⟨t,i,a⟩
  by_cases h : (t,i) ∈ S
  · simp only [mixedMate,h,↓reduceIte,localMate]
    split_ifs <;> exact selected_crossing_component P p hp S t i h _ _
  · simp only [mixedMate,h,↓reduceIte,dartComponent]
    rw [circle_local]

theorem mixedReach_component (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) {x y : Dart P} (h : MixedReach P p S x y) :
    dartComponent P p hp S x = dartComponent P p hp S y := by
  induction h with
  | rel x y h =>
    rcases h with rfl | rfl
    · exact (mixedMate_component P p hp S x).symm
    · unfold dartComponent
      rw [circle_external]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The actual mixed-circle to spanning-component map, obtained by descent. -/
def mixedComponentMap (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) :
    MixedCircle P p S → (referenceGraph P p hp S).ConnectedComponent :=
  Quotient.lift (dartComponent P p hp S)
    (fun _ _ h => mixedReach_component P p hp S h)

/-- This is the implication needed in the rank-increasing surgery case. -/
theorem distinct_reference_components_force_distinct_mixed_circles
    (P : Parameters) (p : ℕ) (hp : p < 2) (S : Finset (Crossing P))
    (x y : Dart P) (h : dartComponent P p hp S x ≠ dartComponent P p hp S y) :
    mixedCircle P p S x ≠ mixedCircle P p S y := by
  intro he
  exact h (congrArg (mixedComponentMap P p hp S) he)

/-- Connectedness follows from the actual wires and four crossing ports.
It uses neither an untyped geometry certificate nor the desired circle count. -/
theorem referenceGraph_connected (P : Parameters) (p : ℕ) (hp : p < 2) :
    (referenceGraph P p hp Finset.univ).Connected := by
  let z : Fin P.n := ⟨0,by have := P.hn; omega⟩
  let F := dartComponent P p hp Finset.univ
  have ports (t : ZMod P.m) (i : Fin P.n) (a b : Port) :
      F (t,i,a) = F (t,i,b) :=
    selected_crossing_component P p hp Finset.univ t i (Finset.mem_univ _) a b
  have wire (x : Dart P) : F (external P x) = F x := by
    dsimp [F,dartComponent]
    rw [circle_external]
  have boxes (t : ZMod P.m) : ∀ j (hj : j < P.n),
      F (t,(⟨j,hj⟩ : Fin P.n),.tl) = F (t,z,.tl) := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      let i : Fin P.n := ⟨j,by omega⟩
      have hi : i.val + 1 < P.n := hj
      have he : external P (t,i,.br) = (t,(⟨j+1,hj⟩ : Fin P.n),.tl) := by
        simp [external,hi,succIndex,i]
      calc
        F (t,(⟨j+1,hj⟩ : Fin P.n),.tl) = F (t,i,.br) := he ▸ wire (t,i,.br)
        _ = F (t,i,.tl) := ports t i .br .tl
        _ = F (t,z,.tl) := ih i.isLt
  have periods (t : ZMod P.m) : F (t+1,z,.tl) = F (t,z,.tl) := by
    have he : external P (t,z,.bl) = (t+1,z,.tl) := by simp [external,z]
    exact (he ▸ wire (t,z,.bl)).trans (ports t z .bl .tl)
  have times (t : ZMod P.m) : F (t,z,.tl) = F (0,z,.tl) := by
    obtain ⟨j,rfl⟩ := ZMod.natCast_zmod_surjective t
    induction j with
    | zero => simp only [Nat.cast_zero]
    | succ j ih =>
      simpa only [Nat.cast_add,Nat.cast_one] using (periods (j : ZMod P.m)).trans ih
  have all (x : Dart P) : F x = F (0,z,.tl) := by
    rcases x with ⟨t,i,a⟩
    exact (ports t i a .tl).trans ((boxes t i.val i.isLt).trans (times t))
  apply (referenceGraph P p hp Finset.univ).connected_iff_exists_forall_reachable.mpr
  refine ⟨circle P p (0,z,.tl),?_⟩
  intro v
  induction v using Quotient.inductionOn with
  | h x =>
    apply SimpleGraph.ConnectedComponent.exact
    exact (all x).symm

end D5.S3.Topology.WeavingMixedComponents

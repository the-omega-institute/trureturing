/- GID: D5/S3/Topology/ColoredMatchingSwitch
   generality: G
   mirror-B: D5/B/S3/Topology/ColoredMatchingSwitch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Basic]
   utility: none
   digest: Two-edge surgery controls actual colored matching component counts. -/

import D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Sum

/-! Connectivity retains both matching colors, including coincident matching edges.
The cut first-return pairing identifies the affected connectivity quotients. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Topology.ColoredMatchingSwitch

noncomputable section
attribute [local instance] Classical.propDecidable
open Equiv
open D5.S3.Combinatorics.PerfectMatchings

variable {V W : Type*}

/-- The two actual colored edges, before any forgetting of parallel edges. -/
def Step (s t : Perm V) (x y : V) : Prop := s x = y ∨ t x = y

abbrev Reach (s t : Perm V) := Relation.EqvGen (Step s t)

/-- Actual connected-component quotient of the two matching adjacency. -/
abbrev Circle (s t : Perm V) := Quotient (Relation.EqvGen.setoid (Step s t))

def circle (s t : Perm V) (x : V) : Circle s t := Quotient.mk _ x

private theorem reach_refl (s t : Perm V) (x : V) : Reach s t x x := .refl _

private theorem reach_symm {s t : Perm V} {x y : V} (h : Reach s t x y) :
    Reach s t y x := .symm _ _ h

private theorem reach_trans {s t : Perm V} {x y z : V}
    (h : Reach s t x y) (k : Reach s t y z) : Reach s t x z :=
  .trans _ _ _ h k

theorem reach_iff_matchingConnected (s t : Perm V)
    (hs : Function.Involutive s) (ht : Function.Involutive t) (x y : V) :
    Reach s t x y ↔ InvolutionOrbitSplit.Connected s t x y := by
  haveI : Std.Symm (Step s t) := ⟨by
    intro u v huv
    rcases huv with huv | huv
    · left
      rw [← huv]
      exact hs u
    · right
      rw [← huv]
      exact ht u⟩
  change Relation.EqvGen (Step s t) x y ↔ Relation.ReflTransGen (Step s t) x y
  rw [Relation.EqvGen.eqvGen_eq_reflTransGen]

/-- Consume the supplier's genuine disjoint alternating-component split.
Singleton product orbits correspond to two parallel colored edges. -/
private theorem reach_two_orbits (s t : Perm V)
    (hs : Function.Involutive s) (ht : Function.Involutive t)
    (hsfree : ∀ x, s x ≠ x) (htfree : ∀ x, t x ≠ x) (x y : V) :
    Reach s t x y ↔ (s * t).SameCycle x y ∨ (s * t).SameCycle (s x) y := by
  rw [reach_iff_matchingConnected s t hs ht]
  have h := (InvolutionOrbitSplit.component_split s t hs ht hsfree htfree x).2.2.2.1
  exact Set.ext_iff.mp h y

private theorem reach_map (e : V ≃ W) (s t : Perm V) {x y : V}
    (h : Reach s t x y) :
    Reach (e.permCongr s) (e.permCongr t) (e x) (e y) := by
  induction h with
  | rel u v h =>
    apply Relation.EqvGen.rel
    simpa only [Step, Equiv.permCongr_apply, Equiv.symm_apply_apply,
      e.injective.eq_iff] using h
  | refl => exact .refl _
  | symm _ _ _ ih => exact reach_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact reach_trans ih₁ ih₂

private theorem reach_permCongr_iff (e : V ≃ W) (s t : Perm V) (x y : V) :
    Reach (e.permCongr s) (e.permCongr t) (e x) (e y) ↔ Reach s t x y := by
  constructor
  · intro h
    have hs : e.symm.permCongr (e.permCongr s) = s :=
      e.permCongr.symm_apply_apply s
    have ht : e.symm.permCongr (e.permCongr t) = t :=
      e.permCongr.symm_apply_apply t
    simpa only [hs, ht, Equiv.symm_apply_apply] using
      reach_map e.symm (e.permCongr s) (e.permCongr t) h
  · exact reach_map e s t

private def circleCongr (e : V ≃ W) (s t : Perm V) :
    Circle s t ≃ Circle (e.permCongr s) (e.permCongr t) :=
  Quotient.congr e (fun x y => (reach_permCongr_iff e s t x y).symm)

/- Components avoiding a marked set: a changed edge can only be encountered
after reaching the marked set. This proves the unchanged-component assertion
in both directions, including all components disjoint from the surgery. -/

private def Touched (s t : Perm V) (E : Set V) (q : Circle s t) : Prop :=
  ∃ e : E, circle s t e = q

private abbrev Untouched (s t : Perm V) (E : Set V) :=
  {q : Circle s t // ¬ Touched s t E q}

private theorem reach_from_avoiding (s f g : Perm V)
    (hs : Function.Involutive s) (hg : Function.Involutive g) (E : Set V)
    (hfg : ∀ x, x ∉ E → f x = g x) {x y : V}
    (hx : ∀ e : E, ¬ Reach s f x e) (hxy : Reach s g x y) : Reach s f x y := by
  have h := (reach_iff_matchingConnected s g hs hg x y).mp hxy
  clear hxy
  induction h with
  | refl => exact reach_refl s f x
  | @tail u v h huv ih =>
    have hu : u ∉ E := by
      intro hu
      exact hx ⟨u, hu⟩ ih
    apply reach_trans ih
    apply Relation.EqvGen.rel
    rcases huv with huv | huv
    · exact Or.inl huv
    · exact Or.inr ((hfg u hu).trans huv)

private theorem untouched_out (s f : Perm V) (E : Set V)
    (q : Untouched s f E) : ∀ e : E, ¬ Reach s f q.val.out e := by
  intro e he
  apply q.property
  refine ⟨e, ?_⟩
  exact (Quotient.sound he).symm.trans (Quotient.out_eq q.val)

private def untouchedMap (s f g : Perm V)
    (hs : Function.Involutive s) (hg : Function.Involutive g) (E : Set V)
    (hfg : ∀ x, x ∉ E → f x = g x) : Untouched s f E → Untouched s g E := by
  intro q
  refine ⟨circle s g q.val.out, ?_⟩
  rintro ⟨e, he⟩
  have hge : Reach s g q.val.out e := Quotient.exact he.symm
  exact untouched_out s f E q e
    (reach_from_avoiding s f g hs hg E hfg (untouched_out s f E q) hge)

private def untouchedEquiv (s f g : Perm V)
    (hs : Function.Involutive s) (hf : Function.Involutive f)
    (hg : Function.Involutive g) (E : Set V)
    (hfg : ∀ x, x ∉ E → f x = g x) : Untouched s f E ≃ Untouched s g E := by
  apply Equiv.ofBijective (untouchedMap s f g hs hg E hfg)
  constructor
  · intro q q' he
    apply Subtype.ext
    have hge : Reach s g q.val.out q'.val.out :=
      Quotient.exact (congrArg Subtype.val he)
    have hfe := reach_from_avoiding s f g hs hg E hfg (untouched_out s f E q) hge
    exact (Quotient.out_eq q.val).symm.trans
      ((Quotient.sound hfe).trans (Quotient.out_eq q'.val))
  · intro q'
    have hgf : ∀ x, x ∉ E → g x = f x := fun x hx => (hfg x hx).symm
    have hxg := untouched_out s g E q'
    have hxf : ∀ e : E, ¬ Reach s f q'.val.out e := by
      intro e he
      exact hxg e (reach_from_avoiding s g f hs hf E hgf hxg he)
    have hq : ¬ Touched s f E (circle s f q'.val.out) := by
      rintro ⟨e, he⟩
      exact hxf e (Quotient.exact he.symm)
    let q : Untouched s f E := ⟨circle s f q'.val.out, hq⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    have hfo : Reach s f q.val.out q'.val.out :=
      Quotient.exact (Quotient.out_eq (circle s f q'.val.out))
    have hgo := reach_from_avoiding s g f hs hf E hgf hxg (reach_symm hfo)
    exact (Quotient.sound hgo).symm.trans (Quotient.out_eq q'.val)

/- Actual cut closure. At exposed endpoints r is the identity; elsewhere
reattachment changes nothing. No simple-graph degree assertion is used. -/

private abbrev Endpoints (r : Perm V) := {x : V // r x = x}

private def close (r : Perm V) (J : Perm (Endpoints r)) : Perm V := r * J.ofSubtype

private theorem close_endpoint (r : Perm V) (J : Perm (Endpoints r))
    (x : Endpoints r) : close r J x = (J x : V) := by
  simp only [close, Perm.mul_apply, Perm.ofSubtype_apply_coe, (J x).property]

private theorem close_outside (r : Perm V) (J : Perm (Endpoints r))
    {x : V} (hx : r x ≠ x) : close r J x = r x := by
  rw [close, Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem J hx]

private theorem close_involutive (r : Perm V) (hr : Function.Involutive r)
    (J : Perm (Endpoints r)) (hJ : Function.Involutive J) :
    Function.Involutive (close r J) := by
  intro x
  by_cases hx : r x = x
  · change close r J (close r J (⟨x, hx⟩ : Endpoints r)) = x
    rw [close_endpoint, close_endpoint, hJ]
  · have hrx : r (r x) ≠ r x := fun he => hx (r.injective he)
    rw [close_outside r J hx, close_outside r J hrx, hr]

private theorem close_free (r : Perm V) (J : Perm (Endpoints r))
    (hJfree : ∀ x, J x ≠ x) : ∀ x, close r J x ≠ x := by
  intro x he
  by_cases hx : r x = x
  · apply hJfree ⟨x, hx⟩
    apply Subtype.ext
    exact (close_endpoint r J ⟨x, hx⟩).symm.trans he
  · exact hx ((close_outside r J hx).symm.trans he)

private theorem endpoint_reach_iff [Finite V] (s r : Perm V)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (hsfree : ∀ x, s x ≠ x) (J : Perm (Endpoints r))
    (hJ : Function.Involutive J) (hJfree : ∀ x, J x ≠ x)
    (x y : Endpoints r) :
    Reach s (close r J) x y ↔ Reach (FiniteEndpointPairing.endpointPairing s r hs hr) J x y := by
  let P := FiniteEndpointPairing.endpointPairing s r hs hr
  have hP := FiniteEndpointPairing.endpoint_pairing_involutive s r hs hr
  have hPfree := FiniteEndpointPairing.endpoint_pairing_fixed_point_free s r hs hr hsfree
  rw [reach_two_orbits s (close r J) hs (close_involutive r hr J hJ)
    hsfree (close_free r J hJfree), reach_two_orbits P J hP hJ hPfree hJfree]
  have hstep : (s * close r J) (J x : V) = s x := by
    rw [Perm.mul_apply, close_endpoint, hJ]
  have hstepP : (P * J) (J x) = P x := by rw [Perm.mul_apply, hJ]
  have hb : (s * close r J).SameCycle (s x) y ↔
      (s * close r J).SameCycle (J x : V) y := by
    rw [← hstep, Perm.sameCycle_apply_left]
  have hbP : (P * J).SameCycle (P x) y ↔ (P * J).SameCycle (J x) y := by
    rw [← hstepP, Perm.sameCycle_apply_left]
  rw [hb, hbP]
  exact or_congr (FiniteEndpointPairing.endpoint_pairing_reattach_same_cycle s r hs hr J x y)
    (FiniteEndpointPairing.endpoint_pairing_reattach_same_cycle s r hs hr J (J x) y)

/-- Every affected component is represented by an actual cut endpoint, and
two such representatives agree exactly when their endpoint circles agree. -/
private def touchedEquiv [Finite V] (s r : Perm V)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (hsfree : ∀ x, s x ≠ x) (J : Perm (Endpoints r))
    (hJ : Function.Involutive J) (hJfree : ∀ x, J x ≠ x) :
    Circle (FiniteEndpointPairing.endpointPairing s r hs hr) J ≃
      {q : Circle s (close r J) // Touched s (close r J) {x | r x = x} q} := by
  let P := FiniteEndpointPairing.endpointPairing s r hs hr
  let f : Circle P J →
      {q : Circle s (close r J) // Touched s (close r J) {x | r x = x} q} :=
    Quotient.lift (fun x : Endpoints r => ⟨circle s (close r J) x, ⟨x, rfl⟩⟩)
      (by
        intro x y hxy
        apply Subtype.ext
        exact Quotient.sound ((endpoint_reach_iff s r hs hr hsfree J hJ hJfree x y).mpr hxy))
  apply Equiv.ofBijective f
  constructor
  · intro q q'
    induction q using Quotient.inductionOn with
    | h x =>
      induction q' using Quotient.inductionOn with
      | h y =>
        intro he
        apply Quotient.sound
        exact (endpoint_reach_iff s r hs hr hsfree J hJ hJfree x y).mp
          (Quotient.exact (congrArg Subtype.val he))
  · intro q
    obtain ⟨x, hx⟩ := q.property
    exact ⟨circle P J x, Subtype.ext hx⟩

private theorem close_card [Finite V] (s r : Perm V)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (hsfree : ∀ x, s x ≠ x) (J : Perm (Endpoints r))
    (hJ : Function.Involutive J) (hJfree : ∀ x, J x ≠ x) :
    Nat.card (Circle s (close r J)) =
      Nat.card (Untouched s (close r J) {x | r x = x}) +
      Nat.card (Circle (FiniteEndpointPairing.endpointPairing s r hs hr) J) := by
  classical
  have hsum := Nat.card_congr (Equiv.sumCompl
    (Touched s (close r J) {x | r x = x}))
  rw [Nat.card_sum] at hsum
  change Nat.card {q : Circle s (close r J) // Touched s (close r J) {x | r x = x} q} +
    Nat.card (Untouched s (close r J) {x | r x = x}) = Nat.card (Circle s (close r J)) at hsum
  have ht := Nat.card_congr (touchedEquiv s r hs hr hsfree J hJ hJfree)
  omega

/- Four endpoint arithmetic, with explicit quotient equivalences. Finite
case analysis is confined to the three proved forms of a four-point matching.
The arbitrary finite dart carrier is never enumerated. -/

private theorem four_involutive (J : Perm (Fin 4))
    (hJ : J = FiniteBandSwitch.FourEndpoint.J0 ∨ J = FiniteBandSwitch.FourEndpoint.thirdPairing ∨ J = FiniteBandSwitch.FourEndpoint.J1) :
    Function.Involutive J := by
  rcases hJ with rfl | rfl | rfl <;> intro i <;> fin_cases i <;> rfl

private theorem four_free (J : Perm (Fin 4))
    (hJ : J = FiniteBandSwitch.FourEndpoint.J0 ∨ J = FiniteBandSwitch.FourEndpoint.thirdPairing ∨ J = FiniteBandSwitch.FourEndpoint.J1) : ∀ i, J i ≠ i := by
  rcases hJ with rfl | rfl | rfl <;> intro i <;> fin_cases i <;>
    simp [FiniteBandSwitch.FourEndpoint.J0, FiniteBandSwitch.FourEndpoint.thirdPairing,
      FiniteBandSwitch.FourEndpoint.J1, Perm.mul_apply, swap_apply_def]

private theorem four_offdiag_connected (P J : Perm (Fin 4))
    (hP : Function.Involutive P) (hJ : Function.Involutive J)
    (hPfree : ∀ i, P i ≠ i) (hJfree : ∀ i, J i ≠ i) (hne : P ≠ J) :
    ∀ x y, Reach P J x y := by
  have hprod : Function.Involutive (P * J) := by
    rcases FiniteBandSwitch.FourEndpoint.pairing_three_forms P hP hPfree with rfl | rfl | rfl <;>
      rcases FiniteBandSwitch.FourEndpoint.pairing_three_forms J hJ hJfree with rfl | rfl | rfl <;>
      intro i <;> fin_cases i <;> rfl
  intro x y
  rw [reach_iff_matchingConnected P J hP hJ,
    InvolutionOrbitSplit.connected_iff_rotation_orbits P J hP hJ]
  simp only [FiniteBandSwitch.FourEndpoint.same_cycle_involutive_iff (P * J) hprod]
  rcases FiniteBandSwitch.FourEndpoint.pairing_three_forms P hP hPfree with rfl | rfl | rfl <;>
    rcases FiniteBandSwitch.FourEndpoint.pairing_three_forms J hJ hJfree with rfl | rfl | rfl
  all_goals try exact False.elim (hne rfl)
  all_goals fin_cases x <;> fin_cases y <;>
    simp [FiniteBandSwitch.FourEndpoint.J0, FiniteBandSwitch.FourEndpoint.thirdPairing,
      FiniteBandSwitch.FourEndpoint.J1, Perm.mul_apply, swap_apply_def]

private def quotientByClassifier {A B : Type*} (S : Setoid A) (f : A → B)
    (hker : ∀ x y, f x = f y ↔ S x y) (hsurj : Function.Surjective f) :
    Quotient S ≃ B := by
  let F : Quotient S → B := Quotient.lift f (fun x y h => (hker x y).mpr h)
  apply Equiv.ofBijective F
  constructor
  · intro q q'
    induction q using Quotient.inductionOn with
    | h x =>
      induction q' using Quotient.inductionOn with
      | h y =>
        intro he
        exact Quotient.sound ((hker x y).mp he)
  · intro b
    obtain ⟨a, ha⟩ := hsurj b
    exact ⟨Quotient.mk S a, ha⟩

private theorem four_diagonal_card (P : Perm (Fin 4))
    (hP : Function.Involutive P) (hPfree : ∀ i, P i ≠ i) :
    Nat.card (Circle P P) = 2 := by
  classical
  let f : Fin 4 → Bool := fun i => if i = 0 ∨ i = P 0 then false else true
  have hreach (x y : Fin 4) : Reach P P x y ↔ x = y ∨ P x = y := by
    rw [reach_iff_matchingConnected P P hP hP,
      InvolutionOrbitSplit.connected_iff_rotation_orbits P P hP hP]
    simp only [FiniteEndpointPairing.square_of_involutive P hP, Perm.sameCycle_one]
  have hker : ∀ x y, f x = f y ↔ Reach P P x y := by
    intro x y
    rw [hreach]
    rcases FiniteBandSwitch.FourEndpoint.pairing_three_forms P hP hPfree with rfl | rfl | rfl <;>
      fin_cases x <;> fin_cases y <;>
      simp [f, FiniteBandSwitch.FourEndpoint.J0,
        FiniteBandSwitch.FourEndpoint.thirdPairing, FiniteBandSwitch.FourEndpoint.J1,
        Perm.mul_apply, swap_apply_def]
  have hsurj : Function.Surjective f := by
    intro b
    rcases FiniteBandSwitch.FourEndpoint.pairing_three_forms P hP hPfree with rfl | rfl | rfl <;> cases b
    · exact ⟨0, by simp [f]⟩
    · exact ⟨1, by simp [f, FiniteBandSwitch.FourEndpoint.J0, Perm.mul_apply, swap_apply_def]⟩
    · exact ⟨0, by simp [f]⟩
    · exact ⟨2, by simp [f, FiniteBandSwitch.FourEndpoint.thirdPairing, Perm.mul_apply, swap_apply_def]⟩
    · exact ⟨0, by simp [f]⟩
    · exact ⟨1, by simp [f, FiniteBandSwitch.FourEndpoint.J1, Perm.mul_apply, swap_apply_def]⟩
  have he := quotientByClassifier (Relation.EqvGen.setoid (Step P P)) f hker hsurj
  calc
    Nat.card (Circle P P) = Nat.card Bool := Nat.card_congr he
    _ = 2 := by simp only [Nat.card_eq_fintype_card, Fintype.card_bool]

private theorem four_card (P J : Perm (Fin 4))
    (hP : Function.Involutive P) (hJ : Function.Involutive J)
    (hPfree : ∀ i, P i ≠ i) (hJfree : ∀ i, J i ≠ i) :
    Nat.card (Circle P J) = if P = J then 2 else 1 := by
  classical
  by_cases he : P = J
  · subst J
    simpa using four_diagonal_card P hP hPfree
  · rw [if_neg he]
    haveI : Subsingleton (Circle P J) := ⟨by
      intro q q'
      induction q using Quotient.inductionOn with
      | h x =>
        induction q' using Quotient.inductionOn with
        | h y => exact Quotient.sound (four_offdiag_connected P J hP hJ hPfree hJfree he x y)⟩
    exact Nat.card_of_subsingleton (circle P J 0)

private theorem permCongr_involutive (e : V ≃ W) (p : Perm V)
    (hp : Function.Involutive p) : Function.Involutive (e.permCongr p) := by
  intro x
  change e (p (e.symm (e (p (e.symm x)))) ) = x
  rw [e.symm_apply_apply, hp, e.apply_symm_apply]

private theorem permCongr_free (e : V ≃ W) (p : Perm V)
    (hp : ∀ x, p x ≠ x) : ∀ x, e.permCongr p x ≠ x := by
  intro x hx
  apply hp (e.symm x)
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using congrArg e.symm hx

private theorem four_closure_surgery [Finite V] (s r : Perm V)
    (hs : Function.Involutive s) (hr : Function.Involutive r)
    (hsfree : ∀ x, s x ≠ x) (e : Fin 4 ≃ Endpoints r) :
    let f := close r (e.permCongr FiniteBandSwitch.FourEndpoint.J0)
    let g := close r (e.permCongr FiniteBandSwitch.FourEndpoint.thirdPairing)
    |(Nat.card (Circle s g) : ℤ) - (Nat.card (Circle s f) : ℤ)| ≤ 1 ∧
      (¬ Reach s f (e 0) (e 1) →
        (Nat.card (Circle s g) : ℤ) = (Nat.card (Circle s f) : ℤ) - 1) := by
  classical
  let P := FiniteEndpointPairing.endpointPairing s r hs hr
  let Q := e.symm.permCongr P
  let J := e.permCongr FiniteBandSwitch.FourEndpoint.J0
  let K := e.permCongr FiniteBandSwitch.FourEndpoint.thirdPairing
  have h0 := four_involutive FiniteBandSwitch.FourEndpoint.J0 (Or.inl rfl)
  have h1 := four_involutive FiniteBandSwitch.FourEndpoint.thirdPairing (Or.inr (Or.inl rfl))
  have h0free := four_free FiniteBandSwitch.FourEndpoint.J0 (Or.inl rfl)
  have h1free := four_free FiniteBandSwitch.FourEndpoint.thirdPairing (Or.inr (Or.inl rfl))
  have hJ := permCongr_involutive e FiniteBandSwitch.FourEndpoint.J0 h0
  have hK := permCongr_involutive e FiniteBandSwitch.FourEndpoint.thirdPairing h1
  have hJfree := permCongr_free e FiniteBandSwitch.FourEndpoint.J0 h0free
  have hKfree := permCongr_free e FiniteBandSwitch.FourEndpoint.thirdPairing h1free
  have hP := FiniteEndpointPairing.endpoint_pairing_involutive s r hs hr
  have hPfree := FiniteEndpointPairing.endpoint_pairing_fixed_point_free s r hs hr hsfree
  have hQ := permCongr_involutive e.symm P hP
  have hQfree := permCongr_free e.symm P hPfree
  have hrestore : e.permCongr Q = P := e.permCongr.apply_symm_apply P
  have hc0 := close_card s r hs hr hsfree J hJ hJfree
  have hc1 := close_card s r hs hr hsfree K hK hKfree
  have hunchanged := Nat.card_congr (untouchedEquiv s (close r J) (close r K)
    hs (close_involutive r hr J hJ) (close_involutive r hr K hK)
    {x | r x = x} (by
      intro x hx
      exact (close_outside r J hx).trans (close_outside r K hx).symm))
  have he0 : Nat.card (Circle P J) = Nat.card (Circle Q FiniteBandSwitch.FourEndpoint.J0) := by
    have he := Nat.card_congr (circleCongr e Q FiniteBandSwitch.FourEndpoint.J0)
    simpa only [hrestore] using he.symm
  have he1 : Nat.card (Circle P K) = Nat.card (Circle Q FiniteBandSwitch.FourEndpoint.thirdPairing) := by
    have he := Nat.card_congr (circleCongr e Q FiniteBandSwitch.FourEndpoint.thirdPairing)
    simpa only [hrestore] using he.symm
  have hb0 := four_card Q FiniteBandSwitch.FourEndpoint.J0 hQ h0 hQfree h0free
  have hb1 := four_card Q FiniteBandSwitch.FourEndpoint.thirdPairing hQ h1 hQfree h1free
  have hdiff :
      (Nat.card (Circle s (close r K)) : ℤ) - Nat.card (Circle s (close r J)) =
      (Nat.card (Circle Q FiniteBandSwitch.FourEndpoint.thirdPairing) : ℤ) - Nat.card (Circle Q FiniteBandSwitch.FourEndpoint.J0) := by
    dsimp only [P] at he0 he1
    omega
  change |(Nat.card (Circle s (close r K)) : ℤ) - Nat.card (Circle s (close r J))| ≤ 1 ∧ _
  constructor
  · rw [hdiff, hb0, hb1]
    split_ifs <;> norm_num
  · intro hn
    have hnQ : ¬ Reach Q FiniteBandSwitch.FourEndpoint.J0 0 1 := by
      intro hq
      have hep : Reach P J (e 0) (e 1) := by
        have hh := (reach_permCongr_iff e Q FiniteBandSwitch.FourEndpoint.J0 0 1).mpr hq
        simpa only [hrestore] using hh
      exact hn ((endpoint_reach_iff s r hs hr hsfree J hJ hJfree (e 0) (e 1)).mpr hep)
    have hQ0 : Q = FiniteBandSwitch.FourEndpoint.J0 := by
      by_contra hne
      exact hnQ (four_offdiag_connected Q FiniteBandSwitch.FourEndpoint.J0 hQ h0 hQfree h0free hne 0 1)
    have h01 : FiniteBandSwitch.FourEndpoint.J0 ≠ FiniteBandSwitch.FourEndpoint.thirdPairing := by
      intro he
      have hz := congrArg (fun f : Perm (Fin 4) => f 0) he
      norm_num [FiniteBandSwitch.FourEndpoint.J0, FiniteBandSwitch.FourEndpoint.thirdPairing,
        Perm.mul_apply, swap_apply_def] at hz
    rw [hQ0, if_pos rfl] at hb0
    rw [hQ0, if_neg h01] at hb1
    rw [hQ0, hb0, hb1] at hdiff
    change (Nat.card (Circle s (close r K)) : ℤ) =
      (Nat.card (Circle s (close r J)) : ℤ) - 1
    omega

/- The original matching supplies the cut. Its four labels are a,c,b,d;
the two closures J0 and thirdPairing are therefore exactly t and tPrime. -/

private theorem cut_fixed_iff (t : Perm V) (ht : Function.Involutive t)
    (htfree : ∀ x, t x ≠ x) (a c x : V) :
    FiniteBandSwitch.OriginalCut.cutPerm t ht a c x = x ↔ x ∈ FiniteBandSwitch.OriginalCut.boundary t a c := by
  classical
  change (if x ∈ FiniteBandSwitch.OriginalCut.boundary t a c then x else t x) = x ↔ _
  by_cases hx : x ∈ FiniteBandSwitch.OriginalCut.boundary t a c <;> simp [hx, htfree x]

private theorem closure_of_actions (r f : Perm V) (e : Fin 4 ≃ Endpoints r)
    (J : Perm (Fin 4))
    (he : ∀ i, f (e i) = (e (J i) : V))
    (ho : ∀ x, r x ≠ x → f x = r x) : f = close r (e.permCongr J) := by
  ext x
  by_cases hx : r x = x
  · obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    have hix : (e i : V) = x := congrArg Subtype.val hi
    rw [← hix, close_endpoint, Equiv.permCongr_apply, e.symm_apply_apply]
    exact he i
  · exact (ho x hx).trans (close_outside r (e.permCongr J) hx).symm

/-- A two-edge switch of actual finite fixed-point-free matchings changes the
number of actual connectivity classes by at most one. Distinct old circles
merge exactly. No orientation, embedding, or supplied partition is assumed. -/
theorem colored_switch_circle_count [Finite V] (s t tPrime : Perm V)
    (hs : Function.Involutive s) (ht : Function.Involutive t)
    (htPrime : Function.Involutive tPrime)
    (hsfree : ∀ x, s x ≠ x) (htfree : ∀ x, t x ≠ x)
    (htPrimefree : ∀ x, tPrime x ≠ x)
    (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (htab : t a = b) (htcd : t c = d)
    (htPac : tPrime a = c) (htPbd : tPrime b = d)
    (houtside : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → tPrime x = t x) :
    |(Nat.card (Circle s tPrime) : ℤ) - (Nat.card (Circle s t) : ℤ)| ≤ 1 ∧
      (¬ Reach s t a c →
        (Nat.card (Circle s tPrime) : ℤ) = (Nat.card (Circle s t) : ℤ) - 1) := by
  classical
  have htba : t b = a := by simpa only [htab] using ht a
  have htdc : t d = c := by simpa only [htcd] using ht c
  have htPca : tPrime c = a := by simpa only [htPac] using htPrime a
  have htPdb : tPrime d = b := by simpa only [htPbd] using htPrime b
  have hinj : Function.Injective (FiniteBandSwitch.OriginalCut.boundaryLabel t a c) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [FiniteBandSwitch.OriginalCut.boundaryLabel]
  let r := FiniteBandSwitch.OriginalCut.cutPerm t ht a c
  let e := FiniteBandSwitch.OriginalCut.cutEquiv t ht htfree a c hinj
  have hr : Function.Involutive r := by
    intro x
    exact (FiniteBandSwitch.OriginalCut.cutPerm t ht a c).symm_apply_apply x
  have he (i : Fin 4) : (e i : V) = FiniteBandSwitch.OriginalCut.boundaryLabel t a c i := rfl
  have h0 : t = close r (e.permCongr FiniteBandSwitch.FourEndpoint.J0) := by
    apply closure_of_actions r t e FiniteBandSwitch.FourEndpoint.J0
    · intro i
      simp only [he]
      fin_cases i <;> simp [FiniteBandSwitch.OriginalCut.boundaryLabel, FiniteBandSwitch.FourEndpoint.J0, Perm.mul_apply,
        swap_apply_def, htab, htcd, htba, htdc]
    · intro x hx
      have hn : x ∉ FiniteBandSwitch.OriginalCut.boundary t a c := by
        intro hm
        exact hx ((cut_fixed_iff t ht htfree a c x).mpr hm)
      change t x = if x ∈ FiniteBandSwitch.OriginalCut.boundary t a c then x else t x
      rw [if_neg hn]
  have h1 : tPrime = close r (e.permCongr FiniteBandSwitch.FourEndpoint.thirdPairing) := by
    apply closure_of_actions r tPrime e FiniteBandSwitch.FourEndpoint.thirdPairing
    · intro i
      simp only [he]
      fin_cases i <;> simp [FiniteBandSwitch.OriginalCut.boundaryLabel, FiniteBandSwitch.FourEndpoint.thirdPairing, Perm.mul_apply,
        swap_apply_def, htab, htcd, htPac, htPbd, htPca, htPdb]
    · intro x hx
      have hn : x ∉ FiniteBandSwitch.OriginalCut.boundary t a c := by
        intro hm
        exact hx ((cut_fixed_iff t ht htfree a c x).mpr hm)
      have hxa : x ≠ a := fun h => hn ⟨0, by simpa [FiniteBandSwitch.OriginalCut.boundaryLabel] using h.symm⟩
      have hxc : x ≠ c := fun h => hn ⟨1, by simpa [FiniteBandSwitch.OriginalCut.boundaryLabel] using h.symm⟩
      have hxb : x ≠ b := fun h => hn ⟨2, by simpa [FiniteBandSwitch.OriginalCut.boundaryLabel, htab] using h.symm⟩
      have hxd : x ≠ d := fun h => hn ⟨3, by simpa [FiniteBandSwitch.OriginalCut.boundaryLabel, htcd] using h.symm⟩
      change tPrime x = if x ∈ FiniteBandSwitch.OriginalCut.boundary t a c then x else t x
      rw [if_neg hn]
      exact houtside x hxa hxb hxc hxd
  have hea : (e 0 : V) = a := rfl
  have hec : (e 1 : V) = c := rfl
  have h := four_closure_surgery s r hs hr hsfree e
  simpa only [← h0, ← h1, hea, hec] using h

#print axioms colored_switch_circle_count

end
end D5.S3.Topology.ColoredMatchingSwitch

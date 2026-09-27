/- GID: D5/S3/ConceptDynamics/Coding/CompatibleResponseForgettingBound
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CompatibleResponseForgettingBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lagged square responses yield a linearly bounded exchange chain. -/

import D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

namespace CompatibleCertificate

variable {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
  {R : CountMat n k} {S : CountMat k n}

private def squareIncomingLift (c : CompatibleCertificate A B R S m) :
    IncomingLift A (Edge R) where
  project := Edge.source
  onto := (square_graph_essential_and_projections c).2.2.1
  lift := by
    intro a r
    exact c.incomingLift a r.val r.property.symm

private def squareOutgoingLift (c : CompatibleCertificate A B R S m) :
    IncomingLift B.transpose (Edge R) where
  project := Edge.target
  onto := (square_graph_essential_and_projections c).2.2.2.1
  lift := by
    intro b r
    exact c.outgoingLift r.val ⟨b.target, b.source, b.number⟩ r.property

private theorem squareOutgoingLift_path (c : CompatibleCertificate A B R S m) :
    ∀ {d : ℕ} {z t : Fin k} {i : Fin n}
      (beta : FinitePath B.transpose d z t) (r : Fin (R i t)),
      (c.squareOutgoingLift.liftPath beta
        ⟨(⟨i, t, r⟩ : Edge R), rfl⟩).val =
      (let lifted := c.liftOutgoingPath r
          (reverseFinitePath beta : FinitePath B d t z)
       (⟨lifted.1, z, lifted.2.2⟩ : Edge R)) := by
  intro d z t i beta
  induction beta generalizing i with
  | nil z =>
      intro r
      rfl
  | @cons d z u t b tail ih =>
      intro r
      let p : FinitePath B d t u := reverseFinitePath tail
      let prior := c.liftOutgoingPath r p
      have htail : c.squareOutgoingLift.liftPath tail
          ⟨(⟨i, t, r⟩ : Edge R), rfl⟩ =
          ⟨(⟨prior.1, u, prior.2.2⟩ : Edge R), rfl⟩ := by
        apply Subtype.ext
        exact ih r
      change (c.squareOutgoingLift.lift ⟨z, u, b⟩
          (c.squareOutgoingLift.liftPath tail
            ⟨(⟨i, t, r⟩ : Edge R), rfl⟩)).val =
        (let lifted := unsweep c.phi r (appendPath p b)
         (⟨lifted.1, z, lifted.2.2⟩ : Edge R))
      rw [htail]
      dsimp only
      rw [unsweep_append c.phi r p b]
      rfl

private theorem squareIncomingLift_path (c : CompatibleCertificate A B R S m) :
    ∀ {d : ℕ} {i j : Fin n} {z : Fin k}
      (alpha : FinitePath A d i j) (r : Fin (R j z)),
      (c.squareIncomingLift.liftPath alpha
        ⟨(⟨j, z, r⟩ : Edge R), rfl⟩).val =
      (let lifted := c.liftIncomingPath alpha r
       (⟨i, lifted.1, lifted.2⟩ : Edge R)) := by
  intro d i j z alpha
  induction alpha with
  | nil i =>
      intro r
      rfl
  | @cons d i j t a tail ih =>
      intro r
      have htail : c.squareIncomingLift.liftPath tail
          ⟨(⟨t, z, r⟩ : Edge R), rfl⟩ =
          ⟨(let rest := c.liftIncomingPath tail r
            (⟨j, rest.1, rest.2⟩ : Edge R)), rfl⟩ := by
        apply Subtype.ext
        exact ih r
      simp only [IncomingLift.liftPath, liftIncomingPath]
      rw [htail]
      rfl

private theorem squareIncomingLift_forgets_at_lag
    (c : CompatibleCertificate A B R S m) :
    c.squareIncomingLift.response m = Setoid.ker Edge.source := by
  apply Setoid.ext
  intro u v
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    rcases u with ⟨us, uz, ur⟩
    rcases v with ⟨vs, vz, vr⟩
    change us = vs at h
    subst vs
    change c.squareIncomingLift.responseReadout m
        (⟨us, uz, ur⟩ : Edge R) =
      c.squareIncomingLift.responseReadout m
        (⟨us, vz, vr⟩ : Edge R)
    unfold IncomingLift.responseReadout
    apply Prod.ext
    · rfl
    · funext i j alpha
      by_cases hj : us = j
      · cases hj
        have hsame :
            (c.squareIncomingLift.liftPath alpha
              ⟨(⟨us, uz, ur⟩ : Edge R), rfl⟩).val =
            (c.squareIncomingLift.liftPath alpha
              ⟨(⟨us, vz, vr⟩ : Edge R), rfl⟩).val := by
          calc
            _ = (let lifted := c.liftIncomingPath alpha ur
              (⟨i, lifted.1, lifted.2⟩ : Edge R)) :=
                c.squareIncomingLift_path alpha ur
            _ = (let rs := (c.psiA i us).symm alpha
              (⟨i, rs.1, rs.2.1⟩ : Edge R)) :=
                (square_lifts_left_forgetting c).2.2 alpha ur
            _ = (let lifted := c.liftIncomingPath alpha vr
              (⟨i, lifted.1, lifted.2⟩ : Edge R)) :=
                ((square_lifts_left_forgetting c).2.2 alpha vr).symm
            _ = _ := (c.squareIncomingLift_path alpha vr).symm
        simpa [squareIncomingLift] using congrArg some hsame
      · simp [squareIncomingLift, hj]

private theorem squareOutgoingLift_forgets_at_lag
    (c : CompatibleCertificate A B R S m) :
    c.squareOutgoingLift.response m = Setoid.ker Edge.target := by
  apply Setoid.ext
  intro u v
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    rcases u with ⟨ui, ut, ur⟩
    rcases v with ⟨vi, vt, vr⟩
    change ut = vt at h
    subst vt
    change c.squareOutgoingLift.responseReadout m
        (⟨ui, ut, ur⟩ : Edge R) =
      c.squareOutgoingLift.responseReadout m
        (⟨vi, ut, vr⟩ : Edge R)
    unfold IncomingLift.responseReadout
    apply Prod.ext
    · rfl
    · funext i j alpha
      by_cases hj : ut = j
      · cases hj
        have hsame :
            (c.squareOutgoingLift.liftPath alpha
              ⟨(⟨ui, ut, ur⟩ : Edge R), rfl⟩).val =
            (c.squareOutgoingLift.liftPath alpha
              ⟨(⟨vi, ut, vr⟩ : Edge R), rfl⟩).val := by
          let beta : FinitePath B m ut i := reverseFinitePath alpha
          calc
            _ = (let lifted := c.liftOutgoingPath ur beta
              (⟨lifted.1, i, lifted.2.2⟩ : Edge R)) :=
                c.squareOutgoingLift_path alpha ur
            _ = (let sr := (c.psiB ut i).symm beta
              (⟨sr.1, i, sr.2.2⟩ : Edge R)) :=
                square_lifts_right_forgetting c ur beta
            _ = (let lifted := c.liftOutgoingPath vr beta
              (⟨lifted.1, i, lifted.2.2⟩ : Edge R)) :=
                (square_lifts_right_forgetting c vr beta).symm
            _ = _ := (c.squareOutgoingLift_path alpha vr).symm
        simpa [squareOutgoingLift] using congrArg some hsame
      · simp [squareOutgoingLift, hj]

/-- A column counts the numbered A edges whose incoming square lift reaches
    its row edge. The proof reconstructs each square from that A edge and its
    terminal R edge, so parallel edges are not collapsed. -/
theorem square_column_lift_count (c : CompatibleCertificate A B R S m)
    (r s : Edge R) :
    c.squareMatrix ((Fintype.equivFin (Edge R)) s)
        ((Fintype.equivFin (Edge R)) r) =
      Nat.card {a : Edge A //
        ∃ h : a.target = r.source, (c.incomingLift a r h).val = s} := by
  classical
  let e := Fintype.equivFin (Edge R)
  let fiber := {sq : Square c // e sq.initialR = e s ∧ e sq.terminalR = e r}
  let incidence := {a : Edge A //
    ∃ h : a.target = r.source, (c.incomingLift a r h).val = s}
  have reconstruct (sq : Square c) :
      c.incomingSquare sq.leftA sq.terminalR rfl = sq := by
    apply (squareCoordinates c).injective
    rcases sq with ⟨i, z, ⟨j, a, edge⟩, output, commutes⟩
    rfl
  let toIncidence : fiber → incidence := fun p =>
    ⟨p.val.leftA, by
    rcases p with ⟨sq, ⟨hs, hr⟩⟩
    have hs' : sq.initialR = s := e.injective hs
    have hr' : sq.terminalR = r := e.injective hr
    have h : sq.leftA.target = r.source := by
      simpa [Square.leftA, Square.terminalR] using congrArg Edge.source hr'
    refine ⟨h, ?_⟩
    subst r
    have hLift := congrArg Square.initialR (reconstruct sq)
    change (c.incomingLift sq.leftA sq.terminalR rfl).val =
      sq.initialR at hLift
    exact hLift.trans hs'⟩
  have injective : Function.Injective toIncidence := by
    intro p q hpq
    apply Subtype.ext
    have ha := congrArg Subtype.val hpq
    change p.val.leftA = q.val.leftA at ha
    have hrp : p.val.terminalR = r := e.injective p.property.2
    have hrq : q.val.terminalR = r := e.injective q.property.2
    have hr : p.val.terminalR = q.val.terminalR := hrp.trans hrq.symm
    calc
      p.val = c.incomingSquare p.val.leftA p.val.terminalR rfl :=
        (reconstruct p.val).symm
      _ = c.incomingSquare q.val.leftA q.val.terminalR rfl := by
        simpa only [ha, hr]
      _ = q.val := reconstruct q.val
  have surjective : Function.Surjective toIncidence := by
    rintro ⟨a, ⟨h, hlift⟩⟩
    let sq := c.incomingSquare a r h
    have hstart : sq.initialR = s := by
      change (c.incomingLift a r h).val = s at hlift
      exact hlift
    have hterminal : sq.terminalR = r :=
      (square_lifts_left_forgetting c).1 a r h
    have hleft : sq.leftA = a := by
      rcases a with ⟨i, j, number⟩
      rcases r with ⟨j', z, edge⟩
      cases h
      rfl
    refine ⟨⟨sq, congrArg e hstart, congrArg e hterminal⟩, ?_⟩
    apply Subtype.ext
    exact hleft
  have hcard : Nat.card fiber = Nat.card incidence :=
    Nat.card_congr (Equiv.ofBijective toIncidence ⟨injective, surjective⟩)
  have hnumber := Fintype.card_congr (c.squareFiberEquiv (e s) (e r))
  calc
    c.squareMatrix (e s) (e r) = Fintype.card fiber := by
      simpa only [Fintype.card_fin] using hnumber
    _ = Nat.card fiber := (Nat.card_eq_fintype_card (α := fiber)).symm
    _ = Nat.card incidence := hcard

/-- A row counts the numbered B edges whose outgoing square lift reaches
    its column edge. The inverse phi square is reconstructed from its B edge
    and initial R edge. -/
theorem square_row_lift_count (c : CompatibleCertificate A B R S m)
    (r s : Edge R) :
    c.squareMatrix ((Fintype.equivFin (Edge R)) r)
        ((Fintype.equivFin (Edge R)) s) =
      Nat.card {b : Edge B //
        ∃ h : r.target = b.source, (c.outgoingLift r b h).val = s} := by
  classical
  let e := Fintype.equivFin (Edge R)
  let fiber := {sq : Square c // e sq.initialR = e r ∧ e sq.terminalR = e s}
  let incidence := {b : Edge B //
    ∃ h : r.target = b.source, (c.outgoingLift r b h).val = s}
  have reconstruct (sq : Square c) :
      c.outgoingSquare sq.initialR sq.rightB rfl = sq := by
    apply (squareCoordinates c).injective
    rcases sq with ⟨i, z, input, ⟨t, edge, b⟩, commutes⟩
    have hinput : (c.phi i z).symm ⟨t, edge, b⟩ = input := by
      rw [← commutes]
      exact (c.phi i z).symm_apply_apply input
    dsimp only [squareCoordinates, outgoingSquare, Square.initialR, Square.rightB]
    exact congrArg (fun p : EdgePair A R i z =>
      (⟨i, z, p⟩ : Σ i : Fin n, Σ z : Fin k, EdgePair A R i z)) hinput
  let toIncidence : fiber → incidence := fun p =>
    ⟨p.val.rightB, by
    rcases p with ⟨sq, ⟨hr, hs⟩⟩
    have hr' : sq.initialR = r := e.injective hr
    have hs' : sq.terminalR = s := e.injective hs
    have h : r.target = sq.rightB.source := by
      simpa [Square.initialR, Square.rightB] using (congrArg Edge.target hr').symm
    refine ⟨h, ?_⟩
    subst r
    have hLift := congrArg Square.terminalR (reconstruct sq)
    change (c.outgoingLift sq.initialR sq.rightB rfl).val =
      sq.terminalR at hLift
    exact hLift.trans hs'⟩
  have injective : Function.Injective toIncidence := by
    intro p q hpq
    apply Subtype.ext
    have hb := congrArg Subtype.val hpq
    change p.val.rightB = q.val.rightB at hb
    have hrp : p.val.initialR = r := e.injective p.property.1
    have hrq : q.val.initialR = r := e.injective q.property.1
    have hr : p.val.initialR = q.val.initialR := hrp.trans hrq.symm
    calc
      p.val = c.outgoingSquare p.val.initialR p.val.rightB rfl :=
        (reconstruct p.val).symm
      _ = c.outgoingSquare q.val.initialR q.val.rightB rfl := by
        simpa only [hr, hb]
      _ = q.val := reconstruct q.val
  have surjective : Function.Surjective toIncidence := by
    rintro ⟨b, ⟨h, hlift⟩⟩
    let sq := c.outgoingSquare r b h
    have hstart : sq.initialR = r :=
      (square_lifts_left_forgetting c).2.1 r b h
    have hterminal : sq.terminalR = s := by
      change (c.outgoingLift r b h).val = s at hlift
      exact hlift
    have hright : sq.rightB = b := by
      rcases r with ⟨i, t, edge⟩
      rcases b with ⟨t', z, number⟩
      cases h
      rfl
    refine ⟨⟨sq, congrArg e hstart, congrArg e hterminal⟩, ?_⟩
    apply Subtype.ext
    exact hright
  have hcard : Nat.card fiber = Nat.card incidence :=
    Nat.card_congr (Equiv.ofBijective toIncidence ⟨injective, surjective⟩)
  have hnumber := Fintype.card_congr (c.squareFiberEquiv (e r) (e s))
  calc
    c.squareMatrix (e r) (e s) = Fintype.card fiber := by
      simpa only [Fintype.card_fin] using hnumber
    _ = Nat.card fiber := (Nat.card_eq_fintype_card (α := fiber)).symm
    _ = Nat.card incidence := hcard

#print axioms square_column_lift_count
#print axioms square_row_lift_count

private theorem square_first_column_invariance
    (c : CompatibleCertificate A B R S m) {r v : Edge R}
    (h : c.squareIncomingLift.response 1 r v) (s : Edge R) :
    c.squareMatrix ((Fintype.equivFin (Edge R)) s)
        ((Fintype.equivFin (Edge R)) r) =
      c.squareMatrix ((Fintype.equivFin (Edge R)) s)
        ((Fintype.equivFin (Edge R)) v) := by
  classical
  have hp : r.source = v.source := congrArg Prod.fst h
  have hstep {x y : Edge R} (hxy : c.squareIncomingLift.response 1 x y)
      (a : Edge A) (hx : a.target = x.source) (hy : a.target = y.source) :
      (c.incomingLift a x hx).val = (c.incomingLift a y hy).val := by
    have hzero := incoming_response_step c.squareIncomingLift 0 hxy a
      hx.symm hy.symm
    rw [(response_zero_and_step c.squareIncomingLift).1] at hzero
    exact hzero
  have hpred (a : Edge A) :
      (∃ ha : a.target = r.source, (c.incomingLift a r ha).val = s) ↔
      (∃ hb : a.target = v.source, (c.incomingLift a v hb).val = s) := by
    constructor
    · rintro ⟨ha, hs⟩
      let hb : a.target = v.source := ha.trans hp
      exact ⟨hb, (hstep h a ha hb).symm.trans hs⟩
    · rintro ⟨hb, hs⟩
      let ha : a.target = r.source := hb.trans hp.symm
      exact ⟨ha,
        (hstep ((c.squareIncomingLift.response 1).iseqv.symm h)
          a hb ha).symm.trans hs⟩
  let leftFiber := {a : Edge A //
    ∃ ha : a.target = r.source, (c.incomingLift a r ha).val = s}
  let rightFiber := {a : Edge A //
    ∃ hb : a.target = v.source, (c.incomingLift a v hb).val = s}
  let e : leftFiber ≃ rightFiber := {
    toFun := fun x => ⟨x.val, (hpred x.val).mp x.property⟩
    invFun := fun x => ⟨x.val, (hpred x.val).mpr x.property⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }
  calc
    c.squareMatrix ((Fintype.equivFin (Edge R)) s)
        ((Fintype.equivFin (Edge R)) r) = Nat.card leftFiber :=
          c.square_column_lift_count r s
    _ = Nat.card rightFiber := Nat.card_congr e
    _ = c.squareMatrix ((Fintype.equivFin (Edge R)) s)
          ((Fintype.equivFin (Edge R)) v) :=
            (c.square_column_lift_count v s).symm

private theorem square_first_row_invariance
    (c : CompatibleCertificate A B R S m) {r v : Edge R}
    (h : c.squareOutgoingLift.response 1 r v) (s : Edge R) :
    c.squareMatrix ((Fintype.equivFin (Edge R)) r)
        ((Fintype.equivFin (Edge R)) s) =
      c.squareMatrix ((Fintype.equivFin (Edge R)) v)
        ((Fintype.equivFin (Edge R)) s) := by
  classical
  have hp : r.target = v.target := congrArg Prod.fst h
  have hstep {x y : Edge R} (hxy : c.squareOutgoingLift.response 1 x y)
      (b : Edge B) (hx : x.target = b.source) (hy : y.target = b.source) :
      (c.outgoingLift x b hx).val = (c.outgoingLift y b hy).val := by
    have hzero := incoming_response_step c.squareOutgoingLift 0 hxy
      (⟨b.target, b.source, b.number⟩ : Edge B.transpose) hx hy
    rw [(response_zero_and_step c.squareOutgoingLift).1] at hzero
    exact hzero
  have hpred (b : Edge B) :
      (∃ hr : r.target = b.source, (c.outgoingLift r b hr).val = s) ↔
      (∃ hv : v.target = b.source, (c.outgoingLift v b hv).val = s) := by
    constructor
    · rintro ⟨hr, hs⟩
      let hv : v.target = b.source := hp.symm.trans hr
      exact ⟨hv, (hstep h b hr hv).symm.trans hs⟩
    · rintro ⟨hv, hs⟩
      let hr : r.target = b.source := hp.trans hv
      exact ⟨hr,
        (hstep ((c.squareOutgoingLift.response 1).iseqv.symm h)
          b hv hr).symm.trans hs⟩
  let leftFiber := {b : Edge B //
    ∃ hr : r.target = b.source, (c.outgoingLift r b hr).val = s}
  let rightFiber := {b : Edge B //
    ∃ hv : v.target = b.source, (c.outgoingLift v b hv).val = s}
  let e : leftFiber ≃ rightFiber := {
    toFun := fun x => ⟨x.val, (hpred x.val).mp x.property⟩
    invFun := fun x => ⟨x.val, (hpred x.val).mpr x.property⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }
  calc
    c.squareMatrix ((Fintype.equivFin (Edge R)) r)
        ((Fintype.equivFin (Edge R)) s) = Nat.card leftFiber :=
          c.square_row_lift_count r s
    _ = Nat.card rightFiber := Nat.card_congr e
    _ = c.squareMatrix ((Fintype.equivFin (Edge R)) v)
          ((Fintype.equivFin (Edge R)) s) :=
            (c.square_row_lift_count v s).symm

private theorem square_left_zero_fiber_count
    (c : CompatibleCertificate A B R S m) (r s : Edge R) :
    Nat.card (incomingResponseFiber c.squareIncomingLift 0
      (Quotient.mk (c.squareIncomingLift.response 0) s) r) =
    c.squareMatrix ((Fintype.equivFin (Edge R)) s)
      ((Fintype.equivFin (Edge R)) r) := by
  classical
  let L := c.squareIncomingLift
  let leftFiber := incomingResponseFiber L 0
    (Quotient.mk (L.response 0) s) r
  let rightFiber := {a : Edge A //
    ∃ h : a.target = r.source, (c.incomingLift a r h).val = s}
  let e : leftFiber ≃ rightFiber := {
    toFun := fun x => by
      let a := x.val
      let hv := Classical.choose x.property
      have hclass := Classical.choose_spec x.property
      have heq : (c.incomingLift a r hv.symm).val = s := by
        change (L.lift a ⟨r, hv⟩).val = s
        have hrel : (L.response 0).r (L.lift a ⟨r, hv⟩).val s :=
          Quotient.exact hclass
        exact Eq.mp
          (congrArg (fun T : Setoid (Edge R) =>
            T.r (L.lift a ⟨r, hv⟩).val s) (response_zero_and_step L).1)
          hrel
      exact ⟨a, ⟨hv.symm, heq⟩⟩
    invFun := fun x => by
      let a := x.val
      let h := Classical.choose x.property
      have heq := Classical.choose_spec x.property
      refine ⟨a, ⟨h.symm, Quotient.sound ?_⟩⟩
      rw [(response_zero_and_step L).1]
      exact heq
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }
  calc
    Nat.card leftFiber = Nat.card rightFiber := Nat.card_congr e
    _ = c.squareMatrix ((Fintype.equivFin (Edge R)) s)
          ((Fintype.equivFin (Edge R)) r) :=
            (c.square_column_lift_count r s).symm

private theorem square_right_zero_fiber_count
    (c : CompatibleCertificate A B R S m) (r s : Edge R) :
    Nat.card (incomingResponseFiber c.squareOutgoingLift 0
      (Quotient.mk (c.squareOutgoingLift.response 0) s) r) =
    c.squareMatrix ((Fintype.equivFin (Edge R)) r)
      ((Fintype.equivFin (Edge R)) s) := by
  classical
  let L := c.squareOutgoingLift
  let flip : Edge B.transpose ≃ Edge B := {
    toFun := fun a => ⟨a.target, a.source, a.number⟩
    invFun := fun b => ⟨b.target, b.source, b.number⟩
    left_inv := by intro a; cases a; rfl
    right_inv := by intro b; cases b; rfl }
  let leftFiber := incomingResponseFiber L 0
    (Quotient.mk (L.response 0) s) r
  let rightFiber := {b : Edge B //
    ∃ h : r.target = b.source, (c.outgoingLift r b h).val = s}
  let e : leftFiber ≃ rightFiber := {
    toFun := fun x => by
      let b := flip x.val
      let hv := Classical.choose x.property
      have hclass := Classical.choose_spec x.property
      have heq : (c.outgoingLift r b hv).val = s := by
        change (L.lift x.val ⟨r, hv⟩).val = s
        have hrel : (L.response 0).r (L.lift x.val ⟨r, hv⟩).val s :=
          Quotient.exact hclass
        exact Eq.mp
          (congrArg (fun T : Setoid (Edge R) =>
            T.r (L.lift x.val ⟨r, hv⟩).val s) (response_zero_and_step L).1)
          hrel
      exact ⟨b, ⟨hv, heq⟩⟩
    invFun := fun x => by
      let b := x.val
      let h := Classical.choose x.property
      have heq := Classical.choose_spec x.property
      refine ⟨flip.symm b, ⟨h, Quotient.sound ?_⟩⟩
      rw [(response_zero_and_step L).1]
      exact heq
    left_inv := by
      intro x
      apply Subtype.ext
      exact flip.symm_apply_apply x.val
    right_inv := by
      intro x
      apply Subtype.ext
      exact flip.apply_symm_apply x.val }
  calc
    Nat.card leftFiber = Nat.card rightFiber := Nat.card_congr e
    _ = c.squareMatrix ((Fintype.equivFin (Edge R)) r)
          ((Fintype.equivFin (Edge R)) s) :=
            (c.square_row_lift_count r s).symm

private noncomputable def firstLeftClass
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareIncomingLift.response 1))] :
    Fin (Fintype.card (Edge R)) →
      Fin (Fintype.card (Quotient (c.squareIncomingLift.response 1))) := by
  classical
  exact fun u => (Fintype.equivFin _)
    (Quotient.mk _ ((Fintype.equivFin (Edge R)).symm u))

private noncomputable def firstRightClass
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareOutgoingLift.response 1))] :
    Fin (Fintype.card (Edge R)) →
      Fin (Fintype.card (Quotient (c.squareOutgoingLift.response 1))) := by
  classical
  exact fun u => (Fintype.equivFin _)
    (Quotient.mk _ ((Fintype.equivFin (Edge R)).symm u))

private noncomputable def firstLeftRep
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareIncomingLift.response 1))] :
    Fin (Fintype.card (Quotient (c.squareIncomingLift.response 1))) →
      Fin (Fintype.card (Edge R)) := by
  classical
  exact fun f => (Fintype.equivFin (Edge R))
    (Quotient.out ((Fintype.equivFin _).symm f))

private noncomputable def firstRightRep
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareOutgoingLift.response 1))] :
    Fin (Fintype.card (Quotient (c.squareOutgoingLift.response 1))) →
      Fin (Fintype.card (Edge R)) := by
  classical
  exact fun f => (Fintype.equivFin (Edge R))
    (Quotient.out ((Fintype.equivFin _).symm f))

private theorem square_left_first_matrix
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareIncomingLift.response 1))]
    (f g : Fin (Fintype.card
      (Quotient (c.squareIncomingLift.response 1)))) :
    incomingResponseMatrix c.squareIncomingLift 1
        ((Fintype.equivFin _).symm f) ((Fintype.equivFin _).symm g) =
      (FirstResponseDiamond.columnMembership c.firstLeftClass *
        c.squareMatrix * FirstResponseDiamond.columnSelector c.firstLeftRep)
        f g := by
  classical
  let L := c.squareIncomingLift
  let e := Fintype.equivFin (Edge R)
  let eL := Fintype.equivFin (Quotient (L.response 1))
  let e0 : Edge R ≃ Quotient (L.response 0) :=
    Equiv.ofBijective (fun r => Quotient.mk (L.response 0) r) (by
      constructor
      · intro r s hrs
        have hrel := Quotient.exact hrs
        exact Eq.mp
          (congrArg (fun T : Setoid (Edge R) => T.r r s)
            (response_zero_and_step L).1) hrel
      · intro F
        exact ⟨Quotient.out F, Quotient.out_eq F⟩)
  have hfiber (r : Edge R) :
      incomingResponseU L 0 (e0 r) (eL.symm g) =
        c.squareMatrix (e r) (c.firstLeftRep g) := by
    change Nat.card (incomingResponseFiber L 0
      (Quotient.mk (L.response 0) r) (Quotient.out (eL.symm g))) = _
    simpa [firstLeftRep, e, eL] using
      c.square_left_zero_fiber_count (Quotient.out (eL.symm g)) r
  have hclass (r : Edge R) :
      incomingResponseV L 0 (eL.symm f) (e0 r) =
        FirstResponseDiamond.columnMembership c.firstLeftClass f (e r) := by
    have hprojection : incomingResponseProjection L 0 (e0 r) =
        Quotient.mk (L.response 1) r := rfl
    have hclass_eq : c.firstLeftClass (e r) =
        eL (Quotient.mk (L.response 1) r) := by
      change eL (Quotient.mk (L.response 1) (e.symm (e r))) =
        eL (Quotient.mk (L.response 1) r)
      rw [e.symm_apply_apply]
    change (if incomingResponseProjection L 0 (e0 r) = eL.symm f
      then 1 else 0) = (if c.firstLeftClass (e r) = f then 1 else 0)
    rw [hprojection, hclass_eq]
    by_cases h : f = eL (Quotient.mk (L.response 1) r)
    · subst f
      simp
    · have hne : Quotient.mk (L.response 1) r ≠ eL.symm f := by
        intro hk
        apply h
        calc
          f = eL (eL.symm f) := (eL.apply_symm_apply f).symm
          _ = eL (Quotient.mk (L.response 1) r) := congrArg eL hk.symm
      simp [h, hne, eq_comm]
  calc
    incomingResponseMatrix L 1 (eL.symm f) (eL.symm g) =
        (incomingResponseV L 0 * incomingResponseU L 0)
          (eL.symm f) (eL.symm g) := by
            rw [incoming_response_matrix_factor_step L 0]
    _ = ∑ r : Edge R,
          FirstResponseDiamond.columnMembership c.firstLeftClass f (e r) *
            c.squareMatrix (e r) (c.firstLeftRep g) := by
        rw [Matrix.mul_apply]
        exact (Fintype.sum_equiv e0 _ _ (fun r => by
          rw [hclass r, hfiber r])).symm
    _ = (FirstResponseDiamond.columnMembership c.firstLeftClass *
          c.squareMatrix * FirstResponseDiamond.columnSelector c.firstLeftRep)
          f g := by
        have hsum :
            (∑ r : Edge R,
              FirstResponseDiamond.columnMembership c.firstLeftClass f (e r) *
                c.squareMatrix (e r) (c.firstLeftRep g)) =
            ∑ u : Fin (Fintype.card (Edge R)),
              FirstResponseDiamond.columnMembership c.firstLeftClass f u *
                c.squareMatrix u (c.firstLeftRep g) :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
        rw [hsum]
        simp only [Matrix.mul_apply, FirstResponseDiamond.columnSelector]
        simp

private theorem square_right_first_matrix
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareOutgoingLift.response 1))]
    (f g : Fin (Fintype.card
      (Quotient (c.squareOutgoingLift.response 1)))) :
    incomingResponseMatrix c.squareOutgoingLift 1
        ((Fintype.equivFin _).symm f) ((Fintype.equivFin _).symm g) =
      (FirstResponseDiamond.rowSelector c.firstRightRep *
        c.squareMatrix * FirstResponseDiamond.rowMembership c.firstRightClass)
        g f := by
  classical
  let L := c.squareOutgoingLift
  let e := Fintype.equivFin (Edge R)
  let eR := Fintype.equivFin (Quotient (L.response 1))
  let e0 : Edge R ≃ Quotient (L.response 0) :=
    Equiv.ofBijective (fun r => Quotient.mk (L.response 0) r) (by
      constructor
      · intro r s hrs
        have hrel := Quotient.exact hrs
        exact Eq.mp
          (congrArg (fun T : Setoid (Edge R) => T.r r s)
            (response_zero_and_step L).1) hrel
      · intro F
        exact ⟨Quotient.out F, Quotient.out_eq F⟩)
  have hfiber (r : Edge R) :
      incomingResponseU L 0 (e0 r) (eR.symm g) =
        c.squareMatrix (c.firstRightRep g) (e r) := by
    change Nat.card (incomingResponseFiber L 0
      (Quotient.mk (L.response 0) r) (Quotient.out (eR.symm g))) = _
    simpa [firstRightRep, e, eR] using
      c.square_right_zero_fiber_count (Quotient.out (eR.symm g)) r
  have hclass (r : Edge R) :
      incomingResponseV L 0 (eR.symm f) (e0 r) =
        FirstResponseDiamond.rowMembership c.firstRightClass (e r) f := by
    have hprojection : incomingResponseProjection L 0 (e0 r) =
        Quotient.mk (L.response 1) r := rfl
    have hclass_eq : c.firstRightClass (e r) =
        eR (Quotient.mk (L.response 1) r) := by
      change eR (Quotient.mk (L.response 1) (e.symm (e r))) =
        eR (Quotient.mk (L.response 1) r)
      rw [e.symm_apply_apply]
    change (if incomingResponseProjection L 0 (e0 r) = eR.symm f
      then 1 else 0) = (if c.firstRightClass (e r) = f then 1 else 0)
    rw [hprojection, hclass_eq]
    by_cases h : f = eR (Quotient.mk (L.response 1) r)
    · subst f
      simp
    · have hne : Quotient.mk (L.response 1) r ≠ eR.symm f := by
        intro hk
        apply h
        calc
          f = eR (eR.symm f) := (eR.apply_symm_apply f).symm
          _ = eR (Quotient.mk (L.response 1) r) := congrArg eR hk.symm
      simp [h, hne, eq_comm]
  calc
    incomingResponseMatrix L 1 (eR.symm f) (eR.symm g) =
        (incomingResponseV L 0 * incomingResponseU L 0)
          (eR.symm f) (eR.symm g) := by
            rw [incoming_response_matrix_factor_step L 0]
    _ = ∑ r : Edge R,
          FirstResponseDiamond.rowMembership c.firstRightClass (e r) f *
            c.squareMatrix (c.firstRightRep g) (e r) := by
        rw [Matrix.mul_apply]
        exact (Fintype.sum_equiv e0 _ _ (fun r => by
          rw [hclass r, hfiber r])).symm
    _ = (FirstResponseDiamond.rowSelector c.firstRightRep *
          c.squareMatrix * FirstResponseDiamond.rowMembership c.firstRightClass)
          g f := by
        have hsum :
            (∑ r : Edge R,
              FirstResponseDiamond.rowMembership c.firstRightClass (e r) f *
                c.squareMatrix (c.firstRightRep g) (e r)) =
            ∑ u : Fin (Fintype.card (Edge R)),
              c.squareMatrix (c.firstRightRep g) u *
                FirstResponseDiamond.rowMembership c.firstRightClass u f := by
          calc
            _ = ∑ u : Fin (Fintype.card (Edge R)),
                  FirstResponseDiamond.rowMembership c.firstRightClass u f *
                    c.squareMatrix (c.firstRightRep g) u :=
              Fintype.sum_equiv e _ _ (fun _ => rfl)
            _ = _ := by
              apply Finset.sum_congr rfl
              intro u _
              exact Nat.mul_comm _ _
        rw [hsum]
        simp [Matrix.mul_apply, FirstResponseDiamond.rowSelector]

private theorem square_first_diamond
    (c : CompatibleCertificate A B R S m)
    [Fintype (Quotient (c.squareIncomingLift.response 1))]
    [Fintype (Quotient (c.squareOutgoingLift.response 1))] :
    let IL := FirstResponseDiamond.columnMembership c.firstLeftClass
    let IJ := FirstResponseDiamond.rowMembership c.firstRightClass
    let SL := FirstResponseDiamond.columnSelector c.firstLeftRep
    let SJ := FirstResponseDiamond.rowSelector c.firstRightRep
    ∃ D : CountMat
        (Fintype.card (Quotient (c.squareOutgoingLift.response 1)))
        (Fintype.card (Quotient (c.squareIncomingLift.response 1))),
      IL * c.squareMatrix * SL = (IL * IJ) * D ∧
      SJ * c.squareMatrix * IJ = D * (IL * IJ) ∧
      Nonempty (ExchangeChain ℕ
        (IL * c.squareMatrix * SL)
        (SJ * c.squareMatrix * IJ) 1) := by
  classical
  let e := Fintype.equivFin (Edge R)
  let eL := Fintype.equivFin (Quotient (c.squareIncomingLift.response 1))
  let eR := Fintype.equivFin (Quotient (c.squareOutgoingLift.response 1))
  have hleftRep (f) : c.firstLeftClass (c.firstLeftRep f) = f := by
    simp [firstLeftClass, firstLeftRep, e, eL]
  have hrightRep (f) : c.firstRightClass (c.firstRightRep f) = f := by
    simp [firstRightClass, firstRightRep, e, eR]
  have hcolumns (u v) (h : c.firstLeftClass u = c.firstLeftClass v)
      (i) : c.squareMatrix i u = c.squareMatrix i v := by
    have hq : Quotient.mk (c.squareIncomingLift.response 1) (e.symm u) =
        Quotient.mk (c.squareIncomingLift.response 1) (e.symm v) := by
      exact eL.injective h
    have hrel : c.squareIncomingLift.response 1 (e.symm u) (e.symm v) :=
      Quotient.exact hq
    simpa [e] using
      c.square_first_column_invariance hrel (e.symm i)
  have hrows (u v) (h : c.firstRightClass u = c.firstRightClass v)
      (i) : c.squareMatrix u i = c.squareMatrix v i := by
    have hq : Quotient.mk (c.squareOutgoingLift.response 1) (e.symm u) =
        Quotient.mk (c.squareOutgoingLift.response 1) (e.symm v) := by
      exact eR.injective h
    have hrel : c.squareOutgoingLift.response 1 (e.symm u) (e.symm v) :=
      Quotient.exact hq
    simpa [e] using
      c.square_first_row_invariance hrel (e.symm i)
  obtain ⟨D, hleft, hright, chain⟩ :=
    FirstResponseDiamond.first_response_diamond c.squareMatrix
      c.firstLeftClass c.firstRightClass c.firstLeftRep c.firstRightRep
      hleftRep hrightRep hcolumns hrows
  exact ⟨D, hleft, hright, chain⟩

private theorem square_exchange_chain_ge_two
    (c : CompatibleCertificate A B R S m) (hm : 2 ≤ m) :
    Nonempty (ExchangeChain ℕ A B (2 * m - 1)) := by
  classical
  let L := c.squareIncomingLift
  let K := c.squareOutgoingLift
  letI := responseFintype L 1
  letI := responseFintype K 1
  let Cleft := FirstResponseDiamond.columnMembership c.firstLeftClass *
    c.squareMatrix * FirstResponseDiamond.columnSelector c.firstLeftRep
  let Cright := FirstResponseDiamond.rowSelector c.firstRightRep *
    c.squareMatrix * FirstResponseDiamond.rowMembership c.firstRightClass
  have hleftFirst : finiteResponseMatrix L 1 = Cleft := by
    ext f g
    change incomingResponseMatrix L 1
      ((Fintype.equivFin _).symm f) ((Fintype.equivFin _).symm g) =
        Cleft f g
    exact c.square_left_first_matrix f g
  have hrightFirst : (finiteResponseMatrix K 1).transpose = Cright := by
    ext f g
    change incomingResponseMatrix K 1
      ((Fintype.equivFin _).symm g) ((Fintype.equivFin _).symm f) =
        Cright f g
    exact c.square_right_first_matrix g f
  let d := 1 + (m - 2) + 1
  have hd : d = m := by dsimp [d]; omega
  have hleftForget : L.response d = Setoid.ker Edge.source := by
    rw [hd]
    exact c.squareIncomingLift_forgets_at_lag
  have hrightForget : K.response d = Setoid.ker Edge.target := by
    rw [hd]
    exact c.squareOutgoingLift_forgets_at_lag
  obtain ⟨eA, hA⟩ := response_matrix_forgetting_reindexed L d hleftForget
  obtain ⟨eB, hB⟩ := response_matrix_forgetting_reindexed K d hrightForget
  have left : ExchangeChain ℕ A Cleft ((m - 2) + 1) := by
    have chain := finite_response_chain_to L 1 (m - 2) eA
    rw [hleftFirst, hA] at chain
    exact exchange_chain_reverse chain
  have right : ExchangeChain ℕ Cright B ((m - 2) + 1) := by
    have chain := finite_response_chain_to K 1 (m - 2) eB
    rw [hB] at chain
    have transposed := exchange_chain_transpose chain
    simpa only [hrightFirst, Matrix.transpose_transpose] using transposed
  obtain ⟨_, _, _, ⟨middle⟩⟩ := c.square_first_diamond
  have assembled := exchange_chain_trans (exchange_chain_trans left middle) right
  refine ⟨?_⟩
  convert assembled using 1 <;> omega

private theorem square_exchange_chain_one
    (c : CompatibleCertificate A B R S 1) :
    Nonempty (ExchangeChain ℕ A B 1) := by
  classical
  let L := c.squareIncomingLift
  let K := c.squareOutgoingLift
  letI := responseFintype L 1
  letI := responseFintype K 1
  let Cleft := FirstResponseDiamond.columnMembership c.firstLeftClass *
    c.squareMatrix * FirstResponseDiamond.columnSelector c.firstLeftRep
  let Cright := FirstResponseDiamond.rowSelector c.firstRightRep *
    c.squareMatrix * FirstResponseDiamond.rowMembership c.firstRightClass
  have hleftFirst : finiteResponseMatrix L 1 = Cleft := by
    ext f g
    change incomingResponseMatrix L 1
      ((Fintype.equivFin _).symm f) ((Fintype.equivFin _).symm g) =
        Cleft f g
    exact c.square_left_first_matrix f g
  have hrightFirst : (finiteResponseMatrix K 1).transpose = Cright := by
    ext f g
    change incomingResponseMatrix K 1
      ((Fintype.equivFin _).symm g) ((Fintype.equivFin _).symm f) =
        Cright f g
    exact c.square_right_first_matrix g f
  obtain ⟨eA, hA⟩ := response_matrix_forgetting_reindexed L 1
    c.squareIncomingLift_forgets_at_lag
  obtain ⟨eB, hB⟩ := response_matrix_forgetting_reindexed K 1
    c.squareOutgoingLift_forgets_at_lag
  let eLeft := (responseIndex L 1).symm.trans eA
  let eRight := (responseIndex K 1).symm.trans eB
  have hleftIndex (i : Fin n) :
      (responseIndex L 1).symm (eLeft.symm i) = eA.symm i := by
    simp [eLeft]
  have hrightIndex (i : Fin k) :
      (responseIndex K 1).symm (eRight.symm i) = eB.symm i := by
    simp [eRight]
  have hleftReindex : Matrix.reindex eLeft eLeft Cleft = A := by
    ext i j
    rw [← hleftFirst]
    change incomingResponseMatrix L 1
      ((responseIndex L 1).symm (eLeft.symm i))
      ((responseIndex L 1).symm (eLeft.symm j)) = A i j
    rw [hleftIndex i, hleftIndex j]
    exact congrArg (fun X : CountMat n n => X i j) hA
  have hrightReindex : Matrix.reindex eRight eRight Cright = B := by
    ext i j
    rw [← hrightFirst]
    change incomingResponseMatrix K 1
      ((responseIndex K 1).symm (eRight.symm j))
      ((responseIndex K 1).symm (eRight.symm i)) = B i j
    rw [hrightIndex j, hrightIndex i]
    exact congrArg (fun X : CountMat k k => X j i) hB
  obtain ⟨D, hcol, hrow, _⟩ := c.square_first_diamond
  let P := FirstResponseDiamond.columnMembership c.firstLeftClass *
    FirstResponseDiamond.rowMembership c.firstRightClass
  let P' := Matrix.reindex eLeft eRight P
  let D' := Matrix.reindex eRight eLeft D
  have hprodA : A = P' * D' := by
    calc
      A = Matrix.reindex eLeft eLeft Cleft := hleftReindex.symm
      _ = Matrix.reindex eLeft eLeft (P * D) :=
        congrArg (Matrix.reindex eLeft eLeft) hcol
      _ = P' * D' := by
        change (P * D).submatrix eLeft.symm eLeft.symm =
          P.submatrix eLeft.symm eRight.symm *
            D.submatrix eRight.symm eLeft.symm
        exact (Matrix.submatrix_mul_equiv P D eLeft.symm eRight.symm eLeft.symm).symm
  have hprodB : B = D' * P' := by
    calc
      B = Matrix.reindex eRight eRight Cright := hrightReindex.symm
      _ = Matrix.reindex eRight eRight (D * P) :=
        congrArg (Matrix.reindex eRight eRight) hrow
      _ = D' * P' := by
        change (D * P).submatrix eRight.symm eRight.symm =
          D.submatrix eRight.symm eLeft.symm *
            P.submatrix eLeft.symm eRight.symm
        exact (Matrix.submatrix_mul_equiv D P eRight.symm eLeft.symm eRight.symm).symm
  rw [hprodA, hprodB]
  exact ⟨ExchangeChain.cons P' D' (ExchangeChain.nil _)⟩

end CompatibleCertificate
end D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting

namespace D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound

open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

variable {n k m : ℕ} {A : CountMat n n} {B : CountMat k k}
  {R : CountMat n k} {S : CountMat k n}

/-- A compatible numbered certificate produces a strong-shift-equivalence
    chain with a linear length bound from its positive lag. -/
theorem compatible_exchange_chain_bound
    (c : CompatibleCertificate A B R S m) :
    Nonempty (ExchangeChain ℕ A B (2 * m - 1)) := by
  by_cases h : m = 1
  · subst m
    simpa using CompatibleCertificate.square_exchange_chain_one c
  · have hm : 2 ≤ m := by
      have hpos := c.positiveLag
      omega
    exact CompatibleCertificate.square_exchange_chain_ge_two c hm

private abbrev unitCountMatrix : CountMat 1 1 := fun _ _ => 1

/-- A one-state numbered certificate realizes the lag-one exchange. -/
example : Nonempty (ExchangeChain ℕ unitCountMatrix unitCountMatrix 1) := by
  classical
  let M := unitCountMatrix
  have pairUnique (i j : Fin 1) (x y : EdgePair M M i j) : x = y := by
    rcases x with ⟨u, a, b⟩
    rcases y with ⟨v, c, d⟩
    have huv : u = v := Subsingleton.elim _ _
    subst v
    have hac : a = c := Subsingleton.elim _ _
    have hbd : b = d := Subsingleton.elim _ _
    subst c
    subst d
    rfl
  have pathUnique (i j : Fin 1) (x y : FinitePath M 1 i j) : x = y := by
    cases x with
    | cons a tail =>
        cases tail with
        | nil _ =>
            cases y with
            | cons b rest =>
                cases rest with
                | nil _ =>
                    have hab : a = b := Subsingleton.elim _ _
                    subst b
                    rfl
  have pathOne (i j : Fin 1) : FinitePath M 1 i j := by
    have h : i = j := Subsingleton.elim _ _
    subst j
    exact .cons 0 (.nil i)
  have pairOne (i j : Fin 1) : EdgePair M M i j := ⟨0, 0, 0⟩
  let psi (i j : Fin 1) : EdgePair M M i j ≃ FinitePath M 1 i j :=
    Equiv.ofBijective (fun _ => pathOne i j) ⟨
      by intro x y _; exact pairUnique i j x y,
      by intro y; exact ⟨pairOne i j, pathUnique i j _ y⟩⟩
  have outputUnique (i z : Fin 1)
      (x y : Σ t : Fin 1, Fin (M i t) × FinitePath M 1 t z) : x = y := by
    rcases x with ⟨t, a, p⟩
    rcases y with ⟨u, b, q⟩
    have htu : t = u := Subsingleton.elim _ _
    subst u
    have hab : a = b := Subsingleton.elim _ _
    subst b
    have hpq : p = q := pathUnique t z p q
    subst q
    rfl
  let c : CompatibleCertificate M M M M 1 := {
    positiveLag := by omega
    essentialA := ⟨by intro i; exact ⟨0, by simp [M, unitCountMatrix]⟩,
      by intro j; exact ⟨0, by simp [M, unitCountMatrix]⟩⟩
    essentialB := ⟨by intro i; exact ⟨0, by simp [M, unitCountMatrix]⟩,
      by intro j; exact ⟨0, by simp [M, unitCountMatrix]⟩⟩
    phi := fun _ _ => Equiv.refl _
    psiA := psi
    psiB := psi
    compatible := by
      intro i j z alpha r
      exact outputUnique i z _ _
  }
  exact compatible_exchange_chain_bound c

#print axioms compatible_exchange_chain_bound

end D5.S3.ConceptDynamics.Coding.CompatibleResponseForgettingBound

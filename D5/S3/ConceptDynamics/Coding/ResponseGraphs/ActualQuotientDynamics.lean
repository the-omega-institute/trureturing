/- GID: D5/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseGraphs/ActualQuotientDynamics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual same-base response quotient shifts every path-response depth by the quotient depth. -/

import D5.S3.ConceptDynamics.Coding.ResponseKernelRecursion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualQuotientDynamics
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
open D5.S3.ConceptDynamics.Coding.ResponseKernelRecursion
open D5.S3.ConceptDynamics.Coding.CompatibleResponseForgetting
variable {n : ℕ} {A : CountMat n n} {Q R : Type}

def projection (L : IncomingLift A Q) (d : ℕ) : Quotient (L.response d) → Fin n :=
  Quotient.lift L.project (fun _ _ h => congrArg Prod.fst h)

theorem projection_out (L : IncomingLift A Q) (d : ℕ) (F : Quotient (L.response d)) :
    L.project (Quotient.out F) = projection L d F := by
  change projection L d (Quotient.mk _ (Quotient.out F)) = _
  rw [Quotient.out_eq]

def quotientLift (L : IncomingLift A Q) (d : ℕ) :
    IncomingLift A (Quotient (L.response d)) where
  project := projection L d
  onto := by
    intro i
    obtain ⟨u,hu⟩ := L.onto i
    exact ⟨Quotient.mk _ u,hu⟩
  lift a F := ⟨Quotient.mk _ (L.lift a
    ⟨Quotient.out F.val,(projection_out L d F.val).trans F.property⟩).val,
    (L.lift a ⟨Quotient.out F.val,(projection_out L d F.val).trans F.property⟩).property⟩

theorem lift_mk (L : IncomingLift A Q) (d : ℕ) (a : Edge A) (u : Q)
    (hu : L.project u = a.target) :
    ((quotientLift L d).lift a ⟨Quotient.mk _ u,hu⟩).val =
      Quotient.mk (L.response d) (L.lift a ⟨u,hu⟩).val := by
  apply Quotient.sound
  apply incoming_response_step L d
  exact (response_zero_and_step L).2 d (Quotient.exact (Quotient.out_eq _))

/-- Quotient response depth adds to the original response depth. -/
theorem response_shift (L : IncomingLift A Q) (d j : ℕ) (u v : Q) :
    (quotientLift L d).response j (Quotient.mk _ u) (Quotient.mk _ v) ↔
      L.response (d+j) u v := by
  induction j generalizing u v with
  | zero =>
    rw [(response_zero_and_step (quotientLift L d)).1]
    change (Quotient.mk (L.response d) u = Quotient.mk (L.response d) v) ↔ _
    simpa only [Nat.add_zero] using (Quotient.eq :
      Quotient.mk (L.response d) u = Quotient.mk (L.response d) v ↔ L.response d u v)
  | succ j ih =>
    rw [response_successor_iff, Nat.add_succ, response_successor_iff]
    constructor
    · rintro ⟨hp,hs⟩
      refine ⟨hp,?_⟩
      intro a hu hv
      have h := hs a hu hv
      rw [lift_mk, lift_mk] at h
      exact (ih _ _).mp h
    · rintro ⟨hp,hs⟩
      refine ⟨hp,?_⟩
      intro a hu hv
      rw [lift_mk, lift_mk]
      exact (ih _ _).mpr (hs a hu hv)

-- A value-preserving conjugacy carries every actual path, with no assumed response law.
theorem path_conjugacy (L : IncomingLift A Q) (K : IncomingLift A R) (e : Q ≃ R)
    (hp : ∀ u, K.project (e u) = L.project u)
    (hl : ∀ (a : Edge A) (u : Q) (hu : L.project u = a.target),
      (K.lift a ⟨e u,(hp u).trans hu⟩).val = e (L.lift a ⟨u,hu⟩).val)
    {d : ℕ} {i j : Fin n} (p : FinitePath A d i j)
    (u : {u : Q // L.project u = j}) :
    (K.liftPath p ⟨e u.val,(hp u.val).trans u.property⟩).val = e (L.liftPath p u).val := by
  induction p with
  | nil => rfl
  | @cons d i j k a tail ih =>
    simp only [IncomingLift.liftPath]
    have hv := ih u
    have hs : K.liftPath tail ⟨e u.val,(hp u.val).trans u.property⟩ =
        ⟨e (L.liftPath tail u).val,(hp _).trans (L.liftPath tail u).property⟩ := Subtype.ext hv
    rw [hs]
    exact hl _ _ _

theorem response_conjugacy (L : IncomingLift A Q) (K : IncomingLift A R) (e : Q ≃ R)
    (hp : ∀ u, K.project (e u) = L.project u)
    (hl : ∀ (a : Edge A) (u : Q) (hu : L.project u = a.target),
      (K.lift a ⟨e u,(hp u).trans hu⟩).val = e (L.lift a ⟨u,hu⟩).val)
    (d : ℕ) (u v : Q) : K.response d (e u) (e v) ↔ L.response d u v := by
  induction d generalizing u v with
  | zero =>
    rw [(response_zero_and_step K).1,(response_zero_and_step L).1]
    change e u = e v ↔ u = v
    exact e.injective.eq_iff
  | succ d ih =>
    rw [response_successor_iff,response_successor_iff]
    constructor
    · rintro ⟨hpv,hs⟩
      refine ⟨(hp u).symm.trans (hpv.trans (hp v)),fun a hu hv => ?_⟩
      have h := hs a ((hp u).trans hu) ((hp v).trans hv)
      rw [hl a u hu,hl a v hv] at h
      exact (ih _ _).mp h
    · rintro ⟨hpv,hs⟩
      refine ⟨(hp u).trans (hpv.trans (hp v).symm),fun a hu hv => ?_⟩
      have hu' := (hp u).symm.trans hu
      have hv' := (hp v).symm.trans hv
      rw [show (K.lift a ⟨e u,hu⟩).val = e (L.lift a ⟨u,hu'⟩).val from hl a u hu',
        show (K.lift a ⟨e v,hv⟩).val = e (L.lift a ⟨v,hv'⟩).val from hl a v hv']
      exact (ih _ _).mpr (hs a hu' hv')

-- Recursive first quotients start with the original Q, not with its numbered matrix.
def iteration (L : IncomingLift A Q) : ℕ → Σ R : Type, IncomingLift A R
  | 0 => ⟨Q,L⟩
  | d+1 => ⟨_,quotientLift (iteration L d).2 1⟩

def iterMap (L : IncomingLift A Q) : (d : ℕ) → Q → (iteration L d).1
  | 0,u => u
  | d+1,u => Quotient.mk _ (iterMap L d u)

theorem iter_onto (L : IncomingLift A Q) (d : ℕ) : Function.Surjective (iterMap L d) := by
  induction d with
  | zero => exact Function.surjective_id
  | succ d ih =>
    intro F
    obtain ⟨u,hu⟩ := ih (Quotient.out F)
    exact ⟨u,by change Quotient.mk _ (iterMap L d u) = F; rw [hu,Quotient.out_eq]⟩

theorem iter_project (L : IncomingLift A Q) (d : ℕ) (u : Q) :
    (iteration L d).2.project (iterMap L d u) = L.project u := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem iter_lift (L : IncomingLift A Q) (d : ℕ) (a : Edge A) (u : Q)
    (hu : L.project u = a.target) :
    ((iteration L d).2.lift a ⟨iterMap L d u,(iter_project L d u).trans hu⟩).val =
    iterMap L d (L.lift a ⟨u,hu⟩).val := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change ((quotientLift (iteration L d).2 1).lift a
      ⟨Quotient.mk _ (iterMap L d u),_⟩).val = _
    rw [lift_mk,ih]
    rfl

theorem iter_response (L : IncomingLift A Q) (d j : ℕ) (u v : Q) :
    (iteration L d).2.response j (iterMap L d u) (iterMap L d v) ↔ L.response (d+j) u v := by
  induction d generalizing j with
  | zero =>
    change L.response j u v ↔ L.response (0+j) u v
    rw [Nat.zero_add]
  | succ d ih =>
    change (quotientLift (iteration L d).2 1).response j
      (Quotient.mk _ (iterMap L d u)) (Quotient.mk _ (iterMap L d v)) ↔ _
    rw [response_shift,ih]
    rw [show d+(1+j) = d+1+j by omega]


#print axioms response_shift
#print axioms response_conjugacy
#print axioms iter_response
end D5.S3.ConceptDynamics.Coding.ResponseGraphs.ActualQuotientDynamics

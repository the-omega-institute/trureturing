/- GID: D5/S3/ConceptDynamics/Coding/ResponseQuotientKernel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseQuotientKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Numbered finite path lifts define a response kernel; depth zero remembers the state and deeper responses only forget information.
-/

import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Setoid.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap

/- Endpoint-indexed paths retain the identity of every parallel edge. -/
inductive FinitePath {n : ℕ} (A : CountMat n n) : ℕ → Fin n → Fin n → Type
  | nil (i : Fin n) : FinitePath A 0 i i
  | cons {d : ℕ} {i j k : Fin n} (edge : Fin (A i j))
      (tail : FinitePath A d j k) : FinitePath A (d + 1) i k

/- An incoming lift chooses a unique predecessor above every numbered base edge. -/
structure IncomingLift {n : ℕ} (A : CountMat n n) (Q : Type) where
  project : Q → Fin n
  onto : Function.Surjective project
  lift : (a : Edge A) → {q : Q // project q = a.target} →
    {q : Q // project q = a.source}

variable {n : ℕ} {A : CountMat n n} {Q : Type}

def IncomingLift.liftPath (L : IncomingLift A Q) :
    {d : ℕ} → {i j : Fin n} → FinitePath A d i j →
      {q : Q // L.project q = j} → {q : Q // L.project q = i}
  | _, _, _, .nil _, q => q
  | _, i, _, .cons (j := j) a tail, q =>
      L.lift ⟨i, j, a⟩ (L.liftPath tail q)

/- The readout is computed from actual path lifts, rather than from a proxy
   recursion.  Its kernel is the response equivalence at the given depth. -/
def IncomingLift.responseReadout (L : IncomingLift A Q) (d : ℕ) (q : Q) :
    Fin n × ((i j : Fin n) → FinitePath A d i j → Option Q) :=
  (L.project q, fun _ j path => if h : L.project q = j then
      some (L.liftPath path ⟨q, h⟩).val else none)

def IncomingLift.response (L : IncomingLift A Q) (d : ℕ) : Setoid Q :=
  Setoid.ker (L.responseReadout d)

/- At depth zero the endpoint and the lifted empty path recover the entire
   state.  At the next depth the extra coordinates are obtained by applying
   the preceding readout to the tail, so no distinction can reappear. -/
theorem response_zero_and_step (L : IncomingLift A Q) :
    L.response 0 = ⊥ ∧ ∀ d, L.response d ≤ L.response (d + 1) := by
  constructor
  · apply Setoid.ext
    intro u v
    constructor
    · intro h
      have hobs : L.responseReadout 0 u = L.responseReadout 0 v := h
      have hp : L.project u = L.project v := congrArg Prod.fst hobs
      have hf := congrArg (fun o => o.2 (L.project u) (L.project u)
        (FinitePath.nil (L.project u))) hobs
      simp only [IncomingLift.responseReadout, IncomingLift.liftPath, dif_pos rfl,
        dif_pos hp.symm, Option.some.injEq] at hf
      exact hf
    · intro h
      change u = v at h
      subst v
      rfl
  · intro d u v h
    have hobs : L.responseReadout d u = L.responseReadout d v := h
    have hp : L.project u = L.project v := congrArg Prod.fst hobs
    change L.responseReadout (d + 1) u = L.responseReadout (d + 1) v
    apply Prod.ext hp
    funext i j path
    by_cases hu : L.project u = j
    · have hv : L.project v = j := hp.symm.trans hu
      simp only [IncomingLift.responseReadout, dif_pos hu, dif_pos hv]
      cases path with
      | @cons d i m j a tail =>
        have hf := congrArg (fun o => o.2 m j tail) hobs
        simp only [IncomingLift.responseReadout, dif_pos hu, dif_pos hv,
          Option.some.injEq] at hf
        have ht : L.liftPath tail ⟨u, hu⟩ =
            L.liftPath tail ⟨v, hv⟩ := Subtype.ext hf
        simp only [IncomingLift.liftPath, ht]
    · have hv : L.project v ≠ j := fun hv => hu (hp.trans hv)
      simp only [IncomingLift.responseReadout, dif_neg hu, dif_neg hv]

#print axioms response_zero_and_step

end D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel

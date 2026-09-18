/- GID: D5/S3/Geometry/Hyperideal/FaceColourPropagation
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FaceColourPropagation
   mirror-E: none(waiver:arbitrary-connected-face-pairing)
   anchors: []
   utility: none
   digest: Connected face pairings preserve the opposite-pair colour signature. -/

import D5.S3.Geometry.Hyperideal.FourCycleCurvature
import Mathlib.Logic.Relation

/-!
This obstruction is combinatorial and independent of lengths. Opposite-paired
low colours cannot have one-pair and two-pair tetrahedra in a connected
face-paired system. The proof transports the actual three-edge face count
through a face permutation and then along arbitrary finite dual-graph paths.
Neither equality of neighbouring signatures nor global constancy is assumed.

It applies before checking orientability or vertex links. It does not say
that a local tetrahedral colour specification alone defines a manifold.
No theorem is obtained by enumerating all triangulations or bounding their size.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.FaceColourPropagation
open D5.S3.Geometry.Hyperideal.FourCycleCurvature

/-- Edges of the face opposite each vertex, in the same six-edge convention. -/
def faceEdges (f : Fin 4) : Fin 3 → Fin 6 :=
  ![![3,4,5], ![1,2,3], ![0,2,4], ![0,1,5]] f

variable {T E : Type*}

/-- Face identifications preserve actual global edge labels. Any permutation
of three triangle edges comes from a triangle vertex permutation. -/
structure FacePairing (s : Incidence T E) where
  partner : T × Fin 4 → T × Fin 4
  involutive : Function.Involutive partner
  permutation : T × Fin 4 → Equiv.Perm (Fin 3)
  preserves : ∀ a j,
    s.edge a.1 (faceEdges a.2 j) =
      s.edge (partner a).1 (faceEdges (partner a).2 (permutation a j))

/-- Natural-number indicator, so all counts retain multiplicity. -/
def mark (s : Incidence T E) (t : T) (i : Fin 6) : ℕ :=
  if s.low (s.edge t i) = true then 1 else 0

def faceCount (s : Incidence T E) (t : T) (f : Fin 4) : ℕ :=
  ∑ j : Fin 3, mark s t (faceEdges f j)

/-- Under opposite pairing, this is the number of low opposite pairs. -/
def pairCount (s : Incidence T E) (t : T) : ℕ :=
  mark s t 0 + mark s t 1 + mark s t 2

def Balanced (s : Incidence T E) : Prop :=
  ∀ t, s.low (s.edge t 0) = s.low (s.edge t 3) ∧
    s.low (s.edge t 1) = s.low (s.edge t 4) ∧
    s.low (s.edge t 2) = s.low (s.edge t 5)

def Adjacent {s : Incidence T E} (p : FacePairing s) (t u : T) : Prop :=
  ∃ f : Fin 4, (p.partner (t,f)).1 = u

def Connected {s : Incidence T E} (p : FacePairing s) : Prop :=
  ∀ t u : T, Relation.ReflTransGen (Adjacent p) t u

/-- Every face has the local pair count, which is consequently global on
an arbitrarily large connected system with opposite-paired colouring. -/
theorem balanced_signature_constant (s : Incidence T E) (p : FacePairing s)
    (hb : Balanced s) (hc : Connected p) :
    (∀ t f, faceCount s t f = pairCount s t) ∧
    (∀ t u, pairCount s t = pairCount s u) := by
  have hlocal : ∀ t f, faceCount s t f = pairCount s t := by
    intro t f
    obtain ⟨h03,h14,h25⟩ := hb t
    have h3 : mark s t 3 = mark s t 0 := by unfold mark; rw [← h03]
    have h4 : mark s t 4 = mark s t 1 := by unfold mark; rw [← h14]
    have h5 : mark s t 5 = mark s t 2 := by unfold mark; rw [← h25]
    fin_cases f <;>
      simp [faceCount, faceEdges, pairCount, Fin.sum_univ_succ, h3, h4, h5] <;> omega
  have hglue : ∀ a : T × Fin 4,
      faceCount s a.1 a.2 = faceCount s (p.partner a).1 (p.partner a).2 := by
    intro a
    unfold faceCount
    calc
      _ = ∑ j : Fin 3, mark s (p.partner a).1
          (faceEdges (p.partner a).2 (p.permutation a j)) := by
            apply Finset.sum_congr rfl
            intro j _
            unfold mark
            rw [p.preserves a j]
      _ = _ := Equiv.sum_comp (p.permutation a)
        (fun j => mark s (p.partner a).1 (faceEdges (p.partner a).2 j))
  have hstep : ∀ t u, Adjacent p t u → pairCount s t = pairCount s u := by
    intro t u h
    obtain ⟨f,hf⟩ := h
    calc
      pairCount s t = faceCount s t f := (hlocal t f).symm
      _ = faceCount s (p.partner (t,f)).1 (p.partner (t,f)).2 := hglue (t,f)
      _ = pairCount s (p.partner (t,f)).1 := hlocal _ _
      _ = pairCount s u := congrArg (pairCount s) hf
  refine ⟨hlocal, ?_⟩
  intro t u
  have h := hc t u
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (hstep _ _ hbc)

#print axioms balanced_signature_constant
end D5.S3.Geometry.Hyperideal.FaceColourPropagation

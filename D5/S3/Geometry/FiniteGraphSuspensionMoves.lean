/- GID: D5/S3/Geometry/FiniteGraphSuspensionMoves
   generality: G
   mirror-B: none(waiver:source-only-stage)
   mirror-E: none(waiver:source-only-stage)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Maps]
   utility: none
   digest: Concrete finite move chains consume the three proved graph identifications and their integral singular-homology shifts. -/
import D5.S3.Geometry.FiniteGraphSuspensionMoves.Lozin

/-!
UNCOMPILED, including every imported terminal-candidate dependency.
Source-only implementation for the SAME induced-king-grid Question 32 route.
No 93999-vertex expansion, degree-31327 theorem, torsion comparison, SW
refutation, CI, PR, or original-problem completion is asserted here.

`SimpleGraph.Iso.map` is the proved relabeling interface. The move-chain
constructors consume it after EVERY literal operation. Thus finite Nat labels
can be supplied as equivalences onto the actual finite vertex subtype, with
freshness and deletion represented exactly by the equivalence domain. No
graph isomorphism, homotopy equivalence, or homology shift is an input.
-/

noncomputable section
open CategoryTheory

namespace D5.S3.Geometry.FiniteGraphSuspensionMoves

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Relabeling uses the existing graph-map isomorphism, not a caller-supplied
isomorphism. This interface is consumed by all three chain constructors. -/
def relabelReducedIso (G : SimpleGraph V) (e : V ≃ W) (q : ℕ) :
    Reduced (G.map e) q ≅ Reduced G q :=
  (graphReducedIso (SimpleGraph.Iso.map e G) q).symm

def tripleRelabeledReducedHomologyIso (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) (e : (V ⊕ Fin 3) ≃ W) (q : ℕ) (hq : 1 ≤ q) :
    Reduced ((tripleSubdivision G a b).map e) (q + 1) ≅ Reduced G q :=
  relabelReducedIso (tripleSubdivision G a b) e (q + 1) ≪≫
    tripleSubdivisionReducedHomologyIso G hab q hq

def crossingRelabeledReducedHomologyIso (G : SimpleGraph V) (ends : (Bool × Bool) ↪ V)
    (hab : G.Adj (ends (false, false)) (ends (false, true)))
    (hcd : G.Adj (ends (true, false)) (ends (true, true)))
    (e : (V ⊕ Option (Bool × Bool)) ≃ W) (q : ℕ) (hq : 1 ≤ q) :
    Reduced ((crossingSuspension G ends).map e) (q + 1) ≅ Reduced G q :=
  relabelReducedIso (crossingSuspension G ends) e (q + 1) ≪≫
    crossingSuspensionReducedHomologyIso G ends hab hcd q hq

def lozinRelabeledReducedHomologyIso (G : SimpleGraph V) (v : V) (Y Z : Finset V)
    (hpart : ∀ x, G.Adj v x ↔ x ∈ Y ∨ x ∈ Z) (hdisj : Disjoint Y Z)
    (hYn : Y.Nonempty) (e : LozinVertex v ≃ W) (q : ℕ) (hq : 1 ≤ q) :
    Reduced ((lozinSuspension G v Y Z).map e) (q + 1) ≅ Reduced G q :=
  relabelReducedIso (lozinSuspension G v Y Z) e (q + 1) ≪≫
    lozinSuspensionReducedHomologyIso G v Y Z hpart hdisj hYn q hq

/-- A finite sequence of just the three literal graph operations. The index
counts suspensions exactly. This contains concrete operation data, never an
assumed homology-shift record or a generic certificate-correctness premise. -/
inductive MoveChain :
    {V W : Type} → [Fintype V] → [DecidableEq V] → [Fintype W] → [DecidableEq W] →
      SimpleGraph V → SimpleGraph W → ℕ → Type 1
  | refl {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : MoveChain G G 0
  | triple {V W X : Type} [Fintype V] [DecidableEq V]
      [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X]
      {G : SimpleGraph V} {F : SimpleGraph W} {n : ℕ}
      (prior : MoveChain G F n) (a b : W) (hab : F.Adj a b)
      (labels : (W ⊕ Fin 3) ≃ X) :
      MoveChain G ((tripleSubdivision F a b).map labels) (n + 1)
  | crossing {V W X : Type} [Fintype V] [DecidableEq V]
      [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X]
      {G : SimpleGraph V} {F : SimpleGraph W} {n : ℕ}
      (prior : MoveChain G F n) (ends : (Bool × Bool) ↪ W)
      (hab : F.Adj (ends (false, false)) (ends (false, true)))
      (hcd : F.Adj (ends (true, false)) (ends (true, true)))
      (labels : (W ⊕ Option (Bool × Bool)) ≃ X) :
      MoveChain G ((crossingSuspension F ends).map labels) (n + 1)
  | lozin {V W X : Type} [Fintype V] [DecidableEq V]
      [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X]
      {G : SimpleGraph V} {F : SimpleGraph W} {n : ℕ}
      (prior : MoveChain G F n) (v : W) (Y Z : Finset W)
      (hpart : ∀ x, F.Adj v x ↔ x ∈ Y ∨ x ∈ Z) (hdisj : Disjoint Y Z)
      (hYn : Y.Nonempty) (labels : LozinVertex v ≃ X) :
      MoveChain G ((lozinSuspension F v Y Z).map labels) (n + 1)

/-- Genuine iteration: n concrete suspensions shift degree q to q+n, for
every q≥1, in actual integral reduced singular homology. -/
def MoveChain.reducedHomologyIso {G : SimpleGraph V} {F : SimpleGraph W} {n : ℕ}
    (moves : MoveChain G F n) (q : ℕ) (hq : 1 ≤ q) :
    Reduced F (q + n) ≅ Reduced G q := by
  induction moves with
  | refl G => exact Iso.refl _
  | triple prior a b hab labels ih =>
    exact tripleRelabeledReducedHomologyIso _ hab labels _ (by omega) ≪≫ ih
  | crossing prior ends hab hcd labels ih =>
    exact crossingRelabeledReducedHomologyIso _ ends hab hcd labels _ (by omega) ≪≫ ih
  | lozin prior v Y Z hpart hdisj hYn labels ih =>
    exact lozinRelabeledReducedHomologyIso _ v Y Z hpart hdisj hYn labels _ (by omega) ≪≫ ih

/-- Finite Nat-labeled replay endpoint. The sequence itself supplies each
literal step and relabeling. This consumes the iterated shift; it does not
postulate correctness of the scientific replay or identify its final graph. -/
def natReplayReducedHomologyIso (S T : Finset ℕ)
    (G : SimpleGraph ↥S) (F : SimpleGraph ↥T) (n : ℕ)
    (moves : MoveChain G F n) (q : ℕ) (hq : 1 ≤ q) :
    (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) (q + n)).obj
      (TopCat.of (FiniteCoordinateTruncation.Ispace F)) ≅
    (TauCeti.reducedSingularHomologyFunctor (ModuleCat.of ℤ ℤ) q).obj
      (TopCat.of (FiniteCoordinateTruncation.Ispace G)) :=
  moves.reducedHomologyIso q hq

end D5.S3.Geometry.FiniteGraphSuspensionMoves

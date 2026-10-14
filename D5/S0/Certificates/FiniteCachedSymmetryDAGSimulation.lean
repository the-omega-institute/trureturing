/- GID: D5/S0/Certificates/FiniteCachedSymmetryDAGSimulation
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteCachedSymmetryDAGSimulation
   mirror-E: none(waiver:finite-cached-dag-simulation)
   anchors: []
   utility: none
   digest: Fuel-indexed node simulation transports checked replay while retaining each actual cache and partial assignment. -/

/- Prepared source for the existing EJM suffix. This theorem relates only node
representations. It never changes a cache, partial assignment, gap or symmetry
test, and cannot transfer arithmetic acceptance between different contexts.
Concrete alignment and every original frontier receipt remain obligations. -/

import D5.S0.Certificates.FiniteCachedSymmetryDAGReplay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)

variable {Coord Value Sym Cache : Type*} [Fintype Value]
  [DecidableEq Coord] {N M : ℕ}

/-- Corresponding nodes have the same bound test, symmetry action, or split
coordinate. Every value branch has related successors at the remaining fuel.
The relation need not be injective: actual contexts remain separate in replay. -/
inductive StepRelated (relation : Fin N → Fin M → Prop) :
    Node N Coord Value Sym → Node M Coord Value Sym → Prop where
  | bound : StepRelated relation .bound .bound
  | symmetry (s : Sym) : StepRelated relation (.symmetry s) (.symmetry s)
  | split (i : Coord) (left : Value → Fin N) (right : Value → Fin M)
      (children : ∀ a, relation (left a) (right a)) :
      StepRelated relation (.split i left) (.split i right)

/-- A fuel-indexed simulation preserves full cached acceptance. Split branches
use exactly the same actual cache step and partial update on both sides. No
cache table equality, native verdict or arithmetic abstraction is a premise. -/
theorem checked_simulation
    (leftNodes : ℕ → Fin N → Node N Coord Value Sym)
    (rightNodes : ℕ → Fin M → Node M Coord Value Sym)
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (dominates : Sym → Partial Coord Value → Bool) (gap : ℤ)
    (relation : ℕ → Fin N → Fin M → Prop)
    (alignment : ∀ fuel left right, relation (fuel + 1) left right →
      StepRelated (relation fuel) (leftNodes (fuel + 1) left)
        (rightNodes (fuel + 1) right))
    (fuel : ℕ) (left : Fin N) (right : Fin M) (cache : Cache)
    (p : Partial Coord Value) (related : relation fuel left right)
    (accepted : check leftNodes step lower dominates gap fuel left cache p = true) :
    check rightNodes step lower dominates gap fuel right cache p = true := by
  induction fuel generalizing left right cache p with
  | zero => simp only [check, Bool.false_eq_true] at accepted
  | succ fuel ih =>
    have same := alignment fuel left right related
    generalize hl : leftNodes (fuel + 1) left = leftNode at same
    generalize hr : rightNodes (fuel + 1) right = rightNode at same
    cases same with
    | bound => simpa only [check, hl, hr] using accepted
    | symmetry s => simpa only [check, hl, hr] using accepted
    | split i leftChildren rightChildren children =>
      simp only [check, hl] at accepted
      have all := of_decide_eq_true accepted
      simp only [check, hr]
      apply decide_eq_true
      intro a
      exact ih (leftChildren a) (rightChildren a) (step cache i a)
        (Function.update p i (some a)) (children a) (all a)

#print axioms checked_simulation

end D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

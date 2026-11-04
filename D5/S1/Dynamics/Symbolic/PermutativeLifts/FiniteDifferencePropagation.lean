/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/FiniteDifferencePropagation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-difference propagation through finite-window codes and their iterates. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativePreinjectivity

/-!
proof_shape:
  finite_difference_code: content;
    escape_witness: the finite union of translated copies of the input
      disagreement set covering every output disagreement;
    consumer: finite_difference_code_iterate.
  codeIter: definition; consumer: finite_difference_code_iterate.
  finite_difference_code_iterate: content;
    escape_witness: induction over arbitrary iteration depth using the
      finite-window support propagation;
    admission_basis: escape-witness.
Direct frozen dependency:
  D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity;
dependency state statement_id:
  sha256:9fb67b695eed10da02cbe201890996cd808067c2899dda05c098dd6219f74b07;
unfinished Reg audit:
  https://github.com/the-omega-institute/trureturing/issues/26254;
utility: none; these are unbounded symbolic statements over arbitrary
alphabets, window lengths, configurations and iteration depths, with no
bounded enumeration, checker, numeric reduction, or certified instance.
-/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.FiniteDifferencePropagation

open BipermutativeLift
open BipermutativePreinjectivity
open SymbolicDynamics.FullShift

variable {A : Type*} {k : ℕ}
variable {h : (Fin (k + 2) → A) → A}

/-!
An output disagreement at `i` can only be caused by an input disagreement in
the length-`k+2` window beginning at `i`.  Thus the output disagreement set is
contained in a finite union of integer translates of the input disagreement
set.
-/
theorem finite_difference_code {x y : ℤ → A} (hfin : FiniteDifference x y) :
    FiniteDifference (code h x) (code h y) := by
  let D : Set ℤ := {i : ℤ | x i ≠ y i}
  let E : Set ℤ := {i : ℤ | code h x i ≠ code h y i}
  have hD : D.Finite := hfin
  have hsubset : E ⊆ ⋃ j : Fin (k + 2), (fun d : ℤ => d - (j : ℕ)) '' D := by
    intro i hi
    by_contra hnot
    have hall : ∀ j : Fin (k + 2), x (i + (j : ℕ)) = y (i + (j : ℕ)) := by
      intro j
      by_contra hne
      apply hnot
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      refine ⟨i + (j : ℕ), ?_, ?_⟩
      · exact hne
      · push_cast
        omega
    apply hi
    change h (window x i) = h (window y i)
    congr 1
    funext j
    exact hall j
  have hfinite : (⋃ j : Fin (k + 2), (fun d : ℤ => d - (j : ℕ)) '' D).Finite := by
    exact Set.finite_iUnion (fun j => hD.image _)
  exact hfinite.subset hsubset

/-- The `n`-fold iterate of a fixed finite-window code. -/
def codeIter (h : (Fin (k + 2) → A) → A) : ℕ → (ℤ → A) → (ℤ → A)
  | 0, x => x
  | n + 1, x => code h (codeIter h n x)

/-!
Finite disagreement is preserved at every finite iterate.  The induction is
the reusable bridge for later homoclinic-class and code-composition arguments.
-/
theorem finite_difference_code_iterate (n : ℕ) {x y : ℤ → A}
    (hfin : FiniteDifference x y) :
    FiniteDifference (codeIter h n x) (codeIter h n y) := by
  induction n with
  | zero => exact hfin
  | succ n ih =>
      simpa [codeIter] using (finite_difference_code (h := h) ih)

end D5.S1.Dynamics.Symbolic.PermutativeLifts.FiniteDifferencePropagation

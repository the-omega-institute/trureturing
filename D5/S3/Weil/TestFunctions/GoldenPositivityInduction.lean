/- GID: D5/S3/Weil/TestFunctions/GoldenPositivityInduction
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/GoldenPositivityInduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Propagate positivity through Fibonacci support layers and all compact tests. -/

import D5.S3.Weil.TestFunctions
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import Mathlib.Data.Nat.Fib.Basic

namespace D5.S3.Weil.TestFunctions.GoldenPositivityInduction

open D5.S3.Weil.TestFunctions

/-!
Search receipt (2026-09-02): repository name and body-shape searches found no
frozen theorem combining two-step positivity induction with the compact-support
consequence. `Zeta23.EF.exists_abs_le_of_hasCompactSupport` supplies the exact
support-bound bridge. Pinned Mathlib supplies `Nat.twoStepInduction` and
`Nat.le_fib_self`; no new support-layer definition is introduced.
-/

/-- Base positivity, a two-layer recurrence, and nonnegative residuals make
every Fibonacci support layer nonnegative. Cofinality of those support radii
then gives nonnegativity for every compactly supported Weil test. -/
theorem golden_positivity_induction (Q : WeilTestFunction -> Real) :
    let Layer := fun n : Nat =>
      {f : WeilTestFunction // forall x : Real,
        f x ≠ 0 -> |x| <= (Nat.fib (n + 5) : Real)}
    forall
      (A : forall n, Layer (n + 2) -> Layer (n + 1))
      (B : forall n, Layer (n + 2) -> Layer n)
      (R : forall n, Layer (n + 2) -> Real),
      (forall f : Layer 0, 0 <= Q f.1) ->
      (forall f : Layer 1, 0 <= Q f.1) ->
      (forall n (f : Layer (n + 2)),
        Q f.1 = Q (A n f).1 + Q (B n f).1 + R n f) ->
      (forall n (f : Layer (n + 2)), 0 <= R n f) ->
      (forall n (f : Layer n), 0 <= Q f.1) /\
        forall f : WeilTestFunction, 0 <= Q f := by
  dsimp only
  intro A B R hQ0 hQ1 hrec hR
  have hLayer : forall n (f :
      {f : WeilTestFunction // forall x : Real,
        f x ≠ 0 -> |x| <= (Nat.fib (n + 5) : Real)}), 0 <= Q f.1 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => exact hQ0
    | one => exact hQ1
    | more n hn hn1 =>
        intro f
        rw [hrec n f]
        exact add_nonneg (add_nonneg (hn1 (A n f)) (hn (B n f))) (hR n f)
  refine ⟨hLayer, ?_⟩
  intro f
  obtain ⟨radius, supportBound⟩ :=
    Zeta23.EF.exists_abs_le_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨n, radiusLe⟩ := exists_nat_ge radius
  have largeScale : n + 5 <= Nat.fib (n + 5) := Nat.le_fib_self (by omega)
  have nLeFib : n <= Nat.fib (n + 5) := by omega
  have nLeFibReal : (n : Real) <= (Nat.fib (n + 5) : Real) := by
    exact_mod_cast nLeFib
  exact hLayer n
    ⟨f, fun x hx => (supportBound x hx).trans (radiusLe.trans nLeFibReal)⟩

#print axioms golden_positivity_induction

end D5.S3.Weil.TestFunctions.GoldenPositivityInduction

/- GID: D5/S3/Weil/TestFunctions/GoldenPositivityInduction
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/GoldenPositivityInduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Propagate positivity through chosen recurrent support layers and all compact tests. -/

import D5.S3.Weil.TestFunctions
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import Mathlib.Algebra.Order.Archimedean.Basic

namespace D5.S3.Weil.TestFunctions.GoldenPositivityInduction

open D5.S3.Weil.TestFunctions

/-!
Search receipt (2026-09-02): repository name and body-shape searches found no
frozen theorem combining two-step positivity induction with the compact-support
consequence. `Zeta23.EF.exists_abs_le_of_hasCompactSupport` supplies the exact
support-bound bridge. Pinned Mathlib supplies `Nat.twoStepInduction` and the
Archimedean bound `exists_nat_ge`; no new support-layer definition is introduced.
-/

/-- Let the chosen positive support schedule obey the source relation
`L (n + 2) = L (n + 1) + L n` (equation (1219.1)). Base positivity, the
two-layer form recurrence (1219.2), and nonnegative residuals make every layer
nonnegative. The support schedule is cofinal by positivity and its recurrence,
so every compactly supported Weil test belongs to some layer. -/
theorem golden_positivity_induction
    (L : Nat -> Real) (Q : WeilTestFunction -> Real)
    (hLpos : forall n, 0 < L n)
    (hLrec : forall n, L (n + 2) = L (n + 1) + L n) :
    let Layer := fun n : Nat =>
      {f : WeilTestFunction // forall x : Real,
        f x ≠ 0 -> |x| <= L n}
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
        f x ≠ 0 -> |x| <= L n}), 0 <= Q f.1 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => exact hQ0
    | one => exact hQ1
    | more n hn hn1 =>
        intro f
        rw [hrec n f]
        exact add_nonneg (add_nonneg (hn1 (A n f)) (hn (B n f))) (hR n f)
  have hTail : forall n, L 2 <= L (n + 2) := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        calc
          L 2 <= L (n + 2) := ih
          _ <= L (n + 2) + L (n + 1) :=
            le_add_of_nonneg_right (hLpos (n + 1)).le
          _ = L ((n + 1) + 2) := by
            simpa only [Nat.add_assoc] using (hLrec (n + 1)).symm
  have hGrowth : forall n : Nat, (n : Real) * L 2 <= L (2 * n + 2) := by
    intro n
    induction n with
    | zero => simpa using (hLpos 2).le
    | succ n ih =>
        have hright : L 2 <= L ((2 * n + 2) + 1) := by
          convert hTail (2 * n + 1) using 1
        calc
          (Nat.succ n : Real) * L 2 = L 2 + (n : Real) * L 2 := by
            rw [Nat.cast_succ]
            ring
          _ <= L ((2 * n + 2) + 1) + L (2 * n + 2) := add_le_add hright ih
          _ = L ((2 * n + 2) + 2) := (hLrec (2 * n + 2)).symm
          _ = L (2 * Nat.succ n + 2) := by
            congr 1
  have hCofinal : forall radius : Real, exists n, radius <= L n := by
    intro radius
    obtain ⟨n, hn⟩ := exists_nat_ge (radius / L 2)
    refine ⟨2 * n + 2, ?_⟩
    exact ((div_le_iff₀ (hLpos 2)).mp hn).trans (hGrowth n)
  refine ⟨hLayer, ?_⟩
  intro f
  obtain ⟨radius, supportBound⟩ :=
    Zeta23.EF.exists_abs_le_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨n, radiusLe⟩ := hCofinal radius
  exact hLayer n
    ⟨f, fun x hx => (supportBound x hx).trans radiusLe⟩

#print axioms golden_positivity_induction

end D5.S3.Weil.TestFunctions.GoldenPositivityInduction

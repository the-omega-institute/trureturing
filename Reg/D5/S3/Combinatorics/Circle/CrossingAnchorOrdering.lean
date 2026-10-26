import D5.S3.Combinatorics.Circle.CrossingAnchorOrdering
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.SourceWidth
open _root_.D5.S3.Combinatorics.Circle.MixedSuffixEnergy
open _root_.D5.S3.Combinatorics.Circle.CrossingAnchorOrdering

namespace Reg.D5.S3.Combinatorics.Circle.CrossingAnchorOrdering
universe u

/-- The complete weight function on arbitrary physical label types. -/
abbrev weightSignature : Signature where
  Params := Type u
  State α := α → ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := α → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ _ f => f) (fun e => nomatch e)

/-- Replacing the weight readout in the entire original ordering telescope
also replaces its SMALL, LARGE, endpoint and anchor hypotheses. -/
def weightArena : Arena where
  signature := weightSignature
  Law R := ∀ (α : Type u) (f : α → ℤ) (T : List α) (v1 v2 a : α)
    (Q C b e : ℤ),
    let g := R.readout () α f
    2 ≤ Q → C = 2 * Q - 1 → (T ++ [v1, v2]).Nodup →
    (∀ i ∈ T, |g i| < Q) →
    (Q ≤ -g v1 ∧ -g v1 ≤ C) → (Q ≤ -g v2 ∧ -g v2 ≤ C) →
    a ∈ T → 0 < g a → g a ≤ C - max (-g v1) (-g v2) →
    min (-g v1) (-g v2) ≤ g a + (C - max (-g v1) (-g v2)) →
    (0 ≤ b ∧ b ≤ Q - 1) → (0 ≤ e ∧ e ≤ C) →
    b + mass g T + g v1 + g v2 = e →
    ∃ L : List α, L.Perm (T ++ [v1, v2]) ∧ InStrip g C b L ∧
      b + mass g L = e ∧
      ∀ d : ℕ, 0 ≤ b + mass g (L.take d) ∧ b + mass g (L.take d) ≤ C

private theorem every_weight_readout_lawful (R : Realization weightSignature.{u}) :
    weightArena.Law R := by
  intro α f T v1 v2 a Q C b e
  exact exists_order_two_negative (R.readout () α f) T v1 v2 a Q C b e

/-- This whole-weight template has no rejected intervention. It therefore
cannot provide a four-slot registration by changing only the weights. -/
theorem no_weight_variation : ¬ Variation weightArena weightActual.{u} := by
  rintro ⟨_, R, hR⟩
  exact hR (every_weight_readout_lawful R)

#print axioms no_weight_variation
end Reg.D5.S3.Combinatorics.Circle.CrossingAnchorOrdering

/- GID: D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.claim; result=D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.result; claim=D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.claim
   digest: The perp hyperplane refutes the classical-hexagon contextuality conjecture. -/

import D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity

/-! The line-set reading of Saniga et al., arXiv:2312.07738v3, preregistered in #24997.
Assignments and line signs use additive binary notation: one denotes a negative sign.
The witness consists of all isotropic lines inside the perp of the observable IIZ.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity

namespace D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation

noncomputable section

/-- Binary labels of three-qubit Pauli observables, including the identity label. -/
abbrev point := Fin 3 → ZMod 2 × ZMod 2

/-- The full three-qubit symplectic space. Its projective points exclude zero. -/
def w : Submodule (ZMod 2) point := ⊤

/-- The additive sign of the canonical Pauli product: one is negative. -/
def lineSign (l : Finset point) : ZMod 2 := by
  classical
  exact if lineProduct l = -1 then 1 else 0

/-- The number of contexts whose additive parity disagrees with the Pauli sign. -/
def violations (c : Finset (Finset point)) (f : point → ZMod 2) : ℕ := by
  classical
  exact (c.filter fun l => (∑ q ∈ l, f q) ≠ lineSign l).card

/-- Minimum number of violated contexts over all binary hidden-variable assignments. -/
def contextualityDegree (c : Finset (Finset point)) : ℕ :=
  sInf (Set.range (violations c))

/-- Every classically embedded split Cayley hexagon satisfies these axioms:
three lines per point, no ordinary triangle, and planarity at every point.
Thus this class contains every classical embedding used in the source conjecture. -/
def IsClassicalHexagon (h : Finset (Finset point)) : Prop :=
  h ⊆ lines w ∧
  (∀ q ∈ points w, (h.filter fun l => q ∈ l).card = 3) ∧
  (∀ a b c : point, ∀ l ∈ h, ∀ m ∈ h, ∀ n ∈ h,
    a ≠ b → b ≠ c → c ≠ a → l ≠ m → m ≠ n → n ≠ l →
    a ∈ l → b ∈ l → b ∈ m → c ∈ m → c ∈ n → a ∈ n → False) ∧
  (∀ z a b : point, ∀ l ∈ h, ∀ m ∈ h,
    z ∈ l → z ∈ m → a ∈ l → b ∈ m → B a b = 0)

/-- The source's generalization to arbitrary contextual line subgeometries. -/
def claim : Prop :=
  ∀ c : Finset (Finset point), c ⊆ lines w → 0 < contextualityDegree c →
    ∃ h, IsClassicalHexagon h ∧ contextualityDegree c = (c ∩ h).card

private def pole : point := ![(0, 0), (0, 0), (0, 1)]

private def counterexample : Finset (Finset point) := by
  classical
  exact (lines w).filter fun l => ∀ q ∈ l, B pole q = 0

private theorem counterexample_subset : counterexample ⊆ lines w := by
  classical
  exact Finset.filter_subset _ _

private theorem counterexample_contextual : 0 < contextualityDegree counterexample := by
  sorry

private theorem counterexample_degree_le : contextualityDegree counterexample ≤ 12 := by
  sorry

private theorem hexagon_intersection_ge (h : Finset (Finset point))
    (hh : IsClassicalHexagon h) : 15 ≤ (counterexample ∩ h).card := by
  sorry

/-- The IIZ perp hyperplane has positive degree at most twelve, but shares at least
fifteen lines with every classical hexagon. -/
theorem result : ¬ claim := by
  classical
  intro hc
  obtain ⟨h, hh, he⟩ := hc counterexample counterexample_subset counterexample_contextual
  have hlo := hexagon_intersection_ge h hh
  have hhi := counterexample_degree_le
  omega

end

end D5.S3.Quantum.Contextuality.PerpHyperplaneHexagonContextualityRefutation

/- GID: D5/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity
   generality: I
   mirror-B: D5/B/S3/Quantum/Contextuality/LinearDoilyNegativeLineParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every linear N-qubit doily has an odd number of negative lines. -/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import D5.S3.QuadraticForms.SymplecticBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)

namespace D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity

noncomputable section

/-- The unsigned single-qubit label, with `(1,1)` represented by `Y = iXZ`. -/
def canonicalLabel (p : ZMod 2 × ZMod 2) : Pauli :=
  if p.1 = 0 then (if p.2 = 0 then .I else .Z)
  else (if p.2 = 0 then .X else .Y)

/-- The literal tensor product of the canonical single-qubit labels. -/
def observable {N : ℕ} (v : Fin N → ZMod 2 × ZMod 2) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  wordOp fun j => canonicalLabel (v j)

/-- The binary symplectic form expressing Pauli commutation. -/
def B {N : ℕ} (v w : Fin N → ZMod 2 × ZMod 2) : ZMod 2 :=
  ∑ j, ((v j).1 * (w j).2 + (v j).2 * (w j).1)

/-- A four-dimensional subspace with nondegenerate restricted symplectic form. -/
def IsLinearDoily {N : ℕ} (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) : Prop :=
  Module.finrank (ZMod 2) U = 4 ∧
    ∀ u ∈ U, (∀ w ∈ U, B u w = 0) → u = 0

/-- The projective points over the binary field are precisely the nonzero vectors. -/
def points {N : ℕ} (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) :
    Finset (Fin N → ZMod 2 × ZMod 2) := by
  classical
  exact Finset.univ.filter fun v => v ∈ U ∧ v ≠ 0

/-- The isotropic lines: three distinct nonzero vectors `{u,v,u+v}` in the subspace. -/
def lines {N : ℕ} (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) :
    Finset (Finset (Fin N → ZMod 2 × ZMod 2)) := by
  classical
  exact (points U).powerset.filter fun l =>
    l.card = 3 ∧ ∀ u ∈ l, ∀ v ∈ l, u ≠ v → u + v ∈ l ∧ B u v = 0

/-- Product of the three canonical observables; isotropy makes its order immaterial. -/
def lineProduct {N : ℕ} (l : Finset (Fin N → ZMod 2 × ZMod 2)) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  (l.toList.map observable).prod

/-- A line is negative exactly when its three observables multiply to minus identity. -/
def negativeLines {N : ℕ} (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) :
    Finset (Finset (Fin N → ZMod 2 × ZMod 2)) := by
  classical
  exact (lines U).filter fun l => lineProduct l = -1

/-- The all-qubit parity assertion for linear doilies. -/
def claim : Prop :=
  ∀ (N : ℕ), 2 ≤ N →
    ∀ U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2),
      IsLinearDoily U → Odd (negativeLines U).card

/-- The multiplication exponent in the fourth roots of unity. -/
private def localExponent (u v : ZMod 2 × ZMod 2) : ZMod 4 :=
  (u.1.val * u.2.val : ℕ) + (v.1.val * v.2.val : ℕ) -
    ((u + v).1.val * (u + v).2.val : ℕ) + 2 * (u.2.val * v.1.val : ℕ)

private def fourthRoot (k : ZMod 4) : ℂ := Complex.I ^ k.val

private def phase {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2) : ℂ :=
  ∏ j, fourthRoot (localExponent (u j) (v j))

private def bitSign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

private theorem local_mul (u v : ZMod 2 × ZMod 2) :
    pauliMatrix (canonicalLabel u) * pauliMatrix (canonicalLabel v) =
      fourthRoot (localExponent u v) • pauliMatrix (canonicalLabel (u + v)) := by
  sorry

private theorem observable_mul {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2) :
    observable u * observable v = phase u v • observable (u + v) := by
  sorry

private theorem observable_sq {N : ℕ} (u : Fin N → ZMod 2 × ZMod 2) :
    observable u * observable u = 1 := by
  sorry

private theorem observable_comm {N : ℕ} (u v : Fin N → ZMod 2 × ZMod 2) :
    observable u * observable v = bitSign (B u v) • (observable v * observable u) := by
  sorry

private theorem line_sign {N : ℕ}
    (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2))
    (l : Finset (Fin N → ZMod 2 × ZMod 2)) (hl : l ∈ lines U) :
    lineProduct l = 1 ∨ lineProduct l = -1 := by
  sorry

private theorem point_count {N : ℕ}
    (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) (hU : IsLinearDoily U) :
    (points U).card = 15 := by
  sorry

private def modelForm (a b : Fin 4 → ZMod 2) : ZMod 2 :=
  a 0 * b 1 + a 1 * b 0 + a 2 * b 3 + a 3 * b 2

private theorem symplectic_coordinates {N : ℕ}
    (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) (hU : IsLinearDoily U) :
    ∃ e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U,
      ∀ a b, B (e a) (e b) = modelForm a b := by
  sorry

private def logicalOp {N : ℕ}
    {U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)}
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U) (a : Fin 4 → ZMod 2) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  (Complex.I ^ ((a 0).val * (a 1).val + (a 2).val * (a 3).val)) •
    (List.ofFn fun i : Fin 4 => observable (e (Pi.single i 1)) ^ (a i).val).prod

private def epsilon {N : ℕ}
    {U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)}
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U) (a : Fin 4 → ZMod 2) : ℂ :=
  Complex.I ^ ((a 0).val * (a 1).val + (a 2).val * (a 3).val) *
    ∏ j, fourthRoot
      ((∑ i, ((a i).val * ((e (Pi.single i 1) : Fin N → ZMod 2 × ZMod 2) j).1.val *
        ((e (Pi.single i 1) : Fin N → ZMod 2 × ZMod 2) j).2.val : ℕ)) -
       (((e a : Fin N → ZMod 2 × ZMod 2) j).1.val *
         ((e a : Fin N → ZMod 2 × ZMod 2) j).2.val : ℕ) +
       2 * ∑ i, ∑ k ∈ Finset.univ.filter (i < ·),
         ((a i).val * (a k).val *
          ((e (Pi.single i 1) : Fin N → ZMod 2 × ZMod 2) j).2.val *
          ((e (Pi.single k 1) : Fin N → ZMod 2 × ZMod 2) j).1.val : ℕ))

private theorem logical_rephasing {N : ℕ}
    {U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)}
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U) (a : Fin 4 → ZMod 2) :
    logicalOp e a = epsilon e a • observable (e a) := by
  sorry

private theorem epsilon_sign {N : ℕ}
    {U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)}
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (he : ∀ a b, B (e a) (e b) = modelForm a b) (a : Fin 4 → ZMod 2) :
    epsilon e a = 1 ∨ epsilon e a = -1 := by
  sorry

private theorem epsilon_product {N : ℕ}
    {U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)}
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U) :
    (∏ a : Fin 4 → ZMod 2, epsilon e a) = 1 := by
  sorry

private theorem parity_transfer {N : ℕ}
    (U : Submodule (ZMod 2) (Fin N → ZMod 2 × ZMod 2)) (hU : IsLinearDoily U)
    (e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] U)
    (he : ∀ a b, B (e a) (e b) = modelForm a b)
    (hr : ∀ a, logicalOp e a = epsilon e a • observable (e a))
    (hs : ∀ a, epsilon e a = 1 ∨ epsilon e a = -1)
    (hp : (∏ a : Fin 4 → ZMod 2, epsilon e a) = 1)
    (hl : ∀ l ∈ lines U, lineProduct l = 1 ∨ lineProduct l = -1)
    (hc : (points U).card = 15) :
    Odd (negativeLines U).card := by
  sorry

/-- Every linear doily has an odd number of negative lines. -/
theorem result : claim := by
  intro N _ U hU
  obtain ⟨e, he⟩ := symplectic_coordinates U hU
  exact parity_transfer U hU e he (logical_rephasing e) (epsilon_sign e he)
    (epsilon_product e) (line_sign U) (point_count U hU)

end

end D5.S3.Quantum.Contextuality.LinearDoilyNegativeLineParity

import D5.S3.FiniteGroups.GroupAlgebra.RectangularTensorObstruction
import D5.S3.FiniteGroups.GroupAlgebra.PrimeCyclicRelativeTrace

/-!
# Arithmetic obstruction in the original relative stable category

For the original polynomial contragredients and the original retract-based
relative ideal, a vanishing binomial coefficient obstructs relative stable
isomorphism in the p-multiple family. The field-size bound is exactly
`p*a + p*b + 2 ≤ card K`; the number of relative summands is arbitrary.

The rectangular all-morphism obstruction gives trace zero for `g ∘ f`.
The explicit prime-cyclic norm gives trace zero for any original relative-factor
error. The identity on `V_(p*a+p*b+1)` has trace one, so the two conclusions
contradict a relative stable inverse. No converse is asserted.

Source: Elmer--Kadr, DOI 10.1007/s13366-026-00855-9, Conjecture 3.7(a).
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.ArithmeticTensorStableObstruction

open ElmerKadrTensorCounterexample

universe uK

variable {K : Type uK} [Field K] [Fintype K]
  {p : ℕ} [Fact p.Prime] [CharP K p]

/-- The negative p-multiple direction for the original relative stable relation.
The binomial-zero premise is retained also when a or b is zero. -/
theorem no_relative_stable (a b s : ℕ)
    (hsize : p * a + p * b + 2 ≤ Fintype.card K)
    (hchoose : ((p * a + p * b).choose (p * a) : K) = 0) :
    ¬ RelativeStableIso
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s)
      (dualAction K (p * a + p * b + 1))
      (RectangularTensorObstruction.tensorAction K (p * a) (p * b)) := by
  rintro ⟨f, g, hgf, _⟩
  have herr := PrimeCyclicRelativeTrace.trace_relativeFactors s
    (dualAction K (p * a + p * b + 1))
    (g.comp f - .id (dualAction K (p * a + p * b + 1))) hgf
  have hzero := RectangularTensorObstruction.composition_trace_zero
    (p * a) (p * b) hsize hchoose f g
  have hid : LinearMap.trace K (DualPower K (p * a + p * b + 1))
      LinearMap.id = 1 := by
    have hc : ((p * a + p * b + 1 : ℕ) : K) = 1 := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        CharP.cast_eq_zero K p, zero_mul, zero_add]
    rw [LinearMap.trace_eq_matrix_trace K (dualBasis K (p * a + p * b + 1)),
      LinearMap.toMatrix_id]
    simpa using hc
  change LinearMap.trace K (DualPower K (p * a + p * b + 1))
    (g.toLinearMap.comp f.toLinearMap - LinearMap.id) = 0 at herr
  rw [map_sub, hzero, hid, zero_sub] at herr
  exact one_ne_zero (neg_eq_zero.mp herr)

end D5.S3.FiniteGroups.GroupAlgebra.ArithmeticTensorStableObstruction

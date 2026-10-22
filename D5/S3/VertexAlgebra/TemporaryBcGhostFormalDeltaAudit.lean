import D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi

set_option autoImplicit false

open D5.S3.VertexAlgebra
open FormalDeltaDistribution BcGhostFockSupport BcGhostSuperGenerators
open BcGhostSuperStateField BcGhostSuperBorcherdsTerms BcGhostSuperJacobi
open BcGhostFormalDeltaJacobi SuperFieldProducts
open scoped VertexOperator

noncomputable section

example (region : Region) (power : ℤ) (offset : ℕ) :
    deltaDistribution region (deltaExponent region power offset) =
      deltaWeight region power offset :=
  delta_coefficient region power offset

example (region : Region) (exponent : Exponent) :
    Function.HasFiniteSupport (fun index : deltaFiber region exponent =>
      deltaWeight region index.val.1 index.val.2) :=
  delta_fiber_finite region exponent

example (parameter first last : ℤ) (left right vector : Carrier) :
    regionDistribution .forward left right vector
      ⟨-parameter - 1, -first - 1, -last - 1⟩ =
        ∑ᶠ offset : ℕ, ((-1 : ℂ) ^ offset * integerBinomial parameter offset) •
          (((Y left)[[first + parameter - offset]]) (((Y right)[[last + offset]]) vector)) := by
  exact forward_coefficient parameter first last left right vector

example (parameter first last : ℤ) (left right vector : Carrier) :
    regionDistribution .reverse left right vector
      ⟨-parameter - 1, -first - 1, -last - 1⟩ =
        ∑ᶠ offset : ℕ, ((-1 : ℂ) ^ offset * integerBinomial parameter offset) •
          (epsilon parameter •
            (((Y right)[[last + parameter - offset]]) (((Y left)[[first + offset]]) vector))) := by
  simpa only [jacobiRightSecondTerm, exchangeEpsilon, mul_one, mu, weight, modeExponent] using
    reverse_coefficient parameter first last left right vector

example (parameter first last : ℤ) (left right vector : Carrier) :
    regionDistribution .iterate left right vector
      ⟨-parameter - 1, -first - 1, -last - 1⟩ =
        ∑ᶠ offset : ℕ, integerBinomial first offset •
          (((Y (((Y left)[[parameter + offset]]) right))[[first + last - offset]]) vector) := by
  exact iterate_coefficient parameter first last left right vector

example (first : ℤ) (offset : ℕ) :
    (-1 : ℂ) ^ offset * (((Ring.choose ((offset : ℤ) - first - 1) offset : ℤ) : ℂ)) =
      (((Ring.choose first offset : ℤ) : ℂ)) := by
  exact signed_negative_binomial first offset

example (leftParity rightParity : ℕ) (left right : Carrier)
    (leftHomogeneous : left ∈ homogeneous leftParity)
    (rightHomogeneous : right ∈ homogeneous rightParity) :
    operatorDistribution .forward left right -
      koszul leftParity rightParity • operatorDistribution .reverse left right =
        operatorDistribution .iterate left right :=
  (homogeneous_operator_formal_delta_jacobi leftParity rightParity left right
    leftHomogeneous rightHomogeneous).symm

example (left right : Carrier) :
    (∑ leftParity ∈ Finset.range 2, ∑ rightParity ∈ Finset.range 2,
      (operatorDistribution .forward (parityPart leftParity left) (parityPart rightParity right) -
        koszul leftParity rightParity • operatorDistribution .reverse
          (parityPart leftParity left) (parityPart rightParity right))) =
      operatorDistribution .iterate left right :=
  (mixed_operator_formal_delta_jacobi left right).symm

example (region : Region) (exponent : Exponent) (left right vector : Carrier) :
    Function.HasFiniteSupport (fun atom : coefficientFiber region exponent =>
      atomOperator region left right atom.val vector) :=
  region_fiber_finite region exponent left right vector

example (exponent : Exponent) (left right vector : Carrier) :
    Function.HasFiniteSupport (mixedResolvedTerm exponent left right vector) :=
  mixed_resolved_finite exponent left right vector

end

# Canonical Zeta Cayley Krein Inverse

## Abstract

The zero Cayley coefficient at a same-height mirror point is the reciprocal of the conjugate original coefficient. This node uses that symmetry to construct a bounded reciprocal diagonal operator and prove it is the two-sided inverse of the zero Cayley operator for every valid `ZeroData`.

## Main identities

Writing `U` for the zero Cayley operator and `J` for the mirror fundamental symmetry, the node proves

\[
U^{-1}=J U^* J,
\]

and both conservation laws

\[
U^*JU=J,
\qquad
UJU^*=J.
\]

The boundedness of the reciprocal multiplier is transported from the already bounded Cayley coefficient vector through mirror permutation and complex conjugation. No ordinary-unitarity or RH assumption is used.

## Truth anchors

- `zeroCayleyOperator_isUnit_unconditional`
- `zeroCayleyKreinInverse_comp_cayley`
- `zeroCayleyKreinInverse_eq_explicit`
- `cayley_comp_zeroCayleyKreinInverse`
- `zeroCayleyOperator_companion_j_unitary`
- `zero_cayley_krein_inverse_spec`

# Golden Algebraic Model

## Abstract

The golden integer carrier is a quadratic quotient with explicit conjugation, trace, and norm.

**Definition 1.1 (Quadratic quotient, conjugation, trace, and norm).**

Lean statement: `D5/S0/Carrier/AlgebraicModel.golden_algebraic_model_spec`

*Formalization.* `D5/S0/Carrier/AlgebraicModel.golden_algebraic_model_spec` (`✓ std3`).

*Citation.* Ian Stewart and David Tall (2025). *Algebraic Number Theory and Fermat's Last Theorem*. DOI: [10.1201/9781003462002](https://doi.org/10.1201/9781003462002).

*Commentary.*

The coordinate ring is realized as the quotient at the golden polynomial. The kernel-checked conjunction identifies its distinguished root and gives the conjugate, trace, and norm formulas in integral coordinates.

**Theorem 1.2 (Trace discriminant identity).**

$\forall x\in\mathbb{Z}[\varphi],\ \operatorname{trace}(x)^2-4\operatorname{norm}(x)=5\,x_b^2$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/AlgebraicModel.trace_sq_sub_four_norm_eq_five_mul_b_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfolding the existing coordinate formulas for `trace` and `norm` reduces the discriminant `trace(x)^2 - 4 * norm(x)` to the integer polynomial identity `5 * x.b^2`. The constants come from the quadratic basis `(1, phi)` and the golden polynomial `t^2 - t - 1`.

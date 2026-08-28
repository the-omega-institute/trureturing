# Off-Line One-Point Witness

## Abstract

The shifted finite-difference observer has a quantitative negative one-point witness at an off-line zero.

**Theorem 1.1 (Off-line one-point witness).**

$$\forall rho\in\mathbb{C}, \forall delta\in\mathbb{R}, \forall gamma\in\mathbb{R}, \forall omega\in\mathbb{R}, (rho=\frac{1}{2}+delta+i\cdot gamma\land 0<delta\land 0<omega\land omega<delta\land xiReading(rho)=0\land xiReading(rho-2\cdot omega)\neq0) \Rightarrow diagonalValue(omega,-gamma+i\cdot (delta-omega))=-\frac{1}{omega\cdot (delta-omega)}\land diagonalValue(omega,-gamma+i\cdot (delta-omega))<0\land diagonalValue(omega,-gamma+i\cdot (delta-omega))\leq-\frac{4}{delta^2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaCore/OffLinePickWitness.off_line_one_point_pick_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a zero represented as one half plus a positive real displacement and an imaginary ordinate, and for a positive shift smaller than that displacement, the finite-difference observer evaluates to a negative diagonal value. The value is exactly minus the reciprocal product of the shift and the remaining displacement, and is bounded above by minus four over the squared displacement. The nonvanishing shifted evaluation is the source condition that keeps the observer defined.

## References

- Truth anchor: `D5/S3/Weil/ZetaCore/OffLinePickWitness.off_line_one_point_pick_witness`
- Dependency: [D5/S3/Zeros/CompletedZeta](../../Zeros/CompletedZeta.md)

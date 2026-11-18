# Prime-selection density integrals

## Abstract

For s>1, normalized prime-selection profiles have explicit mass, logarithmic moment and binary entropy.

**Definition 1.1 (Selection density).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For s>1 and u>0, q(s,u)=a(s)^s/(a(s)^s+u^s), where a(s)=s*sin(pi/s)/pi. This is a Bernoulli inclusion probability for primes on the logarithmic spatial scale.

**Theorem 1.2 (Interior probabilities).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_range`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s>1, the density lies strictly between zero and one on the positive half-line. Thus every nondegenerate compact interval has both selected and unselected capacity.

**Theorem 1.3 (Continuous profile).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s>1, the density is continuous on the positive half-line. Compact restrictions can therefore be approximated by finitely many bins.

**Theorem 1.4 (Unit mass).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s>1, the density is integrable on (0,infinity) and its total integral is one. The proof applies the existing power-kernel integral to the parameter a(s)^s.

**Theorem 1.5 (Logarithmic moment).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_log_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_log_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s>1, the logarithmic moment is absolutely integrable on (0,infinity) and equals log(a(s))-(pi/s)*cos(pi/s)/sin(pi/s). A power substitution first evaluates the Mellin integral for exponents between zero and s. Differentiation at exponent one is justified by an integrable bound using two nearby Mellin exponents.

**Theorem 1.6 (Integrated binary entropy).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_entropy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s>1, the binary entropy of the density is integrable on (0,infinity) and its total integral equals s-pi*cos(pi/s)/sin(pi/s). The pointwise entropy identity separates the logarithmic weight, mass and logarithmic moment. The logarithmic weight integrates to s by an improper integration by parts with vanishing endpoint terms.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_continuous`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_entropy`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_log_moment`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_mass`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_range`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTailUpper](../OmegaTailUpper.md)

# The all-length integer transversality certificate

## Abstract

Division-free integer recurrences certify nonzero real derivative slopes at every pair of positive exterior lengths.

**Definition 1.1 (The left covector recurrence).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.lu`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.lu` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The integer triple lu starts at (1,0,-1) and sends (a,b,c) to (3a-2b,5c,-2a+3b). Its real cast computes the left inverse-power readout in OpenBoundaryMPSInteriorTransversality.left_inverse_read.

**Definition 1.2 (The left target recurrence).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.lv`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.lv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The integer triple lv starts at (1,0,1) and sends (a,b,c) to (3a+2b,c,2a+3b). Its real cast computes the actual left target in OpenBoundaryMPSInteriorTransversality.left_forward_coords.

**Definition 1.3 (The right inverse-power recurrence).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.rx`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.rx` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The integer triple rx starts at (0,1,0) and sends (a,b,c) to (3a-2b,5c,-2a+3b). Its real cast computes the radial inverse-power contribution in the consuming transversality proof.

**Definition 1.4 (The right target recurrence).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.ry`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.ry` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The integer triple ry starts at (1,0,0) and sends (a,b,c) to (3a+2c,2a+3c,b). Its real cast computes the iterated actual right environment in the consuming transversality proof.

**Definition 1.5 (The left slope numerator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.U`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

U(0)=0 and U(n+1)=5U(n)+2(lu(n+1,0)lv(n+1,1)+lu(n+1,1)lv(n+1,0)). The consuming proof establishes U(p)=5^p L after casting to the reals.

**Definition 1.6 (The right slope numerator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.V`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.V` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

V(0)=0 and V(n+1)=5V(n)+2(-1)^(n+2)(rx(n+1,0)+5^(n+1)ry(n+2,2)). The consuming proof establishes V(q)=5^q R after casting to the reals.

**Theorem 1.7 (Nonzero integer slope certificates at all positive lengths).**

$$\forall p \in Nat,\; \forall q \in Nat,\; \left((1 \le p) \land (1 \le q)\right) \Rightarrow \left(((U\left(p\right) \neq 0) \land (V\left(q\right) \neq 0)) \land (intCastZModFive\left(U\left(p\right) \cdot V\left(q\right)\right) = 2 \cdot (-1)^{q + 1} \cdot (3)^{q})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.certificate_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For positive p and q, both integer numerators are nonzero and their product has the displayed residue in ZMod 5. Induction on the vector recurrences gives lu(n+1)=3^(n+1)(1,0,1), lv(n+1)=2^n(3,1,2), and rx(n+1)=3^(n+1)(1,0,1) modulo 5. Substitution in the scalar recurrences yields U(p)=1 and V(q)=2(-1)^(q+1)3^q modulo 5. Since the latter residue is nonzero, neither integer numerator vanishes.

OpenBoundaryMPSInteriorTransversality consumes the recurrences in its coordinate and finite-sum inductions, then consumes certificate_nonzero to construct the invertible ordinary real derivative at the fixed native sector and boundaries. This is an integer certificate for that witness; full C9 remains open and the solved-open-problem count remains zero. It supplies no physical positive inverse, normalization, dynamics, time, energy or thermodynamic conclusion.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.U`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.V`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.certificate_nonzero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.lu`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.lv`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.rx`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate.ry`

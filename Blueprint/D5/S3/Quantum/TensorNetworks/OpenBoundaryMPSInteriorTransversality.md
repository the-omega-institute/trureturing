# An all-length actual real transversality witness

## Abstract

Every pair of positive exterior lengths has the same actual fixed-sector interior zero with positive definite target environments and an invertible ordinary real derivative.

**Definition 1.1 (The fixed sector).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.fixedSector`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.fixedSector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The native Sector is (lambda,mu,a)=(2,0,1), with original parameter z0=1. Thus B=diag(2,0) and G(1) has rows (1,1) and (1,-1).

**Definition 1.2 (The actual left boundary).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.leftBoundary`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.leftBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The original finite left row is l=(1,1).

**Definition 1.3 (The actual right boundary).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.rightBoundary`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.rightBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The original finite right column is r=(1,I).

**Theorem 1.4 (The integrated universal witness).**

$$\forall p \in Nat,\; \forall q \in Nat,\; \left((1 \le p) \land (1 \le q)\right) \Rightarrow \left((((((PosDef\left(leftTarget\left(fixedSector, 1, leftBoundary, p\right)\right)) \land (PosDef\left(rightTarget\left(fixedSector, 1, rightBoundary, q\right)\right))) \land (trialLeft\left(fixedSector, p, leftTarget\left(fixedSector, 1, leftBoundary, p\right), 1\right) = vecMulVec\left(star\left(leftBoundary\right), leftBoundary\right))) \land (trialRight\left(fixedSector, q, rightTarget\left(fixedSector, 1, rightBoundary, q\right), 1\right) = vecMulVec\left(rightBoundary, star\left(rightBoundary\right)\right))) \land (residual\left(fixedSector, p, q, leftTarget\left(fixedSector, 1, leftBoundary, p\right), rightTarget\left(fixedSector, 1, rightBoundary, q\right)\right)\left(1\right) = 0)) \land (\exists L \in Real,\; \exists C \in Real,\; \exists R \in Real,\; \exists e \in ContinuousLinearEquiv\left(Real, Complex, Complex\right),\; \exists u \in Int,\; \exists v \in Int,\; (((((((\forall w \in Complex,\; e\left(w\right) = L \cdot re\left(w\right) + I \cdot \left(C \cdot re\left(w\right) + R \cdot im\left(w\right)\right)) \land (HasFDerivAt\left(residual\left(fixedSector, p, q, leftTarget\left(fixedSector, 1, leftBoundary, p\right), rightTarget\left(fixedSector, 1, rightBoundary, q\right)\right), toContinuousLinearMap\left(e\right), 1\right))) \land (det\left(\begin{pmatrix}L&0\\C&R\end{pmatrix}\right) = L \cdot R)) \land (L \cdot R \neq 0)) \land ((5)^{p} \cdot L = ofInt\left(u\right))) \land ((5)^{q} \cdot R = ofInt\left(v\right))) \land ((5)^{p + q} \cdot L \cdot R = ofInt\left(u \cdot v\right))) \land (intCastZMod5\left(u \cdot v\right) = 2 \cdot (-1)^{q + 1} \cdot (3)^{q}))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.interior_q2_fixed_target_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every p,q at least one, both native actual targets are positive definite, both trial matrices recover the original rank-one boundary Grams at 1, and the native residual vanishes there. There exist real L,C,R, a continuous real linear equivalence e and integers u,v satisfying the displayed triangular derivative, determinant, scaling and nonzero mod-5 certificates. The only inputs are p,q and their positivity proofs. All targets are fixed outside the trial-parameter lambda.

Write W=G(1), E=transfer(core(1)), S=dualTransfer(core(1)). The first left target is [[8,4],[4,4]] and E(rr dagger)=[[10,2I],[-2I,2]], both with determinant 16. Kraus congruences give positive semidefiniteness, their nonzero determinants give positive definiteness, and the invertible W congruence plus a positive semidefinite summand preserves strict positivity under every subsequent iterate. G(1)^2=2I, so the actual right target is 4 times E iterated q on rr dagger.

The proof reuses the native inverseTransfer, inverseDualTransfer, trialLeft, trialRight and residual. At nonzero z the explicit native G inverse has rows (1/2,1/2) and (z inverse/2,-z inverse/2). Joint real derivatives on the pair (z,X) are established before composing with a varying inverse iterate. Conjugation is differentiated as a real linear map. The central inverse-square sandwich uses two product rules, retaining the derivative of each G inverse factor. The parameter-dependent iterates are proved by induction with fixed original targets, without the fixed-point iterate theorem.

In Hermitian coordinates h(s,d,u,v)=[[ (s+d)/2,(u+Iv)/2 ],[ (u-Iv)/2,(s-d)/2 ]], the determinant is (s squared-d squared-u squared-v squared)/4. Its differentials at the left and right rank-one Grams are delta s-delta u and delta s+delta v. The resulting real derivative is triangular: w maps to L Re(w)+I(C Re(w)+R Im(w)). The left angular entry is zero; C retains the full radial contribution of the right trial matrix.

OpenBoundaryMPSInteriorTransversalityCertificate supplies the division-free integer recurrences and their nonzero mod-5 product certificate. The recurrences used on the live proof path are a0=(1,0,-1), b0=(1,0,1), x0=(0,1,0), y0=(1,0,0). Set a'=(3a0-2a1,5a2,-2a0+3a1), b'=(3b0+2b1,b2,2b0+3b1), x'=(3x0-2x1,5x2,-2x0+3x1), y'=(3y0+2y2,2y0+3y2,y1). With t(n)=a(n)0 b(n)1+a(n)1 b(n)0, set U0=V0=0, U(n+1)=5Un+2t(n+1), and V(n+1)=5Vn+2(-1)^(n+2)(x(n+1)0+5^(n+1)y(n+2)2). Coordinate inverse-power induction and finite-sum induction prove U(p)=5^p L and V(q)=5^q R after integer-to-real casts.

Over ZMod 5, induction gives a(n+1)=3^(n+1)(1,0,1), b(n+1)=2^n(3,1,2), and x(n+1)=3^(n+1)(1,0,1). Therefore U(p)=1 and V(q)=2(-1)^(q+1)3^q for every positive p,q. Their nonzero residues imply nonzero integer and real values, hence L and R are nonzero. This certificate is consumed to build e with inverse w maps to Re(w)/L+I((Im(w)-C Re(w)/L)/R). No rational-to-finite-field homomorphism or bounded experiment supplies this inference.

This closes the explicit derivative premise at one actual all-length witness for the conditional root-to-actual unit. It does not prove the annular boundary signs, endpoint operator limits, polynomial clearance, finite-chart descent, genericity or full C9, and adds zero solved-open-problem credit. The Critch-Morton problem and Ma-Zhang C8 attribution remain as in the owning library note. No normalization, positive physical inverse, clock, dynamics, energy or thermodynamic conclusion is asserted.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.fixedSector`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.interior_q2_fixed_target_witness`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.leftBoundary`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality.rightBoundary`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization](OpenBoundaryMPSInteriorRootRealization.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversalityCertificate](OpenBoundaryMPSInteriorTransversalityCertificate.md)

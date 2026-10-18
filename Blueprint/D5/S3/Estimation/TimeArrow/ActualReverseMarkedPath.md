# Actual Transpose Kernel Marked Counts

## Abstract

Actual Transpose Kernel Marked Counts

**Definition 1.1 (reverseProbability).**

$$\forall M,q,s:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall e:\operatorname{Experiment}(), \forall o:\operatorname{Obs}(M, s, e), \operatorname{reverseProbability}(r, e, S, o)=\operatorname{transposeHistoryMass}(M, r, e, S, o)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For pairs, transposeHistoryMass is the product over s ordered pairs (x,y) of (2M)^(-1) transition(r,S,y,x). For a path it is (2M)^(-1) times the product of transition(r,S,X(t+1),X(t)). The support S is fixed for the entire history.

**Definition 1.2 (reversePGF).**

$$\forall M,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall zp,zm:\operatorname{Fin}(k)\to Complex, \forall e:\operatorname{Experiment}(), \operatorname{reversePGF}(r, S, m, zp, zm, s, e)=\operatorname{reverseCountMonomialSum}(r, S, m, zp, zm, s, e)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reversePGF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The right side sums reverseProbability times the product over marked rows j of zp(j)^count(e,o,m(j),1) zm(j)^count(e,o,m(j),-1), over all complete histories o of the chosen experiment.

**Definition 1.3 (reverseA).**

$$\forall M,k:Nat, \forall zp,zm:\operatorname{Fin}(k)\to Complex, \operatorname{reverseA}(M, zp, zm)=\frac{\operatorname{sumSymmetricTilt}(zp, zm)}{(2) \cdot (M)}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A is the sum of u(j)/(2M), where u(j)=(zp(j)+zm(j))/2-1. The reverse one-edge marked means are s/(4M).

**Definition 1.4 (reverseG).**

$$\forall M,k:Nat, \forall zp,zm:\operatorname{Fin}(k)\to Complex, \operatorname{reverseG}(M, zp, zm)=\frac{\operatorname{sumAntisymmetricTilt}(zp, zm)}{(2) \cdot (M)}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G is the sum of v(j)/(2M), where v(j)=(zp(j)-zm(j))/2.

**Definition 1.5 (reverseD).**

$$\forall M,q,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall zp,zm:\operatorname{Fin}(k)\to Complex, \operatorname{reverseD}(r, S, m, zp, zm)=\operatorname{symmetricProfileAverage}(M, r, S, m, zp, zm)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The symmetricProfileAverage is (2M)^(-1) times the sum of b(r,S,inl(m(j))) times the u(j) tilt. Marks can lie in signal or background rows.

**Definition 1.6 (reverseE).**

$$\forall M,q,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), \forall zp,zm:\operatorname{Fin}(k)\to Complex, \operatorname{reverseE}(r, S, m, zp, zm)=\operatorname{antisymmetricProfileAverage}(M, r, S, m, zp, zm)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The antisymmetricProfileAverage is (2M)^(-1) times the sum of b(r,S,inl(m(j))) times the v(j) tilt. Marks can lie in signal or background rows.

**Definition 1.7 (reverseMatrix).**

$$\forall A,G,D,E:Complex, \operatorname{reverseMatrix}(A, G, D, E)=\operatorname{matrix}(1+A, G, A+G, A, G, 1+A+G, D, E, D+E)$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nine matrix entries are in row order. At zero drift the lower two coordinates form a length-two nilpotent block.

**Definition 1.8 (reverseState).**

$$\forall A,G,D,E:Complex, \operatorname{reverseState}(A, G, D, E, 0)=\operatorname{vector}(1, 0, 0) \land \forall t:Nat, \operatorname{reverseState}(A, G, D, E, t+1)=\operatorname{rowTransfer}(\operatorname{reverseState}(A, G, D, E, t), \operatorname{matrix}(1+A, G, A+G, A, G, 1+A+G, D, E, D+E))$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state is a row-coordinate vector initialized at (1,0,0); rowTransfer multiplies it by the displayed matrix. Its coordinates are the coefficients of the endpoint density (x+chi(y) ycoef+b(y) z)/(2M).

**Theorem 1.9 (actual reverse marked path pgf).**

$$\forall M,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), {1\leq q \land q<M \land 0<r \land r<1 \land \operatorname{compensation}(M, q, r)<1 \land \operatorname{injective}(m)} \Rightarrow \forall zp,zm:\operatorname{Fin}(k)\to Complex, \operatorname{reversePGF}(r, S, m, zp, zm, s, path)=\operatorname{entry}({\operatorname{reverseMatrix}(\operatorname{reverseA}(M, zp, zm), \operatorname{reverseG}(M, zp, zm), \operatorname{reverseD}(r, S, m, zp, zm), \operatorname{reverseE}(r, S, m, zp, zm))}^{s}, 0, 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.actual_reverse_marked_path_pgf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural s, including s=0, the actual continuous transpose-kernel history PGF is the (0,0) entry of the s-th power of Cminus. The complex tilts are unrestricted, including zero. Cminus is reverseMatrix evaluated at A,G,D,E of the same support and marked rows.

**Theorem 1.10 (actual reverse marked pair pgf).**

$$\forall M,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), {1\leq q \land q<M \land 0<r \land r<1 \land \operatorname{compensation}(M, q, r)<1 \land \operatorname{injective}(m)} \Rightarrow \forall zp,zm:\operatorname{Fin}(k)\to Complex, \operatorname{reversePGF}(r, S, m, zp, zm, s, pair)={1+\operatorname{reverseA}(M, zp, zm)}^{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.actual_reverse_marked_pair_pgf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For independent stationary adjacent pairs, the actual transpose kernel gives the single-pair PGF 1+A exactly, before the independent product is taken.

**Theorem 1.11 (actual reverse marked poisson envelope).**

$$\forall M,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), {1\leq q \land q<M \land 0<r \land r<1 \land \operatorname{compensation}(M, q, r)<1 \land \operatorname{injective}(m)} \Rightarrow \forall zp,zm:\operatorname{Fin}(k)\to Complex, \forall e:\operatorname{Experiment}(), \forall eta:Real, {0\leq eta \land eta\leq \frac{1}{64} \land \operatorname{fourDriftBounds}(M, r, S, m, zp, zm, eta) \land (s) \cdot ({eta}^{2})\leq \frac{1}{256}} \Rightarrow \operatorname{norm}(\operatorname{reversePGF}(r, S, m, zp, zm, s, e)-\operatorname{exp}((s) \cdot (\operatorname{reverseA}(M, zp, zm))))\leq (((80) \cdot (s)) \cdot ({eta}^{2})) \cdot (\operatorname{exp}((s) \cdot (\operatorname{realPart}(\operatorname{reverseA}(M, zp, zm)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.actual_reverse_marked_poisson_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

fourDriftBounds bounds the norms of A,G,D,E by eta. The estimate holds for the actual pair and path experiments, retaining the signed real exponential scale. Dividing the three-coordinate recurrence by exp(A)^t gives a transient norm 4 norm(y)+norm(z). Its contraction and the quadratic defect of exp(A) yield the bound uniformly on every polydisk on which the drift hypotheses hold.

**Theorem 1.12 (actual reverse marked count relative).**

$$\forall Czero:Real, {1\leq Czero} \Rightarrow \exists A:Real, \exists Mzero:Nat, \exists etazero:Real, 0<A \land 1\leq Mzero \land 0<etazero \land \forall M,q,s,k:Nat, \forall r:Real, \forall S:\operatorname{Support}(M, q), \forall m:\operatorname{Fin}(k)\to \operatorname{Fin}(M), {1\leq q \land q<M \land 0<r \land r<1 \land \operatorname{compensation}(M, q, r)<1 \land \operatorname{injective}(m) \land Mzero\leq M \land 1\leq \frac{s}{(2) \cdot (M)} \land \frac{\frac{s}{(2) \cdot (M)}}{M}\leq etazero \land (k=1 \lor k=2)} \Rightarrow \forall np,nm:\operatorname{Fin}(k)\to Nat, {\operatorname{coordinateCountBound}(np, nm, Czero, \frac{s}{(2) \cdot (M)})} \Rightarrow \forall e:\operatorname{Experiment}(), \lvert \frac{\operatorname{reversePointMass}(r, S, m, s, e, np, nm)}{\operatorname{fairPoissonPointMass}(\frac{s}{(2) \cdot (M)}, np, nm)}-1 \rvert\leq \frac{(A) \cdot ({\frac{s}{(2) \cdot (M)}}^{k+1})}{M}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.actual_reverse_marked_count_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Constants depend only on Czero. The scale L=s/(2M) is real; no divisibility is imposed on s. For M>=Mzero, 1<=q<M, 0<r<1, compensation<1, L>=1, L/M<=etazero, k=1 or 2, every fixed support, distinct marks and both experiments, P is the mass of the simultaneous count tuple and Q is the product of 2k Poisson masses at the exact mean L/2. Every prescribed coordinate is at most Czero L. The estimate includes all zero counts and rare point masses.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.actual_reverse_marked_count_relative`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.actual_reverse_marked_pair_pgf`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.actual_reverse_marked_path_pgf`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.actual_reverse_marked_poisson_envelope`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseA`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseD`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseE`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseG`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseMatrix`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reversePGF`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseProbability`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualReverseMarkedPath.reverseState`
- Dependency: [D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope](ActualMarkedPathPgfPoissonEnvelope.md)
- Dependency: [D5/S3/Estimation/TimeArrow/MarkedPoissonCoefficient](MarkedPoissonCoefficient.md)

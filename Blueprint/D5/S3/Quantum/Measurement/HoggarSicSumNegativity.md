# The sharp Hoggar-SIC sum negativity

## Abstract

The sum negativity of the Hoggar-SIC Q-minus representation in dimension eight has global maximum 7/8 over all density matrices.

**Definition 1.1 (The three-qubit Pauli orbit).**

$$\forall j : \operatorname{Fin}\left(64\right), \forall b : \operatorname{Fin}\left(8\right), \operatorname{hoggarVector}\left(j, b\right) = \operatorname{toComplex}\left((\operatorname{ite}\left((\left(\operatorname{val}\left(j\right) \bmod 8 \bmod 2 \cdot \operatorname{xor}\left(\operatorname{val}\left(b\right), \operatorname{div}\left(\operatorname{val}\left(j\right), 8\right)\right) \bmod 2 + \operatorname{div}\left(\operatorname{val}\left(j\right) \bmod 8, 2\right) \bmod 2 \cdot \operatorname{div}\left(\operatorname{xor}\left(\operatorname{val}\left(b\right), \operatorname{div}\left(\operatorname{val}\left(j\right), 8\right)\right), 2\right) \bmod 2 + \operatorname{div}\left(\operatorname{val}\left(j\right) \bmod 8, 4\right) \bmod 2 \cdot \operatorname{div}\left(\operatorname{xor}\left(\operatorname{val}\left(b\right), \operatorname{div}\left(\operatorname{val}\left(j\right), 8\right)\right), 4\right) \bmod 2\right) \bmod 2 = 0), 1, -1\right)) \cdot (\operatorname{ite}\left((\operatorname{val}\left(b\right) = \operatorname{div}\left(\operatorname{val}\left(j\right), 8\right)), \operatorname{Zsqrtd.mk}\left(-1, 2\right), 1\right))\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.hoggarVector` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs (2017). *Negativity Bounds for Weyl–Heisenberg Quasiprobability Representations*. DOI: [10.1007/s10701-017-0098-z](https://doi.org/10.1007/s10701-017-0098-z). URL: <https://arxiv.org/abs/1703.08272v2>.

*Commentary.*

The Hoggar fiducial is v = (-1+2i, 1, 1, 1, 1, 1, 1, 1). Stacey, arXiv:1609.03075, equation (26), writes this vector and generates its orbit by three qubit Weyl-Heisenberg factors. Here j = 8x + z, with x and z the integers 0 through 7 representing their three low binary bits; b also runs from 0 through 7. The private Gaussian-integer expression orbitG(j,b) is bitSign(z, xor(b,x)) times (-1+2i if b=x, otherwise 1). The sign bitSign(z,a) is 1 if the sum of the three products of the corresponding binary bits is even, and -1 otherwise. In the displayed formula val maps Fin to Nat, div is Nat.div, mod is Nat remainder, xor is Nat.xor, and ite selects its branches. Zsqrtd.mk(-1,2) is the Gaussian integer with real part -1 and imaginary part 2. Thus the coefficient at b is (-1)^(z dot (b+x)) v_(b+x), exactly the action D_(x,z)|a> = (-1)^(z dot a)|a+x>; addition of bit vectors is xor. GaussianInt.toComplex is the canonical map from the Gaussian integers to C.

**Definition 1.2 (The normalized Hoggar projectors).**

$$\forall j : \operatorname{Fin}\left(64\right), \operatorname{hoggarProjector}\left(j\right) = \frac{1}{12} \cdot \operatorname{vecMulVec}\left(\operatorname{hoggarVector}\left(j\right), \operatorname{star}\left(\operatorname{hoggarVector}\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.hoggarProjector` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs (2017). *Negativity Bounds for Weyl–Heisenberg Quasiprobability Representations*. DOI: [10.1007/s10701-017-0098-z](https://doi.org/10.1007/s10701-017-0098-z). URL: <https://arxiv.org/abs/1703.08272v2>.

*Commentary.*

Each orbit vector has squared norm 12. The projector is the outer product of that vector with its conjugate, scaled by 1/12. vecMulVec(f,g) has entry (a,b) equal to f(a)g(b); star on a vector is pointwise complex conjugation. Scalars in this formula are complex. Distinct projectors have trace overlap 1/9.

**Definition 1.3 (The paper's Q-minus representation).**

$$\forall j : \operatorname{Fin}\left(64\right), \operatorname{hoggarQ}\left(j\right) = 3 \cdot \operatorname{hoggarProjector}\left(j\right) - \frac{1}{4} \cdot I$$

*Formalization.* `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.hoggarQ` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs (2017). *Negativity Bounds for Weyl–Heisenberg Quasiprobability Representations*. DOI: [10.1007/s10701-017-0098-z](https://doi.org/10.1007/s10701-017-0098-z). URL: <https://arxiv.org/abs/1703.08272v2>.

*Commentary.*

DeBrota and Fuchs, arXiv:1703.08272v2, equation (12), define Q_j^plus/minus = minus/plus sqrt(d+1) Pi_j + (1/d)(1 plus/minus sqrt(d+1)) I. For the minus choice and d=8 this is 3 Pi_j - I/4. Here the scalars are complex and I is the 8 by 8 identity matrix.

**Definition 1.4 (The real quasiprobability coordinates).**

$$\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(8\right), \operatorname{Fin}\left(8\right), \mathbb{C}\right), \forall j : \operatorname{Fin}\left(64\right), \operatorname{quasiprobability}\left(\rho, j\right) = \frac{\operatorname{Re}\left(\operatorname{Tr}\left(\rho \cdot \operatorname{hoggarQ}\left(j\right)\right)\right)}{8}$$

*Formalization.* `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.quasiprobability` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs (2017). *Negativity Bounds for Weyl–Heisenberg Quasiprobability Representations*. DOI: [10.1007/s10701-017-0098-z](https://doi.org/10.1007/s10701-017-0098-z). URL: <https://arxiv.org/abs/1703.08272v2>.

*Commentary.*

The paper's definition of a quasiprobability representation and equation (10) use q(j) = Tr(rho F_j) with F_j = Q_j/8. The definition explicitly takes the real part. For density matrices the trace is real because rho and Q_j are Hermitian; this is used in the proof of Parseval. The division by 8 is real division and introduces no extra dimension factor into negativity.

**Definition 1.5 (The negative part).**

$$\forall p : \mathbb{R}, \operatorname{negativePart}\left(p\right) = \frac{(\left|p\right| - p)}{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.negativePart` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs (2017). *Negativity Bounds for Weyl–Heisenberg Quasiprobability Representations*. DOI: [10.1007/s10701-017-0098-z](https://doi.org/10.1007/s10701-017-0098-z). URL: <https://arxiv.org/abs/1703.08272v2>.

*Commentary.*

Equation (8), page 7, defines the negative part as (|p(j)|-p(j))/2, "which replaces the positive elements of 𝔭 with zero and the negative elements with their absolute value." Here p is one real coordinate, so negativePart(p) is this scalar expression. The proof establishes its equality to max(0,-p).

**Definition 1.6 (Sum negativity of a density matrix).**

$$\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(8\right), \operatorname{Fin}\left(8\right), \mathbb{C}\right), \operatorname{sumNegativity}\left(\rho\right) = \sum_{j : \operatorname{Fin}\left(64\right)} \operatorname{negativePart}\left(\operatorname{quasiprobability}\left(\rho, j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.sumNegativity` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs (2017). *Negativity Bounds for Weyl–Heisenberg Quasiprobability Representations*. DOI: [10.1007/s10701-017-0098-z](https://doi.org/10.1007/s10701-017-0098-z). URL: <https://arxiv.org/abs/1703.08272v2>.

*Commentary.*

Page 7: "We will refer to the special cases $N^{1}$ and $N^{\infty}$, which we see are equivalent to the two natural candidates proposed above, as the sum negativity and the ceiling negativity respectively." Equations (9) and (10) define N^p as the L^p norm of the negative part. For p=1 the nonnegative negative-part coordinates sum to the displayed expression, over each of the 64 indices exactly once.

**Definition 1.7 (The conjectured global maximum).**

$$claim \Leftrightarrow (\operatorname{IsGreatest}\left(\{r : \mathbb{R} \mid \exists \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(8\right), \operatorname{Fin}\left(8\right), \mathbb{C}\right), (\operatorname{PosSemidef}\left(\rho\right)) \land ((\operatorname{Tr}\left(\rho\right) = 1) \land (\operatorname{sumNegativity}\left(\rho\right) = r))\}, \frac{7}{8}\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.claim` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs (2017). *Negativity Bounds for Weyl–Heisenberg Quasiprobability Representations*. DOI: [10.1007/s10701-017-0098-z](https://doi.org/10.1007/s10701-017-0098-z). URL: <https://arxiv.org/abs/1703.08272v2>.

*Commentary.*

DeBrota and Fuchs, arXiv:1703.08272v2, Section 6, page 17: "Although dimension $5$ was the last in which we were able to explicitly calculate the sum negativity for the SIC Q-reps by exhaustive combinatorial searching, we suspect that we have found the correct sum negativity for $\{Q_{j}^{-}\}$ constructed with the Hoggar SIC in dimension $8$. Rather than calculating the eigenvalues of every partial sum matrix (since this is infeasible for $2^{64}$, $8 \times 8$ matrices), we used a numerical local maximization procedure and around $10^{6}$ random pure state seeds. The overall maximum value we found, $7/8$, occurred frequently in our data and is significantly larger than all of the smaller local maxima. Of course, we could still be falling short of the global maximum value if it occurs at very hard to access positions. The states whose quasiprobability representations achieve the sum negativity of $7/8$ consist of $28$ copies of value $-1/32$ and $36$ copies of value $5/96$." Equation (11) takes the maximum over quantum state space. The encoding uses every complex 8 by 8 positive-semidefinite matrix rho with complex trace equal to 1, including mixed states. IsGreatest asserts both membership of 7/8 in the displayed set and the upper bound for every member; r is real.

**Theorem 1.8 (The maximum is seven eighths).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John B. DeBrota; Christopher A. Fuchs (2017). *Negativity Bounds for Weyl–Heisenberg Quasiprobability Representations*. DOI: [10.1007/s10701-017-0098-z](https://doi.org/10.1007/s10701-017-0098-z). URL: <https://arxiv.org/abs/1703.08272v2>.

*Commentary.*

The Gaussian-integer orbit certificate gives all 4096 squared overlaps: 144 on the diagonal and 16 off it. The 64 Q matrices are trace-orthogonal with trace(Q_j Q_k)=8 delta_(j,k), so they form a basis of the 64-dimensional complex matrix space. Recovering the expansion coefficients gives sum_j q(j)^2 = Tr(rho^2)/8, while sum_j q(j)=1 and q(j)>=-1/32. Nonnegative eigenvalues and trace one imply Tr(rho^2)<=1. The quadratic majorant (9/2)(t-5/96)^2 bounds max(0,-t) for t>=-1/32; summing gives N<=7/8. For w=conj(v), the state w w*/12 has 28 coordinates -1/32 and 36 coordinates 5/96, giving N=7/8. The conclusion includes every mixed density matrix, not just the pure attaining state.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.hoggarProjector`
- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.hoggarQ`
- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.hoggarVector`
- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.negativePart`
- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.quasiprobability`
- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.result`
- Truth anchor: `D5/S3/Quantum/Measurement/HoggarSicSumNegativity.sumNegativity`
- Dependency: [D5/S3/Observer/BornReduction](../../Observer/BornReduction.md)
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](../Dynamics/ProjectionProbabilityFlow.md)

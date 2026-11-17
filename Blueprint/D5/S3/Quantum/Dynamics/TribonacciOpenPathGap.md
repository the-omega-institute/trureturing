# Vanishing spectral distance for positive Tribonacci open chains

## Abstract

For every fixed real rho between zero and one, the minimum absolute eigenvalue of the actual positive Tribonacci even open prefixes tends to zero along all levels.

Use the literal A-starting word W for A to AB, B to AC, C to A. TribonacciPrefixRefutation supplies the original weights A=2, B=1, C=0, the recursive words U(0)=empty and U(n+1)=sigma^(4(n+1))(C) U(n), their exact occurrence at position zero, and their closed alternating charge. TribonacciAlignedWindows supplies L(j)=length(sigma^j(A)) and N(j)=2 floor(L(j)/2).

**Definition 1.1 (Alternating integer charge).**

$$\forall a \in \mathbb{N} \to \mathbb{Z},\; \forall k \in \mathbb{N},\; alternatingCharge\left(a, k\right) = alternatingSum\left(map\left(a, range\left(k\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.alternatingCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural-indexed integer sequence a, the charge of k entries is a(0)-a(1)+a(2)-... with exactly k terms. The empty charge is zero.

**Theorem 1.2 (The exact exponential Green entry).**

$$\forall r \in \mathbb{R},\; r \ne 0 \Rightarrow \left(\forall a \in \mathbb{N} \to \mathbb{Z},\; \forall q \in \mathbb{N},\; greenEntry\left((i: \mathbb{N}) \mapsto (r^{a\left(i\right)}), 0, q\right) = r^{-alternatingCharge\left(a, 2 \cdot q + 1\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.green_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real rho different from zero, every integer sequence a and every natural q, the original greenEntry at start zero and displacement q equals rho raised to the negative alternating charge of exactly 2q+1 entries. Integer powers allow arbitrary signs of a. The proof inducts on q using the original Green recursion and alternatingSum_append. It establishes the odd-over-even ratio, including the final even bond in the denominator; the reciprocal ratio has the opposite charge sign.

**Definition 1.3 (The actual finite open-chain matrix).**

$$\forall t \in \mathbb{N} \to \mathbb{R},\; \forall m \in \mathbb{N},\; \forall i \in Fin\left(2 \cdot m\right),\; \forall j \in Fin\left(2 \cdot m\right),\; openPath\left(t, m, i, j\right) = ite\left(val\left(i\right) + 1 = val\left(j\right), complex\left(t\left(val\left(i\right)\right)\right), ite\left(val\left(j\right) + 1 = val\left(i\right), complex\left(t\left(val\left(j\right)\right)\right), 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.openPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here t maps natural indices to real hoppings, m is natural, and i,j lie in Fin(2m). The real entries displayed in the formula are cast to complex numbers. There are 2m sites, zero diagonal and exactly 2m-1 bonds when m is positive. The last physical bond is t(2m-2); there is no boundary-to-boundary bond.

**Definition 1.4 (Positive Tribonacci hoppings).**

$$\forall r \in \mathbb{R},\; \forall i \in \mathbb{N},\; hopping\left(r, i\right) = r^{weight\left(W\left(i\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.hopping` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For 0<rho<1 every hopping is positive. The values are exactly rho squared on A, rho on B and one on C. Integer powers agree with these nonnegative natural powers.

**Definition 1.5 (The finite absolute eigenvalue set).**

$$\forall r \in \mathbb{R},\; \forall j \in \mathbb{N},\; absEigenvalues\left(r, j\right) = image\left((i: Fin\left(N\left(j\right)\right)) \mapsto (abs\left(eigenvalues\left(openPath\left(hopping\left(r\right), floorhalf\left(L\left(j\right)\right)\right), i\right)\right)), univ\left(\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.absEigenvalues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Hermitian matrix is openPath(hopping(rho), floor(L(j)/2)), acting on Fin(N(j)). Its real spectrum is the range of its real eigenvalue function. The finite image therefore equals the set of absolute values of that spectrum. For j>=1, iterate_growth gives L(j)>=j+1>=2, so this set is nonempty.

**Definition 1.6 (Minimum absolute eigenvalue).**

$$\forall r \in \mathbb{R},\; \forall j \in \mathbb{N},\; gap\left(r, j\right) = ite\left(1 \le j, min\left(absEigenvalues\left(r, j\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For j>=1 this is the minimum of the finite nonempty absolute eigenvalue set, hence precisely the single-particle distance from zero energy. The value at j=0 is defined as zero and has no effect on the limit.

**Theorem 1.7 (The limit along every actual even iterate prefix).**

$$\forall r \in \mathbb{R},\; \left(0 < r \land r < 1\right) \Rightarrow Tendsto\left(gap\left(r\right), atTop\left(\right), nhds\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.gap_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed rho in (0,1), gap(rho,j) tends to zero as j tends to infinity. The quantifier is over the entire deterministic sequence N(j), without selecting a subsequence or replacing the endpoints by periodic boundaries.

To connect the original inverse to positive hoppings, let D be diagonal with D(i,i)=(-1)^i. The positive lower bidiagonal block C is D lowerBlock(t,m) D. Its diagonal is t(2i), its subdiagonal is positive t(2i-1), and D squared is I. The original block_inverse and greenMatrix give C inverse as D greenMatrix(t,m) D. Reordering actual sites into evens and odds produces the block matrix [0,C;C transpose,0]. The explicit parity bijection sends inl(i) to 2i and inr(i) to 2i+1. For q<m the absolute value of the full inverse entry in row 2q+1, column zero is greenEntry(t,0,q). Every used bond has index at most 2q, so no artificial boundary bond enters.

All matrix norms in the spectral step are the L2 operator norm on complex Euclidean coordinate spaces. The original arbitrary-dimension entry_le_norm bounds this inverse entry by the full inverse norm. Pinned Mathlib's CStarAlgebra.norm_or_neg_norm_mem_spectrum, spectrum inverse-unit correspondence, Matrix.IsHermitian.inv and spectrum_real_eq_range_eigenvalues supply the spectral conversion. Thus the actual matrix has a real spectral value of absolute value at most the reciprocal Green entry. Positive diagonal entries make the bidiagonal block and the full even chain nonsingular.

Induction using four_odd gives length(U(n)) congruent to n modulo two. For odd n write length(U(n))=2q+1. The original prefixWord_actual and prefixCharge_closed give charge(U(n))=(n+1)(n+2). Consequently, whenever N(j)>=length(U(n))+1, the full-chain inverse entry has magnitude rho^(-(n+1)(n+2)), and the spectral distance is at most rho^((n+1)(n+2)). The inequality N(j)>=length(U(n))+1 is exactly what ensures q<L(j)/2.

$$
\forall r \in \mathbb{R},\; \left(0 < r \land r < 1\right) \Rightarrow \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists J \in \mathbb{N},\; 1 \le J \land \left(\forall j \in \mathbb{N},\; J \le j \Rightarrow \left(\exists x \in \mathbb{R},\; x \in spectrum\left(\mathbb{R}, openPath\left(hopping\left(r\right), floorhalf\left(L\left(j\right)\right)\right)\right) \land abs\left(x\right) < e\right)\right)\right)\right)
$$

Given epsilon>0, choose k with rho^k<epsilon and take the fixed odd level n=2k+1. Since (n+1)(n+2)>=k, its spectral bound is below epsilon. The original iterate_growth implies N(j)>=length(U(n))+1 for every sufficiently large j. This proves the displayed epsilon formulation along all j>=J. For a finite nonempty real spectrum, its minimum absolute value is below epsilon if and only if some real spectral value has absolute value below epsilon; nonnegativity then gives the stated limit.

The conclusion concerns the original open chain with positive hoppings: for any fixed 0<rho<1, the minimum absolute eigenvalue tends to zero along the full sequence of lengths N(j) rounded down to even integers. The proof uses the original actual prefixes and closed charge formula, retains all external sites, and connects the full inverse matrix through a parity coordinate permutation and alternating-sign conjugation. First fix an odd-level prefix satisfying the error requirement, then use growth of the actual iterate lengths to cover every sufficiently large j; thus no subsequence replaces the full sequence.

This is a consequence for the specified finite single-particle matrices. It supplies no uniform rate in N, matching lower rate, entropy or filling law, many-body excitation gap, infinite-volume spectral statement or physical realization. No literature novelty or external open-problem resolution is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.absEigenvalues`
- Truth anchor: `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.alternatingCharge`
- Truth anchor: `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.gap`
- Truth anchor: `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.gap_tendsto_zero`
- Truth anchor: `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.green_charge`
- Truth anchor: `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.hopping`
- Truth anchor: `D5/S3/Quantum/Dynamics/TribonacciOpenPathGap.openPath`
- Dependency: [D5/S1/Words/TribonacciPrefixRefutation](../../../S1/Words/TribonacciPrefixRefutation.md)
- Dependency: [D5/S3/Quantum/Dynamics/OddSquareGreenMass](OddSquareGreenMass.md)
- Dependency: [D5/S3/Quantum/Measurement/MaximalCoherenceAncillaNonmonotone](../Measurement/MaximalCoherenceAncillaNonmonotone.md)

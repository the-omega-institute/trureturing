# Two-wall universality of Jordan block spectra

## Abstract

Every two-wall cyclicity class has maximal hypereclectic power ranks, attained generically by the eclectic operator.

Work over the complex numbers. A filling contains a letters 1, b letters 2 and two walls 3, so L = a+b+2. Cyclicity indices k range over Fin(L), with val(k) in {0,...,L−1}. The space retains literal periodic words; its cyclicity class is the eigenspace of the one-site right shift. The three coupling coordinates xi(0), xi(1), xi(2) multiply F1, F2, F3, respectively. Thus ![0,0,1] is the hypereclectic point with coefficient one on F3.

**Definition 1.1 (Cyclicity eigenvalue).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \operatorname{eigenvalue}\left(a, b, k\right) = \operatorname{Complex.exp}\left(\frac{2 \cdot \operatorname{cast}\left(\pi, \mathbb{C}\right) \cdot \operatorname{Complex.I} \cdot \operatorname{cast}\left(\operatorname{val}\left(k\right), \mathbb{C}\right)}{\operatorname{cast}\left(a + b + 2, \mathbb{C}\right)}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.eigenvalue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Complex.I is the imaginary unit. Natural and real scalars in this expression are cast into the complex numbers.

**Definition 1.2 (The cyclicity class).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \operatorname{sector}\left(a, b, k\right) = \operatorname{eigenspace}\left(\operatorname{U}\left(\mathbb{C}, a, b\right), \operatorname{eigenvalue}\left(a, b, k\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is a complex submodule of Space(C,a,b), including the possibility of a zero-dimensional eigenspace.

**Definition 1.3 (Restricted bond operators).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{sectorF}\left(a, b, k, j\right) = \operatorname{restrict}\left(\operatorname{F}\left(\mathbb{C}, a, b, j\right), \operatorname{sector}\left(a, b, k\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sectorF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each bond sum commutes with U and therefore preserves the eigenspace. The index 2 selects F3, the literal 21 to 12 bond sum.

**Definition 1.4 (The restricted eclectic operator).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \forall xi \in (\operatorname{Fin}\left(3\right) \to \mathbb{C}),\; \operatorname{sectorT}\left(a, b, k, xi\right) = \operatorname{restrict}\left(\operatorname{T}\left(\mathbb{C}, a, b, xi\right), \operatorname{sector}\left(a, b, k\right)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sectorT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coupled operator also commutes with U. Its restriction is the same linear combination of the three restricted bond sums.

**Definition 1.5 (Universality for every filling with a,b at least two).**

$$(\operatorname{claim}) \Leftrightarrow (\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (2 \le a) \Rightarrow ((2 \le b) \Rightarrow ((\forall xi \in (\operatorname{Fin}\left(3\right) \to \mathbb{C}),\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \forall r \in \mathbb{N},\; \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorT}\left(a, b, k, xi\right))^{r}\right)\right) \le \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorF}\left(a, b, k, 2\right))^{r}\right)\right)) \land (\exists P \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(3\right), \mathbb{C}\right),\; (\operatorname{eval}\left(![0, 0, 1], P\right) = 1) \land (\forall xi \in (\operatorname{Fin}\left(3\right) \to \mathbb{C}),\; (\operatorname{eval}\left(xi, P\right) \ne 0) \Rightarrow (\forall k \in \operatorname{Fin}\left(a + b + 2\right),\; (\forall r \in \mathbb{N},\; \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorT}\left(a, b, k, xi\right))^{r}\right)\right) = \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorF}\left(a, b, k, 2\right))^{r}\right)\right)) \land ((\operatorname{IsNilpotent}\left(\operatorname{sectorT}\left(a, b, k, xi\right)\right)) \land ((\operatorname{IsNilpotent}\left(\operatorname{sectorF}\left(a, b, k, 2\right)\right)) \land ((\exists I \in Type,\; [\operatorname{Fintype}\left(I\right)] \exists s \in (I \to \operatorname{PNat}),\; \exists bt \in \operatorname{Basis}\left((\Sigma (i : I), \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right)), \mathbb{C}, \operatorname{sector}\left(a, b, k\right)\right),\; \forall m \in \mathbb{N},\; \forall i \in I,\; \forall t \in \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right),\; \left((\operatorname{sectorT}\left(a, b, k, xi\right))^{m}\right)\left(bt\left(\langle i, t\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(t\right) + m < \operatorname{val}\left(s\left(i\right)\right), bt\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(t\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right))\rangle\right), 0\right)) \land ((\exists J \in Type,\; [\operatorname{Fintype}\left(J\right)] \exists q \in (J \to \operatorname{PNat}),\; \exists bf \in \operatorname{Basis}\left((\Sigma (i : J), \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right)), \mathbb{C}, \operatorname{sector}\left(a, b, k\right)\right),\; \forall m \in \mathbb{N},\; \forall i \in J,\; \forall t \in \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right),\; \left((\operatorname{sectorF}\left(a, b, k, 2\right))^{m}\right)\left(bf\left(\langle i, t\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(t\right) + m < \operatorname{val}\left(q\left(i\right)\right), bf\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(t\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right))\rangle\right), 0\right)) \land (\forall I \in Type,\; \forall J \in Type,\; [\operatorname{Fintype}\left(I\right)] [\operatorname{Fintype}\left(J\right)] \forall s \in (I \to \operatorname{PNat}),\; \forall q \in (J \to \operatorname{PNat}),\; \forall bt \in \operatorname{Basis}\left((\Sigma (i : I), \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right)), \mathbb{C}, \operatorname{sector}\left(a, b, k\right)\right),\; \forall bf \in \operatorname{Basis}\left((\Sigma (i : J), \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right)), \mathbb{C}, \operatorname{sector}\left(a, b, k\right)\right),\; (\forall m \in \mathbb{N},\; \forall i \in I,\; \forall t \in \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right),\; \left((\operatorname{sectorT}\left(a, b, k, xi\right))^{m}\right)\left(bt\left(\langle i, t\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(t\right) + m < \operatorname{val}\left(s\left(i\right)\right), bt\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(t\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right))\rangle\right), 0\right)) \Rightarrow ((\forall m \in \mathbb{N},\; \forall i \in J,\; \forall t \in \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right),\; \left((\operatorname{sectorF}\left(a, b, k, 2\right))^{m}\right)\left(bf\left(\langle i, t\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(t\right) + m < \operatorname{val}\left(q\left(i\right)\right), bf\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(t\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right))\rangle\right), 0\right)) \Rightarrow (\forall j \in \mathbb{N},\; \operatorname{card}\left(\left\{i \mid i \in I \land \operatorname{val}\left(s\left(i\right)\right) = j\right\}\right) = \operatorname{card}\left(\left\{i \mid i \in J \land \operatorname{val}\left(q\left(i\right)\right) = j\right\}\right))))))))))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

§5, Eq. (5.1), arXiv:2112.04506v1: "However, we claim a universality hypothesis: The Jordan block spectrum of the eclectic model for generic couplings ξ1, ξ2, ξ3 is identical to that of the hypereclectic model, provided L, M, K satisfy L1 = L−M ≥ K, M1 = M−K ≥ K. (5.1)" Here K = 2, L = a+b+2 and M = b+2, so the two inequalities become a,b at least two. All couplings satisfy the power-rank upper bound. A single polynomial for the filling certifies equality of every power rank and every Jordan block multiplicity in every cyclicity class. Both restricted operators are nilpotent and admit positive-length chain bases; these bases are their Jordan block decompositions. The multiplicity equality holds for every pair of such bases. The basis index is the dependent sum of Fin(val(s(i))), and the conditional basis entry is used only when the new position is below s(i). Normalization at the hypereclectic point implies that this polynomial is nonzero.

Let K be any field, I a finite matrix index type with decidable equality, and S any type of variables. For a polynomial matrix A and a point x : S → K, write A(x) for the matrix obtained by evaluating every entry at x. No characteristic assumption or finiteness assumption on S is needed.

**Theorem 1.6 (One polynomial certifies all powers).**

$$\forall K \in \operatorname{Type},\; \forall I \in \operatorname{Type},\; \forall S \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall A \in \operatorname{Matrix}\left(I, I, \operatorname{MvPolynomial}\left(S, K\right)\right),\; \forall z \in (S \to K),\; \forall H \in \mathbb{N},\; (((\operatorname{map}\left(A, \operatorname{eval}\left(z\right)\right))^{H} = 0) \land (\forall x \in (S \to K),\; \forall r \in \mathbb{N},\; \operatorname{rank}\left((\operatorname{map}\left(A, \operatorname{eval}\left(x\right)\right))^{r}\right) \le \operatorname{rank}\left((\operatorname{map}\left(A, \operatorname{eval}\left(z\right)\right))^{r}\right))) \Rightarrow (\exists P \in \operatorname{MvPolynomial}\left(S, K\right),\; (\operatorname{eval}\left(z, P\right) = 1) \land (\forall x \in (S \to K),\; (\operatorname{eval}\left(x, P\right) \ne 0) \Rightarrow (\forall r \in \mathbb{N},\; \operatorname{rank}\left((\operatorname{map}\left(A, \operatorname{eval}\left(x\right)\right))^{r}\right) = \operatorname{rank}\left((\operatorname{map}\left(A, \operatorname{eval}\left(z\right)\right))^{r}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.exists_polynomial_power_rank_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the specialization at z is nilpotent with cutoff H and dominates the rank of every power at every point. There is a polynomial P whose value at z is one. At every point where P is nonzero, all power ranks agree with their values at z.

For each r below H, put d equal to the rank of A(z) raised to r. Choose constant left and right matrices taking this power to rank normal form, with an identity block of size d. Lift their entries to constant polynomials and take the determinant of the corresponding block of the transformed polynomial power. Evaluation commutes with multiplication, powers, and determinants, so this determinant evaluates to one at z. A nonzero value gives a full-rank block, and the submatrix and product rank inequalities force rank at least d.

The finite product of these determinants is P. Its value at z is one, and a nonzero product forces every factor to be nonzero. The assumed rank bound supplies the opposite inequality. For powers at least H, nilpotence makes the reference power zero, and the same bound forces rank zero at every point. Empty blocks have determinant one, so zero ranks and empty matrix index types are included.

**Theorem 1.7 (The two-wall universality theorem).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; (2 \le a) \Rightarrow ((2 \le b) \Rightarrow ((\forall xi \in (\operatorname{Fin}\left(3\right) \to \mathbb{C}),\; \forall k \in \operatorname{Fin}\left(a + b + 2\right),\; \forall r \in \mathbb{N},\; \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorT}\left(a, b, k, xi\right))^{r}\right)\right) \le \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorF}\left(a, b, k, 2\right))^{r}\right)\right)) \land (\exists P \in \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(3\right), \mathbb{C}\right),\; (\operatorname{eval}\left(![0, 0, 1], P\right) = 1) \land (\forall xi \in (\operatorname{Fin}\left(3\right) \to \mathbb{C}),\; (\operatorname{eval}\left(xi, P\right) \ne 0) \Rightarrow (\forall k \in \operatorname{Fin}\left(a + b + 2\right),\; (\forall r \in \mathbb{N},\; \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorT}\left(a, b, k, xi\right))^{r}\right)\right) = \operatorname{finrank}\left(\mathbb{C}, \operatorname{range}\left((\operatorname{sectorF}\left(a, b, k, 2\right))^{r}\right)\right)) \land ((\operatorname{IsNilpotent}\left(\operatorname{sectorT}\left(a, b, k, xi\right)\right)) \land ((\operatorname{IsNilpotent}\left(\operatorname{sectorF}\left(a, b, k, 2\right)\right)) \land ((\exists I \in Type,\; [\operatorname{Fintype}\left(I\right)] \exists s \in (I \to \operatorname{PNat}),\; \exists bt \in \operatorname{Basis}\left((\Sigma (i : I), \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right)), \mathbb{C}, \operatorname{sector}\left(a, b, k\right)\right),\; \forall m \in \mathbb{N},\; \forall i \in I,\; \forall t \in \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right),\; \left((\operatorname{sectorT}\left(a, b, k, xi\right))^{m}\right)\left(bt\left(\langle i, t\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(t\right) + m < \operatorname{val}\left(s\left(i\right)\right), bt\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(t\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right))\rangle\right), 0\right)) \land ((\exists J \in Type,\; [\operatorname{Fintype}\left(J\right)] \exists q \in (J \to \operatorname{PNat}),\; \exists bf \in \operatorname{Basis}\left((\Sigma (i : J), \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right)), \mathbb{C}, \operatorname{sector}\left(a, b, k\right)\right),\; \forall m \in \mathbb{N},\; \forall i \in J,\; \forall t \in \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right),\; \left((\operatorname{sectorF}\left(a, b, k, 2\right))^{m}\right)\left(bf\left(\langle i, t\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(t\right) + m < \operatorname{val}\left(q\left(i\right)\right), bf\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(t\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right))\rangle\right), 0\right)) \land (\forall I \in Type,\; \forall J \in Type,\; [\operatorname{Fintype}\left(I\right)] [\operatorname{Fintype}\left(J\right)] \forall s \in (I \to \operatorname{PNat}),\; \forall q \in (J \to \operatorname{PNat}),\; \forall bt \in \operatorname{Basis}\left((\Sigma (i : I), \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right)), \mathbb{C}, \operatorname{sector}\left(a, b, k\right)\right),\; \forall bf \in \operatorname{Basis}\left((\Sigma (i : J), \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right)), \mathbb{C}, \operatorname{sector}\left(a, b, k\right)\right),\; (\forall m \in \mathbb{N},\; \forall i \in I,\; \forall t \in \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right),\; \left((\operatorname{sectorT}\left(a, b, k, xi\right))^{m}\right)\left(bt\left(\langle i, t\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(t\right) + m < \operatorname{val}\left(s\left(i\right)\right), bt\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(t\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(s\left(i\right)\right)\right))\rangle\right), 0\right)) \Rightarrow ((\forall m \in \mathbb{N},\; \forall i \in J,\; \forall t \in \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right),\; \left((\operatorname{sectorF}\left(a, b, k, 2\right))^{m}\right)\left(bf\left(\langle i, t\rangle\right)\right) = \operatorname{ite}\left(\operatorname{val}\left(t\right) + m < \operatorname{val}\left(q\left(i\right)\right), bf\left(\langle i, (\operatorname{Fin.mk}\left(\operatorname{val}\left(t\right) + m\right) : \operatorname{Fin}\left(\operatorname{val}\left(q\left(i\right)\right)\right))\rangle\right), 0\right)) \Rightarrow (\forall j \in \mathbb{N},\; \operatorname{card}\left(\left\{i \mid i \in I \land \operatorname{val}\left(s\left(i\right)\right) = j\right\}\right) = \operatorname{card}\left(\left\{i \mid i \in J \land \operatorname{val}\left(q\left(i\right)\right) = j\right\}\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* C. Ahn; L. Corcoran; M. Staudacher (2022). *Combinatorial Solution of the Eclectic Spin Chain*. DOI: [10.1007/JHEP03(2022)028](https://doi.org/10.1007/JHEP03(2022)028). URL: <https://arxiv.org/abs/2112.04506v1>.

*Commentary.*

The literal two-wall sl2 action has lowering operator F3 and commutes with the shift. Its integral weight decomposition restricts to every cyclicity class. When a,b are at least two, each term of T lowers the weight filtration by at least two, so the eigenspace rank comparison gives the upper bound for every coupling and every power. Choose any complex basis of each class and express the three restricted bond sums as matrices. The matrix with entries X0 C(A1(i,j)) + X1 C(A2(i,j)) + X2 C(A3(i,j)) evaluates to the matrix of the restricted T. At ![0,0,1] it is the matrix of F3. Matrix rank equals the dimension of the operator range, and the basis map preserves powers. The weight bound gives F3^(ab+1) = 0, also on each restricted space. The polynomial power-rank certificate with this cutoff therefore supplies a polynomial for each class, normalized to one at the hypereclectic point. Their finite product over Fin(L) has the same normalization, and a nonzero product makes every factor nonzero, giving all equalities simultaneously. Empty bases and zero ranks are included. The weight filtration also makes T^(ab+1) zero, so both restricted operators are nilpotent. The nilpotent chain theorem supplies their Jordan block decompositions. For any such basis with lengths s(i), the rank of the m-th power is the sum of the truncated differences val(s(i))−m. For each positive j, the integer second difference rho(j-1) - 2 rho(j) + rho(j+1) counts chains of length j. Thus equality of all power ranks gives equality of all Jordan block multiplicities, independently of either choice of chain basis. At j=0 both counts vanish because every chain length is positive.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.eigenvalue`
- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.exists_polynomial_power_rank_certificate`
- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.result`
- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sector`
- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sectorF`
- Truth anchor: `D5/S3/Quantum/SpinChains/EclecticTwoWallUniversality.sectorT`
- Dependency: [D5/S1/Eigenstructure/NilpotentJordanChains](../../../S1/Eigenstructure/NilpotentJordanChains.md)
- Dependency: [D5/S3/Quantum/SpinChains/TwoWallWeights](TwoWallWeights.md)

# One symbolic hyperplane for a constant arrangement

## Abstract

One symbolic hyperplane for a constant arrangement

Let F be a characteristic-zero field, A a finite coordinate type, I any index type, and K=Frac(F[T(a): a in A]). The polynomial variables T(a) are independently indeterminate; they are mapped into their fraction field. Coord(A,F) denotes F^A. For v in F^A let c(v)(a) be the scalar inclusion of v(a) in K, and let Ext(V)=span_K c(V), with ExtFamily(V)(i)=Ext(V(i)). The symbol bottom denotes the zero subspace. The one prescribed functional N(F,A) sends w to the sum over a of T(a)w(a). GP is exactly InGeneralPosition from ActualWindowCommonKernel: every indexed member is not contained in ker(N(F,A)), and for all finite subfamilies A0,B0,C0 contained in s, (Tcut(A0)+S(B0)) intersect (Tcut(A0)+S(C0)) being contained in ker(N(F,A)) implies that this intersection equals Tcut(A0). Here S is the span of the uncut members and Tcut is the span of their individual cuts. Empty subfamilies, overlaps and equal subspaces at different indices are permitted.

**Theorem 1.1 (The independent normal satisfies both general-position clauses).**

$$\forall F \in Type*,\; \forall A \in Type*,\; \forall I \in Type*,\; [Field\left(F\right)], [Fintype\left(A\right)], [CharZero\left(F\right)], \forall V \in I \to Submodule\left(F, Coord\left(A, F\right)\right),\; \forall s \in Finset\left(I\right),\; \left(\forall i \in I,\; i \in s \Rightarrow V\left(i\right) \ne bottom\right) \Rightarrow GP\left(ExtFamily\left(V\right), N\left(F, A\right), s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.symbolic_general_position` (`✓ std3`). ∎

*Citation.* Orit E. Raz; Avi Wigderson (2019). *Subspace arrangements, graph rigidity and derandomization through submodular optimization*. URL: <https://arxiv.org/abs/1901.09423v1>.

*Commentary.*

Pinned Mathlib supplies polynomial derivations with prescribed values on the variables and the base-change isomorphism for the module of differentials under localization. Together they give, for every rational direction y, an F-derivation d_y of K with d_y(T(a))=y(a). It acts coordinatewise on vectors and obeys the product rule. Constant vectors have derivative zero, so every extended uncut subspace is stable under differentiation. Differentiating N(c(v))=0 in each coordinate direction shows v=0, which gives memberwise nonvanishing.

For the intersection clause put T=Tcut(A0) and J=(T+S(B0)) intersect (T+S(C0)), and assume J is contained in ker(N). Let psi be any K-linear functional annihilating T. Choose y(a)=psi(e(a)). The product rule gives d_y(N(v))=N(d_y(v))+psi(v). For v in a constituent cut of T, psi(v)=0 and N(v)=0; therefore N(d_y(v))=0. Its uncut subspace is stable as well, so every constituent cut, T, both sums and J are stable. For w in J, both N(w) and N(d_y(w)) vanish, hence psi(w)=0. The double-annihilator theorem gives w in T. The reverse inclusion is a lattice inclusion. This proves the full intersection clause, without a disjointness or nonemptiness restriction on A0,B0,C0.

This is the symbolic genericity input used in R5 (31.6)-(31.7), corresponding to Raz and Wigderson, Theorem 7.1 and its fraction-field Claim 7.2. The displayed conclusion is literature-attested; the directional-derivation proof is a repository derivation. No novelty or finite-field probability bound is claimed. Allowing the subspaces to depend on T would invalidate the constant-subspace stability step.

For the application let B be a finite block type, J(i) a finite coordinate type for each block, and C the dependent sum of the J(i). Set K=Frac(F[T(c): c in C]). A base array b(i,sigma,j) is F-valued, and Lift(b)(i,sigma,j) is its scalar inclusion into K. BlockRows places the indicated row in its own block and zero elsewhere. Normal(T) is the coefficientNormal functional with the prescribed independent tuple T in every row. CR(b,k,s) is the K-dimension of commonRowSpan(BlockRows(Lift(b)),Normal(T),k,s), always with this prescribed normal. The distinguished base row b(k,sigma) is required to be nonzero for every sigma in s. Cost(b,P) is the sum over blocks A0 of P of [(sum over i of dim_K blockSpan(Lift(b),A0,i))-1], with natural-number subtraction inside each summand. Finpartition(s) partitions s into nonempty disjoint blocks and admits the empty partition when s is empty.

**Theorem 1.2 (The common-row partition formula with genericity discharged).**

$$\forall F \in Type*,\; \forall I \in Type*,\; \forall B \in Type*,\; \forall J \in B \to Type*,\; [Field\left(F\right)], [CharZero\left(F\right)], [Fintype\left(B\right)], [\forall i \in B,\; Fintype\left(J\left(i\right)\right)], \forall b \in \left(\forall i \in B,\; I \to J\left(i\right) \to F\right),\; \forall k \in B,\; \forall s \in Finset\left(I\right),\; \left(\forall sigma \in I,\; sigma \in s \Rightarrow b\left(k, sigma\right) \ne 0\right) \Rightarrow \left(\exists P \in Finpartition\left(s\right),\; CR\left(b, k, s\right) = Cost\left(b, P\right) \land \left(\forall Q \in Finpartition\left(s\right),\; CR\left(b, k, s\right) \le Cost\left(b, Q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.symbolic_block_common_rows_partition_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Orit E. Raz; Avi Wigderson (2019). *Subspace arrangements, graph rigidity and derandomization through submodular optimization*. URL: <https://arxiv.org/abs/1901.09423v1>.

*Commentary.*

Flatten the dependent coordinate blocks and take V(sigma) to be the F-span of their block-supported base rows. The nonzero distinguished row makes V(sigma) nonzero. Scalar extension commutes with these spans. The preceding general-position theorem applies to this constant arrangement, and the linear equivalence between flat and block coordinates transports its complete predicate. The distinguished symbolic coefficient is nonzero by the same coordinate-derivation argument. Feeding these two proved facts into ActualWindowCommonKernel.block_common_rows_partition_rank gives an attaining partition and every-partition upper bound. This is a live use of exact symbolic general position in the common-constraint application, with no GP antecedent in the displayed statement.

For the actual embedding application of R5, take F here to be the normal-closure field K_0 of the excerpt and b(i,sigma,j)=sigma(x(i,j)), before adjoining the common parameter tuple. This substitution produces the actual rows of (31.6) and the partition formula in terms of their scalar-extended block-span dimensions. The theorem does not identify those dimensions with degrees of intermediate fields, prove distinctness or completeness of the embedding family, establish independence of the h-1 original common rows, identify the rank of the original-F polynomial map, prove Galois descent or uniqueness of a fewest-block optimum, or return an original-F simultaneous attaining tuple. Those remain separate obligations of the source. The following theorem supplies the missing row-basis assertion. Four-slot Reg registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/29247; no declared_validated status is asserted.


**Theorem 1.3 (The displayed rows are the exact common-cut basis and attain the partition rank).**

For every finite block type $B$, finite coordinate types $J(i)$, characteristic-zero field $F$, base array $b(i,\sigma,j)$, distinguished $k\in B$, and finite $s\subseteq I$, assume
$b(i,\sigma)\ne0$ for every $i\in B$ and $\sigma\in s$. Put
$K=\operatorname{Frac}(F[T(a):a\in\sum_iJ(i)])$ and use the same independent tuple $T$ in every row. Then there is a partition $P$ of $s$ such that, for each $\sigma\in s$, the family

$$
\left\{
U_{k,\sigma}\,\widetilde b_{i,\sigma}-U_{i,\sigma}\,\widetilde b_{k,\sigma}: i\in B,\ i\ne k
\right\}
$$

is linearly independent and spans exactly

$$
\left\langle\widetilde b_{i,\sigma}:i\in B\right\rangle_K
\cap\ker\!\left(\sum_aT(a)(-)\right).
$$
Moreover the total span of all displayed rows satisfies

$$
\operatorname{rank}=\min_{Q\in\operatorname{Finpartition}(s)}
\sum_{A\in Q}\left(\sum_i q_i(A)-1\right),
$$

with equality at $P$. The distinguished row is zero, so the basis contains exactly $|B|-1$ rows. No general-position antecedent, quotient basis, Galois descent, or original-field specialization is assumed.

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.symbolic_block_common_rows_basis_partition_rank` (`✓ std3`). ∎

*Commentary.*

The symbolic normal gives every $U_{i,\sigma}\ne0$ from the nonzero constant row and the independent coordinate variables. In a linear relation among the displayed rows, inspection of the $i$th original block isolates the coefficient of the $i$th row, proving independence. The existing common-row span identity removes the zero distinguished row and identifies the span with the one common kernel cut. The preceding no-GP partition theorem supplies the same attaining partition and the universal partition bound. For normalized embedding bases with first entry one, the nonzero-row premise is immediate. This theorem closes the exact basis clause of (31.6) while leaving the later intermediate-field, descent, and original-$F$ specialization steps outside its statement. Four-slot Reg registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/29247; no declared_validated status is asserted.

## References

- Truth anchor: `D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.symbolic_block_common_rows_basis_partition_rank`
- Truth anchor: `D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.symbolic_block_common_rows_partition_rank`
- Truth anchor: `D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.symbolic_general_position`
- Dependency: [D5/S3/Factorization/Galois/ActualWindowCommonKernel](ActualWindowCommonKernel.md)

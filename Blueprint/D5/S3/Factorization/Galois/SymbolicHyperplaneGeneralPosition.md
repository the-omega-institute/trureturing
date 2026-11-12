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

**Theorem 1.3 (The displayed common rows form the exact cut basis and attain partition rank).**

$$\forall F \in Type*,\; \forall I \in Type*,\; \forall B \in Type*,\; \forall J \in B \to Type*,\; [Field\left(F\right)], [CharZero\left(F\right)], [Fintype\left(B\right)], [\forall i \in B,\; Fintype\left(J\left(i\right)\right)], \forall b \in \left(\forall i \in B,\; I \to J\left(i\right) \to F\right),\; \forall k \in B,\; \forall s \in Finset\left(I\right),\; \left(\forall sigma \in I,\; sigma \in s \Rightarrow \left(\forall i \in B,\; b\left(i, sigma\right) \ne 0\right)\right) \Rightarrow \left(\exists P \in Finpartition\left(s\right),\; \left(\forall sigma \in I,\; sigma \in s \Rightarrow \left(\left(\forall i \in B,\; U\left(b, sigma, i\right) \ne 0\right) \land \left(LinearIndependent\left(K, Rows\left(b, k, sigma\right)\right) \land span\left(K, range\left(Rows\left(b, k, sigma\right)\right)\right) = Cut\left(b, sigma\right)\right)\right)\right) \land \left(CR\left(b, k, s\right) = BaseCost\left(b, P\right) \land \left(\forall Q \in Finpartition\left(s\right),\; CR\left(b, k, s\right) \le BaseCost\left(b, Q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.symbolic_block_common_rows_basis_partition_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Orit E. Raz; Avi Wigderson (2019). *Subspace arrangements, graph rigidity and derandomization through submodular optimization*. URL: <https://arxiv.org/abs/1901.09423v1>.

*Commentary.*

Assume every base row b(i,sigma) is nonzero on the finite family. Put U(b,sigma,i)=Normal(T)(BlockRows(Lift(b),sigma,i)), and let Rows(b,k,sigma) be the family U(b,sigma,k) BlockRows(Lift(b),sigma,i)-U(b,sigma,i) BlockRows(Lift(b),sigma,k), indexed by the actual subtype of blocks i different from k. Cut(b,sigma) is span_K of all block rows for sigma intersected with ker(Normal(T)). The theorem returns every U(b,sigma,i) nonzero. The same independent tuple T is used in every block and every embedding. Inspecting block i in a zero linear combination of Rows isolates its coefficient; U(b,sigma,k) and a selected coordinate of b(i,sigma) are nonzero, giving linear independence. The original span_common_rows_eq_cut is reused for spanning; omitting its zero distinguished row preserves that span. Thus these exact h-1 displayed rows form a basis of Cut(b,sigma).

BaseCost(b,P) denotes the sum over nonempty parts A0 of P of [(sum over i of dim_F blockSpan(b,A0,i))-1]. Scalar inclusion preserves each finite row-span dimension: a base-field basis remains independent by Mathlib's linearIndependent_algebraMap_comp_iff, and its lifted span equals the lifted original row span. Consequently these are the original q_i(A0) of (31.5), before adjoining T. The same theorem combines the explicit basis with one attaining partition and every-partition upper bound for the total common-row span, which includes only an extra zero row for each sigma. Its GP input is proved internally by the preceding symbolic theorem.

For the exact embedding application take this theorem's F to be the normal-closure field K_0, I to be the full type Hom_{F_0}(D,K_0), s to be its universe, J(i)=Fin(n_i+1), so the source dimension m_i=n_i+1, and b=ActualWindowCommonKernel.embeddingRows(id,X,x), where x is the actual F_0-basis of each normalized window X_i and x(i,0)=1. Applying an embedding to that first entry gives b(i,sigma,0)=1, discharging every row-nonvanishing premise. The distinguished block is the source's first block; the coordinate family is z(i,j), and K is K_0(z). A singleton block has an empty displayed basis and zero cut; an empty s has the empty partition. Empty coordinate blocks with an active nonzero row cannot satisfy the premise. No lower bound on h or distinctness of the subspaces is needed. The later intermediate-field identifications, Galois invariance/descent, original polynomial map and original-F simultaneous attainment remain separate. Four-slot Reg registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/29247; no declared_validated status is asserted.

## References

- Truth anchor: `D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.symbolic_block_common_rows_basis_partition_rank`
- Truth anchor: `D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.symbolic_block_common_rows_partition_rank`
- Truth anchor: `D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.symbolic_general_position`
- Dependency: [D5/S3/Factorization/Galois/ActualWindowCommonKernel](ActualWindowCommonKernel.md)

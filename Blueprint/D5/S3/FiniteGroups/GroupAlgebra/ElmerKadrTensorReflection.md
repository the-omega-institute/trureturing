# Finite-field tensor reflection from a single-factor recurrence

## Abstract

Single-factor recurrence makes V_(p-1) an involution in the finite-field relative category and yields two-factor tensor reflection.

Let K be any finite field, p any prime with char K=p, q=card K, and G=(K,+). The Lean type Multiplicative K is the additive group written multiplicatively. For every natural d put V_d=(K[z]_(degree<d))^*, acted on by rho_d(alpha)(lambda)(f)=lambda(f(z-alpha)); V_0 is zero. Set W=V_(p-1) and M=M_(p,q/p), the literal direct sum of V_p,V_(2p),...,V_q. Here q/p is natural-number division and p divides q.

An M-relatively projective P is an actual equivariant retract of X tensor M with X arbitrary. RelativeFactors M f allows factorization through any such P. Write A~_M B for the original RelativeStableIso M A B: two actual equivariant maps have composites differing from the respective identities by maps in RelativeFactors M. The modules P and X are unrestricted and need not be finite-dimensional. The tensor action is diagonal and the polynomial dual uses the inverse translation, including its negative sign.

The mathematical source is Jonathan Elmer and Kazal Kadr, Some formulae relating modular representations of elementary abelian p-groups, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1, formulas (11)--(12), Section 2.2 and Lemma 2.1(iii). The recurrence route follows their Proof of Corollary 1.3. The repository proves the finite-field specialization of the reflection proposed in Conjecture 3.7(b), with no claim of literature priority.

**Theorem 1.1 (Products preserve original relative projectivity).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.projective_prod`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.projective_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any field K, group G and representation M, if A and B are M-relatively projective, then their actual product A times B is M-relatively projective. The projective and tensor witnesses are unrestricted; neither a finite field nor finite-dimensional witnesses are required.

Given retractions through X tensor M and Y tensor M, the actual tensor-product distribution equivalence gives a retraction through (X times Y) tensor M. This existing helper is consumed by the reflection factor calculus and by the literal triple tensor criterion.

**Theorem 1.2 (One copy of W reflects a positive low digit).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.single_factor_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.single_factor_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite field K of prime characteristic p and all natural a,u with 1<=u, u<p and pa+u<q, one has W tensor V_(pa+u) ~_M V_(pa+p-u). The sole index bound is on pa+u. In particular a=0 and p=2 are allowed; this single-factor theorem assumes a positive low digit u.

Divisibility p|q turns pa+u<q into a+1<=q/p. For p>=3 the u=1 base uses the existing actual residue decomposition at (0,a,p-1,1), whose high binomial is choose(a,0)=1. It gives W tensor V_(pa+1) congruent to V_(pa+p-1) direct sum (V_(p-2) tensor V_(pa)). The remainder is relatively projective, including its zero case a=0, so the original relative maps give the base reflection.

For any positive m with (m:K) nonzero, the existing polynomial split gives V_2 tensor V_m congruent to V_(m+1) direct sum V_(m-1). If m,n are positive, both (m:K) and (n:K) are nonzero, and W tensor V_m ~_M V_n, applying this split on both sides gives (W tensor V_(m+1)) direct sum (W tensor V_(m-1)) ~_M V_(n-1) direct sum V_(n+1). Every rearrangement uses actual equivariant tensor equivalences. The relative-factor calculus closes under sums, composition and tensoring by explicitly retaining or constructing original retract witnesses.

At u=2 take m=pa+1 and n=pa+p-1. The two boundary terms are W tensor V_(pa) on the left and V_(p(a+1)) on the right. Both are actual M-relative-projectives: the first includes the zero module when a=0, and the second includes the final literal summand V_q when a+1=q/p. Removing these terms uses their actual relative-projective witnesses, rather than applying cancellation to a module of characteristic dimension zero.

For u>=3, strong induction identifies W tensor V_(pa+u-2) with V_d, where d=pa+p-u+2. Substitute this relation into the preceding split, then cancel this specific common polynomial summand V_d using polynomial_summand_cancellation. The proof establishes 0<d, d+1<=q and (d:K) nonzero before cancellation. Its residue p-u+2 lies strictly between 0 and p, while pa+p<=q gives the size bound. No split at residue zero and no arbitrary-module cancellation principle is used.

When p=2, the only positive low digit is u=1 and W=V_1. The actual tensor-unit equivalence proves the statement directly. The induction therefore preserves the characteristic-two case without invoking a split whose required scalar would vanish.

**Theorem 1.3 (W squares to the tensor unit modulo the original ideal).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.reflection_square`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.reflection_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite field K of prime characteristic p, W tensor W ~_M V_1, with no further parameters or hypotheses. Apply the completed single-factor theorem at a=0 and u=p-1; p<=q supplies p-1<q and the reflected index is 1. This consequence is derived after the single-factor induction and is consumed by tensor_reflection. It is not used as an assumption for that induction. For p=2 it is the tensor-unit case.

**Theorem 1.4 (Reflect both low digits with no sum or carry condition).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.tensor_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.tensor_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite field K, prime p with char K=p, and natural a,b,u,v satisfying u<p, v<p, pa+u<q and pb+v<q, one has V_(pa+p-u) tensor V_(pb+p-v) ~_M V_(pa+u) tensor V_(pb+v). These are exactly the four index inequalities. There is no hypothesis on (pa+u)+(pb+v), on u+v, on a binomial coefficient or on carries in the high indices. Natural-number subtraction in each reflected index is harmless because u,v<p.

If u and v are positive, let I=V_(pa+u) and J=V_(pb+v). The two single-factor reflections identify the reflected tensor with (W tensor I) tensor (W tensor J) in the original relative category. Actual associativity and commutativity equivalences shuffle this to (W tensor W) tensor (I tensor J). Apply reflection_square and then the actual V_1 tensor-unit equivalence. Tensoring relative factors is justified using the original X tensor M retracts, so this chain retains the original relative relation.

If u=0, the original tensor has the p-multiple factor V_(pa), while the reflected tensor has V_(p(a+1)). The block bound puts both within the specified relative summands, with V_0 handled as zero and V_q retained when the upper block is reached. Hence both tensors are relatively projective and the zero maps witness their relative stable relation. If v=0 the tensor flip gives the same argument. It also covers u=v=0 and a=0 or b=0 without a positivity premise. The zero-residue branches do not extend single_factor_reflection to a missing u=0 induction case.

The new mechanism is the single-factor induction with justified polynomial cancellation. Its square relation makes W an invertible tensor object of order dividing two in this relative category, and applying the same W to both factors explains why reflection cancels out. The final tensor assembly and the square specialization are consequences of that mechanism, not separate claims of independent novelty.

This establishes the proposed part 3.7(b) for the realization E_W=K, the additive group of the finite field itself, and even omits the paper's sum and low-residue-sum restrictions in this realization. The paper also treats representations over general coefficient fields and arbitrary additive embeddings. No reduction from those embeddings to E_W=K, or from its broader original W to this finite-field realization, is supplied here. This theorem does not settle that broader formulation or assert a replacement direct-sum decomposition from part 3.7(a).

The results are structural existence statements with utility none. The auxiliary DependentFamily registration audit remains unfinished in https://github.com/the-omega-institute/trureturing/issues/30512: the full typed clients, readouts, reconstruction, equivalence, variation, sensitivity and observational dependence are not validated. No declared_validated status or completion of the broader research program is asserted.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.projective_prod`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.reflection_square`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.single_factor_reflection`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrTensorReflection.tensor_reflection`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrPolynomialCancellation](ElmerKadrPolynomialCancellation.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrResidueCriterion](ElmerKadrResidueCriterion.md)

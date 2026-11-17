# Tensor reflection along an arbitrary additive embedding

## Abstract

The positive-low-digit recurrence along any faithful finite additive embedding yields the square relation and two-factor tensor reflection in the original relative category.

Let K : Type uK be any field of prime characteristic p, E : Type uE a finite nontrivial additive group in an independent universe, and alpha:E->+K an injective additive homomorphism. The Lean assumptions are Field K, Fact p.Prime, CharP K p, AddGroup E, Fintype E, Nontrivial E and Function.Injective alpha, with no Fintype K. Put q=card E and write Multiplicative E for the same group in multiplicative notation. Set V_d=(K[z]_(degree<d))^* with rho_d(e)(lambda)(f)=lambda(f(z-alpha(e))), including V_0=0. Tensor actions are diagonal. Here W abbreviates V_(p-1).

Faithfulness implies p e=0 and every nonzero e has order p, so p divides q. Let M=M_(p,q/p), the literal direct sum of V_p,V_(2p),...,V_q, restricted along alpha. An M-relative-projective P is an actual equivariant retract of X tensor M for an arbitrary representation X. Write A~_M B for the original RelativeStableIso: actual maps F:A->B and G:B->A have G F-id_A and F G-id_B factoring through such P. P and X remain unrestricted representations in K's universe. The proof constructs retracts, factorizations and equivalences within these original definitions.

The mathematical source is Jonathan Elmer and Kazal Kadr, Some formulae relating modular representations of elementary abelian p-groups, DOI 10.1007/s13366-026-00855-9, arXiv:2510.07939v1, formulas (11)--(12), Section 2.2 and Lemma 2.1(iii). The recurrence follows their Proof of Corollary 1.3. Its adaptation to arbitrary faithful additive embeddings uses finite-sample coefficient separation and the justified polynomial-summand cancellation. The square and tensor assembly below are consequences of this recurrence.

**Theorem 1.1 (One W reflects a positive low digit).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection.single_factor_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection.single_factor_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated field, group and embedding assumptions, for natural a,u satisfying 1<=u, u<p and pa+u<q, one has W tensor V_(pa+u) ~_M V_(pa+p-u). The index bound is only on pa+u; a=0 and p=2 are allowed. Divisibility p|q gives the full-block bound a+1<=q/p.

For p>=3, the u=1 base restricts the actual field-level residue decomposition at (0,a,p-1,1). Its high binomial is choose(a,0)=1, so no high-digit carry premise is needed. The literal Fin 1 direct sum identifies with its single polynomial factor, giving an actual equivalence W tensor V_(pa+1) congruent to V_(pa+p-1) direct sum (V_(p-2) tensor V_(pa)). The remainder has an original M-relative-projective retract; it includes the zero case a=0. The actual inclusion, projection and decomposition maps give the base relation.

For positive m with (m:K) nonzero, the actual field-level polynomial split gives V_2 tensor V_m congruent to V_(m+1) direct sum V_(m-1); its binomial scalar is m. Restricting the equivalence along alpha retains its maps and equivariance. If m,n>0, their casts in K are nonzero, and W tensor V_m ~_M V_n, tensoring by V_2 and applying the two splits yields (W tensor V_(m+1)) direct sum (W tensor V_(m-1)) ~_M V_(n-1) direct sum V_(n+1). Actual associativity, commutativity and distribution equivalences implement the rearrangement.

The relative calculus retains its witnesses throughout: sandwiching keeps the same P, addition uses P direct sum Q with retract source (X direct sum Y) tensor M, and tensoring by U uses U tensor P with source (U tensor X) tensor M. These constructions justify sums, composition and tensoring of the relative relations without restricting P or X. Restriction of a field-level retract keeps its original linear maps and X with the restricted action.

At u=2 use m=pa+1 and n=pa+p-1. The two boundary terms are W tensor V_(pa) and V_(p(a+1)). Both have actual original M-relative-projective retracts. Removing them by the direct-sum inclusions and projections retains V_0 when a=0 and the final V_q summand when a+1=q/p. This boundary step uses their projectivity.

For u>=3, strong induction at u-1 feeds the recurrence with m=pa+u-1 and n=pa+p-u+1. Induction at u-2 replaces W tensor V_(pa+u-2) by V_d, where d=pa+p-u+2, producing the same V_d summand on both sides. The proof establishes 0<d, d+1<=q and (d:K) nonzero: its residue p-u+2 lies strictly between 0 and p, and pa+p<=q supplies the size bound. EmbeddedPolynomialCancellation.polynomial_summand_cancellation then removes precisely this summand. Thus the recurrence never splits at residue zero or assumes general relative cancellation.

For p=2 the only positive low digit is u=1 and W=V_1. Restrict the actual equivalence V_1 congruent to the trivial one-dimensional representation and use the tensor unitor. This directly proves the characteristic-two branch.

**Theorem 1.2 (The completed recurrence makes W square to the tensor unit).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection.reflection_square`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection.reflection_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every K,E,alpha,p satisfying the stated assumptions, W tensor W ~_M V_1, with no additional index hypothesis. Since p divides the positive q, p<=q. Apply the completed single-factor theorem at a=0,u=p-1: its original index is p-1<q and its reflected index is 1. This square relation is derived after the positive-low-digit induction and is then used in tensor_reflection. For p=2 it agrees with the actual tensor-unit equivalence.

**Theorem 1.3 (Reflect both digits, including zero residues).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection.tensor_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection.tensor_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the stated field, group and embedding assumptions, for all natural a,b,u,v with u<p, v<p, pa+u<q and pb+v<q, one has V_(pa+p-u) tensor V_(pb+p-v) ~_M V_(pa+u) tensor V_(pb+v). These are exactly the four index inequalities in the theorem. There is no condition on either total index, on u+v, on a binomial coefficient or on carries. Natural-number subtraction gives the displayed reflected indices because u,v<p.

If u,v>0, put I=V_(pa+u), J=V_(pb+v). The two single-factor relations identify the reflected tensor with (W tensor I) tensor (W tensor J) in the original relative category. Actual equivariant associativity and commutativity shuffle this to (W tensor W) tensor (I tensor J). Apply the already derived reflection_square and then the actual V_1 tensor-unit equivalence. This explains the two-factor symmetry directly from the recurrence.

If u=0, the original tensor has factor V_(pa), while the reflected tensor has factor V_(p(a+1)). The full-block bound places both p-multiples among the original relative-projective cases: V_0 is zero, and V_q remains the literal final summand when a+1=q/p. Their tensors with the other factors therefore have actual M-relative-projective retracts. Zero maps between the tensors witness the relative relation, since each negative identity factors through its own relative-projective object. For v=0 use the tensor flip and the same construction. These branches include u=v=0 and zero original factors a=u=0 or b=v=0; they do not require a positive residue or extend the induction to u=0.

The square relation makes the class of W invertible under tensor product, of order dividing two relative to M; applying it to both factors yields the reflection. For p>2 this involution is nontrivial. Indeed, if W were relatively equivalent to V_1, the existing trace_relativeFactors_for_embedding theorem would make both inverse errors have trace zero. The cyclic trace identity for the two finite-dimensional endpoint spaces would force their dimensions to agree as scalars in K, hence p-1=1 in K. But p=0 in K then gives 2=0, contradicting p>2. Thus W tensor W is relatively equivalent to V_1 while W itself is not. For p=2, W=V_1 is already the tensor unit. This is an application of the existing trace and reflection results, rather than an additional library theorem.

This arbitrary-embedding polynomial-model statement is relevant to Elmer--Kadr Conjecture 3.7(b). Identifying the paper's actual original two-dimensional W with this signed polynomial realization and transporting its symmetric powers is separate from these theorems. No conclusion about the full conjecture or the direct-sum formula of part 3.7(a) is asserted here.

These are structural existence statements with utility none. The auxiliary DependentFamily audit remains unfinished: https://github.com/the-omega-institute/trureturing/issues/30512.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection.reflection_square`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection.single_factor_reflection`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTensorReflection.tensor_reflection`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrResidueCriterion](ElmerKadrResidueCriterion.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification](EmbeddedOriginalClassification.md)
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/EmbeddedPolynomialCancellation](EmbeddedPolynomialCancellation.md)

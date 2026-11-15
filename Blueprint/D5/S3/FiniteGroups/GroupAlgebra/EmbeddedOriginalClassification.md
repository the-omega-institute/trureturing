# Finite additive embeddings and the relative tensor criterion

## Abstract

Finite translation samples and a scaled prime-subgroup norm give the original relative tensor criterion over an arbitrary field of prime characteristic.

Elmer and Kadr, Some formulae relating modular representations of elementary abelian p-groups, arXiv:2510.07939v1, DOI 10.1007/s13366-026-00855-9, Conjecture 3.7(a), ask for a relative tensor formula. The objects below are their polynomial translation and contragredient models, formulas (11)--(12), with the relative category of Section 2.2 and Lemma 2.1(iii). The classification concerns those explicit models restricted along a faithful finite additive embedding.

Let K be any field, p a prime with char K=p, and E a finite nontrivial additive group. Fix an injective additive homomorphism alpha:E->K and put q=card E. The field K need not be finite. E and K may lie in independent universes. The notation Multiplicative E only changes the group notation for the additive action; it does not replace E by a multiplicative subgroup of K.

For each natural d, let V_d be the K-linear dual of the polynomials of degree less than d. Its action is rho_d(e)(lambda)(f)=lambda(f(z-alpha(e))). In particular V_0 is zero. For natural a,b,u,v with u<p, v<p and u+v<=p, set i=pa+u, j=pb+v and t=min(u,v), and assume i+j<=q. Let M be the literal direct sum over c in Fin(q/p) of V_(p(c+1)); let S be the literal direct sum over ell in Fin t of V_(i+j-(2ell+1)); and let T=V_i tensor V_j. Each action is restricted along alpha, with the direct-sum action on M and S and the diagonal tensor action on T.

An M-relatively projective representation P is an equivariant retract of X tensor M for some representation X. A map is in the relative ideal if it factors through such a P. RelativeStableIso M S T means that there are actual E-maps f:S->T and g:T->S with g f-id_S and f g-id_T in this ideal. P and X range over the original representation category, without finite-dimensional assumptions. Neither coefficient-intertwining laws for these witnesses nor chosen complementary summands are hypotheses.

**Theorem 1.1 (The high-binomial classification).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.original_relative_criterion_for_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.original_relative_criterion_for_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every K,p,E,alpha,a,b,u,v satisfying exactly the assumptions above, RelativeStableIso M S T holds if and only if u=0 or v=0 or choose(a+b,a), cast into K, is nonzero. Thus both positive low residues require precisely the nonvanishing of the high binomial; either zero low residue gives the relative relation independently of that scalar.

The statement includes a=0, b=0, p=2, u+v=p, equality i+j=q, and zero polynomial spaces. Its only finite carrier is E. The modules, their actions and the unrestricted existential relative factors are the ones specified above.

**Theorem 1.2 (The equivalent no-carry union).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.original_relative_criterion_no_carry`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.original_relative_criterion_no_carry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same assumptions and with the same M,S,T, RelativeStableIso M S T holds if and only if u=0 or v=0 or, for every k in Finset.Ico 1 (Nat.log p (a+b)+1), a mod p^k + b mod p^k < p^k. The half-open interval tests the integers from 1 through Nat.log p (a+b). This is exactly the absence of carries in the base-p addition of a and b.

In prime characteristic a natural scalar vanishes exactly when p divides it. Since choose(a+b,a) is a nonzero natural number, Kummer's factorization formula identifies its p-adic valuation with the number of carry positions in that interval. Valuation zero gives the displayed inequalities. When a+b<p the interval is empty, including a+b=0; when u=0 or v=0 the union requires no carry condition. These are two equivalent forms of one classification.

**Lemma 1.3 (Finite samples separate vector-valued coefficients).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.coefficients_eq_zero_of_samples`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.coefficients_eq_zero_of_samples` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be any finite type, beta:I->K injective, d<=card I, and B any K-vector space. If sum_(j in Fin d) beta(x)^j*v_j=0 for every x in I, then every v_j is zero. B can be infinite-dimensional and need not share I's universe. For each linear functional phi:B->K, the scalar polynomial sum_j phi(v_j) z^j has degree less than d and vanishes at all distinct beta(x), so it is zero. Its coefficients vanish, and separation by the algebraic dual gives v_j=0. For d=0 there are no coefficients to test.

Apply this result to the vector space of linear maps, with coefficients f C_j-D_j f. Intertwining the sampled sums then forces f C_j=D_j f separately. No finite-dimensional assumption on either source or target is needed for this recovery.

Write A_k for the unsigned Hasse coefficient operators on V_d and B_k for those on the polynomial tensor. Their expansions use rho(-alpha(e))=sum_k alpha(e)^k A_k, and similarly for B_k. Accordingly the intertwining equation is evaluated at -e, using alpha(-e)=-alpha(e), before sample separation. Whenever the expansion lengths are at most q, restricted_dual_intertwines_coefficients and the two restricted_tensor_intertwines_coefficients directions recover these laws from every actual E-map. They are consequences of equivariance, rather than extra assumptions on the space of maps.

**Lemma 1.4 (Actual maps satisfy the rectangular trace obstruction).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.embedded_composition_trace_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.embedded_composition_trace_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural n,m with n+m+2<=q and choose(n+m,n)=0 in K, every pair of actual restricted E-maps f:V_(n+m+1)->V_(n+1) tensor V_(m+1) and g in the reverse direction satisfies trace(g f)=0. K is arbitrary and alpha is the same injective finite additive embedding.

Let N=n+m and w=e_n tensor e_m in the dual monomial bases. The top coefficient has image K*w and sends e_0 tensor e_0 to w; a middle coefficient also sends e_n tensor e_0 to w. The recovered intertwining laws force g(w) into K*e_N and make its top coordinate divisible by choose(N,n), hence g(w)=0. They also put f(e_N) in K*w. On V_(N+1), coefficient cyclicity forces every diagonal entry of an equivariant endomorphism h to equal its top entry, so trace(h)=(N+1)*h(e_N)(z^N). The top entry of g f is zero, giving the obstruction for all such maps.

**Lemma 1.5 (The norm on every nonzero prime-field line).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.scaled_relative_norm`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.scaled_relative_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero c in K and every natural s, put M_s=the direct sum over r in Fin s of V_(p(r+1)). Translation by c times the prime-field image of z defines a homomorphism from the additive group ZMod p to K. There is an explicit endomorphism L_c of M_s such that sum_(z in ZMod p) rho(c*z) L_c rho(-c*z)=id_(M_s). This includes the empty sum of modules s=0 and makes no finiteness assumption on K.

On bounded primal polynomials S_c sends f(z) to f(c*z), with inverse S_(c^-1). On the contragredient the required coordinate map D_c is the inverse of S_c.dualMap: D_c rho(c*a)=rho(a) D_c. Taking the literal direct sum gives D on M_s. Conjugating the prime-line norm witness L by D gives L_c=D^-1 L D and transports the norm identity to the scaled line.

**Lemma 1.6 (The prime cycle kills relative-factor traces).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.trace_relativeFactors_for_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.trace_relativeFactors_for_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any additive group E with an injective alpha:E->K, any nonzero e in E, any natural s, and any representation U, an equivariant endomorphism h of U which factors through an M_s-relatively projective module has trace zero, where M_s is restricted along alpha. No finiteness of E is needed for this lemma. In the classification U is a finite-dimensional bounded polynomial dual, but the existential factor P and tensor witness X remain arbitrary.

Injectivity and char K=p give p*e=0. ZMod.lift therefore defines the actual prime-cycle homomorphism beta:ZMod p->E with beta(z)=z*e. Its composite with alpha is exactly the scaled prime line c=alpha(e), which is nonzero. The scaled norm identity and card(ZMod p)=p=0 in K feed the generic relative trace argument through the original P and X. Thus this step does not need coefficient operators on P or X, nor a finite-dimensional cyclic-trace argument through those witnesses.

Because E is nontrivial, choose a nonzero e. Faithfulness gives addOrderOf(e)=p, and the order divides card E, so p divides q. Consequently p*(q/p)=q, and M really has the last summand V_q. The cardinal q is always the size of E, not the cardinality of K. These arithmetic facts explain the upper end of the literal relative generator.

For u,v>0 and choose(a+b,a) nonzero, use the field-level residue decomposition T congruent to S direct sum R, with R=V_(i-t) tensor V_(j-t). At step h<t, Lucas's congruence factors the splitting scalar as choose(u+v-2-2h,u-1-h)*choose(a+b,a). The first factor is nonzero since its upper index is below p. This supplies all actual split maps and hence the whole finite direct sum S. The bound i+j<=q gives a,b<=q/p; one factor of R has dimension pa or pb and is either a literal summand of M or zero. It follows that R is relatively projective.

Restriction transports that decomposition and its relative projectivity along alpha. In restrict_relativeProjective the original X, inclusion and retraction are retained with their actions restricted; their composite remains the identity. The restricted equivalence T congruent to S direct sum R gives f:S->T and g:T->S with g f=id_S and f g-id_T equal to minus the transported remainder projection. That error factors through the same relatively projective remainder. No complement is supplied by the theorem's caller.

If u=0 or v=0 then t=0, and S is genuinely the empty direct sum indexed by Fin 0. The tensor T itself is relatively projective: a positive multiple pa or pb is among M's summands, while a zero dimension makes the tensor zero. The two zero maps between S and T satisfy the relative inverse relations; the error on T is -id_T. These branches are why the criterion is a union with the zero residues, rather than an unconditional no-carry test.

For the converse with u,v>0 and the high binomial zero, Lucas's congruence makes choose(i+j-2,i-1)=0. The first summand U=V_(i+j-1) is an actual retract of the full S. Sandwich g f-id_S by its inclusion and projection, retaining the original relative factor P. The rectangular obstruction gives trace(g_U f_U)=0 and the prime-cycle argument gives trace(g_U f_U-id_U)=0. But dim U has characteristic residue u+v-1 between 1 and p-1, so trace(id_U) is nonzero, a contradiction. This uses the retract inside S; it does not assume a relative stable isomorphism between U and T.

The finite-sample separation, coefficient recovery, scaled norm, restriction and arithmetic statements support the two equivalent classification forms. In particular the no-carry form uses the high-binomial criterion and Kummer's formula, while the positive decomposition is inherited from the polynomial splitting results. The classification is a statement about the explicitly defined polynomial translation model along alpha. A reduction from an arbitrary given faithful two-dimensional representation W, its symmetric powers and their duals to this model is not established here; the representation equivalences and their compatibility with the relative generator remain a separate mathematical obligation.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.coefficients_eq_zero_of_samples`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.embedded_composition_trace_zero`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.original_relative_criterion_for_embedding`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.original_relative_criterion_no_carry`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.scaled_relative_norm`
- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/EmbeddedOriginalClassification.trace_relativeFactors_for_embedding`
- Dependency: [D5/S3/FiniteGroups/GroupAlgebra/ElmerKadrResidueCriterion](ElmerKadrResidueCriterion.md)

# Regularity for actual dividing pairs

## Abstract

Regularity for actual dividing pairs

**Theorem 1.1 (The first dividing direction has a subpower partner bound).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroRegularity.actual_dividing_modular_zero_partner_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroRegularity.actual_dividing_modular_zero_partner_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real epsilon greater than zero, one positive constant bounds the cardinality of the original modularZeroPartners set by C times p^epsilon, uniformly in the prime p and the actual integer chart. The base pair (a,b) must be an ActualPair and not be aligned with q. The linear observation endpointL(q,(a,b)) evaluated at beta must be nonzero modulo p; alpha and kappa=alpha(alpha+q1+beta q2) must be nonzero. The anchor q and every point of E lie in the stated coordinate box, with 8 J1 J2 less than p. The dividing hypothesis is det(a,a+b-q)=0 modulo p.

The nonzero linear observation forces a nonzero quadratic observation. The dividing direction then gives a+b-q=c a. The linear observation excludes c=0. If c=1, q=b modulo p and the ActualPair identity forces the product of the nonzero linear observation and alpha+q1+beta q2 to vanish, contradicting kappa nonzero. If det(b,q) vanished modulo p, c different from one would force both anchor determinants to vanish modulo p; the existing small determinant lift would make the pair aligned over the integers. Thus det(b,q) is nonzero. The identities det(b,a-q)=-c det(a,b) and det(q,a-q)det(q,b)=(c-1)det(a,b)^2 modulo p give the two required nonzero integer determinants. The established regular dividing subpower theorem is then applied to the same original partner set.

This theorem covers the displayed first dividing direction. Nonvanishing of the linear observation is an explicit premise; its derivation from the paper's retained unit data is a separate bridge. No injectivity of actualValue modulo p or membership of zero or q in E is assumed.

**Theorem 1.2 (Both dividing directions share the same subpower constant).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiModularZeroRegularity.actual_dividing_branches_modular_zero_partner_subpower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiModularZeroRegularity.actual_dividing_branches_modular_zero_partner_subpower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the same actual-pair, nonalignment, nonvanishing and coordinate-box hypotheses, the conclusion holds when either det(a,d)=0 or det(d,b)=0 modulo p, where d=a+b-q. The second direction is the first after swapping a and b: the ActualPair product is symmetric, both base endpoint polynomials are unchanged, and consequently the original modularZeroPartners set itself is unchanged. Antisymmetry of the determinant gives the required dividing orientation. The same constant C from the single-direction theorem is used in both cases; no new regularity assumption or factor of two is introduced.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroRegularity.actual_dividing_branches_modular_zero_partner_subpower`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiModularZeroRegularity.actual_dividing_modular_zero_partner_subpower`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiModularZeroPartners](PascadiModularZeroPartners.md)

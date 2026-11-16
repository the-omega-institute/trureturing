# Countable null sets of collision parameters

## Abstract

Distinct prime LCM power thresholds collide at only countably many real parameters kappa>1.

**Remark 1.1 (The threshold function and its prime value sets).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lcmPowerF`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lcmPowerF` (`✓ std3`).

*Citation.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

Fan, Kobayashi and Molnar, Definition 4.2, define F(kappa,x,a) as log(((x^(a+1)-1)^kappa-(x^a-1)^kappa)/((x^(a+1)-x)^kappa-(x^a-x)^kappa))/(kappa*log(x)). The Lean function used here is the existing lcmPowerF. Their Definition 4.19 associates to a prime p the set E_p={F(kappa,p,j): j is a natural number at least one}.

**Theorem 1.2 (Two distinct primes).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCountable.collision_parameters_countable_null`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCountable.collision_parameters_countable_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For natural primes p and q with p distinct from q, the set of real kappa>1 for which there are natural i,j at least one satisfying F(kappa,p,i)=F(kappa,q,j) is countable and has Lebesgue measure zero.

For fixed positive indices, both functions are real analytic on (1,infinity). A zero power base contributes a locally constant zero function there. All other bases have analytic real powers, and the numerator and denominator differences are strictly positive.

Put r=(x^a-1)/(x^(a+1)-1), s=(x^a-x)/(x^(a+1)-x), and L=log((x^(a+1)-1)/(x^(a+1)-x))/log(x). For positive natural m, F(m,x,a)=L+(log(1-r^m)-log(1-s^m))/(m*log(x)), with 0<=s<r<1. The logarithmic correction divided by r^m tends to -1. If p<q, then r(q,j)<1/q<=1/(p+1)<=r(p,i). Identical functions would have equal limits L and equal corrections after division by their base logarithms. Scaling by r(p,i)^m would give both -1/log(p) and zero as the same limit, a contradiction. The analytic identity theorem makes each fixed-index equality set discrete in (1,infinity), hence countable. Take the countable union over indices.

**Theorem 1.3 (Simultaneous separation for almost every parameter).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCountable.all_collision_parameters_countable_null`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCountable.all_collision_parameters_countable_null` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

The set of real kappa>1 admitting any collision between two distinct natural primes at positive natural indices is countable and has Lebesgue measure zero. Consequently, for Lebesgue almost every real kappa, if kappa>1 then every two distinct primes have disjoint sets E_p and E_q. This follows by a countable union over the prime pairs. Together with the separate density theorem, this shows that the exceptional parameters can be dense while having measure zero.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCountable.all_collision_parameters_countable_null`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCountable.collision_parameters_countable_null`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lcmPowerF`
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm](LcmPowerLeadingTerm.md)

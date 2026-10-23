# Seeded Bernoulli stopping and a common endpoint budget

## Abstract

Seeded Bernoulli stopping and a common endpoint budget.

For an arbitrary measurable seed space Seed and a seed probability measure nu, P(p)=nu times the iid Bernoulli(p) stream law on Seed times (Nat -> Bool). The seed law is independent of the parameter. Write X_i=1_{bit_i=true}-p, L(p0,p,k)=product_{i<k}[p/p0 if bit_i=true, else (1-p)/(1-p0)], and A(m)=((2^(2m+1)*(2m)^2)^m)*2^(2m). For t in WithTop Nat define T_n(t)=min(t,n), regarded as a natural number, and C_a(t)=t^a when finite and infinity at top. Put w(a,m,j)=(2^(a-m))^j and H(a,m)=2^a/(2^a-1)+(1-2^(a-m))^(-1). Expectations without a superscript are real Bochner integrals; nonnegative extended expectations allow infinite values.

**Definition 1.1 (The seed and acquired prefix).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.seededFiltration`

*Formalization.* `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.seededFiltration` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every measurable Seed, the filtration at time n is the measurable-space comap of (seed, restriction of the bit stream to indices i<n). Thus the entire private seed is available initially and exactly the first n bits are observed at time n. This definition fixes the filtration used by all stopping-time statements in this document.

**Theorem 1.2 (The density of a stopped observation).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_stopped_output_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_stopped_output_identity` (`✓ std3`). ∎

*Citation.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every seed probability nu, p0 in (0,1), p in [0,1], natural-valued stopping time tau for the seeded filtration, and real f strongly measurable for the stopping-time sigma algebra, the integral of f under P(p) equals its integral under P(p0) tilted by ofReal(L(p0,p,tau)). No boundedness of tau or integrability assumption on f is added: the equality uses the totalized Bochner integral on both sides. This is the stopped likelihood change-of-measure identity.

**Lemma 1.3 (Every centered bit has magnitude at most one).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.centered_bit_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.centered_bit_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every type Seed, p in [0,1], natural i and omega in Seed times the Boolean stream, |1_{omega.bit(i)=true}-p|<=1. No measurable structure or probability law is required.

**Theorem 1.4 (Local parameter changes preserve a random moment).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_stopped_moment_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_stopped_moment_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every seed probability nu, p0 in (0,1), p in [0,1], seeded stopping time tau bounded everywhere by n, and natural m>0, put lambda=(p-p0)/(p0(1-p0)). If |lambda| sqrt(n)<=(2A(m)+1)^(-1), then E_{P(p)}[tau^m] equals the corresponding integral under P(p0) tilted by ofReal(L(p0,p,tau)), and E_{P(p)}[tau^m]<=2 E_{P(p0)}[tau^m]. Both conclusions concern the same parameter-independent stopping rule and seed distribution.

**Lemma 1.5 (Truncation agrees with the WithTop minimum).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_cast`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every function M from Seed times the Boolean stream to WithTop Nat, every natural n and every omega, the WithTop cast of T_n(M(omega)) is min(M(omega),n), including M(omega)=top.

**Lemma 1.6 (A deterministic truncation remains a stopping time).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_stopping`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_stopping` (`✓ std3`). ∎

*Citation.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every WithTop-natural seeded stopping time M and natural n, omega -> T_n(M(omega)), cast to WithTop Nat, is a stopping time for the same seeded filtration.

**Lemma 1.7 (The deterministic truncation bound).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_le`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every t in WithTop Nat and natural n, T_n(t)<=n.

**Lemma 1.8 (Every bounded integer moment is integrable).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncated_moment_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncated_moment_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every measurable space Omega, finite measure mu, measurable M:Omega -> WithTop Nat, and naturals n,m, omega -> (T_n(M(omega)))^m is Bochner integrable under mu. This includes n=0 and m=0.

**Lemma 1.9 (A truncated moment pays its own tail).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_tail_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every measurable space Omega, measure mu, measurable M:Omega -> WithTop Nat, and naturals n,m, ofReal(n^m) times mu{n<M} is at most the nonnegative extended integral of ofReal(T_n(M)^m). No finite-measure hypothesis is required.

**Lemma 1.10 (Finite dyadic moments share one endpoint cost).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.endpoint_budget_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.endpoint_budget_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every measurable space Omega, measure mu, measurable M:Omega -> WithTop Nat, real a>0, natural m with a<m, and natural K, sum_{j<K} ofReal(w(a,m,j)) E_mu^+[ofReal(T_{2^j}(M)^m)] <= ofReal(H(a,m)) E_mu^+[C_a(M)]. The right side uses the same M for every j, and may be infinite.

**Lemma 1.11 (A likelihood at a measurable time is measurable).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.stopped_like_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.stopped_like_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every measurable Seed, p0,p in [0,1], and measurable tau:Seed times the Boolean stream -> Nat, omega -> L(p0,p,tau(omega)) is measurable.

**Theorem 1.12 (All local laws are charged to the same endpoint).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_common_endpoint_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_common_endpoint_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every seed probability nu, p0 in (0,1), sequence p(j) in [0,1], seeded WithTop-natural stopping time M, real a>0 and natural m with a<m, assume |(p(j)-p0)/(p0(1-p0))| sqrt(2^j)<=(2A(m)+1)^(-1) for every j. Five conclusions hold simultaneously. First, for every j, E_{P(p(j))}[T_{2^j}(M)^m]<=2E_{P(p0)}[T_{2^j}(M)^m]. Second, ofReal((2^j)^m) P(p(j)){2^j<M}<=2 E_{P(p0)}^+[ofReal(T_{2^j}(M)^m)]. Third, the infinite sum of the endpoint truncated moments weighted by ofReal(w(a,m,j)) is at most ofReal(H(a,m)) E_{P(p0)}^+[C_a(M)]. Fourth, for every extended nonnegative K, if E_{P(p(j))}^+[C_a(M)]<=K for every j, then E_{P(p0)}^+[C_a(M)]<=K. Fifth, the infinite sum of ofReal(w(a,m,j)) ofReal((2^j)^m) P(p(j)){2^j<M} is at most 2 ofReal(H(a,m)) E_{P(p0)}^+[C_a(M)]. The endpoint transfer uses the convergence of the local parameter laws and finite truncations; it does not replace the common stopping rule by independently chosen rules.

**Theorem 1.13 (The centered stopped score retains the time moment).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_stopped_score_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_stopped_score_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every seed probability nu, p0 in (0,1), seeded natural-valued stopping time tau bounded everywhere by n, and natural m>0, E_{P(p0)}^+[ofReal(|sum_{i<tau} X_i|^(2m))] <= ofReal(2A(m) E_{P(p0)}[tau^m]). No local parameter window is required for this centered-score estimate.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_common_endpoint_budget`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_stopped_moment_bound`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_stopped_output_identity`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.bernoulli_stopped_score_moment`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.centered_bit_bound`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.endpoint_budget_finite`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.seededFiltration`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.stopped_like_measurable`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncated_moment_integrable`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_cast`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_le`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_stopping`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment.truncation_tail_bound`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption](StoppedLikelihoodAbsorption.md)

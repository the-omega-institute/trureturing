# Actual conditional Born blocks and count information

## Abstract

Actual conditional Born blocks, sufficient count and finite boundary information

**Theorem 1.1 (Exact alternating endpoint correction).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_power_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_power_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q>0, natural n and exterior bits l,r, P(q)^n(l,r)=pi(q,r)+(-q)^n(1[l=r]-pi(q,r)), where pi(q,0)=1/(1+q) and pi(q,1)=q/(1+q). The identity includes n=0 and follows by induction on the actual two-state transition matrix. For probabilities require q<1 as well. It retains the alternating correction instead of replacing a finite event by its limiting stationary mass.

**Theorem 1.2 (Forbidden paths have zero mass).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.illegal_mass_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.illegal_mass_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real q, every natural m, both exterior bits l,r, and every Boolean interior word w of length m, failure of Adm(m+2, l::w::r) forces pathMass(q,m,l,w,r)=0. The induction locates a forbidden 11 transition or passes the failure to the remaining padded suffix. No conditional probability is assigned to a forbidden event.

**Theorem 1.3 (The actual endpoint event).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.normalizer_eq_power`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.normalizer_eq_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real q and every natural m, the sum over all interior words equals MarkovBlockWeight.pathNormalizer and the (l,r) entry of P(q)^(m+1), with P(q)=[[1-q,q],[1,0]]. Illegal terms vanish. Splitting the first interior bit proves the matrix-product recurrence, so the length is exactly m+1 transitions.

**Theorem 1.4 (Positive conditioning events).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.normalizer_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.normalizer_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<q<1 and m>=1, the all-zero interior is admissible for every l,r and has positive path mass. Every path product is nonnegative, so the endpoint normalizer is strictly positive. For m=0 and l=r=1 the event instead has zero mass.

**Theorem 1.5 (The conditional probability law).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<q<1, m>=1 and arbitrary exterior bits, conditionalLaw=pathMass/pathNormalizer sums to one, is nonnegative on every word, and is strictly positive exactly on the padded legal support. Division is justified by the positive endpoint event.

**Theorem 1.6 (Differentiating finite normalization).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.tilted_law_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.tilted_law_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K(w) count interior ones, z=q/(1-q)^2, a_t(w)=1[legal] z^K exp(t K), Z_t=sum a_t, and mu_t=a_t/Z_t. For 0<q<1, m>=1 and every real t, differentiating this finite sum and quotient gives mu_t prime(w)=mu_t(w)(K(w)-E_t K), including zero-mass words.

**Theorem 1.7 (The score is the centered count).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.count_score`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.count_score` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On every legal word, mu_t is positive and the derivative of log(mu_t(w)) is K(w)-E_t K. The support is fixed as t varies; logarithmic derivatives are asserted only there.

**Theorem 1.8 (Conditional Fisher information).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.fisher_eq_count_variance`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.fisher_eq_count_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<q<1, m>=1, all exterior pairs and every real t, the classical Fisher sum over the finite word law equals countVariance, the expectation of (K-E_t K)^2. Illegal words have zero summands; logarithmic scores are identified only on positive support. The following count experiment is an application of this finite law and its centered score, rather than a separate retained reconstruction theorem. Let N_k be the number of padded legal words with count k, nu_t(k)=sum over K(w)=k of mu_t(w), and z=q/(1-q)^2. Then nu_t(k)=N_k z^k exp(t k)/Z_t for k=0,...,m. It is a probability law, and empty fibers have zero mass. On each occupied count fiber the kernel R(k,w)=1[legal(w) and K(w)=k]/N_k is normalized and independent of q and t. The identities nu_t(k) R(k,w)=1[K(w)=k]mu_t(w) and sum over k=0,...,m of nu_t(k)R(k,w)=mu_t(w) follow by finite-fiber counting and normalization. Thus recording only K and then sampling uniformly inside its legal fiber restores the same conditional word law. Differentiating the count likelihood gives score k-E_t K on every occupied fiber, so summing its squared score against nu_t gives the same Fisher information as the word observation. This is exact statistical sufficiency for this family; it does not assert recovery of the original sampled word, a quantum state, or a phase history.

**Theorem 1.9 (The activity coordinate comes from the actual Perron equation).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.global_doob_parameter`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.global_doob_parameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<q<1, every positive normalized stationary row pi of P(q), irreducibility and every real t, let lambda be the actual positive complex spectral radius of T_t=P(q) exp(t j). Its positive right-eigenvector equations give lambda squared-(1-q)lambda=q exp(t). Consequently q(t)=1-(1-q)/lambda lies in (0,1), the actual globalDoob kernel equals P(q(t)), and z(q(t))=exp(t)z(q). The parameter correspondence is derived from actual Perron data.

**Theorem 1.10 (The actual conditional family at every tilt).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_tilt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_tilt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the same q, pi, and actual Doob data, for m>=1 the endpoint-conditioned law at source amplitude q(t) equals mu_t word by word, at every real t and including all illegal words. Hence the count score and Fisher, together with the count-observation application described above, describe this same conditioned experiment. The count is taken after this actual endpoint conditioning, with both original exterior bits fixed.

**Theorem 1.11 (Count response is its variance).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.count_mean_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.count_mean_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<q<1, m>=1 and every real t, differentiating the count mean through the finite normalized law gives exactly countVariance. Normalization reduces the second centered moment to the second moment minus the squared mean.

**Theorem 1.12 (Partition response).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.log_partition_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.log_partition_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For this positive finite partition, the derivative of log Z_t is E_t K. Together with the mean derivative, its second derivative is the conditional count variance.

**Theorem 1.13 (Postselection of the actual sequential circuit).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.actual_conditional_experiment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.actual_conditional_experiment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<q<1, arbitrary fixed phase history, m>=1, exterior bits l,r and every real tilt t, one sequence of unitary source gates at q(t) has the following properties. The squared coefficient of the actual register sourcePath(m+1,l,w followed by r), summed over all interior w, equals P(q(t))^(m+1)(l,r), has the displayed stationary-plus-alternating closed form, and is strictly positive. Dividing each coefficient mass by this same event mass gives mu_t(w). Every illegal padded word has coefficient mass zero. The normalized observed law sums to one, is nonnegative and is positive exactly on padded legal words. The stochastic and irreducible properties used to construct the source stationary row are derived from q in (0,1).

**Theorem 1.14 (The exact finite boundary correction).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_fisher_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_fisher_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<q<1, m>=1, exterior bits and every real t, put L=m+1 and B_t=pathNormalizer(q(t),m,l,r). Then conditionalFisher(t)=(L+r-l) p double-prime(t)+(log B) double-prime(t), where p is the actual pressure log(lambda). The proof takes two derivatives of log B=log Z-(L+r-l)p+t r+log(q^r(1-q)^(L-l-r)). Thus the conditioned Fisher is not identified with L times the stationary variance rate. The alternating remainder below decays after two derivatives; the stationary endpoint curvature remains in the finite correction.

**Theorem 1.15 (Stationary and alternating parts of the endpoint log).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_log_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_log_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put x=q(t), L=m+1, k=m+2-l-r and pi_r(x)=x^r/(1+x). For every m>=1, all four exterior pairs and every real t, B_t=pi_r(x)(1-(-x)^k), so log B_t=log pi_r(x)+R_m(t), with R_m(t)=log(1-(-q(t))^k). The actual endpoint_power_formula is used to derive this factorization. The shift k records both endpoints and retains both parities.

**Theorem 1.16 (Explicit decay of the differentiated alternating remainder).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_remainder_second_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_remainder_second_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each real tilt put f=-q(t), a=f prime/f and b=(f double-prime f-(f prime)^2)/f^2. The theorem fixes the explicit nonnegative coefficient C=(a^2+abs(b))/(1-abs(f))+a^2/(1-abs(f))^2 and proves abs(R_m double-prime(t)) <= C(m+2)^2 q(t)^m for every m>=1 and every exterior pair. It derives the two derivatives by product, quotient and logarithm rules and bounds the denominators using 0<q(t)<1; no derivative estimate or regularity certificate is assumed. In particular this differentiated remainder tends to zero at every real tilt.

**Theorem 1.17 (Exact finite Fisher correction with stationary endpoint curvature).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_fisher_stationary_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_fisher_stationary_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m>=1 and all exterior bits, F_m(t)=(m+1+r-l)p double-prime(t)+(log pi_r(q(t))) double-prime(t)+R_m double-prime(t). This uses the actual conditional_fisher_boundary and the differentiated endpoint decomposition. The middle term is independent of m and generally does not vanish. Only the alternating remainder has exponential decay.

**Theorem 1.18 (The stationary boundary limit survives differentiation).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_boundary_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_boundary_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed original exterior bits and every real tilt, log B_m(t) tends to log pi_r(q(t)) as m tends to infinity through every positive interior length. Its second derivative tends to (log pi_r(q(t))) double-prime(t). Both limits are proved from the exact endpoint formula and the derived differentiated remainder bound, without exchanging an unproved derivative and limit.

**Theorem 1.19 (Conditional information rate equals actual pressure curvature).**

Lean statement: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_fisher_rate_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_fisher_rate_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real tilt and every fixed exterior pair, F_(n+1)(t)/(n+2) tends to p double-prime(t). This is every positive interior length m=n+1 divided by its exact transition length m+1. The finite conversion to normalization per interior site is F_m/m=((m+1)/m)(F_m/(m+1)), with (m+1)/m tending to one. The same theorem identifies p double-prime(t) with the actual Poisson varianceRate of the stationary globalDoob kernel at t, using the existing scalar pressure theorem. The legal count experiment, actual circuit, original endpoints and Perron-derived q(t) are those of conditional_tilt and actual_conditional_experiment; no endpoint is changed as t varies.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.actual_conditional_experiment`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_fisher_boundary`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_fisher_rate_tendsto`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_fisher_stationary_remainder`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_normalization`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.conditional_tilt`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.count_mean_deriv`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.count_score`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_boundary_limit`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_log_decomposition`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_power_formula`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.endpoint_remainder_second_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.fisher_eq_count_variance`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.global_doob_parameter`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.illegal_mass_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.log_partition_deriv`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.normalizer_eq_power`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.normalizer_pos`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/ConditionalBornFisher.tilted_law_deriv`
- Dependency: [D5/S3/Combinatorics/Graph/Pressure/MarkovAdditiveTrajectory](../Pressure/MarkovAdditiveTrajectory.md)

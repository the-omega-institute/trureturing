# CDSO fixed-surplus localization and bootstrap

## Abstract

Fixed-surplus actual-array localization and two-stage bootstrap for CDSO Lemma 13.5.

The source is CDSO incidence moments and capacity phases, Definitions 1.1 and 13.1–13.2 and Lemmas 13.4–13.5. One JointArray is the sole law: it assigns nonnegative mass to every nonempty subset of Fin (a+1+h), has total mass one, positive actual marginals and mean cardinality a. Its K, H and d are computed from that same mass function. A TailChoice contains any tied-allowed h-smallest-marginal set and its exact minimum relation.

**Definition 1.1 (Uniform statement of Lemma 13.5).**

Lean statement: `D5/S3/Combinatorics/CDSO/LocalizationBootstrap.Lemma135Statement`

*Formalization.* `D5/S3/Combinatorics/CDSO/LocalizationBootstrap.Lemma135Statement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For fixed h≥2 and M>0, along integer a≥4 tending to infinity, every actual JointArray family with d≤M a^(3/2) and every tied-allowed h-smallest TailChoice has delta→0. Eventually p,u=O_{h,M}(a^(−3/2)) and H_D=O_{h,M}(a^(3/2)), with constants independent of the array and the choice.

The target retains the exact lower chain d≥H_D+(2a^3−C_{h,M}a^2)p≥h^2/p+(2a^3−C_{h,M}a^2)p, with the same actual event and no added localization, support, certificate, minimizer, singleton, independence or graph premise. All four positive constants and the finite threshold precede the quantifiers over arrays and tied choices. The statement includes uniform epsilon thresholds and the resulting sequence limit and eventual estimates.

**Theorem 1.2 (Localization, both bootstraps and the exact lower chain).**

Lean statement: `D5/S3/Combinatorics/CDSO/LocalizationBootstrap.lemma135`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CDSO/LocalizationBootstrap.lemma135` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed integer h≥2 and real M>0, the theorem applies to every raw JointArray and every tied-allowed TailChoice on every sufficiently large integer a≥4. The family version allows the sublevel hypothesis to hold eventually. It has the same constants and follows from the uniform finite statements.

For localization, cut at an arbitrary positive epsilon. If delta≥epsilon, the cutoff contains the a+1 core labels and a tail label. Its marginal deficit is at least two, so its mean reciprocal-square excess is at least four. The actual variance is at most (M+3)a. The pointwise excess is at most 2(h+1)/epsilon², which bounds the covariance error by 4(h+1)sqrt(M+3) a sqrt(a)/epsilon². Thus delta<epsilon whenever a≥(M+4(h+1)sqrt(M+3)/epsilon²+2)².

The common-event Cauchy inequalities are H_D≥h²/p and E[K²;A]≤delta² H_D. For a≥4 and a≥2h, the producer correction satisfies 0≤A_a(u)≤64a². Once delta≤1/(100(M+64h+1)) and a≥100(64h+1), the first bootstrap yields d≥H_D+a³p. It gives p a sqrt(a)≤M, u a sqrt(a)≤hM and H_D≤M a sqrt(a). The second bootstrap gives E[K²;A]≤M²p and E[L;A]≤(M²+1)p. Returning to the exact producer yields the full chain with C=64h+7(M²+1).

The real-power expressions are transported exactly through a^(3/2)=a sqrt(a) and a^(−3/2)=1/(a sqrt(a)). No singleton, support, independence, graph, minimizer or separate-marginal premise is used. These are deductions about the stated incidence-array model; no physical realization or literature-priority conclusion is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/CDSO/LocalizationBootstrap.Lemma135Statement`
- Truth anchor: `D5/S3/Combinatorics/CDSO/LocalizationBootstrap.lemma135`
- Dependency: [D5/S3/Combinatorics/CDSO/ArrayCore](ArrayCore.md)

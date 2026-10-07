# Marked Native Path Generating Function

## Abstract

Compensated finite paths have a uniform complex Poisson generating-function envelope.

**Definition 1.1 (Symmetric tilt).**

$${u}_{j}=\frac{{{z}^{+}}_{j}+{{z}^{-}}_{j}}{2}-1$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.tiltU` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each marked positive departure state has two arbitrary complex tilt coordinates, one for each destination parity. The symmetric coordinate is their half-sum minus one.

**Definition 1.2 (Antisymmetric tilt).**

$${v}_{j}=\frac{{{z}^{+}}_{j}-{{z}^{-}}_{j}}{2}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.tiltV` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The antisymmetric coordinate is half the difference of the positive and negative destination tilts.

**Definition 1.3 (Total-mass drift).**

$$A=\frac{1}{2M} \sum_{j:\operatorname{Fin}(k)} ({u}_{j}+{b}_{j}{v}_{j})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.driftA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The drift A averages u_j + b_j v_j over the 2M states. Here b_j is the native compensated profile at the marked positive state: b is r on positive support states, -c on the positive complement, and zero on negative states; c = rq/(M-q). Marks may lie in the support or its complement.

**Definition 1.4 (Endpoint-parity drift).**

$$B=\frac{1}{2M} \sum_{j:\operatorname{Fin}(k)} ({v}_{j}+{b}_{j}{u}_{j})$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.driftB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The drift B averages v_j + b_j u_j over the same state space. The compensating profile has zero total mass and vanishes on negative states.

**Definition 1.5 (Actual count generating function).**

$$\operatorname{ActualPGF}(T, z)=\sum_{o:\operatorname{path}(T)} {w}_{T}(o) \prod_{j:\operatorname{Fin}(k)} {{{z}^{+}}_{j}}^{{{C}^{+}}_{j}(o)} {{{z}^{-}}_{j}}^{{{C}^{-}}_{j}(o)}$$

*Formalization.* `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.actualPGF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum ranges over all complete histories of T transitions, with the native uniform-start path mass. The positive and negative exponents count departures from each marked state followed by the corresponding destination parity. These counts share one history. A history is a function from Fin(T+1) to Fin(M) + Fin(M). Its mass w_T is (2M)^(-1) times the product of (1 + b(x) chi(y))/(2M) over its T edges, where chi is 1 on positive states and -1 on negative states. C_j^+ and C_j^- count edges whose departure is the positive state m(j) and whose destination chi is respectively 1 and -1. The symbol z denotes the pair (z^+, z^-). Natural powers include zero tilt coordinates and use the convention zero to the zeroth power equals one.

**Theorem 1.6 (Finite Poisson envelope).**

$$\forall M,q,T,k:Nat, r,eta:Real, S\subseteq\operatorname{Fin}(M), m:\operatorname{Fin}(k)\to\operatorname{Fin}(M), {z}^{+},{z}^{-}:\operatorname{Fin}(k)\to Complex, 1\leq q<M \land 0<r<1 \land c=\frac{rq}{M-q}<1 \land \lvert S \rvert=q \land (k=1\lor k=2) \land \operatorname{injective}(m) \land 0\leq eta\leq\frac{1}{4} \land \lvert A \rvert\leq eta \land \lvert B \rvert\leq eta \land T{eta}^{2}\leq\frac{1}{10} \Rightarrow \lvert \operatorname{ActualPGF}(T, z)-\operatorname{exp}(TA) \rvert\leq20T{eta}^{2}\operatorname{exp}(T\operatorname{Re}(A))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.actual_marked_path_pgf_poisson_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 1 <= q < M, 0 < r < 1, and c = rq/(M-q) < 1, where M-q is the natural difference. A support has exactly q positive states. There are one or two distinct positive marked states, with arbitrary complex tilts. If 0 <= eta <= 1/4, both drift norms are at most eta, and T eta squared is at most 1/10, the native generating function differs from exp(TA) by at most 20 T eta squared times exp(T Re A).

Finite product identities turn actual count powers into edge factors without dividing by a tilt. Appending the last state to a complete history gives the forward endpoint sum. Its tilted mass at y is (F_t + chi(y) G_t)/(2M), with F_0 = 1 and G_0 = 0. The physical endpoint recurrence is F_(t+1) = (1+A) F_t + A G_t and G_(t+1) = B F_t + B G_t. Summing endpoints gives F_T.

Normalize by h = 1+A, whose norm is at least 3/4. The parity feedback is a finite geometric sum with ratio B/h. Running maxima bound the normalized increments using theta = norm(AB)/(norm(h)(norm(h)-norm(B))) <= (8/3) eta squared. The total normalized error is at most 2 T theta.

The complex logarithm remainder is bounded by kappa = norm(A) squared/(2(1-norm(A))) <= (2/3) eta squared. Exponentiation then compares h to exp(A), and the two errors combine with coefficient 52/3 <= 20. The sole logarithm is applied to h. All divisions have positive uniform bounds, so T = 0, eta = 0, A = 0, B = 0, and zero tilt coordinates remain included.

This finite generating-function estimate does not supply relative point-mass estimates, coefficient extraction, growing-window uniformity, or entropy asymptotics.

## References

- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.actualPGF`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.actual_marked_path_pgf_poisson_envelope`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.driftA`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.driftB`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.tiltU`
- Truth anchor: `D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope.tiltV`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionBayes](../SequentialDecisionRisk/FiniteSupportSelectionBayes.md)

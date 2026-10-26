# Critical renewal stopped drift and risks

## Abstract

Finite stopped drift, termination and both exponential exit risks.

These results supply the stopped-process part of CriticalRenewal Theorem 5.1, equations (5.9)-(5.13). The input is a measurable score path with its actual block filtration and conditional moments under two probability laws. The conditional moments, source normalization, joint block law, table realization, actual-bit termination, payment and state count must be proved by their owning constructions before the original theorem can be closed. No source law, independence between a score and its own duration, or bit-table realization is asserted here.

**Definition 1.1 (First completed-block exit).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.exitTime`

*Formalization.* `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.exitTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every measurable carrier Omega, real process S indexed by natural numbers, and real threshold b, exitTime(S,b) is Mathlib hittingAfter(S,{x:b<=|x|},1). It takes values in WithTop Nat and equals infinity if no positive block index reaches the threshold. Index zero is excluded.

**Definition 1.2 (Finite truncation of the block clock).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.cappedTime`

*Formalization.* `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.cappedTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every Omega, S, b, natural n and sample omega, cappedTime(S,b,n,omega) is the real cast of untopA(min(n,exitTime(S,b,omega))). The minimum is always finite, including paths whose exit time is infinity, so this value is exactly the number of completed blocks through the bounded stopping index.

**Theorem 1.3 (Predictability, overshoot and finite drift).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.finite_stopped_drift`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.finite_stopped_drift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every probability measure mu on Omega, natural-time filtration F, strongly F-adapted real process S, and real b,d, assume b>0, S(0)=0 everywhere, |S(n+1)-S(n)|<=1 everywhere for every n, and E_mu[S(n+1)-S(n)|F(n)]=d almost surely for every n. With G=exitTime(S,b), the event {n<G} is F(n)-measurable for every n; equivalently {G>=n+1} is predictable before the next block. At every finite n and every sample, |S(min(n,G))|<=b+1. For every finite n, E_mu[S(min(n,G))]=d E_mu[min(n,G)]. Neither G finite nor E_mu[G] finite is assumed. The centered score is a martingale; its bounded stopped expectations give the identity.

**Theorem 1.4 (Finite drift proves termination before risk limits).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.integrable_exit`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.integrable_exit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under every hypothesis of finite_stopped_drift and additionally d>0, the nonnegative expectation of sup_n ofReal(min(n,G)) is at most ofReal((b+1)/d). The exit G is finite almost surely. Its real cast untopA(G) is integrable and has expectation at most (b+1)/d. Monotone convergence of the bounded clocks proves the nonnegative expectation bound first; finite expectation then excludes infinite-exit paths. Only afterwards is untopA(G) used as the real exit count, with arbitrary values on its null exceptional set.

**Theorem 1.5 (One threshold and both proof orientations).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.critical_renewal_stopping_risks`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.critical_renewal_stopping_risks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mu(false),mu(true) be any two probability laws on the same measurable carrier and S one strongly F-adapted score path. Assume S(0)=0 and all increments have absolute value at most one everywhere. Fix positive D0,V0,I, alpha and delta with alpha<1/2 and delta<=1/2, and a real Delta satisfying D0 I<=Delta. Under law i, require the conditional increment mean to equal sigma(i) Delta/2 and the conditional second moment to be at most V0 I, at every block. Here sigma(false)=-1 and sigma(true)=1 are proof signs.

Set lambda=min(1,D0/(2 exp(1) V0)), A=log(1/alpha)/lambda, H=ceil(A/delta) using the integer ceiling, b=H delta, and G=exitTime(S,b). These are the original constants; positivity and A<=b<=A+1/2 are derived. For every finite n and sample, |S(min(n,G))|<=b+1<=A+3/2. Under each law i, {n<G} is F(n)-measurable and E_i[sigma(i) S(min(n,G))]=(Delta/2) E_i[min(n,G)]. The same G is finite almost surely under each law, its real cast is integrable, and E_i G<=2(A+3/2)/Delta.

For each i, every finite stopped exponential exp(-lambda sigma(i) S(min(n,G))) has expectation at most one, and the limiting exp(-lambda sigma(i) S(G)) has expectation at most one. The wrong-exit event {sigma(i) S(G)<=-b} has probability at most exp(-lambda b)<=alpha. For i=false this is the upper exit S(G)>=b; for i=true it is the lower exit S(G)<=-b. Both statements use one score path and threshold; no sign is an input to the controller.

The one-step estimate uses exp(lambda u)<=1+lambda u+(exp(1)/2)lambda^2 u^2 for |u|<=1 and 0<=lambda<=1, derived from Mathlib's exponential remainder bound. Conditional first and second moments give the exponential supermartingale. The proof obtains finite G from the finite drift and monotone convergence before passing to the risk limit. The deterministic overshoot bound dominates the stopped exponentials for bounded convergence. Markov's integral inequality then bounds each wrong exit.

To consume this interface for the actual source, use I=s^(2r) J and delta=J/2^(rJ), prove the two conditional moments in the filtration containing the initial wait and completed joint gap/coin blocks, and identify S with the literal table's completed-block evidence. The actual emitted wrong-label events must be identified with these wrong exits. Actual paid-bit stopping and the exact payment identity require the same-run finite-gap realization. Those instantiations and the remaining full-theorem clauses are not conclusions of this module.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.cappedTime`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.critical_renewal_stopping_risks`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.exitTime`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.finite_stopped_drift`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/CriticalRenewalStoppedDrift.integrable_exit`

# Sample Complexity from Finite Testing-Error Floors

## Abstract

The finite n-sample testing floors culminate in a universal Bretagnolle--Huber lower bound on the divergence budget required to attain a prescribed error.

**Theorem 1.1 (Every accurate i.i.d. test requires a divergence budget).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p, q: \iota\to \mathbb{R},\\\forall n \in \mathbb{N},\\\forall A: \operatorname{Finset}(\operatorname{IidSpace}(\iota, n)),\\\forall \varepsilon \in \mathbb{R},\\((\sum _{i} p(i)=1) \land (\sum _{i} q(i)=1) \land \\(\forall i, 0< p(i)) \land (\forall i, 0< q(i)) \land \\(0< \varepsilon < 1) \land \\(\sum _{z\in A} \operatorname{iidPower}(p, n, z)+\sum _{z\in A^c} \operatorname{iidPower}(q, n, z)\le \varepsilon)) \Rightarrow \\\log (\frac{1}{2 \varepsilon-\varepsilon^{2}})\le n \cdot D_{\operatorname{KL}}(p \Vert q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SampleComplexity.sample_complexity_bretagnolle_huber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preceding waves pinned the single-trial testing floor at one minus total variation and then re-expressed that floor through relative entropy. Frozen additivity on independent powers subsequently made the divergence scale linearly with the sample count. This module closes that arc: it first states the resulting floor at each sample count and then inverts the informative floor.

The two n-sample floors are chained corollaries, not new inequalities. The declaration iid_testing_error_pinsker composes the frozen single-trial Pinsker floor with frozen n-fold KL additivity to give total error at least 1-sqrt(n D/2). The declaration iid_testing_error_bretagnolle_huber makes the same composition with the frozen Bretagnolle--Huber floor and gives total error at least 1-sqrt(1-exp(-n D)). The module consumes both frozen ingredients and re-derives neither; the change of parameter from D to n D is a composition, not a discovery.

The inversion is this wave's contribution, and it answers the question one ordinarily asks. Rather than fixing n and asking how small the error can be, sample_complexity_bretagnolle_huber fixes a target error epsilon. If any test event A on n independent trials has total error at most epsilon, then log(1/(2 epsilon-epsilon^2)) is at most n times the KL divergence. The event A is universally quantified. Consequently the bound constrains every possible test, which makes it a complexity statement rather than a performance guarantee for one selected procedure.

The scale is already substantive at ordinary accuracy levels. At epsilon=0.01 the logarithmic threshold is approximately 3.92, so laws with KL divergence 0.1 require about 40 trials. At epsilon=0.05 the same divergence gives a requirement of about 23 trials. More generally, the required divergence budget grows on the order of log(1/epsilon) as the target error tends to zero.

The conclusion is deliberately a lower bound on the product n D rather than a quotient-form lower bound on n. Dividing by D would require a nonzero-divergence side condition. Retaining the product avoids that condition and remains faithful when the two laws are identical: then D=0, and no finite number of independent trials can meet an error target strictly below one.

Bretagnolle--Huber is essential to the inversion. The frozen theorem pinsker_floor_nonpos_of_two_le shows that the Pinsker floor is nonpositive once its divergence argument reaches two. Thus it loses all invertible information precisely when multiplication by the sample count makes n D large. By contrast, the frozen theorem bretagnolle_huber_floor_pos shows that the Bretagnolle--Huber floor stays strictly positive at every finite divergence. Only that floor survives the inversion, which is the payoff of the earlier Bretagnolle--Huber wave.

The range 0<epsilon<1 is forced by the proof rather than chosen for convenience. The upper inequality makes 1-epsilon positive, as required when the square-root comparison is squared. Together the two strict inequalities make 2 epsilon-epsilon^2=epsilon(2-epsilon) positive, so logarithmic monotonicity applies. The upper inequality also gives 2 epsilon-epsilon^2=1-(1-epsilon)^2<1; hence the logarithm in the conclusion is strictly positive and the lower bound is non-trivial. The remaining assumptions are exactly the collapsed union of those used by the frozen components. N-fold additivity requires strict positivity and normalization, whereas the single-trial floors require nonnegativity, normalization, and discrete absolute continuity. Strict positivity absorbs both nonnegativity and absolute continuity, because a strictly positive reference law never vanishes. Both normalizations remain, since positivity alone does not imply unit mass.

The module reuses the imported IidSpace and iidPower constructions and declares no definition of its own. It proves no matching upper bound and exhibits no test attaining the rate. No minimax formulation, multi-hypothesis or Assouad-style generalization, or measure-theoretic analogue is claimed. Relative entropy and the logarithmic threshold use the natural logarithm, so the units are nats.

## References

- Truth anchor: `D5/S3/Estimation/SampleComplexity.sample_complexity_bretagnolle_huber`
- Dependency: [D5/S3/DivergenceSupport/PowerAdditivity](../DivergenceSupport/PowerAdditivity.md)
- Dependency: [D5/S3/Estimation/TestingDivergenceBounds](TestingDivergenceBounds.md)
- Dependency: [D5/S3/RenyiDivergence/PowerAdditivity](../RenyiDivergence/PowerAdditivity.md)

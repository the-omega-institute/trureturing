# Stopped multiplicative likelihoods and random-time moments

## Abstract

Stopped multiplicative likelihoods and random-time moments.

Let Omega be any measurable space, mu any finite measure, and F a natural-time filtration. Write A(m)=((2^(2m+1)*(2m)^2)^m)*2^(2m), and E_mu for the Bochner integral. The classical martingale maximal and optional-stopping tools are used to control a stopped likelihood; the absorption estimate retains the random stopping-time moment.

**Theorem 1.1 (A local window controls both stopped moments).**

Lean statement: `D5/S3/Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption.stopped_likelihood_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption.stopped_likelihood_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Williams (1991). *Probability with Martingales*. DOI: [10.1017/CBO9780511813658](https://doi.org/10.1017/CBO9780511813658). URL: <https://doi.org/10.1017/CBO9780511813658>.

*Commentary.*

For every real martingale L adapted to F, real process xi with |xi(i,omega)|<=1, natural-valued F-stopping time tau bounded everywhere by n, real lambda, and integer m>0, assume L(0,omega)=1, L(tau(omega),omega)>=0, and L(i+1,omega)-L(i,omega)=lambda L(i,omega) xi(i,omega) for all i and omega. If |lambda| sqrt(n)<=(2A(m)+1)^(-1), then E_mu[(max_{0<=i<=n}|L(min(i,tau),omega)-1|)^(2m)]<=2A(m)|lambda|^(2m) E_mu[tau^m]. Moreover, for the finite measure mu tilted by the density ofReal(L(tau)), the same stopping-time m-th moment is at most 2 E_mu[tau^m]. The theorem imposes no independence between tau and L, and does not assume that mu or its tilt has mass one. The maximal estimate absorbs the contribution involving tau times the maximal likelihood deviation into its left side. The random moment remains E_mu[tau^m], rather than being replaced by n^m. Classical background is cited in the accompanying martingale note.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption.stopped_likelihood_bounds`

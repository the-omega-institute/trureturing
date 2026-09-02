# Information Loss under a Finite Free Group Quotient

## Abstract

A finite free group quotient loses exactly the conditional information in its residual coordinate.

**Theorem 1.1 (Finite free group quotient information loss).**

$$\begin{gathered}\forall G, Y, \operatorname{FiniteGroup}\left(G\right) \land \operatorname{Finite}\left(Y\right) \land \operatorname{FreeAction}\left(G, Y\right),\\B = Y/G, s: B \to Y, \operatorname{section}\left(s\right),\\Z, P, Q: \operatorname{PMF}\left(Y\right) \Rightarrow\\\operatorname{H}\left(Z\right) = \operatorname{H}\left(Z_{B}\right) + \operatorname{Hcond}\left(Z_{s}\right) \land\\\operatorname{H}\left(Z\right) - \operatorname{H}\left(Z_{B}\right) = \operatorname{Hcond}\left(Z_{s}\right) \land\\(\operatorname{H}\left(Z\right) - \operatorname{H}\left(Z_{B}\right) = \log(\operatorname{card}\left(G\right)) \Rightarrow \forall b, Z_{B}(b) \neq 0 \Rightarrow Z_{\Gamma|b} = \operatorname{Unif}\left(G\right)) \land\\D(P \Vert Q) = D(P_{B} \Vert Q_{B}) + \sum_{b}P_{B}(b) \cdot D(P_{\Gamma|b} \Vert Q_{\Gamma|b}) \land\\(D(P_{B} \Vert Q_{B}) \neq \infty \Rightarrow D(P \Vert Q) - D(P_{B} \Vert Q_{B}) = \sum_{b}P_{B}(b) \cdot D(P_{\Gamma|b} \Vert Q_{\Gamma|b})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Fusion/GroupQuotientInformationLoss.group_quotient_information_loss` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite group G act freely on a finite set Y. A chosen section s of the genuine orbit quotient B = Y/G determines the equivalence c_s : Y equiv B x G used by the Lean declaration. For a PMF Z, write Z_B for its quotient pushforward and Z_s for its pushforward along c_s. Entropy is the repository finite Shannon entropy of the real mass underlying the PMF.

The first two conjuncts are respectively the Shannon chain rule in the quotient-residual coordinates and its information-loss rearrangement. The third is only an implication: attaining log(card G) forces every positive-mass conditional residual law of Z to be uniform. It does not assert the converse or constrain zero-mass fibers.

For arbitrary PMFs P and Q, the fourth conjunct is the unrestricted extended-nonnegative-real Kullback-Leibler chain rule. Its conditional divergences are weighted by the P quotient marginal. No positivity or absolute-continuity premise is added; infinite divergence is allowed.

The fifth conjunct names the quotient data-processing loss as total KL minus quotient KL and identifies it with the same weighted conditional divergence. Under the classical extended-value convention this subtraction identity is asserted when the quotient KL is finite, so the undefined infinity-minus-infinity case is not silently collapsed.

## References

- Truth anchor: `D5/S3/Entropy/Fusion/GroupQuotientInformationLoss.group_quotient_information_loss`
- Dependency: [D5/S3/Entropy/EntropyEquality](../EntropyEquality.md)
- Dependency: [D5/S3/Entropy/Forgetting/DeterministicEntropyEquality](../Forgetting/DeterministicEntropyEquality.md)

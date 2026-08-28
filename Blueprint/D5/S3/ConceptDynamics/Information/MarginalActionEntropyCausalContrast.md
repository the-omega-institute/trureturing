# Equal Action Entropy, Different Causal Action

## Abstract

Marginal action entropy does not determine causal control.

**Theorem 1.1 (Equal marginal action entropy does not identify internal control).**

$$\begin{gathered}x : Bool \times Bool, mu : Bool \times Bool \to \mathbb{R}, mu(x) = \frac{1}{4},\\{}f_{ext} : Bool \times Bool \to Bool, f_{int} : Bool \times Bool \to Bool,\\{}f_{ext}(x) = \operatorname{snd}\left(x\right), f_{int}(x) = \operatorname{fst}\left(x\right),\\{}nu : Bool \to \mathbb{R}, nu(u) = \frac{1}{2},\\{}J : (Bool \times Bool \to Bool) \to \left(Bool \to \left(Bool \to \mathbb{R}\right)\right), J(f, m, a) = \operatorname{pushforward}\left(u \mapsto f(m, u), nu\right):\\{}\operatorname{shannonEntropy}\left(\operatorname{conceptLaw}\left(mu, f_{ext}\right)\right) = \operatorname{shannonEntropy}\left(\operatorname{conceptLaw}\left(mu, f_{int}\right)\right) \land\\{}J(f_{ext}, false) = J(f_{ext}, true) \land\\{}J(f_{int}, false) \neq J(f_{int}, true).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/MarginalActionEntropyCausalContrast.marginal_action_entropy_causal_contrast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state consists of a uniform hidden bit and independent uniform noise. One model copies the noise while the other copies the hidden bit.

Their marginal action entropies agree, but intervention on the hidden bit leaves the first action law fixed and changes the second.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/MarginalActionEntropyCausalContrast.marginal_action_entropy_causal_contrast`
- Dependency: [D5/S3/ConceptDynamics/Information/EqualEntropyTargetValueContrast](EqualEntropyTargetValueContrast.md)

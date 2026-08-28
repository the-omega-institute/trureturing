# Conditional-Independent Information Submodularity

## Abstract

Conditional product laws make finite selected information submodular.

**Theorem 1.1 (Selected mutual information has diminishing returns).**

$$\forall I \in \operatorname{Type}, X \in \operatorname{Type}, Y \in I \to \operatorname{Type}, S \in \operatorname{Finset}\left(I\right), T \in \operatorname{Finset}\left(I\right), e \in I, p \in Y_{S} \times (Y_{T \setminus S} \times (X \times Y_{e})) \to \mathbb{R},\; \left(\operatorname{Finite}\left(I\right) \land \left(\operatorname{Fintype}\left(X\right) \land \left(\operatorname{Fintype}\left(Y_{S}\right) \land \left(\operatorname{Fintype}\left(Y_{T \setminus S}\right) \land \left(\operatorname{Fintype}\left(Y_{e}\right) \land \left(S \subseteq T \land \left(\left(\neg e \in T\right) \land \left(\left(\operatorname{Nonnegative}\left(p\right) \land \operatorname{totalMass}\left(p\right) = 1\right) \land \forall (y_{S}, x), \operatorname{active}\left(p, (y_{S}, x)\right) \Rightarrow p(y_{T \setminus S}, y_{e} \mid (y_{S}, x)) = p(y_{T \setminus S} \mid (y_{S}, x)) \times p(y_{e} \mid (y_{S}, x))\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow I_{p}(X, Y_{\operatorname{insert}\left(e, S\right)}) - I_{p}(X, Y_{S}) \geq I_{p}(X, Y_{\operatorname{insert}\left(e, T\right)}) - I_{p}(X, Y_{T})$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/ConditionalIndependentInformationSubmodularity.conditional_independent_information_submodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite experiment index set carries finite dependent output types. For S contained in T and e outside T, the joint law is written on the tuple of outputs from S, the additional tuple from T minus S, the hidden state, and the output of e.

Conditional independence is stated on that joint law: at every active context consisting of the S-output tuple and hidden state, the joint conditional law of the remaining T-outputs and e factors as the product of its two marginals.

The four marginal laws constructed from the same joint mass are exactly the laws for S, S with e, T, and T with e. Their mutual-information increments satisfy the displayed diminishing-returns inequality.

The proof applies the finite mutual-information chain rule twice. The difference of conditional gains is the nonnegative conditional information between the remaining T-outputs and e given S, after the product-slice term is identified with zero.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/ConditionalIndependentInformationSubmodularity.conditional_independent_information_submodular`
- Dependency: [D5/S3/Entropy/Submodularity/MutualInformationChainRule](MutualInformationChainRule.md)

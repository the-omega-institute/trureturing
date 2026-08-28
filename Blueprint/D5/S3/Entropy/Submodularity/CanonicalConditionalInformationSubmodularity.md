# Canonical Conditional Information Submodularity

## Abstract

Conditional product laws make canonical selected-output information submodular.

**Theorem 1.1 (Canonical selected mutual information has diminishing returns).**

$$\begin{gathered}\forall Index: \operatorname{Type}, Hidden: \operatorname{Type},\\{}Output: Index \to \operatorname{Type},\\{}(\operatorname{Fintype}(Hidden) \land \forall i: Index, \operatorname{Fintype}(Output(i))) \Rightarrow\\{}\forall S: \operatorname{Finset}(Index), T: \operatorname{Finset}(Index), e: Index,\\{}p: (Hidden \times (\forall i: \operatorname{insert}(e, T), Output(\operatorname{val}(i)))) \to \mathbb{R},\\{}S \subseteq T \land \neg e \in T \land\\{}((\forall z: (Hidden \times (\forall i: \operatorname{insert}(e, T), Output(\operatorname{val}(i)))), 0 \leq p(z)) \land \sum_{z: (Hidden \times (\forall i: \operatorname{insert}(e, T), Output(\operatorname{val}(i))))} p(z) = 1) \Rightarrow\\{}\operatorname{let} p_{S}: (Hidden \times (\forall i: S, Output(\operatorname{val}(i)))) \to \mathbb{R} := \operatorname{selectedMarginal}(p, S),\\{}p_{\operatorname{insert}(e, S)}: (Hidden \times (\forall i: \operatorname{insert}(e, S), Output(\operatorname{val}(i)))) \to \mathbb{R} := \operatorname{selectedMarginal}(p, \operatorname{insert}(e, S)),\\{}p_{T}: (Hidden \times (\forall i: T, Output(\operatorname{val}(i)))) \to \mathbb{R} := \operatorname{selectedMarginal}(p, T),\\{}p_{\operatorname{insert}(e, T)}: (Hidden \times (\forall i: \operatorname{insert}(e, T), Output(\operatorname{val}(i)))) \to \mathbb{R} := p,\\{}p_{S, Hidden; T \setminus S, e}: (((\forall i: S, Output(\operatorname{val}(i))) \times Hidden) \times ((\forall i: T \setminus S, Output(\operatorname{val}(i))) \times Output(e))) \to \mathbb{R} := \operatorname{canonicalContextLaw}(p, S, T, e)\\{}\operatorname{in} (\forall c: ((\forall i: S, Output(\operatorname{val}(i))) \times Hidden), \operatorname{marginal}(p_{S, Hidden; T \setminus S, e})(c) \neq 0 \Rightarrow \operatorname{conditional}(p_{S, Hidden; T \setminus S, e}, c) = (w: ((\forall i: T \setminus S, Output(\operatorname{val}(i))) \times Output(e)) \mapsto \operatorname{marginal}(\operatorname{conditional}(p_{S, Hidden; T \setminus S, e}, c))(\operatorname{fst}(w)) \times \operatorname{marginal}(\operatorname{swapLaw}(\operatorname{conditional}(p_{S, Hidden; T \setminus S, e}, c)))(\operatorname{snd}(w)))) \Rightarrow\\{}\operatorname{mutualInformation}(p_{\operatorname{insert}(e, S)}) - \operatorname{mutualInformation}(p_{S}) \geq \operatorname{mutualInformation}(p_{\operatorname{insert}(e, T)}) - \operatorname{mutualInformation}(p_{T}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Submodularity/CanonicalConditionalInformationSubmodularity.canonical_conditional_information_submodular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the hidden state and every output alphabet be finite. The joint mass is carried by the hidden state together with the exact dependent output tuple indexed by insert e T; the ambient index type itself need not be finite.

For S contained in T and e outside T, the canonical finite-set equivalences split the T-output tuple into the S outputs and the outputs indexed by T minus S, and split insert e T into the T outputs and the output at e.

The displayed context law is obtained from that same canonical mass. On each active context consisting of the S-output tuple and hidden state, the conditional law of the remaining T-outputs and the e output factors as the product of its two marginals.

The four explicitly typed selected marginals live on S, insert e S, T, and insert e T. Two finite mutual-information chain rules and the conditional product criterion yield the stated diminishing-return inequality.

## References

- Truth anchor: `D5/S3/Entropy/Submodularity/CanonicalConditionalInformationSubmodularity.canonical_conditional_information_submodular`
- Dependency: [D5/S3/Entropy/Submodularity/MutualInformationChainRule](MutualInformationChainRule.md)

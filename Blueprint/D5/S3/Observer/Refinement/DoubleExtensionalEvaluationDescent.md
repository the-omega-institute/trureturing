# Double Extensional Evaluation Descent

## Abstract

Evaluation descends canonically through its row and column kernels.

**Theorem 1.1 (The double quotient evaluation is representative-independent).**

$$\begin{gathered}\forall State, Protocol, Value: \operatorname{Type},\\{}\forall e: State \to Protocol \to Value,\\{}K_{State} = \ker(\lambda x: State, \lambda p: Protocol, e(x, p)),\\{}K_{Protocol} = \ker(\lambda p: Protocol, \lambda x: State, e(x, p)),\\{}\overline{e}: \operatorname{Quotient}(K_{State}) \to \operatorname{Quotient}(K_{Protocol}) \to Value = \operatorname{liftOn2}(e, K_{State}, K_{Protocol}),\\{}(\forall x, y: State, p, q: Protocol, \operatorname{K_{State}}(x, y) \land \operatorname{K_{Protocol}}(p, q) \Rightarrow e(x, p) = e(y, q)) \land\\{}(\forall x: State, p: Protocol, \overline{e}(\operatorname{class}(x), \operatorname{class}(p)) = e(x, p)) \land\\{}(\forall f: \operatorname{Quotient}(K_{State}) \to \operatorname{Quotient}(K_{Protocol}) \to Value, (\forall x: State, p: Protocol, f(\operatorname{class}(x), \operatorname{class}(p)) = e(x, p)) \Rightarrow f = \overline{e}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/DoubleExtensionalEvaluationDescent.double_extensional_evaluation_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary evaluation table, the state relation is constructed by equality of complete evaluation rows and the protocol relation by equality of complete evaluation columns.

Simultaneous relatedness in those two kernels forces equal evaluation values. The pinned quotient lift therefore constructs the displayed map on the two canonical quotient carriers.

The computation rule states representative independence directly. Surjectivity of both quotient projections also makes this canonical map unique among all maps with the same rule.

Repository searches found application-specific quotient metrics and predictive descents, but no existing joint row-and-column evaluation descent.

## References

- Truth anchor: `D5/S3/Observer/Refinement/DoubleExtensionalEvaluationDescent.double_extensional_evaluation_descent`

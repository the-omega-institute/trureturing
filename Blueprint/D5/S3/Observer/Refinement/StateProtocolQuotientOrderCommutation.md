# State-Protocol Quotient Order Commutation

## Abstract

Quotienting equal evaluation rows and columns commutes by canonical carrier equivalences.

**Theorem 1.1 (The two quotient orders are canonically equivalent).**

$$\begin{aligned}\forall State, Protocol, Value: \operatorname{Type},\\{}\forall e: State \to Protocol \to Value,\\{}(\forall x: State, \operatorname{stateOrderEquiv}(e)(\operatorname{QuotientMk}(\operatorname{ker}(e), x)) = \operatorname{QuotientMk}(\operatorname{stateAfterProtocolSetoid}(e), x)) \land\\{}(\forall p: Protocol, \operatorname{protocolOrderEquiv}(e)(\operatorname{QuotientMk}(\operatorname{protocolAfterStateSetoid}(e), p)) = \operatorname{QuotientMk}(\operatorname{ker}({\Lambda p, \Lambda x, e(x, p)}), p)) \land\\{}(\forall xbar: \operatorname{Quotient}(\operatorname{ker}(e)), pbar: \operatorname{Quotient}(\operatorname{protocolAfterStateSetoid}(e)), \operatorname{stateFirstEvaluation}(e, xbar, pbar) = \operatorname{protocolFirstEvaluation}(e, \operatorname{stateOrderEquiv}(e)(xbar), \operatorname{protocolOrderEquiv}(e)(pbar))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/StateProtocolQuotientOrderCommutation.state_protocol_quotient_order_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state and protocol relations are constructed from equality of the evaluation rows and columns. Each second-stage relation tests the induced evaluation on every class of the first quotient.

The two comparison equivalences are the identity on representatives. Their displayed computation rules make both carrier isomorphisms canonical, while the final conjunct identifies the two descended evaluation maps under those equivalences.

## References

- Truth anchor: `D5/S3/Observer/Refinement/StateProtocolQuotientOrderCommutation.state_protocol_quotient_order_commutes`
- Dependency: [D5/S3/Observer/Refinement/DoubleExtensionalEvaluationDescent](DoubleExtensionalEvaluationDescent.md)

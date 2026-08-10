# Strict Growth of Prime Cashflow Cost

## Abstract

The cumulative logarithmic length of a signed prime-event stream strictly increases at every nonzero event.

**Definition 1.1 (Event length is logarithmic prime-weighted variation).**

$$\operatorname{eventLength}(u)=\sum_{p\in\operatorname{support}(u)}\Vert u_{p}\Vert \operatorname{log}(p)$$

*Formalization.* `D5/S3/Analytic/PrimeCashflowCost.eventLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An event is a finitely supported integer-valued function on the primes. Its length sums the absolute real value of each signed coordinate, weighted by the logarithm of that prime.

**Definition 1.2 (Cashflow cost is cumulative event length).**

$$\operatorname{cashflowCost}(events,t)=\sum_{tau<t}\operatorname{eventLength}(events(tau))$$

*Formalization.* `D5/S3/Analytic/PrimeCashflowCost.cashflowCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cost at time t is the finite sum of event lengths at all natural-number times strictly before t.

**Theorem 1.3 (Every nonzero event has positive length).**

$$u\neq0 \Rightarrow 0<\operatorname{eventLength}(u)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeCashflowCost.eventLength_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero finitely supported event has a nonzero coordinate at some prime. Its absolute value is positive, and the logarithm of every prime is positive, so that coordinate makes the finite sum positive.

**Theorem 1.4 (Cashflow cost strictly increases at a nonzero event).**

$$events(t)\neq0 \Rightarrow \operatorname{cashflowCost}(events,t)<\operatorname{cashflowCost}(events,t+1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeCashflowCost.cashflow_cost_strict_at_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Advancing from t to t+1 appends exactly the length of the event at t to the cumulative cost. The positivity theorem therefore gives strict growth whenever that event is nonzero.

## References

- Truth anchor: `D5/S3/Analytic/PrimeCashflowCost.cashflowCost`
- Truth anchor: `D5/S3/Analytic/PrimeCashflowCost.cashflow_cost_strict_at_event`
- Truth anchor: `D5/S3/Analytic/PrimeCashflowCost.eventLength`
- Truth anchor: `D5/S3/Analytic/PrimeCashflowCost.eventLength_pos`

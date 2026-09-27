# Moving Endpoint of a Binomial Power Sum

## Abstract

A truncated weighted binomial power sum has a geometric endpoint factor along every admissible slope sequence.

**Theorem 1.1 (Every endpoint sequence with an interior lower slope).**

Lean statement: `D5/S3/AnalyticClosure/BinomialMovingEndpoint.moving_endpoint_sum`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/BinomialMovingEndpoint.moving_endpoint_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Seok Hyun Byun and Svetlana Poznanović (2026). *Unimodality and log-concavity of generalized Glasby-Paseman sequences*. URL: <https://arxiv.org/abs/2604.14639v1>.

*Commentary.*

Fix a>0, a positive natural l, and 0<q<a/(1+a). For any natural endpoint sequence r(m) with r(m)/m tending to q, the sum of (choose(m,i) a^i)^l over 0<=i<=r(m), divided by (choose(m,r(m)) a^r(m))^l, tends to 1/(1-(q/(a(1-q)))^l). The assumptions imply r(m)<=m eventually; an all-m bound or an exact endpoint formula is not required. Uniform geometric domination in the distance from the endpoint justifies passage to the sum. This repository formulation supplies an ingredient for the published maximum conjecture, without selecting a maximizer.

## References

- Truth anchor: `D5/S3/AnalyticClosure/BinomialMovingEndpoint.moving_endpoint_sum`

# Empty Ledger Conservation

## Abstract

Complete detection discipline makes an empty open ledger exclude detectable residuals.

**Theorem 1.1 (An empty open ledger excludes detectable residuals).**

$$(\forall x,r,\ \operatorname{detectable}(x,r)\Rightarrow r\in \operatorname{OpenLedger}(x))\ \land\ (\forall r, \neg(r\in \operatorname{OpenLedger}(x)))\Rightarrow \neg\exists r,\ \operatorname{detectable}(x,r)$$

*Proof.* Machine-checked in Lean as `D5/S0/History/EmptyLedgerConservation.empty_ledger_excludes_detectable_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Detection discipline requires every residual that can be detected at an object to occur in that object's open ledger. If the open ledger is empty, a detectable residual would therefore supply an element of the empty ledger, contradicting its pointwise emptiness.

## References

- Truth anchor: `D5/S0/History/EmptyLedgerConservation.empty_ledger_excludes_detectable_residual`

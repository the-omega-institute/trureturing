# Termination Transfer for Quasi-Commutation

## Abstract

Quasi-commuting terminating reductions have a terminating union.

**Theorem 1.1 (Union termination under quasi-commutation).**

$$\operatorname{WellFounded}(\operatorname{swap}((a, b) r(a, b) \lor s(a, b)) \land \operatorname{WellFounded}(\operatorname{swap}(r)) \land \operatorname{WellFounded}(\operatorname{swap}(s)) \land \text{s quasi commutes ahead of r} \Rightarrow \operatorname{WellFounded}(\operatorname{swap}(\text{r or s})).)$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/TerminationTransfer.termination_union_of_quasi_commutation` (`✓ std3`). ∎

*Citation.* M. H. A. Newman (1942). *On Theories with a Combinatorial Definition of "Equivalence"*. DOI: [10.2307/1968867](https://doi.org/10.2307/1968867).

*Commentary.*

Nested accessibility induction handles alternating predecessor steps. The quasi-commutation witness moves an r-step ahead of an s-step, while the returned union closure transports accessibility to the endpoint.

## References

- Truth anchor: `D5/S0/Rewriting/TerminationTransfer.termination_union_of_quasi_commutation`

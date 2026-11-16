# Finite Ledger Correction

## Abstract

Admissible legal ledgers admit at most two delayed corrections per proposition.

Let P, Proof, Ax and Model be arbitrary types, k kernel data, D a finite subset of P, and L a chain of actual LegalLedger objects. Each step is a total admissible transformation, and its application gives the next ledger. Admissibility retains every old node, edge and selected proof witness. Consistency means that no proposition and its k-negation are both Proved. No soundness or universal certificate-existence assumption is used.

The readout s(t,p) is frozen when p belongs to the certified core, refuted when only its negation belongs, and open when neither belongs. Claim labels also include unverified, which is not a fourth ledger state. A Policy has arbitrary initial claims q(0,p) on the subtype D. Its mismatch set is M(t) = {p in D : q(t,p) differs from s(t,p)}. C(t) is a subset of M(t), nonempty whenever M(t) is nonempty. Consequently it is empty when M(t) is empty. Only selected claims change: q(t+1,p) is s(t,p) for p in C(t) and q(t,p) otherwise. The next comparison uses L(t+1), so the ledger can change immediately after a correction of the old readout.

Write Delta(p) for the actual times t at which s(t+1,p) differs from s(t,p), R(p) for {t : p is in C(t)}, and E for {(t,p) : p is in C(t)}. Stable(T) abbreviates: for every t at least T and p in D, s(t,p) = s(T,p). Bars on finite sets denote their cardinalities. Subsingleton means any two members are equal.

U(0) lists one claim (p,q(0,p)) for each p in D. B(t) lists (p,s(t,p)) once for every p in C(t), and U(t+1) appends B(t) to U(t). Sequence positions provide increasing record numbers. Last(U,p) reads the last claim about p; its unverified default for an absent entry is never needed on D because U(0) contains every member. The identity below connects this single append-only sequence to the Policy claims.

**Theorem 1.1 (Finite support, two corrections per proposition, and permanent quietness).**

$$\forall P, Proof, Ax, Model: Type, \forall k: \operatorname{KernelData}\left(P, Proof, Ax, Model\right),\\{}\forall L: \operatorname{Chain}\left(k\right), \forall D: \operatorname{Finset}\left(P\right), \forall policy: \operatorname{Policy}\left(L, D\right), \operatorname{Consistent}\left(k\right) \implies\\{}(\forall p: D, \operatorname{Subsingleton}\left(\operatorname{Delta}\left(p\right)\right)) \land\\{}(\forall p: D, \operatorname{Finite}\left(\operatorname{R}\left(p\right)\right) \land |\operatorname{R}\left(p\right)| \le 2) \land\\{}\operatorname{Finite}\left(E\right) \land |E| = \sum_{t=0}^{\infty} |\operatorname{C}\left(t\right)| \land \sum_{t=0}^{\infty} |\operatorname{C}\left(t\right)| \le 2 \times |D| \land\\{}(\exists T, \operatorname{Stable}\left(T\right)) \land\\{}(\forall T, \operatorname{Stable}\left(T\right) \implies \exists stop, stop \le T + |D| \land (\forall t \ge stop, \operatorname{M}\left(t\right) = \emptyset)) \land\\{}(\forall t p, \operatorname{Last}\left(\operatorname{U}\left(t\right), p\right) = \operatorname{q}\left(t, p\right)) \land\\{}(\forall t, \operatorname{U}\left(t+1\right) = \operatorname{append}\left(\operatorname{U}\left(t\right), \operatorname{B}\left(t\right)\right) \land \operatorname{length}\left(\operatorname{B}\left(t\right)\right) = |\operatorname{C}\left(t\right)| \land\\{}\operatorname{Nodup}\left(\operatorname{map}\left(fst, \operatorname{B}\left(t\right)\right)\right) \land \forall p sigma, (p,sigma) \in \operatorname{B}\left(t\right) \Leftrightarrow (p \in \operatorname{C}\left(t\right) \land sigma = \operatorname{s}\left(t, p\right))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/FiniteLedgerCorrection.finite_ledger_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Frozen membership persists by node retention. Refuted membership persists because the retained negation has an actual permitted proof, and consistency excludes a proof of the proposition in any later core. Thus every non-open readout persists and each Delta(p) is a subsingleton.

Two actual corrections at a < b force an actual change at some t with a <= t < b. Otherwise induction through the exact update rule keeps the claim corrected at a equal to the unchanged readout, contradicting selection of a mismatch at b. Equal endpoint readouts are constant through the interval by terminal persistence. Consequently correction times inject into the two phases distinguished by whether the current readout is open. The combined events inject into D times those two phases. These injections first prove actual support finite; only then are finite cardinalities and the natural-number infinite sum used. The sum equals the event cardinality by its finite time fibers.

Finite actual revisions give a terminal value for each proposition by LedgerLimit.finite_revisions_have_terminal_value. A finite maximum gives a common T. For any actual stabilization time T, the exact mismatch recurrence is M(t+1) = M(t) minus C(t). Nonempty mismatches strictly decrease, so FiniteDefectTermination.finite_defect_repairs_terminate gives emptiness within at most |D| more steps; the same recurrence makes emptiness permanent.

The result includes empty D, arbitrary partial nonempty selections, and unverified initial claims. It bounds correction records, with no additional fairness premise and no uniform bound on T. Permanent quietness concerns M on D; the whole ledger need not stop changing.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/FiniteLedgerCorrection.finite_ledger_correction`
- Dependency: [D5/S0/History/LedgerLimit](../../../S0/History/LedgerLimit.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/LegalLedgerFixedSet](LegalLedgerFixedSet.md)
- Dependency: [D5/S3/ConceptDynamics/Termination/FiniteDefectTermination](../Termination/FiniteDefectTermination.md)

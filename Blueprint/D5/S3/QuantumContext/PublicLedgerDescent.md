# Public Ledger Descent Across Overlapping Contexts

## Abstract

Public overlap compatibility is exactly descent to one noncontextual additive valuation.

**Theorem 1.1 (Publicness transports additive decompositions between contexts).**

$$\operatorname{Public}(L) \land \operatorname{Add}_{C}(L) \Rightarrow \forall c, d, w, a, b,\ w, a, b \in C_{c} \land w\in C_{d} \land w=a \operatorname{disjoint union} b \Rightarrow L_{d}(w)=L_{c}(a)+L_{c}(b).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/PublicLedgerDescent.public_ledger_cross_context_additivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose context c displays an event w as the declared disjoint coarse-graining of events a and b, and context d also displays w. The additive law in c gives L_c(w)=L_c(a)+L_c(b). Publicness then identifies L_d(w) with L_c(w), yielding the displayed equality across two contexts.

Unlike a finite sum-union identity, this conclusion names two context rows and changes the presentation of the unchanged coarse event. Its proof uses both the public overlap law and the source context's valuation law.

**Theorem 1.2 (Public compatible context valuations glue uniquely).**

$$\operatorname{Public}(L) \land \operatorname{Add}_{C}(L) \iff \exists! \mu: E_{\mathrm{cov}}\to \mathbb{R},\ (\forall c, e\in C_{c},\ \mu(e)=L_{c}(e)) \land \operatorname{Add}_{C}(\mu).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/PublicLedgerDescent.public_ledger_descent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E_cov contain exactly the events presented by at least one context. A public, contextwise additive family L_c determines one valuation mu on E_cov: choose any context containing an event and read its ledger entry. Publicness proves that the result is independent of the chosen context. Restriction to E_cov makes uniqueness exact; no arbitrary values are assigned to events outside the experiment.

Every local decomposition law transports through the restriction equalities, so the single valuation is additive on every context. Conversely, restrictions of one global valuation automatically agree on overlaps, and its contextual additive law recovers each local additive law. Thus publicness plus local additivity is equivalent to unique noncontextual additive descent.

This is the pre-Gleason bridge claimed by the source atoms. Additivity is an explicit premise on context valuations and becomes noncontextual through descent; the theorem asserts no positivity, Gleason representation, Born-rule uniqueness, or solution-space result.

**Theorem 1.3 (Finite projection events descend to one additive valuation).**

$$\operatorname{Public}(L) \land \operatorname{Add}_{projection contexts}(L) \iff \exists! \mu: E_{\mathrm{proj,cov}}\to \mathbb{R},\ \operatorname{Restrict}(\mu)=L \land \operatorname{Add}_{projection contexts}(\mu).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/PublicLedgerDescent.projection_public_ledger_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each frozen measurement context, the event support is the powerset of its four actual ConfigurationProjection values. A declared decomposition W=A union B requires A and B to be disjoint, so union is a genuine projection-event coarse-graining operation rather than an equality between unrelated bookkeeping sums.

Applying the generic equivalence says that public additive rows on all nine projection contexts are precisely the restrictions of one unique valuation on every projection event that occurs. This does not alter or reprove the frozen binary valuation obstruction.

**Theorem 1.4 (Compatible overlapping contexts descend nontrivially).**

$$C_{0}=\{0,1\}, C_{1}=\{1,2\},\ L_{0}\{1\}=\frac{1}{3}=L_{1}\{1\},\ \operatorname{Public}(L) \land \operatorname{Add}_{C}(L) \land \exists! \mu,\ \operatorname{Restrict}(\mu)=L \land \operatorname{Add}_{C}(\mu).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/PublicLedgerDescent.overlapping_context_ledger_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinct contexts {0,1} and {1,2} share the singleton event {1}. Their atomic rows are (2/3,1/3) and (1/3,2/3), so both totals are one and both presentations give the shared atom value 1/3. Event values are finite sums of these atomic entries and hence satisfy the declared disjoint-union laws.

The theorem proves publicness and local additivity, then obtains a unique global valuation from the descent equivalence. The local valuation functions are distinct, so the witness is genuinely overlapping and nonconstant rather than a duplicated context row.

**Theorem 1.5 (Incompatible overlapping contexts do not descend).**

$$(\forall c,\ L_{c}(C_{c})=1) \land \operatorname{Add}_{C}(L) \land \neg\exists \mu,\ \operatorname{Restrict}(\mu)=L.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/PublicLedgerDescent.incompatible_overlapping_contexts_do_not_descend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep the same overlapping supports and normalized locally additive event rows, but assign the shared atom value 1/3 in the first context and 2/3 in the second. Any global restriction would give the singleton event {1} one value, forcing those unequal numbers to coincide.

This counterexample isolates the load-bearing premise: normalization and contextwise additivity alone do not produce a noncontextual global valuation. Publicness is exactly the missing gluing condition.

## References

- Truth anchor: `D5/S3/QuantumContext/PublicLedgerDescent.incompatible_overlapping_contexts_do_not_descend`
- Truth anchor: `D5/S3/QuantumContext/PublicLedgerDescent.overlapping_context_ledger_witness`
- Truth anchor: `D5/S3/QuantumContext/PublicLedgerDescent.projection_public_ledger_descent`
- Truth anchor: `D5/S3/QuantumContext/PublicLedgerDescent.public_ledger_cross_context_additivity`
- Truth anchor: `D5/S3/QuantumContext/PublicLedgerDescent.public_ledger_descent_iff`
- Dependency: [D5/S3/QuantumContext/ProjectionValuationObstruction](ProjectionValuationObstruction.md)

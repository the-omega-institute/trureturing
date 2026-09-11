# Free Ultrafilter Charge Countermodel

## Abstract

A free ultrafilter gives full residual mass at every finite budget, although the common blind residual is empty.

**Definition 1.1 (The two-sign full-powerset charge).**

$$\begin{aligned}X = \mathbb{N} \times \operatorname{Bool}\left(\right)\\q: X \to \mathbb{N}, T: X \to \operatorname{Bool}\left(\right)\\\forall k: \mathbb{N}, \forall i: \operatorname{Bool}\left(\right), q((k,i)) = k\\\forall k: \mathbb{N}, \forall i: \operatorname{Bool}\left(\right), T((k,i)) = i\\\Gamma = \operatorname{setOf}\left(n: \mathbb{N}, 1 \leq n\right)\\d: \mathbb{N} \to X \to \operatorname{Bool}\left(\right)\\\forall n: \mathbb{N}, \forall k: \mathbb{N}, \forall i: \operatorname{Bool}\left(\right), d(n)((k,i)) = \operatorname{ite}\left(k \leq n, i, \operatorname{false}\left(\right)\right)\\c: \mathbb{N} \to \mathbb{R}\\\forall n: \mathbb{N}, c(n) = 1\\e: \operatorname{Bool}\left(\right) \to \mathbb{N} \to X \times X\\\forall b: \operatorname{Bool}\left(\right), \forall k: \mathbb{N}, e(b)(k) = ((k,b),(k,\operatorname{BoolNot}\left(b\right)))\\E = \operatorname{defectRelation}\left(q, T\right)\\U = \operatorname{hyperfilter}\left(\mathbb{N}\right)\\\mu: \operatorname{Set}\left(\mathbb{N}\right) \to \operatorname{NNReal}\left(\right)\\\forall C: \operatorname{Set}\left(\mathbb{N}\right), \mu(C) = \operatorname{toNNReal}\left(\operatorname{ultrafilterCharge}\left(U, C\right)\right)\\\nu: \operatorname{AddContent}\left(\operatorname{NNReal}\left(\right), \operatorname{univ}\left(\right): \operatorname{Set}\left(\operatorname{Set}\left(X \times X\right)\right)\right)\\\forall C: \operatorname{Set}\left(X \times X\right), \nu(C) = \frac{1}{2} \mu(\operatorname{preimage}\left(e(\operatorname{false}\left(\right)), C\right)) + \frac{1}{2} \mu(\operatorname{preimage}\left(e(\operatorname{true}\left(\right)), C\right))\\w: \operatorname{EscapeWeight}\left(X \times X\right)\\\forall C: \operatorname{Set}\left(X \times X\right), \operatorname{mass}\left(w, C\right) = \operatorname{coeReal}\left(\nu(C)\right)\\\forall S: \operatorname{Finset}\left(\Gamma\right), R(S) = \operatorname{defectRelation}\left(\operatorname{conceptJoin}\left(q, \operatorname{finiteSelectionSupplement}\left(\Gamma, d, S\right)\right), T\right)\\B = \operatorname{intersection}\left(E, \operatorname{jointKernel}\left(i: \Gamma \mapsto d(\operatorname{val}\left(i\right))\right)\right)\\\forall n: \mathbb{N}, F(n) = \operatorname{FinsetImage}\left(j \mapsto \operatorname{subtype}\left(j + 1, \Gamma\right), \operatorname{FinsetRange}\left(n\right)\right)\\\forall n: \mathbb{N}, A(n) = R(F(n + 1))\end{aligned}$$

*Formalization.* `D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.edgeCharge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Patrick S. Mahon (2026). *The ultrafilter charge on P(ℕ)*. URL: <https://github.com/pmahon3/Resolvent_Framework/blob/d01936f728ba0eb67e9bb2c07b8d451c5de4b5f8/formalization/QuerySystem/QuerySystem/UltrafilterCharge.lean>.

*Commentary.*

The state space is the natural numbers times Bool, with false and true representing the two signs. The base readout forgets the sign and the target reads it. Only positive cutoffs belong to the language. The charge is defined on every set of pairs; its restriction to P(E) is the source charge. The real weight is the coercion of this AddContent.

**Theorem 1.2 (The scalar membership formula).**

$$\forall C: \operatorname{Set}\left(\mathbb{N}\right), \mu(C) = \operatorname{ite}\left(C \in U, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.mu_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Patrick S. Mahon (2026). *The ultrafilter charge on P(ℕ)*. URL: <https://github.com/pmahon3/Resolvent_Framework/blob/d01936f728ba0eb67e9bb2c07b8d451c5de4b5f8/formalization/QuerySystem/QuerySystem/UltrafilterCharge.lean>.

*Commentary.*

The ENNReal membership charge has only values zero and one. Its finite-valued conversion to NNReal therefore has the displayed formula. Disjoint additivity is inherited from the ultrafilter charge through toNNReal_add. The chosen ultrafilter is hyperfilter Nat.

**Theorem 1.3 (Every finite selected residual contains a tail).**

$$\forall S: \operatorname{Finset}\left(\Gamma\right), \forall b: \operatorname{Bool}\left(\right), \operatorname{preimage}\left(e(b), R(S)\right) = \operatorname{setOf}\left(k: \mathbb{N}, \forall j: \Gamma, (j \in S) \Rightarrow \operatorname{val}\left(j\right) < k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.residual_edge_preimage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Patrick S. Mahon (2026). *The ultrafilter charge on P(ℕ)*. URL: <https://github.com/pmahon3/Resolvent_Framework/blob/d01936f728ba0eb67e9bb2c07b8d451c5de4b5f8/formalization/QuerySystem/QuerySystem/UltrafilterCharge.lean>.

*Commentary.*

The canonical residual decomposition makes an edge survive precisely when its index exceeds every selected cutoff. The empty selection gives the whole natural-number preimage. For any finite selection, the tail above its largest cutoff belongs to the free ultrafilter; both signs consequently have scalar mass one.

**Theorem 1.4 (All affordable masses equal one).**

$$\forall L: \operatorname{NNReal}\left(\right), \operatorname{finiteBudgetMassValues}\left(\Gamma, d, q, T, c, w, L\right) = \operatorname{singleton}\left(1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.finite_budget_values_eq_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Patrick S. Mahon (2026). *The ultrafilter charge on P(ℕ)*. URL: <https://github.com/pmahon3/Resolvent_Framework/blob/d01936f728ba0eb67e9bb2c07b8d451c5de4b5f8/formalization/QuerySystem/QuerySystem/UltrafilterCharge.lean>.

*Commentary.*

The cost of a finite selection is its cardinality as a real number. The empty selection has cost zero and is affordable at every NNReal budget, including zero. Thus the set whose infimum defines the canonical budget envelope is exactly the singleton one.

**Theorem 1.5 (Finite escape persists without decreasing-chain continuity).**

$$\begin{aligned}(\operatorname{Countable}\left(\Gamma\right)) \land\\(\operatorname{Nonempty}\left(\Gamma\right)) \land\\(\operatorname{Injective}\left(i: \Gamma \mapsto d(\operatorname{val}\left(i\right))\right)) \land\\(\forall i: \mathbb{N}, (i \in \Gamma) \Rightarrow 0 < c(i)) \land\\(\forall S: \operatorname{Finset}\left(\Gamma\right), \operatorname{finiteSelectionCost}\left(\Gamma, c, S\right) = \operatorname{coeReal}\left(\operatorname{card}\left(S\right)\right)) \land\\(E = \operatorname{range}\left(e(\operatorname{false}\left(\right))\right) \cup \operatorname{range}\left(e(\operatorname{true}\left(\right))\right)) \land\\(\operatorname{toFilter}\left(U\right) \leq \operatorname{cofinite}\left(\mathbb{N}\right)) \land\\(\forall C: \operatorname{Set}\left(\mathbb{N}\right), (\operatorname{Finite}\left(C\right)) \Rightarrow \neg (C \in U)) \land\\(\forall C: \operatorname{Set}\left(\mathbb{N}\right), \mu(C) = \operatorname{ite}\left(C \in U, 1, 0\right)) \land\\(\forall C: \operatorname{Set}\left(X \times X\right), \nu(C) = \frac{1}{2} \mu(\operatorname{preimage}\left(e(\operatorname{false}\left(\right)), C\right)) + \frac{1}{2} \mu(\operatorname{preimage}\left(e(\operatorname{true}\left(\right)), C\right))) \land\\(\forall C: \operatorname{Set}\left(X \times X\right), \nu(C) = \nu(\operatorname{intersection}\left(C, E\right))) \land\\(\nu(\emptyset) = 0) \land\\(\operatorname{Monotone}\left(C: \operatorname{Set}\left(X \times X\right) \mapsto \nu(C)\right)) \land\\(\forall C: \operatorname{Set}\left(X \times X\right), 0 \leq \operatorname{coeReal}\left(\nu(C)\right)) \land\\(\forall C: \operatorname{Set}\left(X \times X\right), \forall D: \operatorname{Set}\left(X \times X\right), (\operatorname{Disjoint}\left(C, D\right)) \Rightarrow \nu(C \cup D) = \nu(C) + \nu(D)) \land\\(\nu(E) = 1) \land\\(B = \emptyset) \land\\(\forall S: \operatorname{Finset}\left(\Gamma\right), \operatorname{finiteResidualMass}\left(\Gamma, d, q, T, w, S\right) = 1) \land\\(\forall n: \mathbb{N}, (1 \leq n) \Rightarrow R(F(n)) = \operatorname{image}\left(e(\operatorname{false}\left(\right)), \operatorname{Ioi}\left(n\right)\right) \cup \operatorname{image}\left(e(\operatorname{true}\left(\right)), \operatorname{Ioi}\left(n\right)\right)) \land\\(\operatorname{Monotone}\left(F\right)) \land\\(\forall i: \Gamma, \exists n: \mathbb{N}, i \in F(n + 1)) \land\\(\operatorname{Antitone}\left(A\right)) \land\\(\operatorname{iInter}\left(n: \mathbb{N}, A(n)\right) = \emptyset) \land\\(\neg \operatorname{Tendsto}\left(n: \mathbb{N} \mapsto \operatorname{coeReal}\left(\nu(A(n))\right), \operatorname{atTop}\left(\right), \operatorname{nhds}\left(\operatorname{coeReal}\left(\nu(\emptyset)\right)\right)\right)) \land\\\forall L: \operatorname{NNReal}\left(\right), \operatorname{finiteEscapeSpectrum}\left(\Gamma, d, q, T, c, w, L\right) = 1.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.free_ultrafilter_charge_countermodel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Patrick S. Mahon (2026). *The ultrafilter charge on P(ℕ)*. URL: <https://github.com/pmahon3/Resolvent_Framework/blob/d01936f728ba0eb67e9bb2c07b8d451c5de4b5f8/formalization/QuerySystem/QuerySystem/UltrafilterCharge.lean>.

*Commentary.*

The positive cutoffs are distinct definitions and form a countable nonempty language with unit costs. Each actual residual edge is eventually separated, so the common blind residual is empty. The exhausting initial segments leave exactly the two tails shown. Their antitone residual chain has empty intersection but constant mass one, whereas the empty set has mass zero. Normalization by the baseline mass one makes every finite nonnegative budget's canonical spectrum equal one. The standard classical hyperfilter construction supplies the free ultrafilter; no additional existence or continuity hypothesis is assumed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.edgeCharge`
- Truth anchor: `D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.finite_budget_values_eq_singleton`
- Truth anchor: `D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.free_ultrafilter_charge_countermodel`
- Truth anchor: `D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.mu_formula`
- Truth anchor: `D5/S3/ConceptDynamics/EscapeSpectrum/FreeUltrafilterChargeCountermodel.residual_edge_preimage`
- Dependency: [D5/S3/ConceptDynamics/EscapeSpectrum/BlindResidualChargeDecomposition](BlindResidualChargeDecomposition.md)

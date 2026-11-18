# Infinitely many minimal supports for one proposition

## Abstract

One decidable lawful propositional kernel has infinitely many globally minimal certified supports.

A certified core is a finite set of formulas with an accepted proof selected at each node, only permitted axioms, closure under the selected references, and an acyclic selected reference graph. The support family consists of all sets arising from such cores. Its definition permits different proofs of the same formula in different cores.

**Definition 1.1 (Supports of a target).**

$$\forall P: Type, \forall Proof: Type, \forall Ax: Type, \forall Model: Type, \forall k: \operatorname{KernelData}\left(P, Proof, Ax, Model\right), \forall p: P, \forall S: \operatorname{Set}\left(P\right), \operatorname{Supports}\left(k, p, S\right) \iff p \in S \land S \in \operatorname{supportFamily}\left(k\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.Supports` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set S contains the target p and is the node set of an actual certified core. Finiteness follows from that core; no upward closure is assumed.

**Definition 1.2 (Global inclusion minimality).**

$$\forall P: Type, \forall Proof: Type, \forall Ax: Type, \forall Model: Type, \forall k: \operatorname{KernelData}\left(P, Proof, Ax, Model\right), \forall p: P, \operatorname{minimalSupports}\left(k, p\right) = \{S: \operatorname{Set}\left(P\right) \mid \operatorname{Minimal}\left(\operatorname{Supports}\left(k, p\right), S\right)\}$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.minimalSupports` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Minimal uses inclusion on sets: S supports p, and every support T contained in S also contains S. The comparison is with all actual supports of p. This is minimality, with no assertion of a unique least support.

**Definition 1.3 (Unconditional finiteness).**

$$claim \iff \forall P: Type, \forall Proof: Type, \forall Ax: Type, \forall Model: Type, \forall k: \operatorname{KernelData}\left(P, Proof, Ax, Model\right), \operatorname{SourceLaws}\left(k\right) \implies \forall p: P, \operatorname{Finite}\left(\operatorname{minimalSupports}\left(k, p\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All four carriers range over types, and k is kernel data on those carriers. SourceLaws requires soundness in every model of the permitted axioms, a finite closed acyclic certificate for every proved formula, and consistency with negation. The claim asserts finiteness for every target with no finite candidate domain premise.

**Definition 1.4 (The infinitely indexed roots).**

$$\forall n: Nat, \operatorname{a}\left(n\right) = \operatorname{imp}\left(\operatorname{atom}\left(\operatorname{succ}\left(n\right)\right), \operatorname{atom}\left(\operatorname{succ}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural number n, a(n) is the implication from variable n+1 to itself. These are pairwise syntactically distinct tautologies.

**Definition 1.5 (The common target).**

$$q = \operatorname{imp}\left(\operatorname{neg}\left(\operatorname{atom}\left(0\right)\right), \operatorname{neg}\left(\operatorname{atom}\left(0\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let r be variable zero. Using implication and falsity, disjunction u or v is encoded as not u implies v. Thus q is not r implies not r, the encoding of r or not r. It is a tautology and is syntactically different from every a(n). Formula evaluation and negation are the ordinary Boolean semantics.

**Definition 1.6 (One infinite decidable kernel).**

$$kernel: \operatorname{KernelData}\left(Formula, Nat \times Bool, Unit, (Nat \to Bool)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Proof symbols are pairs (n,b) with n a natural number and b a Boolean. The symbol (n,false) accepts exactly a(n) and has no references; (n,true) accepts exactly q and references exactly a(n). There are no other accepted pairs. All axiom readouts and the permitted axiom set are empty. Acceptance uses decidable syntactic equality, and both readouts are executable. Models are all Boolean valuations of the countable variable set.

**Definition 1.7 (The two-node family).**

$$\forall n: Nat, \operatorname{pair}\left(n\right) = \{\operatorname{a}\left(n\right), q\}$$

*Formalization.* `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.pair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set pair(n) is {a(n),q}, in the same kernel for every n.

**Theorem 1.8 (Unconditional finiteness fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, select (n,false) at a(n) and (n,true) at q in pair(n). These proofs are accepted and closed. Every selected edge runs from a(n), of rank zero, to q, of rank one; strict increase gives acyclicity. Every accepted conclusion occurs in one of these finite certificates. Accepted formulas are true under every valuation, so the kernel is sound. A formula and its syntactic negation cannot both evaluate to true at the constant-false valuation, which proves consistency.

Consider any actual support S of q. Its selected accepted proof at q must be (m,true) for some m, since no root formula equals q. Closure therefore forces a(m) into S. If S is contained in pair(n), syntactic distinctness forces m=n. Since q is also in S, S equals pair(n). This proves global inclusion minimality of every pair(n); in particular the singleton {q} is not a support. Equality of two displayed pairs forces equality of their root indices. The resulting injection from the natural numbers into minimalSupports(kernel,q) proves that this one family is infinite and contradicts claim.

The generic minimal-support conclusions follow directly from order and finite-set results. Mathlib setOfPred_minimal_antichain applies to the support predicate. For a given finite support, exists_minimal_le_of_wellFoundedLT on finite subsets, with Finset.wellFoundedLT, supplies a globally minimal support below it. For finite D, the minimal supports contained in D lie in its powerset. Set.Finite.powerset gives finiteness, and Set.ncard_le_ncard together with Set.ncard_powerset bounds their number by two to the cardinality of D. These facts require neither upward closure nor a finite universe of propositions. The infinite construction shows precisely why the finite candidate-domain hypothesis cannot be omitted.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.Supports`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.a`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.claim`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.kernel`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.minimalSupports`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.pair`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.q`
- Truth anchor: `D5/S3/ConceptDynamics/DependencyTopology/InfiniteMinimalCertifiedSupports.result`
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/FiniteSupportPatternRealization](FiniteSupportPatternRealization.md)

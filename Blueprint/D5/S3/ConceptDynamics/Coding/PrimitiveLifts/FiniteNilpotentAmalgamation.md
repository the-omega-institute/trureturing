# Prescribed roots force finite nilpotence

## Abstract

A finite group admitting amalgamation of every prescribed coprime equal-power pair is nilpotent.

Let G be an arbitrary finite group, in any universe. Suppose that for every prescribed pair x,y in G and all natural m,n, coprimality of m,n and x^m=y^n imply the existence of z in G with x=z^n and y=z^m. The common root must recover those particular x and y; existence of some mth and nth roots of their common power is a weaker condition. No uniqueness, commutativity or positivity of the exponents is assumed.

**Theorem 1.1 (Finite converse for coprime power amalgamation).**

$$\forall G \in Type,\; (\operatorname{Group}\left(G\right)) \implies ((\operatorname{Finite}\left(G\right)) \implies ((\forall x \in G, y \in G, m \in Nat, n \in Nat,\; (\operatorname{NatCoprime}\left(m, n\right)) \implies ((x^{m} = y^{n}) \implies (\exists z \in G,\; (x = z^{n} \land y = z^{m})))) \implies (\operatorname{GroupIsNilpotent}\left(G\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteNilpotentAmalgamation.nilpotent_of_coprime_power_amalgamation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the displayed prescribed-pair hypothesis, Group.IsNilpotent G holds. Finite means finite as a type, with no chosen enumeration. The trivial group is included. The quantifiers m,n range over all naturals, including zero: if m=0, coprimality forces n=1 and the equal-power condition forces y=1, so z=x realizes the required pair; the other zero boundary is symmetric.

First take m=orderOf(x) and n=orderOf(y) for elements of coprime orders. Both displayed powers equal 1, so the hypothesis places x and y in the same cyclic subgroup as powers of one z. Powers of one element commute. This step uses the actual prescribed pair, not merely the existence of roots of 1.

Fix a Sylow p subgroup P. For a different prime q, each element of a Sylow q subgroup Q has order coprime to every element order in P: element orders divide subgroup cardinalities, and these cardinalities are powers of distinct primes. Thus Q centralizes P and lies in its normalizer. P itself also lies in its normalizer. For each prime power q^k dividing the order of G, Sylow's theorem places q^k in the cardinality of such a Q, hence in the normalizer cardinality; when q=p use P. The prime-power divisibility criterion gives |G| dividing |N(P)|, while Lagrange gives the reverse divisibility. Equality of finite cardinalities makes N(P)=G, so P is normal. This covers primes absent from |G| without any nontrivial-Sylow assumption. Mathlib's finite nilpotence TFAE then supplies nilpotence from normality of every Sylow subgroup.

The mature ingredients are Sylow theory, Lagrange's theorem and the finite-group nilpotence criterion, reused from pinned Mathlib v4.35.0. Its Sylow development credits Chris Hughes and Thomas Browning; the p-group development also credits Snir Broshi; the nilpotent-group development credits Kevin Buzzard, Ines Wright and Joachim Breitner. The prime-power divisibility criterion comes from Mathlib's factorization development by Stuart Presnell. No priority claim is made for these finite-group facts or their combination.

For group-valued return holonomy, this converse identifies the finite-group constraint behind compatibility of prescribed roots. Together with a generic nilpotent-group forward theorem, it would give the finite characterization. That forward direction is a separate result and is not asserted or proved here. Mere closure of the set of root degrees does not provide the prescribed-pair input used in the commutation step.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/FiniteNilpotentAmalgamation.nilpotent_of_coprime_power_amalgamation`

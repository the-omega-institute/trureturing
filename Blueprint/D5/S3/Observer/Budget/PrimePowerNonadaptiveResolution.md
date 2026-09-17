# Prime-power Nonadaptive Resolution

## Abstract

For every prime and positive depth, fixed capped valuation queries identify a residue exactly when their centers omit at most one leaf from each final sibling fiber. The minimum number of actual calls is attained.

Fix a prime p and a natural e at least one. Write X for ZMod of p to the power e, Y for ZMod of p to the power e minus one, and K for the product of p minus one with p to the power e minus one. The map rho at depth d is the canonical reduction from X to ZMod of p to the power d; pi is rho at depth e minus one. The symbols h and q below abbreviate depth and query at the fixed p and e. Write r for PadicInt.toZModPow at depth e and P for the p-adic integers.

**Definition 1.1 (The maximum congruence depth).**

$$\forall c,a \in X, \operatorname{h}\left(c, a\right) = \operatorname{max}\left(\{d \in \mathbb{N} \mid 0 \leq d \leq e \land \operatorname{rho}\left(d, a\right) = \operatorname{rho}\left(d, c\right)\}\right).$$

*Formalization.* `D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution.depth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite maximum includes depth zero, where the modulus is one. The supremum is implemented on a filtered finite range.

**Definition 1.2 (A capped valuation query at a natural center).**

$$\forall x \in P, n \in \mathbb{N}, \operatorname{q}\left(n, x\right) = \operatorname{ite}\left(x + n = 0, e, \operatorname{min}\left(e, \operatorname{valuation}\left(x + n\right)\right)\right).$$

*Formalization.* `D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution.query` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conditional returns e when x plus n is zero. Otherwise it returns the smaller of e and the p-adic valuation. Thus the zero input has the cap value, as required for an extended valuation.

For a finite center set S, H(S) is jointReadout of the family sending a center c in S to h(c, a). The notation O(S, y) denotes the finite set of a in the complement of S with pi(a) equal to y. Its cardinality counts omitted leaves in that fiber. For n indexed by Fin(k), Q(n) is jointReadout of the actual functions q(n(i), x). FactorsThrough(r, Q(n)) says that equal full query signatures imply equal target residues for every pair of p-adic states. It imposes no distinctness condition on n; all k calls are charged.

**Theorem 1.3 (The resolving criterion and the attained call minimum).**

$$\begin{aligned}\forall p,e \in \mathbb{N}, \operatorname{Prime}\left(p\right) \land 1 \leq e \Rightarrow\\(\forall c,a \in X, \operatorname{h}\left(c, a\right) \leq e \land (\forall d \in \mathbb{N}, d \leq e \Rightarrow (d \leq \operatorname{h}\left(c, a\right) \iff \operatorname{rho}\left(d, a\right) = \operatorname{rho}\left(d, c\right)))) \land\\(\forall c,a \in X, (\operatorname{h}\left(c, a\right) = e \iff a = c)) \land\\(\forall x \in P, n \in \mathbb{N}, \operatorname{q}\left(n, x\right) = \operatorname{h}\left(\operatorname{cast}\left(n\right), -\operatorname{r}\left(x\right)\right)) \land\\(\operatorname{Surjective}\left(x \mapsto -\operatorname{r}\left(x\right)\right)) \land\\(\forall c \in X, \exists n \in \mathbb{N}, n < p^{e} \land \operatorname{cast}\left(n\right) = c) \land\\(\operatorname{card}\left(Y\right) = p^{e - 1}) \land\\(\forall y \in Y, \operatorname{card}\left(\{a \in X \mid \operatorname{pi}\left(a\right) = y\}\right) = p) \land\\(\forall S: \operatorname{Finset}\left(X\right), (\operatorname{Injective}\left(\operatorname{H}\left(S\right)\right) \iff (\forall y \in Y, \operatorname{card}\left(\operatorname{O}\left(S, y\right)\right) \leq 1))) \land\\(\exists S: \operatorname{Finset}\left(X\right), \operatorname{card}\left(S\right) = K \land (\forall y \in Y, \operatorname{card}\left(\operatorname{O}\left(S, y\right)\right) = 1) \land \operatorname{Injective}\left(\operatorname{H}\left(S\right)\right)) \land\\\operatorname{IsLeast}\left(\{k \in \mathbb{N} \mid \exists n: \operatorname{Fin}\left(k\right) \to \mathbb{N}, \operatorname{FactorsThrough}\left(r, \operatorname{Q}\left(n\right)\right)\}, K\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reduction compatibility gives the threshold characterization of h. The kernel of p-adic reduction identifies its zero test with the valuation threshold, including the separate zero case. Consequently the target leaf is minus r(x) and the center is the natural number n reduced in X. Every target leaf is realized by the negative of its natural representative.

The final reduction is a surjective additive homomorphism, so its fibers have equal cardinalities. Summing them gives p leaves per fiber. Two omitted siblings have the same reply at every selected center. Conversely a selected endpoint separates a same-fiber pair; for different fibers a selected center in the first fiber separates them. Such a center exists because the fiber has p leaves and at most one is omitted.

The final reduction is injective on the omitted set, bounding its cardinality by the cardinality of Y. To attain the resulting lower bound, omit the canonical natural representative of each element of Y and query every other leaf. Enumerating that finite set and using natural representatives supplies an actual query list. For any list, its image has cardinality at most its length and gives exactly the same distinctions. Repeated centers therefore cannot improve the minimum. The argument includes e equal to one and p equal to two.

## References

- Truth anchor: `D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution.depth`
- Truth anchor: `D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution.query`
- Truth anchor: `D5/S3/Observer/Budget/PrimePowerNonadaptiveResolution.result`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/Factorization/PrimePowers/PrimeBudgetReadoutDichotomy](../../Factorization/PrimePowers/PrimeBudgetReadoutDichotomy.md)

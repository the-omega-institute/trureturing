# Ruleset domination does not imply nimber domination

## Abstract

Equal outcomes under the enforce operator do not imply equal nimbers.

**Definition 1.1 (Short rulesets).**

$$\forall X \in Type,\; \forall f \in X \to \operatorname{Set}\left(X\right),\; \operatorname{Short}\left(f\right) = (\forall x \in X,\; \exists T \in Nat,\; \forall s \in Nat \to X,\; (s\left(0\right) = x) \Rightarrow (\exists i \in Nat,\; (i \le T) \land (\neg (s\left(i + 1\right) \in f\left(s\left(i\right)\right)))))$$

*Formalization.* `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.Short` (`✓ std3`).

*Citation.* Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita (2024). *Enforce and selective operators of combinatorial games*. DOI: [10.1007/s00182-024-00910-6](https://doi.org/10.1007/s00182-024-00910-6). URL: <https://arxiv.org/abs/2311.01006v2>.

*Commentary.*

Definition 4, page 6: “The ruleset A = (X, f) is short if for any x ∈ X, there exists a non-negative integer T_A(x) such that every play sequence, even ignoring the alternating play condition, starting in x, terminates in at most T_A(x) moves.” X is a type and f assigns a set of options. The sequence s must fail to follow an option at some index i ≤ T.

**Definition 1.2 (Joint shortness).**

$$\forall X \in Type,\; \forall fA \in X \to \operatorname{Set}\left(X\right),\; \forall fB \in X \to \operatorname{Set}\left(X\right),\; \operatorname{JointlyShort}\left(fA, fB\right) = \operatorname{Short}\left((\lambda x \mapsto \operatorname{fA}\left(x\right) \cup \operatorname{fB}\left(x\right))\right)$$

*Formalization.* `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.JointlyShort` (`✓ std3`).

*Citation.* Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita (2024). *Enforce and selective operators of combinatorial games*. DOI: [10.1007/s00182-024-00910-6](https://doi.org/10.1007/s00182-024-00910-6). URL: <https://arxiv.org/abs/2311.01006v2>.

*Commentary.*

Definition 10, page 10: “Let A = (X, f_A) and B = (X, f_B) be short rulesets on a set X. Then A and B are jointly short if the ruleset (X, f) given by, for all x ∈ X, f(x) = f_A(x) ∪ f_B(x), is short.” The two option maps are fA and fB.

**Definition 1.3 (The two perfect-play outcomes).**

$$inductive Outcome:Type | \operatorname{Outcome}.P | \operatorname{Outcome}.N$$

*Formalization.* `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.Outcome` (`✓ std3`).

*Citation.* Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita (2024). *Enforce and selective operators of combinatorial games*. DOI: [10.1007/s00182-024-00910-6](https://doi.org/10.1007/s00182-024-00910-6). URL: <https://arxiv.org/abs/2311.01006v2>.

*Commentary.*

Definition 5, page 6: “Consider a short impartial ruleset A = (X, f). Then O(x) = O_A(x) ∈ {P, N} is the perfect play outcome of the position x ∈ X, under ruleset A.” The inductive type Outcome has constructors P and N, for a win by the previous and current player respectively; equality of its constructors is decidable.

**Definition 1.4 (The ordinary outcome recursion).**

$$\forall X \in Type,\; \forall f \in X \to \operatorname{Set}\left(X\right),\; \forall O \in X \to Outcome,\; \operatorname{IsOutcome}\left(f, O\right) = (\forall x \in X,\; (\operatorname{O}\left(x\right) = \operatorname{Outcome}.P) \Leftrightarrow (\forall y \in X,\; (y \in \operatorname{f}\left(x\right)) \Rightarrow (\operatorname{O}\left(y\right) = \operatorname{Outcome}.N)))$$

*Formalization.* `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.IsOutcome` (`✓ std3`).

*Citation.* Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita (2024). *Enforce and selective operators of combinatorial games*. DOI: [10.1007/s00182-024-00910-6](https://doi.org/10.1007/s00182-024-00910-6). URL: <https://arxiv.org/abs/2311.01006v2>.

*Commentary.*

Definition 5, page 6: “Consider a short impartial ruleset A = (X, f). Then O(x) = O_A(x) ∈ {P, N} is the perfect play outcome of the position x ∈ X, under ruleset A.” Normal play gives P exactly when all options are N; the formula specifies this recursion for the function O.

**Definition 1.5 (The enforce outcome recursion).**

$$\forall X \in Type,\; \forall fA \in X \to \operatorname{Set}\left(X\right),\; \forall fB \in X \to \operatorname{Set}\left(X\right),\; \forall O \in X \to Outcome,\; \operatorname{IsEnforceOutcome}\left(fA, fB, O\right) = (\forall x \in X,\; (\operatorname{O}\left(x\right) = \operatorname{Outcome}.P) \Leftrightarrow ((\forall y \in X,\; (y \in \operatorname{fA}\left(x\right)) \Rightarrow (\operatorname{O}\left(y\right) = \operatorname{Outcome}.N)) \lor (\forall y \in X,\; (y \in \operatorname{fB}\left(x\right)) \Rightarrow (\operatorname{O}\left(y\right) = \operatorname{Outcome}.N))))$$

*Formalization.* `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.IsEnforceOutcome` (`✓ std3`).

*Citation.* Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita (2024). *Enforce and selective operators of combinatorial games*. DOI: [10.1007/s00182-024-00910-6](https://doi.org/10.1007/s00182-024-00910-6). URL: <https://arxiv.org/abs/2311.01006v2>.

*Commentary.*

Definition 13, page 11: “The enforce operator on these rulesets is the combined ruleset A ⊙ B, where on each turn, before a play, the opponent enforces one of these two rulesets, and the current player plays according to that ruleset.” Thus P means that at least one of fA and fB has only N options. The choice is made anew at every position.

**Definition 1.6 (The least excluded natural).**

$$\forall s \in \operatorname{Set}\left(Nat\right),\; \operatorname{mex}\left(s\right) = \operatorname{sInf}\left(\operatorname{Set}.compl\left(s\right)\right)$$

*Formalization.* `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.mex` (`✓ std3`).

*Citation.* Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita (2024). *Enforce and selective operators of combinatorial games*. DOI: [10.1007/s00182-024-00910-6](https://doi.org/10.1007/s00182-024-00910-6). URL: <https://arxiv.org/abs/2311.01006v2>.

*Commentary.*

Definition 28, page 17: “Let S denote a finite set of non-negative integers. Then the minimal excludant mex(S) is the least non-negative integer not in S.” For a set s of naturals this is sInf of the complement. The finite option-value sets in the three-position example have nonempty complements.

**Definition 1.7 (Ordinary nimbers).**

$$\forall X \in Type,\; \forall f \in X \to \operatorname{Set}\left(X\right),\; \forall G \in X \to Nat,\; \operatorname{IsNimValue}\left(f, G\right) = (\forall x \in X,\; \operatorname{G}\left(x\right) = \operatorname{mex}\left(\operatorname{Set}.image\left(G, \operatorname{f}\left(x\right)\right)\right))$$

*Formalization.* `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.IsNimValue` (`✓ std3`).

*Citation.* Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita (2024). *Enforce and selective operators of combinatorial games*. DOI: [10.1007/s00182-024-00910-6](https://doi.org/10.1007/s00182-024-00910-6). URL: <https://arxiv.org/abs/2311.01006v2>.

*Commentary.*

Definition 29, page 18: “For any game position x, the nim-value function G(x) is G(x) = mex({G(x′) | x′ ∈ f(x)}).” The image of f(x) under G is represented by Set.image.

**Definition 1.8 (Enforce nimbers).**

$$\forall X \in Type,\; \forall fA \in X \to \operatorname{Set}\left(X\right),\; \forall fB \in X \to \operatorname{Set}\left(X\right),\; \forall G \in X \to Nat,\; \operatorname{IsEnforceNimValue}\left(fA, fB, G\right) = (\forall x \in X,\; \operatorname{G}\left(x\right) = \operatorname{mex}\left(\operatorname{Set}.inter\left(\operatorname{Set}.image\left(G, \operatorname{fA}\left(x\right)\right), \operatorname{Set}.image\left(G, \operatorname{fB}\left(x\right)\right)\right)\right))$$

*Formalization.* `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.IsEnforceNimValue` (`✓ std3`).

*Citation.* Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita (2024). *Enforce and selective operators of combinatorial games*. DOI: [10.1007/s00182-024-00910-6](https://doi.org/10.1007/s00182-024-00910-6). URL: <https://arxiv.org/abs/2311.01006v2>.

*Commentary.*

Definition 33, page 18: “Let A and B be jointly short rulesets on X, and consider the game A ⊙ B. Then, the enforce nimber of x ∈ X is Gᴱ(x) = Gᴱ_A⊙B(x) where Gᴱ(x) = mex({Gᴱ(x′) | x′ ∈ f_A(x)} ∩ {Gᴱ(x′) | x′ ∈ f_B(x)}).” The formula takes the intersection of the two option-value images.

**Definition 1.9 (The implication asked about in Problem 42).**

$$claim = (\forall X \in Type,\; \forall fA \in X \to \operatorname{Set}\left(X\right),\; \forall fB \in X \to \operatorname{Set}\left(X\right),\; (\operatorname{JointlyShort}\left(fA, fB\right)) \Rightarrow (\forall OA \in X \to Outcome,\; \forall OE \in X \to Outcome,\; \forall GA \in X \to Nat,\; \forall GE \in X \to Nat,\; (\operatorname{IsOutcome}\left(fA, OA\right)) \Rightarrow ((\operatorname{IsEnforceOutcome}\left(fA, fB, OE\right)) \Rightarrow ((\operatorname{IsNimValue}\left(fA, GA\right)) \Rightarrow ((\operatorname{IsEnforceNimValue}\left(fA, fB, GE\right)) \Rightarrow ((\forall x \in X,\; \operatorname{OE}\left(x\right) = \operatorname{OA}\left(x\right)) \Rightarrow (\forall x \in X,\; \operatorname{GE}\left(x\right) = \operatorname{GA}\left(x\right))))))))$$

*Formalization.* `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita (2024). *Enforce and selective operators of combinatorial games*. DOI: [10.1007/s00182-024-00910-6](https://doi.org/10.1007/s00182-024-00910-6). URL: <https://arxiv.org/abs/2311.01006v2>.

*Commentary.*

Problem 42, page 23: “If a ruleset dominates another, does it also ‘nimber dominate’ that ruleset? That is, does it follow that all nimbers of the combined ruleset are the same as those of the dominating ruleset?” X is arbitrary; fA and fB are jointly short. OA and OE satisfy the ordinary and enforce outcome recursions, and GA and GE satisfy the ordinary and enforce nimber recursions. Domination means equality of OE and OA at every position. The proposed conclusion is equality of GE and GA at every position.

**Theorem 1.10 (A three-position refutation).**

$$\neg (\forall X \in Type,\; \forall fA \in X \to \operatorname{Set}\left(X\right),\; \forall fB \in X \to \operatorname{Set}\left(X\right),\; (\operatorname{JointlyShort}\left(fA, fB\right)) \Rightarrow (\forall OA \in X \to Outcome,\; \forall OE \in X \to Outcome,\; \forall GA \in X \to Nat,\; \forall GE \in X \to Nat,\; (\operatorname{IsOutcome}\left(fA, OA\right)) \Rightarrow ((\operatorname{IsEnforceOutcome}\left(fA, fB, OE\right)) \Rightarrow ((\operatorname{IsNimValue}\left(fA, GA\right)) \Rightarrow ((\operatorname{IsEnforceNimValue}\left(fA, fB, GE\right)) \Rightarrow ((\forall x \in X,\; \operatorname{OE}\left(x\right) = \operatorname{OA}\left(x\right)) \Rightarrow (\forall x \in X,\; \operatorname{GE}\left(x\right) = \operatorname{GA}\left(x\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.result` (`✓ std3`). ∎

*Resolves.* `Problems/abuku-etal-2024-enforce-nimber-domination` (refuted) by `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"abuku-etal-2024-enforce-nimber-domination","declaration_gid":"D5/S0/Certificates/Games/AbukuEnforceNimberDomination.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tomoaki Abuku; Shun-ichi Kimura; Hironori Kiya; Urban Larsson; Indrajit Saha; Koki Suetsugu; Takahiro Yamashita (2024). *Enforce and selective operators of combinatorial games*. DOI: [10.1007/s00182-024-00910-6](https://doi.org/10.1007/s00182-024-00910-6). URL: <https://arxiv.org/abs/2311.01006v2>.

*Commentary.*

On Fin 3, the option sets for A are ∅, {0}, {0,1}, while those for B are ∅, {0}, {0}. Every move strictly decreases the position, so the union is short. Both outcomes are (P,N,N). The ordinary nimbers are (0,1,2), and the enforce nimbers are (0,1,1). At position 2 the ordinary option values are {0,1}, whereas the intersection for the enforce operator is {0}. Their least excluded values are 2 and 1. Equality of outcomes therefore leaves a positive nimber distinction undetermined.

## References

- Truth anchor: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.IsEnforceNimValue`
- Truth anchor: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.IsEnforceOutcome`
- Truth anchor: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.IsNimValue`
- Truth anchor: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.IsOutcome`
- Truth anchor: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.JointlyShort`
- Truth anchor: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.Outcome`
- Truth anchor: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.Short`
- Truth anchor: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.claim`
- Truth anchor: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.mex`
- Truth anchor: `D5/S0/Certificates/Games/AbukuEnforceNimberDomination.result`

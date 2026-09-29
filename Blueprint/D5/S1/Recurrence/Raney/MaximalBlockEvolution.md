# Maximal-Block Evolution in a Uniform Fixed Word

## Abstract

A support-stabilized uniform morphism gives boundary-safe predecessor and successor control for actual maximal blocks.

Let A be a finite alphabet, mu a P-uniform morphism, w its pointwise fixed word, and Delta a finite set of letters. Bugeaud, Krieger, and Shallit provide the support-stabilization and inverse/image mechanism. This owner records the repository's exact natural-indexed, boundary-safe specialization. In particular, an interval starting at zero is maximal without reading w(-1).

**Definition 1.1 (Literal iteration of a word morphism).**

$$\begin{aligned}\operatorname{morphismPower}\left(mu, 0, x\right) = x\\\operatorname{morphismPower}\left(mu, n + 1, x\right) = \operatorname{flatMap}\left(\operatorname{morphismPower}\left(mu, n, x\right), mu\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Raney/MaximalBlockEvolution.morphismPower` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

The zero iterate returns the input word. The successor iterate first applies the previous iterate and then flat-maps mu. This orientation is used unchanged when one stabilizing power is promoted to the downstream uniform morphism.

**Theorem 1.2 (A positive power stabilizes every letter support).**

$$\exists q \in \mathbb{N},\; 0 < q \land \forall a \in A,\; \forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\operatorname{support}\left(\operatorname{morphismPower}\left(mu, q \cdot n, \operatorname{singleton}\left(a\right)\right)\right) = \operatorname{support}\left(\operatorname{morphismPower}\left(mu, q, \operatorname{singleton}\left(a\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/MaximalBlockEvolution.exists_support_stabilizing_power` (`✓ std3`). ∎

*Citation.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

BKS Lemma 10 is formalized for an arbitrary finite decidable alphabet. Iteration of the support map on the finite powerset eventually repeats. Choosing a positive multiple beyond the preperiod makes the selected support idempotent, so for every letter a and every positive n the supports of mu^(q*n)(a) and mu^q(a) agree.

**Definition 1.3 (A letter at a uniform-image offset).**

$$\operatorname{uniformLetter}\left(mu, a, t\right) = \operatorname{get}\left(\operatorname{mu}\left(a\right), t\right)$$

*Formalization.* `D5/S1/Recurrence/Raney/MaximalBlockEvolution.uniformLetter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

For offset t in Fin(P), uniformity proves that t is a valid index of mu(a). The definition returns that literal list entry; it adds no cyclic or padded indexing convention.

**Definition 1.4 (Actual finite maximal intervals).**

$$\operatorname{IsMaximalDeltaInterval}\left(Delta, w, i, j\right) \iff (i \leq j \land (\forall n \in \mathbb{N},\; (i \leq n \land n \leq j) \Rightarrow (w\left(n\right) \in Delta)) \land (i = 0 \lor \neg (w\left(i - 1\right) \in Delta)) \land \neg (w\left(j + 1\right) \in Delta))$$

*Formalization.* `D5/S1/Recurrence/Raney/MaximalBlockEvolution.IsMaximalDeltaInterval` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

An interval [first,last] is nonempty, every included word value lies in Delta, the right neighbor lies outside Delta, and either first is zero or its predecessor lies outside. The disjunction is the exact start-zero correction needed for an infinite word indexed by natural numbers.

**Theorem 1.5 (A long late block has a bounded predecessor core).**

$$\operatorname{BKS11Hyp}\left(P, mu, w, Delta, i, j\right) \Rightarrow (\operatorname{div}\left(i, P\right) + P \leq \operatorname{div}\left(j, P\right) - P \land (\forall n \in \mathbb{N},\; (\operatorname{div}\left(i, P\right) + P \leq n \land n \leq \operatorname{div}\left(j, P\right) - P) \Rightarrow (w\left(n\right) \in Delta)) \land \operatorname{leftComplementWitness}\left(P, w, Delta, i\right) \land \operatorname{rightComplementWitness}\left(P, w, Delta, j\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/MaximalBlockEvolution.uniform_bks11_predecessor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

Assume P>1, a P-uniform pointwise fixed word, two-step support equal to one-step support, an actual maximal Delta interval, first>P, and length>2P^2. Writing s=first/P and t=last/P, the central source interval [s+P,t-P] is nonempty and lies in Delta. Complementary letters occur in [s-P,s+P-1] and [t-P+1,t+P]. Complete second-order image cells and support stability force the central membership. The widened endpoint ranges are a conservative repository adaptation of BKS Lemma 11.

**Theorem 1.6 (A predecessor core returns to one actual successor).**

$$\operatorname{BKS12Hyp}\left(P, mu, w, Delta, i, j\right) \Rightarrow (\operatorname{centralImageInDelta}\left(P, w, Delta, i, j\right) \land \operatorname{leftImageComplementWitness}\left(P, w, Delta, i\right) \land \operatorname{rightImageComplementWitness}\left(P, w, Delta, j\right) \land \operatorname{existsUniqueActualSuccessor}\left(P, w, Delta, i, j\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/MaximalBlockEvolution.uniform_bks12_successor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yann Bugeaud, Dalia Krieger, and Jeffrey Shallit (2009). *Morphic and Automatic Words: Maximal Blocks and Diophantine Approximation*. URL: <https://arxiv.org/abs/0808.2544v2>.

*Commentary.*

Under P>1 and length>P^2, the image interval from P(first+P) through P(last-P+1)-1 lies in Delta. Complementary letters occur before and after it inside the displayed P-scaled neighborhoods. Those witnesses select a unique actual maximal Delta interval crossing the central image. This is the boundary-explicit uniform specialization of the BKS Lemma 12 mechanism.

## References

- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockEvolution.IsMaximalDeltaInterval`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockEvolution.exists_support_stabilizing_power`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockEvolution.morphismPower`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockEvolution.uniformLetter`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockEvolution.uniform_bks11_predecessor`
- Truth anchor: `D5/S1/Recurrence/Raney/MaximalBlockEvolution.uniform_bks12_successor`

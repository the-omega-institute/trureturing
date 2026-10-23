# Unifilar word affinity and pair survival

## Abstract

The affinity of words whose two unifilar trajectories have not merged equals a killed pair matrix row sum at every length.

**Theorem 1.1 (sum words).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.sum_words`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.sum_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real sum over Boolean words of length n+1 equals the sum over the first Boolean symbol and all length-n tails. UnifilarAffinityContraction.word_total and the existing pair recurrence consume the same equivalence.

**Theorem 1.2 (pairMatrix action).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.pairMatrix_action`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.pairMatrix_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real test function on distinct pairs, the pairMatrix row action is exactly the sum over common symbols of their square-root weight times the successor-pair test value, discarding merged successors. The strict contraction proof uses this identity with the constant-one test function.

Let H be a finite state set. A single successor function delta maps a state and an emitted Boolean symbol to its next state. The nonnegative symbol mass p(a,x) belongs to this same producer. For a word w of length n, endpoint(delta,n,a,w) follows its deterministic trajectory and wordMass(p,delta,n,a,w) multiplies its successive symbol masses. Empty words retain their starting state and have mass one. Zero symbol masses are allowed; their chosen successors have zero contribution.

Pair H consists of ordered distinct state pairs. The matrix pairMatrix(p,delta) uses one common symbol on both trajectories, assigns weight sqrt(p(a,x)p(b,x)), and discards a transition if its successor states coincide. Its entries sum the weights of all symbols with the specified ordered successor pair. survivingAffinity(p,delta,n,s) uses the existing Bhattacharyya coefficient on the two word-mass functions, masking the first function to zero precisely on words with coincident endpoints. Thus it is the sum of sqrt(P(a,w)P(b,w)) over the nonmerged words, with both trajectories reading the same w.

**Theorem 1.3 (Exact nonmerged-word identity at every length).**

$$\forall H \in \mathrm{Type},\; [\mathrm{Fintype}\left(H\right)] \forall p \in H \to \left(\mathrm{Bool} \to \mathbb{R}\right),\; \forall d \in H \to \left(\mathrm{Bool} \to H\right),\; (\forall a \in H,\; \forall x \in \mathrm{Bool},\; 0 \le p\left(a, x\right)) \Rightarrow (\forall n \in \mathbb{N},\; \forall s \in \mathrm{Pair}\left(H\right),\; \sum_{t: \mathrm{Pair}\left(H\right)} \left((\mathrm{pairMatrix}\left(p, d\right))^{n}\right)\left(s, t\right) = \mathrm{survivingAffinity}\left(p, d, n, s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.pair_survival_word_affinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induct on the original emitted-bit length. Split every nonempty word into its first symbol and tail. If the first successors coincide, all later states coincide because the two trajectories use the same successor function and the same tail. Such words contribute zero. Otherwise the one-symbol square-root weight multiplies the surviving affinity from the resulting distinct pair. Expanding the matrix product gives precisely this recurrence. At length zero the identity matrix has row sum one and the unique empty word has affinity one.

Square-root weights on common-symbol pair paths are used in the quantum pairwise-merger construction of Riechers, Mahoney, Aghamohammadi and Crutchfield, A Closed-Form Shave from Occam's Quantum Razor: Exact Results for Quantum Compression, Section IV (https://arxiv.org/html/1510.08186v1). Their construction adds a synchronization sink and removes pairs without a path to it. The survival matrix here retains all ordered distinct pairs and discards transitions that merge their states.

For the row-unifilar marked quotient of FIB legal-edge producers, p and delta are its actual symbol masses and successors. The identity is the pair-process step behind geometric classification estimates: it retains words with distinct final quotient states rather than multiplying independent visible marginals. No row normalization or stationarity is needed for this algebraic identity. It therefore also applies to subprobability weights. Stochasticity, a distinguishing block, MAP error comparisons and conditional erasure estimates require separate hypotheses. No all-producer summability, uniform rate, posterior band, attainment or finite-hidden separation is established here.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.pairMatrix_action`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.pair_survival_word_affinity`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/UnifilarPairSurvival.sum_words`
- Dependency: [D5/S3/TotalVariation/Bhattacharyya](../../../TotalVariation/Bhattacharyya.md)

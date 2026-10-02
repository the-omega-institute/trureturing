# The relaxed Hardy test under no-signalling: at most 1/4 for four parties

## Abstract

For four parties with two outcomes each, every no-signalling box that satisfies the relaxed Hardy conditions of S. S. Bhattacharya, A. Roy, A. Mukherjee and R. Rahaman (arXiv:1507.07327) has success probability q at most 1/4. This refutes their conjecture that the optimal success probability under no-signalling is 1/3 for any number of parties and any dimension, and corrects their observation of the value 1/3 for four parties.

**Definition 1.1 (No-signalling boxes).**

$$\forall N : \mathbb{N}, \forall d : \mathbb{N}, \forall P : (\operatorname{Fin}\left(N\right) \to \operatorname{Bool}) \to \left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right)) \to \mathbb{R}\right), \operatorname{IsNSBox}\left(N, d, P\right) \Leftrightarrow ((\forall s : \operatorname{Fin}\left(N\right) \to \operatorname{Bool}, \forall x : \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), 0 \le \operatorname{P}\left(s, x\right)) \land \left((\forall s : \operatorname{Fin}\left(N\right) \to \operatorname{Bool}, \sum_{x} \operatorname{P}\left(s, x\right) = 1) \land \forall p : \operatorname{Fin}\left(N\right), \forall s : \operatorname{Fin}\left(N\right) \to \operatorname{Bool}, \forall t : \operatorname{Fin}\left(N\right) \to \operatorname{Bool}, (\forall k : \operatorname{Fin}\left(N\right), k \ne p \Rightarrow s_{k} = t_{k}) \Rightarrow \forall x : \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), \sum_{a} \operatorname{P}\left(s, x[p := a]\right) = \sum_{a} \operatorname{P}\left(t, x[p := a]\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.IsNSBox` (`✓ std3`).

*Citation.* Some Sankar Bhattacharya; Arup Roy; Amit Mukherjee; Ramij Rahaman (2015). *Witnessing Genuine Mutipartite Non-locality*. DOI: [10.48550/arXiv.1507.07327](https://doi.org/10.48550/arXiv.1507.07327). URL: <https://arxiv.org/abs/1507.07327v1>.

*Commentary.*

A box of N parties with d outcomes assigns to every input string s in {u, v}^N (in Lean a map Fin N -> Bool, with false for u and true for v) a probability distribution P(s, .) on the outcome strings x in (Fin d)^N. It is no-signalling when, for every party p and all input strings s, t that agree away from p, the marginal of the other parties is the same: summing P(s, x) over the outcome a of p, with x[p := a] the string x with a at p, gives the same value for s and t.

**Definition 1.2 (The relaxed Hardy conditions).**

$$\forall N : \mathbb{N}, \forall d : \mathbb{N}, \forall P : (\operatorname{Fin}\left(N\right) \to \operatorname{Bool}) \to \left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right)) \to \mathbb{R}\right), \forall q : \mathbb{R}, \operatorname{RelaxedHardy}\left(N, d, P, q\right) \Leftrightarrow (((0 < q) \land \forall x : \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), (\forall k : \operatorname{Fin}\left(N\right), x_{k} = 0) \Rightarrow \operatorname{P}\left(\emptyset, x\right) = q) \land \left((\forall r : \operatorname{Fin}\left(N\right), \forall x : \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), (\forall k : \operatorname{Fin}\left(N\right), k \ne r \Rightarrow x_{k} = 0) \Rightarrow \left(x_{r} \ne d-1 \Rightarrow \operatorname{P}\left(\{r\}, x\right) = 0\right)) \land \exists j : \operatorname{Fin}\left(N\right), \forall i : \operatorname{Fin}\left(N\right), i \ne j \Rightarrow \forall x : \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right), ((x_{i} = d-1) \land \left((x_{j} = d-1) \land \forall k : \operatorname{Fin}\left(N\right), ((k \ne i) \land k \ne j) \Rightarrow x_{k} = 0\right)) \Rightarrow \operatorname{P}\left(\{i, j\}, x\right) = 0\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.RelaxedHardy` (`✓ std3`).

*Citation.* Some Sankar Bhattacharya; Arup Roy; Amit Mukherjee; Ramij Rahaman (2015). *Witnessing Genuine Mutipartite Non-locality*. DOI: [10.48550/arXiv.1507.07327](https://doi.org/10.48550/arXiv.1507.07327). URL: <https://arxiv.org/abs/1507.07327v1>.

*Commentary.*

The outcome value 0 stands for the paper's outcome 1 and the value d - 1 for its outcome d. With all inputs u, all outcomes 1 have probability q > 0. With v at party r only, every outcome string with 1 at the other parties and a value other than d at r has probability 0. For one fixed party j and every i other than j, with v at i and j, the outcome string with d at i and j and 1 elsewhere has probability 0. In the display an input string is written as the set of parties with input v: the empty set for all inputs u, {r} for v at r only, {i, j} for v at i and j (in Lean the maps k |-> false, k |-> decide (k = r) and k |-> decide (k = i or k = j)).

**Definition 1.3 (The conjecture).**

$$claim \Leftrightarrow (\forall N : \mathbb{N}, \forall d : \mathbb{N}, 3 \le N \Rightarrow \left(2 \le d \Rightarrow \forall \varepsilon : \mathbb{R}, 0 < \varepsilon \Rightarrow \exists P : (\operatorname{Fin}\left(N\right) \to \operatorname{Bool}) \to \left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(d\right)) \to \mathbb{R}\right), \exists q : \mathbb{R}, (\operatorname{IsNSBox}\left(N, d, P\right)) \land \left((\operatorname{RelaxedHardy}\left(N, d, P, q\right)) \land \frac{1}{3} - \varepsilon < q\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.claim` (`✓ std3`).

*Citation.* Some Sankar Bhattacharya; Arup Roy; Amit Mukherjee; Ramij Rahaman (2015). *Witnessing Genuine Mutipartite Non-locality*. DOI: [10.48550/arXiv.1507.07327](https://doi.org/10.48550/arXiv.1507.07327). URL: <https://arxiv.org/abs/1507.07327v1>.

*Commentary.*

For every number N >= 3 of parties, every common number d >= 2 of outcomes and every epsilon > 0, some no-signalling box satisfies the relaxed Hardy conditions with success probability q > 1/3 - epsilon. The paper conjectures that the optimal success probability is 1/3 for any dimension and any number of parties, which implies this whether the optimum is read as a maximum or a supremum; requiring N >= 3 and a common d only weakens the claim, and the fixed party j may be chosen.

**Theorem 1.4 (At most 1/4 for four parties).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/bhattacharya-2015-relaxed-hardy-no-signalling-optimum` (refuted) by `D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bhattacharya-2015-relaxed-hardy-no-signalling-optimum","declaration_gid":"D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Some Sankar Bhattacharya; Arup Roy; Amit Mukherjee; Ramij Rahaman (2015). *Witnessing Genuine Mutipartite Non-locality*. DOI: [10.48550/arXiv.1507.07327](https://doi.org/10.48550/arXiv.1507.07327). URL: <https://arxiv.org/abs/1507.07327v1>.

*Commentary.*

Take N = 4, d = 2 and a box with success probability q. Let m_r be the probability of 1 at all parties other than r under the inputs u. No-signalling at r and the second condition give probability m_r to the outcome d at r and 1 elsewhere under S_r. For i other than j, no-signalling at j, the third condition and nonnegativity give the outcome d at i and 1 elsewhere probability at least m_i under S_ij, and symmetrically for j. No-signalling at i and at j moves the marginal of the remaining parties back to the inputs u, so the outcome d at i and j with 1 elsewhere has probability at least q under u. These three outcome strings and the all-1 string are distinct, so normalization gives 4 q <= 1, and q > 1/3 - 1/12 = 1/4 is impossible. In Lean the four choices of j are split, and in each case the instantiated equalities and inequalities are combined by linarith.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.IsNSBox`
- Truth anchor: `D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.RelaxedHardy`
- Truth anchor: `D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/RelaxedHardyNoSignallingOptimum.result`

# The strict-majority threshold for quantum hedging

## Abstract

Certain success in a strict majority of repetitions of the qubit game is equivalent to certain single-game success.

A qubit has computational indices Fin(2) = {0, 1}. A word is a function from Fin(n) to Fin(2). Joint indices are ordered pairs of words, with Bob's register first and Alice's retained register second. Real scalars are viewed in C. The real square root is nonnegative and is defined to be zero on negative arguments. A star denotes the conjugate transpose. The symbol I denotes the identity on the indicated register, and kronecker(A, B) denotes A ⊗ B.

**Definition 1.1 (The shared one-game amplitudes).**

$$\forall (\alpha: \mathbb{R}), (\forall (x: \operatorname{Fin}\left(2\right)), (\forall (z: \operatorname{Fin}\left(2\right)), (\operatorname{sharedAmp}\left(\alpha, x, z\right)= \left(u_{\alpha}\right)\left(x, z\right)= \begin{cases}\alpha&x=z=0\\\sqrt{1 - (\alpha)^{2}}&x=z=1\\0&x \ne z\end{cases})))$$

*Formalization.* `D5/S3/Quantum/Information/HedgingMajorityThreshold.sharedAmp` (`✓ std3`).

*Citation.* Srinivasan Arunachalam; Abel Molina; Vincent Russo (2018). *Quantum hedging in two-round prover-verifier interactions*. DOI: [10.4230/LIPIcs.TQC.2017.5](https://doi.org/10.4230/LIPIcs.TQC.2017.5). URL: <https://arxiv.org/abs/1310.7954v5>.

*Commentary.*

The function sharedAmp gives the computational amplitudes of u_alpha. Thus u_alpha = alpha |00> + sqrt(1 - alpha²) |11>. The formula defines these amplitudes for every real alpha; the shared vector is normalized when 0 < alpha <= 1, as in the source's game.

**Definition 1.2 (The shared vector in parallel).**

$$\forall (n: \mathbb{N}), (\forall (\alpha: \mathbb{R}), (\forall (x: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\forall (z: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\operatorname{sharedVec}\left(n, \alpha, (x, z)\right)= \left(\psi_{n,\alpha}\right)\left((x, z)\right)= \prod_{(i: \operatorname{Fin}\left(n\right))} (\operatorname{sharedAmp}\left(\alpha, x\left(i\right), z\left(i\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Information/HedgingMajorityThreshold.sharedVec` (`✓ std3`).

*Citation.* Srinivasan Arunachalam; Abel Molina; Vincent Russo (2018). *Quantum hedging in two-round prover-verifier interactions*. DOI: [10.4230/LIPIcs.TQC.2017.5](https://doi.org/10.4230/LIPIcs.TQC.2017.5). URL: <https://arxiv.org/abs/1310.7954v5>.

*Commentary.*

The vector psi is the tensor product of n copies of u_alpha, with the registers regrouped into Bob's word and Alice's retained word. The product is over all i in Fin(n), including the empty product when n = 0.

**Definition 1.3 (The successful one-game amplitudes).**

$$\forall (\theta: \mathbb{R}), (\forall (y: \operatorname{Fin}\left(2\right)), (\forall (z: \operatorname{Fin}\left(2\right)), (\operatorname{winVec}\left(\theta, y, z\right)= \left(v_{\theta}\right)\left(y, z\right)= \begin{cases}\operatorname{cos}\left(\theta\right)&y=z=0\\\operatorname{sin}\left(\theta\right)&y=z=1\\0&y \ne z\end{cases})))$$

*Formalization.* `D5/S3/Quantum/Information/HedgingMajorityThreshold.winVec` (`✓ std3`).

*Citation.* Srinivasan Arunachalam; Abel Molina; Vincent Russo (2018). *Quantum hedging in two-round prover-verifier interactions*. DOI: [10.4230/LIPIcs.TQC.2017.5](https://doi.org/10.4230/LIPIcs.TQC.2017.5). URL: <https://arxiv.org/abs/1310.7954v5>.

*Commentary.*

The function winVec gives the amplitudes of v_theta = cos(theta) |00> + sin(theta) |11>. This vector is normalized for every real theta. The source takes theta in [0, 2 pi); the same formulas are periodic and are defined here for all real theta.

**Definition 1.4 (The two outcome projections).**

$$\forall (\theta: \mathbb{R}), (\forall (b: \operatorname{Fin}\left(2\right)), (\operatorname{outcomeProj}\left(\theta, b\right)= P_{b,\theta}= \begin{cases}v_{\theta} \cdot (v_{\theta})^{*}&b = 1\\I - P_{1,\theta}&b = 0\end{cases}))$$

*Formalization.* `D5/S3/Quantum/Information/HedgingMajorityThreshold.outcomeProj` (`✓ std3`).

*Citation.* Srinivasan Arunachalam; Abel Molina; Vincent Russo (2018). *Quantum hedging in two-round prover-verifier interactions*. DOI: [10.4230/LIPIcs.TQC.2017.5](https://doi.org/10.4230/LIPIcs.TQC.2017.5). URL: <https://arxiv.org/abs/1310.7954v5>.

*Commentary.*

Write v_theta for the column whose (y, z) entry is winVec(theta, y, z). Outcome 1 is the rank-one projection P(1,theta) = v_theta v_theta*, and outcome 0 is its full orthogonal complement P(0,theta) = I - P(1,theta). These are respectively the winning and losing outcomes.

**Definition 1.5 (The game-by-game tensor product).**

$$\forall (n: \mathbb{N}), (\forall (M: (\operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right)\times \operatorname{Fin}\left(2\right)), \mathbb{C}\right))), (\forall (x: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\forall (z: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\forall (xp: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\forall (zp: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\operatorname{gameTensor}\left(n, M, (x, z), (xp, zp)\right) = \prod_{(i: \operatorname{Fin}\left(n\right))} (M\left(i\right)\left((x\left(i\right), z\left(i\right)), (xp\left(i\right), zp\left(i\right))\right))))))))$$

*Formalization.* `D5/S3/Quantum/Information/HedgingMajorityThreshold.gameTensor` (`✓ std3`).

*Citation.* Srinivasan Arunachalam; Abel Molina; Vincent Russo (2018). *Quantum hedging in two-round prover-verifier interactions*. DOI: [10.4230/LIPIcs.TQC.2017.5](https://doi.org/10.4230/LIPIcs.TQC.2017.5). URL: <https://arxiv.org/abs/1310.7954v5>.

*Commentary.*

Each M(i) acts on one pair of qubits. The entry formula is the tensor product of these operators, expressed in the order (Bob's word, Alice's word). It applies to arbitrary complex matrices M(i).

**Definition 1.6 (At least k successful outcomes).**

$$\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (\theta: \mathbb{R}), (\operatorname{winAtLeast}\left(n, k, \theta\right)= \left(\pi_{k}\right)\left(n, \theta\right)= \sum_{(a: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), k \le \operatorname{card}\left(\{(i: \operatorname{Fin}\left(n\right)) \mid a\left(i\right) = 1\}\right)} (\operatorname{gameTensor}\left(n, ((i: \operatorname{Fin}\left(n\right)) \mapsto \operatorname{outcomeProj}\left(\theta, a\left(i\right)\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/HedgingMajorityThreshold.winAtLeast` (`✓ std3`).

*Citation.* Srinivasan Arunachalam; Abel Molina; Vincent Russo (2018). *Quantum hedging in two-round prover-verifier interactions*. DOI: [10.4230/LIPIcs.TQC.2017.5](https://doi.org/10.4230/LIPIcs.TQC.2017.5). URL: <https://arxiv.org/abs/1310.7954v5>.

*Commentary.*

The projector Pi_k(n,theta) sums the mutually orthogonal outcome-word projections for words a having at least k entries equal to 1. The cardinality counts coordinates, and each summand acts game by game. The definition allows every natural n and k.

**Definition 1.7 (The output of a joint channel).**

$$\forall (m: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (K: (\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right))), (\forall (\alpha: \mathbb{R}), (\operatorname{output}\left(K, \alpha\right) = \sum_{(l: \operatorname{Fin}\left(m\right))} (\operatorname{kronecker}\left(K\left(l\right), (I: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right))\right) \cdot \psi_{n,\alpha} \cdot (\psi_{n,\alpha})^{*} \cdot (\operatorname{kronecker}\left(K\left(l\right), (I: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right))\right))^{*})))))$$

*Formalization.* `D5/S3/Quantum/Information/HedgingMajorityThreshold.output` (`✓ std3`).

*Citation.* Srinivasan Arunachalam; Abel Molina; Vincent Russo (2018). *Quantum hedging in two-round prover-verifier interactions*. DOI: [10.4230/LIPIcs.TQC.2017.5](https://doi.org/10.4230/LIPIcs.TQC.2017.5). URL: <https://arxiv.org/abs/1310.7954v5>.

*Commentary.*

Bob's matrices K(l) act jointly on his entire word, while I acts on Alice's retained word. The sum defines output for every finite family K, without assuming trace preservation. In the channel assertion below, the inline equation sum K(l)* K(l) = I supplies that condition. The vector psi is sharedVec(n,alpha).

**Definition 1.8 (The strict-majority assertion).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), ((n < 2 \cdot k) \Rightarrow ((k \le n) \Rightarrow (\forall (\alpha: \mathbb{R}), (\forall (\theta: \mathbb{R}), ((0 < \alpha) \Rightarrow ((\alpha \le 1) \Rightarrow ((\exists (m: \mathbb{N}), (\exists (K: (\operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right))), ((\sum_{(l: \operatorname{Fin}\left(m\right))} ((K\left(l\right))^{*} \cdot K\left(l\right)) = (I: \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right))) \land (\operatorname{tr}\left(\operatorname{winAtLeast}\left(n, k, \theta\right) \cdot \operatorname{output}\left(K, \alpha\right)\right) = 1)))) \Leftrightarrow ((\alpha)^{2} = (\operatorname{cos}\left(\theta\right))^{2}))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/HedgingMajorityThreshold.claim` (`✓ std3`).

*Citation.* Srinivasan Arunachalam; Abel Molina; Vincent Russo (2018). *Quantum hedging in two-round prover-verifier interactions*. DOI: [10.4230/LIPIcs.TQC.2017.5](https://doi.org/10.4230/LIPIcs.TQC.2017.5). URL: <https://arxiv.org/abs/1310.7954v5>.

*Commentary.*

The source's strict-majority question is expressed as an equivalence: a joint channel can win at least k games with certainty exactly when alpha² = cos²(theta), the case in which a single game can be won with certainty. The bounds n < 2k and k <= n imply n >= 1. All finite Kraus families are allowed, and theta ranges over all real numbers. The assertion concerns strict majorities; it makes no characterization for k <= n/2.

**Theorem 1.9 (Certain majority success requires certain single-game success).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/HedgingMajorityThreshold.result` (`✓ std3`). ∎

*Resolves.* `Problems/arunachalam-molina-russo-2013-hedging-majority-threshold` (proved) by `D5/S3/Quantum/Information/HedgingMajorityThreshold.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"arunachalam-molina-russo-2013-hedging-majority-threshold","declaration_gid":"D5/S3/Quantum/Information/HedgingMajorityThreshold.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Srinivasan Arunachalam; Abel Molina; Vincent Russo (2018). *Quantum hedging in two-round prover-verifier interactions*. DOI: [10.4230/LIPIcs.TQC.2017.5](https://doi.org/10.4230/LIPIcs.TQC.2017.5). URL: <https://arxiv.org/abs/1310.7954v5>.

*Commentary.*

Put c = cos(theta), s = sin(theta), D = diag(s², -c²), and T = I ⊗ D on one game. Since v_theta* T v_theta = 0, the winning projection satisfies P(1,theta) T P(1,theta) = 0. Two outcome words with more than n/2 ones share a coordinate where both entries are 1. At that coordinate the compressed tensor factor vanishes. Summing over the two outcome words therefore gives Pi_k T^{⊗n} Pi_k = 0 whenever n < 2k.

For 0 < alpha <= 1 the retained one-game marginal is R = diag(alpha², 1 - alpha²). A trace-preserving channel on Bob's word leaves Alice's marginal R^{⊗n} unchanged. Hence the output state rho obeys tr(T^{⊗n} rho) = tr(D R)^n = (alpha² s² - (1 - alpha²)c²)^n = (alpha² - c²)^n.

The output rho is positive semidefinite with trace one, and Pi_k is an orthogonal projection. Full weight tr(Pi_k rho) = 1 forces rho = Pi_k rho Pi_k. Its support therefore lies in the range of Pi_k. The zero compression and cyclicity of trace give tr(T^{⊗n} rho) = 0. Thus (alpha² - c²)^n = 0, and n >= 1 yields alpha² = c².

Conversely, if alpha² = c² and alpha > 0, then alpha = |c| and sqrt(1 - alpha²) = |s|. Let epsilon(t) be 1 for t >= 0 and -1 otherwise. The diagonal unitary with entries epsilon(c), epsilon(s) maps u_alpha to v_theta on Bob's qubit. Its n-fold tensor product is a single Kraus operator and produces v_theta in every game. All n outcomes are therefore 1 with certainty, giving at least k wins for k <= n.

## References

- Truth anchor: `D5/S3/Quantum/Information/HedgingMajorityThreshold.claim`
- Truth anchor: `D5/S3/Quantum/Information/HedgingMajorityThreshold.gameTensor`
- Truth anchor: `D5/S3/Quantum/Information/HedgingMajorityThreshold.outcomeProj`
- Truth anchor: `D5/S3/Quantum/Information/HedgingMajorityThreshold.output`
- Truth anchor: `D5/S3/Quantum/Information/HedgingMajorityThreshold.result`
- Truth anchor: `D5/S3/Quantum/Information/HedgingMajorityThreshold.sharedAmp`
- Truth anchor: `D5/S3/Quantum/Information/HedgingMajorityThreshold.sharedVec`
- Truth anchor: `D5/S3/Quantum/Information/HedgingMajorityThreshold.winAtLeast`
- Truth anchor: `D5/S3/Quantum/Information/HedgingMajorityThreshold.winVec`
- Dependency: [D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence](../Entanglement/LocalObservationPartialTraceEquivalence.md)
- Dependency: [D5/S3/QuantumBounds/NonlocalityDepthQuantumBound](../../QuantumBounds/NonlocalityDepthQuantumBound.md)
- Dependency: [D5/S3/QuantumStates/UnitWeightSupport](../../QuantumStates/UnitWeightSupport.md)

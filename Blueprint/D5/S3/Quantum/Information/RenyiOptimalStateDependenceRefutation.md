# Optimal quantum states depend on the Renyi orders

## Abstract

A qutrit basis projector is Pareto optimal for the Shannon dual pair (1,1), but ceases to be optimal for the dual pair (3/5,3). Thus the optimal states for two projective measurements can depend on their Renyi orders.

**Definition 1.1 (Standard-basis probabilities).**

$$\forall d \in \mathbb{N},\; \forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \forall i \in \operatorname{Fin}\left(d\right),\; \operatorname{pX}\left(rho, i\right) = \operatorname{Re}\left(\operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\right)\right)\left(i, i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.pX` (`✓ std3`).

*Citation.* Kais Abdelkhalek; René Schwonnek; Hans Maassen; Fabian Furrer; Jörg Duhme; Philippe Raynal; Berthold-Georg Englert; Reinhard F. Werner (2015). *Optimality of entropic uncertainty relations*. DOI: [10.1142/S0219749915500458](https://doi.org/10.1142/S0219749915500458). URL: <https://arxiv.org/abs/1509.00398v1>.

*Commentary.*

The standard basis X gives the real diagonal entries of CStarMatrix.ofMatrix.symm(val(rho)); CStarMatrix.ofMatrix.symm is the inverse identity equivalence from CStarMatrix to Matrix, and val exposes the subtype value. Positivity and trace one make these a probability distribution. Indices run from 0 to d - 1.

**Definition 1.2 (Probabilities in the columns of the overlap matrix).**

$$\forall d \in \mathbb{N},\; \forall U \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; \operatorname{pY}\left(U, rho, j\right) = \operatorname{Re}\left((\operatorname{conjTranspose}\left(\operatorname{val}\left(U\right)\right) \cdot \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\right)\right) \cdot \operatorname{val}\left(U\right))\left(j, j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.pY` (`✓ std3`).

*Citation.* Kais Abdelkhalek; René Schwonnek; Hans Maassen; Fabian Furrer; Jörg Duhme; Philippe Raynal; Berthold-Georg Englert; Reinhard F. Werner (2015). *Optimality of entropic uncertainty relations*. DOI: [10.1142/S0219749915500458](https://doi.org/10.1142/S0219749915500458). URL: <https://arxiv.org/abs/1509.00398v1>.

*Commentary.*

The overlap matrix has entries U_ij = <x_i|y_j>. Thus Y is the column basis of U, and its probabilities are the real diagonal entries of U* CStarMatrix.ofMatrix.symm(val(rho)) U. The star denotes conjugate transpose and val(U) exposes the matrix of the bundled unitary.

**Definition 1.3 (Finite-order Renyi entropy).**

$$\forall d \in \mathbb{N},\; \forall alpha \in \mathbb{R},\; \forall p \in \operatorname{Fin}\left(d\right) \to \mathbb{R},\; \operatorname{H}\left(alpha, p\right) = \operatorname{if} (alpha = 1) \operatorname{then} (\operatorname{shannonEntropy}\left(p\right)) \operatorname{else} (\frac{\operatorname{log}\left(\sum_{i:\operatorname{Fin}\left(d\right)} (\operatorname{if} (p\left(i\right) = 0) \operatorname{then} (0) \operatorname{else} ((p\left(i\right))^{alpha}))\right)}{1 - alpha})$$

*Formalization.* `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.H` (`✓ std3`).

*Citation.* Kais Abdelkhalek; René Schwonnek; Hans Maassen; Fabian Furrer; Jörg Duhme; Philippe Raynal; Berthold-Georg Englert; Reinhard F. Werner (2015). *Optimality of entropic uncertainty relations*. DOI: [10.1142/S0219749915500458](https://doi.org/10.1142/S0219749915500458). URL: <https://arxiv.org/abs/1509.00398v1>.

*Commentary.*

Section II, equation (6), p. 4 defines Renyi entropy by log(sum_i p_i^alpha)/(1-alpha) away from order one, and by the Shannon entropy at order one. Here shannonEntropy(p) = sum_i -p_i log(p_i) is the frozen finite Shannon entropy. All logarithms are natural: the paper states, verbatim, 'The logarithms can be taken in any base (as long as it is always the same base).' The explicit zero-mass branch implements 0^alpha = 0 for the positive orders in the conjecture. Orders are finite real numbers; infinity is outside this encoding.

**Definition 1.4 (Entropy-coordinate order).**

$$\forall d \in \mathbb{N},\; \forall U \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \forall sigma \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{Below}\left(U, alpha, beta, rho, sigma\right) \Leftrightarrow ((\operatorname{H}\left(alpha, \operatorname{pX}\left(rho\right)\right) \le \operatorname{H}\left(alpha, \operatorname{pX}\left(sigma\right)\right)) \land (\operatorname{H}\left(beta, \operatorname{pY}\left(U, rho\right)\right) \le \operatorname{H}\left(beta, \operatorname{pY}\left(U, sigma\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.Below` (`✓ std3`).

*Citation.* Kais Abdelkhalek; René Schwonnek; Hans Maassen; Fabian Furrer; Jörg Duhme; Philippe Raynal; Berthold-Georg Englert; Reinhard F. Werner (2015). *Optimality of entropic uncertainty relations*. DOI: [10.1142/S0219749915500458](https://doi.org/10.1142/S0219749915500458). URL: <https://arxiv.org/abs/1509.00398v1>.

*Commentary.*

Section II, p. 4: 'For any choice we can define the order relation ⊑ on the state space, so that ρ⊑ρ′ stands for “f₁(ρ)≤f₁(ρ′) and f₂(ρ)≤f₂(ρ′)”.' Here f(rho) = (H(alpha,pX(rho)), H(beta,pY(U,rho))); Below(U,alpha,beta,rho,sigma) encodes rho ⊑ sigma.

**Definition 1.5 (Pareto optimality over every density state).**

$$\forall d \in \mathbb{N},\; \forall U \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{Optimal}\left(U, alpha, beta, rho\right) \Leftrightarrow (\forall sigma \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; (\operatorname{Below}\left(U, alpha, beta, sigma, rho\right)) \Rightarrow (\operatorname{Below}\left(U, alpha, beta, rho, sigma\right)))$$

*Formalization.* `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.Optimal` (`✓ std3`).

*Citation.* Kais Abdelkhalek; René Schwonnek; Hans Maassen; Fabian Furrer; Jörg Duhme; Philippe Raynal; Berthold-Georg Englert; Reinhard F. Werner (2015). *Optimality of entropic uncertainty relations*. DOI: [10.1142/S0219749915500458](https://doi.org/10.1142/S0219749915500458). URL: <https://arxiv.org/abs/1509.00398v1>.

*Commentary.*

Section II, p. 4, verbatim: 'We call a state ρ optimal if ρ′⊑ρ implies ρ⊑ρ′, and hence f(ρ)=f(ρ′).' The quantified competitor sigma ranges over all complex density states in the same dimension, with the same U and entropy orders.

**Definition 1.6 (Independence conjecture).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; \forall U \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall alpha \in \mathbb{R},\; \forall beta \in \mathbb{R},\; \forall alphaPrime \in \mathbb{R},\; \forall betaPrime \in \mathbb{R},\; (\frac{1}{2} < alpha) \Rightarrow ((\frac{1}{2} < beta) \Rightarrow ((\frac{1}{2} < alphaPrime) \Rightarrow ((\frac{1}{2} < betaPrime) \Rightarrow ((\frac{1}{alpha} + \frac{1}{beta} = 2) \Rightarrow ((\frac{1}{alphaPrime} + \frac{1}{betaPrime} = 2) \Rightarrow (\forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; (\operatorname{Optimal}\left(U, alpha, beta, rho\right)) \Rightarrow (\operatorname{Optimal}\left(U, alphaPrime, betaPrime, rho\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.claim` (`✓ std3`).

*Citation.* Kais Abdelkhalek; René Schwonnek; Hans Maassen; Fabian Furrer; Jörg Duhme; Philippe Raynal; Berthold-Georg Englert; Reinhard F. Werner (2015). *Optimality of entropic uncertainty relations*. DOI: [10.1142/S0219749915500458](https://doi.org/10.1142/S0219749915500458). URL: <https://arxiv.org/abs/1509.00398v1>.

*Commentary.*

Conjecture V.8, section V.E, p. 21, '(Independence of the optimal states of (α,β))': 'If ρ is an optimal state for any unitary operator and any α,β>½ satisfying the duality relation (2), then ρ is also an optimal state for all other dual pairs.' The optimality definition is, verbatim (section II, p. 4): 'We call a state ρ optimal if ρ′⊑ρ implies ρ⊑ρ′, and hence f(ρ)=f(ρ′).' Encoding: d is a natural dimension, U is any complex unitary, rho is any density state, alpha and beta are the first finite dual pair, and alphaPrime and betaPrime are the second. Both pairs obey 1/alpha + 1/beta = 2 and every order exceeds 1/2. The source excludes the extremal pair {1/2,infinity}. Zero-based Fin(d) indices relabel its d basis outcomes.

**Theorem 1.7 (A qutrit refutes order independence).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/abdelkhalek-et-al-2015-optimal-state-independence-refutation` (refuted) by `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"abdelkhalek-et-al-2015-optimal-state-independence-refutation","declaration_gid":"D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kais Abdelkhalek; René Schwonnek; Hans Maassen; Fabian Furrer; Jörg Duhme; Philippe Raynal; Berthold-Georg Englert; Reinhard F. Werner (2015). *Optimality of entropic uncertainty relations*. DOI: [10.1142/S0219749915500458](https://doi.org/10.1142/S0219749915500458). URL: <https://arxiv.org/abs/1509.00398v1>.

*Commentary.*

Use the real orthogonal overlap matrix with rows (sqrt(2)/2,sqrt(2)/2,0), (sqrt(2)/4,-sqrt(2)/4,sqrt(3)/2), and (sqrt(2)sqrt(3)/4,-sqrt(2)sqrt(3)/4,-1/2). The X basis projectors are OrthogonalRecordEntropy.pointerState specialized to Fin(3). The Y laws of these projectors are p0 = (1/2,1/2,0), p1 = (1/8,1/8,3/4), and p2 = (3/8,3/8,1/4). At orders (1,1), zero X entropy forces any dominating density state to be an X basis projector: the Shannon zero-entropy characterization forces a point mass, and positivity eliminates the off-diagonal entries. The Y entropies are log(2), (9/4)log(2)-(3/4)log(3), and (11/4)log(2)-(3/4)log(3); 27 < 32 makes the last two strictly larger than the first. Hence the first projector is optimal. At orders (3/5,3), the second projector has the same zero X entropy and Y entropy -(1/2)log(109/256) < log(2), since 1/4 < 109/256. It strictly dominates the first projector, so the latter is not optimal. Both pairs satisfy duality and have orders strictly above 1/2.

## References

- Truth anchor: `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.Below`
- Truth anchor: `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.H`
- Truth anchor: `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.Optimal`
- Truth anchor: `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.pX`
- Truth anchor: `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.pY`
- Truth anchor: `D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.result`
- Dependency: [D5/S3/Entropy/EntropyEquality](../../Entropy/EntropyEquality.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](OrthogonalRecordEntropy.md)

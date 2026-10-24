# Interior perfect state transfer without endpoint transfer

## Abstract

A five-vertex weighted path transfers interior states but never transfers endpoint states.

**Definition 1.1 (The interior-to-endpoint transfer assertion).**

$$(\operatorname{InteriorPathTransferConverseRefutation.claim}) \Leftrightarrow (\forall (m: \mathbb{N}), ((3 \le m) \Rightarrow (\forall (r: (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})), ((\forall (k: \operatorname{Fin}\left(m\right)), ((0: \mathbb{R}) < r\left(k\right))) \Rightarrow (\forall (q: (\operatorname{Fin}\left((m + 1)\right)) \to (\mathbb{R})), (\forall (j: \operatorname{Fin}\left((m + 1)\right)), ((1 \le (\operatorname{Fin.val}\left(j\right): \mathbb{N})) \Rightarrow (((\operatorname{Fin.val}\left(j\right): \mathbb{N}) \le (m - 1)) \Rightarrow (((\operatorname{Fin.val}\left(j\right): \mathbb{N}) \ne (m - (\operatorname{Fin.val}\left(j\right): \mathbb{N}))) \Rightarrow ((\exists (t: \mathbb{R}), (((0: \mathbb{R}) < t) \land (\operatorname{RationalWeightPathTransfer.HasPST}\left((\operatorname{RationalWeightPathTransfer.pathHamiltonian}\left(r, q\right)), t, j, \operatorname{Fin.rev}\left(j\right)\right)))) \Rightarrow (\exists (s: \mathbb{R}), (((0: \mathbb{R}) < s) \land (\operatorname{RationalWeightPathTransfer.HasPST}\left((\operatorname{RationalWeightPathTransfer.pathHamiltonian}\left(r, q\right)), s, (0: \operatorname{Fin}\left((m + 1)\right)), \operatorname{Fin.last}\left(m\right)\right))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Acknowledgement.* Rachel Bailey (2024). *Orthogonal polynomials and perfect state transfer*. DOI: [10.1098/rsta.2024.0414](https://doi.org/10.1098/rsta.2024.0414). URL: <https://arxiv.org/abs/2412.16351v1>.

*Commentary.*

For a path on the vertices 0 through m, RationalWeightPathTransfer.pathHamiltonian r q is the complex symmetric tridiagonal matrix whose diagonal entries are the real potentials q and whose two adjacent off-diagonal entries on edge {k,k+1} are the real edge weight r(k), included in the complex numbers. RationalWeightPathTransfer.HasPST J t a b means that the squared modulus of the (a,b) entry of exp(itJ) is one. The assertion quantifies over every natural m at least three, every strictly positive edge-weight function r, every real potential function q, and every interior vertex j distinct from its reflection. Fin.val is the inclusion of a finite vertex index into the natural numbers, Fin.rev j has value m minus Fin.val j, and Fin.last m is the endpoint with value m; the subtractions in the vertex conditions are natural-number subtractions. Perfect transfer at some positive time t between j and its reflection is asserted to imply endpoint transfer at some positive time s, which need not equal t.

Kirkland, McLaren, Pereira, Plosker and Zhang prove this converse when no eigenvector vanishes at the chosen interior vertex and ask whether that hypothesis can be removed (arXiv:1708.03283v2, main.tex, lines 309–315): `D5/L/GraphInvariants/kirkland2019rationalweightspst`. The displayed assertion expresses that question for distinct mirror interior vertices and positive edge weights. Bailey restates the converse with its hypothesis at new.tex, lines 425–427, and lists the general converse as open at line 602 of arXiv:2412.16351v1: `D5/L/GraphInvariants/bailey2024orthogonalpst`.

**Theorem 1.2 (A five-vertex counterexample).**

$$\neg (\operatorname{InteriorPathTransferConverseRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kirkland-2019-interior-pst-converse-refutation` (refuted) by `D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kirkland-2019-interior-pst-converse-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. Kirkland, D. McLaren, R. Pereira, S. Plosker and X. Zhang (2019). *Perfect quantum state transfer in weighted paths with potentials (loops) using orthogonal polynomials*. DOI: [10.1080/03081087.2018.1442810](https://doi.org/10.1080/03081087.2018.1442810). URL: <https://arxiv.org/abs/1708.03283v2>.

*Commentary.*

Take m = 4, zero potentials, edge weights (2√2, √5, √5, 2√2), and j = 1, whose reflection is 3. All four weights are positive. Write J for this path Hamiltonian and e₀,…,e₄ for the coordinate vectors. Its diagonal is zero; the only nonzero entries are J₀₁ = J₁₀ = J₃₄ = J₄₃ = 2√2 and J₁₂ = J₂₁ = J₂₃ = J₃₂ = √5.

Direct multiplication gives the zero-eigenvalue vector h = (−√5, 0, 2√2, 0, −√5), the vectors f₊ = (1, 1, 0, −1, −1) and f₋ = (1, −1, 0, 1, −1) with eigenvalues 2√2 and −2√2, and the vectors g₊ = (2, 3, √2√5, 3, 2) and g₋ = (2, −3, √2√5, −3, 2) with eigenvalues 3√2 and −3√2. For every eigenvector f with eigenvalue E, exponentiation gives exp(isJ)f = exp(isE)f.

The two interior coordinate vectors decompose as e₁ = f₊/4 − f₋/4 + g₊/12 − g₋/12 and e₃ = −f₊/4 + f₋/4 + g₊/12 − g₋/12. At the positive time t = 2π/(2√2), the phases of the eigenvalues 2√2 and −2√2 are one, whereas those of 3√2 and −3√2 are minus one. Applying these phases to the decomposition of e₃ gives exp(itJ)e₃ = −e₁. Thus the (1,3) entry is −1 and its squared modulus is one, proving perfect transfer between the interior pair.

Suppose now that there is endpoint transfer at a real time s, and write γ = exp(isJ)₀₄. To obtain its column condition, consider the Hermitian matrix A = (s/π)J. Its exponential at time π is exp(isJ), so endpoint transfer and unitarity make the fourth column zero away from row zero: exp(isJ)ₓ₄ is γ when x = 0 and zero otherwise. Since J equals its transpose, exp(isJ) also equals its transpose. Evaluating exp(isJ)f = exp(isE)f at coordinate 4 for an eigenvector f therefore gives exp(isE)f₄ = γf₀.

Apply this identity first to h. Its eigenvalue is zero and its equal endpoint entries −√5 are nonzero, so γ = 1. Next apply it to f₊, whose endpoint entries are 1 and −1: exp(is2√2) = −1. Finally apply it to g₊, whose endpoint entries are both 2: exp(is3√2) = 1.

The two scalar exponential identities yield integers k and l such that s(2√2)/π = 2k + 1 and s(3√2)/π = 2l, with the integers included in the real numbers in these equations. But 3[s(2√2)/π] = 2[s(3√2)/π], so 6k + 3 = 4l. This equality holds between integers and is impossible, since its left side is odd and its right side is even. Thus there is no endpoint transfer at any real time s. Applying the asserted implication to m = 4, these positive weights, zero potentials, and j = 1 would give endpoint transfer at a positive time, a contradiction. The zero-eigenvalue vector vanishes at both interior vertices and therefore imposes no interior phase condition, while its nonzero endpoint entries force γ = 1.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/InteriorPathTransferConverseRefutation.result`
- Dependency: [D5/S3/Quantum/Dynamics/EnergyEigenstateStationarity](EnergyEigenstateStationarity.md)
- Dependency: [D5/S3/Quantum/Dynamics/RationalWeightPathTransfer](RationalWeightPathTransfer.md)

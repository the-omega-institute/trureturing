---
bibkey: bordakuhlmannrincon2026magic
authors: A. Borda Kuhlmann; J. Rincón
year: 2026
title: "Magic-protected entanglement and Clifford-irreducible structure in magic state space"
doi: 10.48550/arXiv.2607.18400
url: https://arxiv.org/abs/2607.18400v1
claim: "Remark F.1 states that no Clifford maps a nontrivial Dicke state with n > 2 to a total product state."
strata_touched:
  - D5/S3/Quantum/Information/DickeClifford/DickeCertificate
  - D5/S3/Quantum/Information/DickeCliffordProductObstruction
license: citation-only
triage: anchor
---

# Magic-protected entanglement and Clifford-irreducible structure in magic state space

A. Borda Kuhlmann and J. Rincón, arXiv:2607.18400v1 [quant-ph].
Page numbers refer to the printed PDF.

Page 11, Definition A.1:

> The $n$-qubit Clifford group is defined as the normalizer of the $n$-qubit Pauli
> group $(\mathcal P_n)$ in $\mathrm{SU}(2^n)$, $\mathcal C_n := N_{\mathrm{SU}(2^n)}(\mathcal P_n)$:
> $\mathcal C_n := \{U \in \mathrm{SU}(2^n) : U P U^\dagger \in \mathcal P_n,\ \forall P \in \mathcal P_n\}$.

Page 16, Appendix F.2:

> Dicke states are defined as [46, 47]
> $|D^n_k\rangle = \frac{1}{\sqrt{\binom{n}{k}}}\sum_{w(x)=k}|x\rangle$,
> where $w(x)$ is the Hamming weight of the bitstring $x$.

Page 16, Remark F.1:

> (Dicke states and the fundamental property of $W$-magic). Let $|\psi\rangle = |D^n_k\rangle$
> be a nontrivial Dicke state, with $0 < k < n$ and $n > 2$, and let $C \in \mathcal C_n$
> be an arbitrary $n$-qubit Clifford gate. Then, for any total product state
> $|\varphi_1\rangle \otimes \cdots \otimes |\varphi_n\rangle$,
> $C|\psi\rangle \ne \bigotimes_{j=1}^{n}|\varphi_j\rangle$.
> That is, nontrivial Dicke states are expected to exhibit the fundamental property
> of $W$-magic in Definition V.1.

The same subsection states:

> Although we do not provide a general proof, previous Clifford-orbit computations
> and our numerical searches indicate that no Clifford operation maps nontrivial
> Dicke states to total product states.

The encoding uses complex functions of bitstrings `Fin n → Fin 2`, whose basis has
cardinality $2^n$. The existing Pauli subgroup includes the phases $1,-1,i,-i$;
`pauliMatrices` takes its matrix image. `Clifford` requires the special-unitary
condition and conjugation into that image. The Dicke amplitude is the complex
cast of the reciprocal real square root of `n.choose k` on weight $k$, using
Mathlib's `hammingNorm` to count nonzero bits. Product
amplitudes are the products of arbitrary local coefficients, each with sum of
squared complex norms one. Pauli counts include the identity once and omit
scalar phase copies. The certificate proves upper counts and a binomial common
denominator, without asserting the exact count or the least denominator.

The total-product statement is distinct from irreducibility across every
bipartition and from membership in the source's full $W$-magic class.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2607.18400
- URL: https://arxiv.org/abs/2607.18400v1

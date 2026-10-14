---
bibkey: yuduanxu2017unitarydistance
authors: Nengkun Yu, Runyao Duan and Quanhua Xu
year: 2017
title: "Bounds on the distance between a unital quantum channel and the convex hull of unitary channels"
doi: 10.1109/TIT.2016.2641447
url: https://arxiv.org/abs/1201.1172
claim: "Section V, Eq. (8), asks whether every Schur channel has equal diamond distances to all mixed-unitary channels and to Schur mixed-unitary channels."
strata_touched:
  - D5/S3/QuantumChannels/SchurChannelMixedUnitaryDistance
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1109/TIT.2016.2641447

Source: https://arxiv.org/abs/1201.1172

The journal citation is *IEEE Transactions on Information Theory* 63(2),
1299–1310 (2017). The quotations use arXiv:1201.1172v1;
page numbers refer to that PDF.

## Definitions and question

Page 1 states:

> So any Ψ ∈ Conv(U(H_d)) can be written as a mixture (convex combination) of unitary channels. (The number of unitary channels in the mixture can be made finite due to the Carathéodory’s theorem on convex hull).

It defines the distance by
$D(\Phi,\operatorname{Conv}(U(H)))=\inf\{D(\Phi,\Psi):\Psi\in\operatorname{Conv}(U(H))\}$,
and states:

> where D(Φ, Ψ) will be given by the diamond norm of Φ − Ψ.

Section II, page 4, states:

> For any S ∈ L(H_d), we can define a super-operator Φ_S via the following way:

It gives $\Phi_S(X)=S\circ X$ for every $X\in L(H_d)$ and continues:

> where S ◦ X = [s_kj x_kj] is the entry-wise product or Hadamard product.

Section V, page 8, defines
$\Lambda(H_d)=S(H_d)\cap\operatorname{Conv}(U(H_d))$ and states:

> Intuitively, Λ(H_d) (or simply Λ_d) is the set of Schur channels that are also mixtures of diagonal unitary channels. So any Ψ ∈ Λ_d can be written into the form Ψ = Σ_k p_k U_k · U_k†, where U_k are d × d diagonal unitary matrices.

Theorem 3, page 8, Eq. (8), states
$\tfrac12 D(\Phi,\Lambda_d)\le D(\Phi,\operatorname{Conv}(U_d))\le D(\Phi,\Lambda_d)$
for every Schur channel. After its proof, page 9 reads:

> It seems quite likely that in Eq. (8) the first inequality should be strict and the second one should be an equality. However, this is still an unsettled issue.

The Lean proposition addresses the second inequality. Channels are the
canonical finite completely positive trace-preserving maps on complex
matrices. Schur action is entrywise multiplication by one matrix on every
input matrix. Convex mixtures have nonnegative real weights summing to one;
the index is `Fin n`, and the unitaries belong to `Matrix.unitaryGroup`.
The distance is the unhalved `FiniteDiamondDistance.diamondDistance`, with
arbitrary finite reference systems. Dimension zero is also included.

## Result and boundaries

A basis-copying channel, a retained copy and a coherent recovery channel
give a superchannel that fixes Schur channels, sends mixed-unitary channels
to mixtures of diagonal unitary channels, and contracts diamond distance.
The two infima are consequently equal. The sets used for these infima
contain the identity channel, and all their distances lie between zero and
two, including dimension zero.

Recovery need not preserve the trace norm of each error. For identity and
bit-flip qubit channels on the input projector onto basis vector zero, the
copied output error has trace norm two, whereas both recovered outputs are
the same projector. The proof uses contraction.

The first inequality is strict when the common distance is positive.
Equivalence of positive distance with nonmembership requires closedness or
compactness and is not established by this module. A closed form for the
distance and the quantum Birkhoff question beyond Schur channels remain open.
Literature completeness is `ASSUMED-UNVERIFIED`; the related papers
arXiv:1408.6476 and arXiv:1807.06491 do not supply this equality in the
screen recorded in issue #16745. arXiv:1812.01449 is by Lovitz.

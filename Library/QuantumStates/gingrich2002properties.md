---
bibkey: gingrich2002properties
authors: Robert M. Gingrich
year: 2002
title: "Properties of entanglement monotones for three-qubit pure states"
doi: 10.1103/PhysRevA.65.052302
url: https://arxiv.org/abs/quant-ph/0106042v2
claim: "For a three-qubit pure state sum t_ijk |ijk>, the polynomial invariants are P_{sigma,tau} = sum t_{i_1 j_1 k_1} ... t_{i_n j_n k_n} conj(t_{i_1 j_sigma(1) k_tau(1)}) ... conj(t_{i_n j_sigma(n) k_tau(n)}) over permutations sigma, tau of n elements (Eq. (8)), with I_1 = P_{e,(12)}, I_2 = P_{(12),e}, I_3 = P_{(12),(12)} and the Kempe invariant I_4 = P_{(123),(132)}. The paper proposes sigma_ABC = 3 - (I_1 + I_2 + I_3) I_4 as a fifth entanglement monotone, a function E with E(psi) >= sum_k p_k E(A_k psi / sqrt(p_k)) for every complete local instrument A_k on one party, states that numerical results suggest it is one, and assumes it for the rest of the paper."
strata_touched:
  - D5/S3/Quantum/Entanglement/GingrichKempeMonotoneRefutation
license: citation-only
triage: anchor
---

# Properties of entanglement monotones for three-qubit pure states

Robert M. Gingrich, Phys. Rev. A 65, 052302 (2002); arXiv:quant-ph/0106042v2.
Quotations are from the arXiv v2 source, with its macros kept as printed
(`\sstate` is $|\psi\rangle$).

The definition of an entanglement monotone (Eq. (5)), for Kraus operators
with $\sum_kA_k^{(i)\dagger}A_k^{(i)}=\mathcal I_i$:

> A (non-increasing) EM is a real valued function $E \left( \sstate \right) $ such that $E \left( \sstate \right) \ge \sum_{k} p_k E \left( \frac{I_{1} \otimes \ldots \otimes A_{k}^{(i)} \otimes \ldots \otimes I_{n} \sstate}{\sqrt{p_{k}}} \right)$ for any state $\sstate$, operation $A_{k}^{(i)}$, and space $i$ where $p_k = \| I_{1} \otimes \ldots \otimes A_{k}^{(i)} \otimes \ldots \otimes I_{n} \sstate \|^2 .$

The polynomial invariants (Eq. (8)):

> $P_{\sigma,\tau} \left( \sstate \right) = \sum  t_{i_1 j_1 k_1} \ldots t_{i_n j_n k_n} \bar{t}_{i_1 j_{\sigma (1)} k_{\tau (1)}} \ldots \bar{t}_{i_n j_{\sigma (n)} k_{\tau (n)}}$ where $\sigma$ and $\tau$ are permutations on $n$ elements, repeated indices are summed and $\bar{t}$ stands for the complex conjugate of $t$

The invariants used:

> $I_1 = P_{e,(1 2)}$, $I_2 = P_{(1 2),e}$, $I_3 = P_{(1 2),(1 2)}$, $I_4 = P_{(1 2 3),(1 3 2)}$

The proposal (Eq. (31) and the text after it):

> $\sigma_{ABC} = 3 - (I_1 + I_2 + I_3) I_4$ and numerical results suggest that it is an EM. After generating over 300,000 random states and applying a random operation to each of them the inequality in equation (\ref{moninequality}) was never violated by $\sigma_{ABC}$.

> For the rest of the paper I will assume that $\sigma_{ABC}$ is an EM.

The paper proves that five independent continuous monotones must exist and
uses $\sigma_{ABC}$ as the candidate depending on $I_4$, in a bound on
conversion probabilities (§III) and in the discussion of further monotones
(§IV–§V). Oreshkov and Brun, arXiv:quant-ph/0506181v6 (Phys. Rev. A 73,
042314 (2006)), §VI, record that "no rigorous proof of monotonicity was
given" for $\sigma_{ABC}$ and construct a different, proved monotone.

The encoding takes three-qubit vectors as functions
$(\mathrm{Fin}\,3\to\mathrm{Fin}\,2)\to\mathbb C$, qubits $A,B,C$ at the
indices $0,1,2$ and $t_{ijk}=\psi(i,j,k)$; the permutations are
`Equiv.Perm (Fin n)`, with `finRotate 3` for $(123)$; and a $2\times2$ matrix
$K$ acts on qubit $A$ as the existing `localOp 0 K`. Since the paper's
$\sigma_{ABC}$ is real valued, the statement compares real parts.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.65.052302 (Phys. Rev. A 65, 052302
  (2002)).
- URL: https://arxiv.org/abs/quant-ph/0106042v2 (v2, 2001-07-04, the latest
  version; source `entpaper2.tex`, md5 `16f2785916409ec7b0283ede7f655d19`):
  the definition of an entanglement monotone (l. 160–179), Eq. (8) (l.
  202–216), the invariants $I_1,\dots,I_4$ (l. 236–239), the proposal and its
  numerical support (l. 589–603) and the bound on conversion probabilities
  that uses it (l. 604–627).

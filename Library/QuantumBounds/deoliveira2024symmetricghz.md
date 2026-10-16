---
bibkey: deoliveira2024symmetricghz
authors: Michael de Oliveira, Luís Soares Barbosa, Ernesto F. Galvão
year: 2024
title: Quantum advantage in temporally flat measurement-based quantum computation
doi: 10.22331/q-2024-04-09-1312
url: https://arxiv.org/abs/2212.03668
claim: "Section 4.2, Conjecture 2 asks for an asymptotic lower bound Ω(n^{⌊k/2⌋−1}) on the GHZ resource for deterministic evaluation of the complete symmetric function of constant degree k with symmetric measurement assignments."
strata_touched:
  - D5/S3/Quantum/Contextuality/SymmetricGHZResourceLowerBound
license: citation-only
triage: anchor
---

# de Oliveira–Barbosa–Galvão: symmetric GHZ resources

M. de Oliveira, L. S. Barbosa and E. F. Galvão, *Quantum advantage in temporally flat measurement-based quantum computation*, Quantum 8, 1312 (2024), arXiv:2212.03668v4.

## Verified locator

DOI: https://doi.org/10.22331/q-2024-04-09-1312

Source: https://arxiv.org/abs/2212.03668

Version: https://arxiv.org/pdf/2212.03668v4. The locators below use the printed page numbers.

## Source statements

Definition 5, p. 13: “The complete symmetric function (CSF) of dimension k, Cᵏ(x) : {0, 1}ⁿ → {0, 1} is defined as the sum, modulo 2, of all terms with degree equal to k, i.e.” Equation (27) sums the degree-k squarefree monomials.

Definition 15, p. 26: “The minimum number of qubits necessary for the deterministic evaluation of a Boolean function f : {0, 1}ⁿ → {0, 1} in the NMQC⊕ model can be defined as the sparsest multi-linear polynomial equivalent to the function, i.e.” Equation (70) minimizes sparsity over integer lifts modulo two.

Definition 16, pp. 26–27: “A symmetric measurement assignment for an NMQC⊕ computation is composed of a set of linear functions L, which is limited to having either all parity bases of a specific size or none,” followed by Equation (71), and “and the corresponding dichotomic measurement operators, which have to be equal for all parity bases of the same size, i.e.” Equation (72) assigns one real coefficient to each selected size.

Section 4.2, Conjecture 2, p. 27: “The number of qubits in a GHZ state necessary for the deterministic evaluation of a complete symmetric function Cᵏ, of constant degree k, with an n bit input string and a symmetric measurement assignment, scales as Ω(n^{⌊k/2⌋−1}).”

Corollary 1, p. 27: “Any family of symmetric Boolean functions defined with a constant degree and evaluated with a symmetric measurement assignment in the NMQC⊕ model requires a number of qubits which is asymptotically bounded by Ω(n^{⌊deg(f)/2⌋−1}).” This is a source consequence; the Lean module treats the complete symmetric functions only.

## Mathematical encoding

The input is `Fin n → Bool`. A parity bit is the integer zero or one according to the parity of the number of true entries in a subset. `layer n i x` sums those bits over all i-element subsets. `csf n k x` counts the k-element subsets on which every input is true, modulo two. `ComputesSym` requires the real linear combination of the selected layers to be an integer of that parity for every input. It includes no constant term. Each selected size i contributes `Nat.choose n i` qubits, even when its coefficient vanishes, so the bound holds in particular when only nonzero layers are selected.

The repository proof gives at least `Nat.choose n (k / 2)` qubits for `2 ≤ k ≤ n`, and derives the asymptotic assertion also for `k = 1`. Extension to other symmetric Boolean families, constant phase offsets and nonsymmetric assignments is not separately formalized here.

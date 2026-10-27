---
bibkey: barbergillespietaylor2023purification
authors: Ben Barber; Neil I. Gillespie; J. M. Taylor
year: 2023
title: "Post-selection-free preparation of high-quality physical qubits"
doi: 10.22331/q-2023-05-04-994
url: https://arxiv.org/abs/2209.05391v3
claim: "The paper defines (n,k,e) purification circuits, CNOT and Toffoli circuits that map every n-bit string of weight at most e to a string that is zero in k nominated positions, proves that they exist exactly when the sum of the binomial coefficients up to e is at most 2^(n-k), analyses their output error under independent preparation, idle, CNOT and Toffoli errors, and asks whether, for circuits meeting this bound with equality and preparation error below 1/2, the output error is an increasing function of each of the four error rates."
strata_touched:
  - D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation
license: citation-only
triage: anchor
---

# Barber, Gillespie and Taylor, purification circuits

B. Barber, N. I. Gillespie and J. M. Taylor, arXiv:2209.05391v3 [quant-ph] (26 April 2023; v1 12 September 2022); Quantum 7, 994 (2023). Quotations are from the v3 TeX source, with macros expanded ($p_0$, $p_I$, $p_C$, $p_T$, $p_{\text{out}}$) and cross-references omitted.

Purification circuits (Section 2):

> We define an $(n, k, e)$ purification circuit (or $(n,k,e)$ circuit) to be a CNOT and Toffoli circuit mapping the $n$-long bitstrings of weight at most $e$ into the space of $n$-long bitstrings that are zero in $k$ nominated positions.

For $n\ge1$ and $k,e\in\{1,\dots,n\}$ such a circuit exists if $\binom n0+\binom n1+\cdots+\binom ne\le2^{n-k}$, and the condition is necessary.

The error model (Section 2.1): a qubit is prepared as $|1\rangle$ instead of $|0\rangle$ with probability $p_0$; a qubit not involved in the current round of gates depolarises with probability $p_I$; a CNOT gate depolarises the set of qubits it acts on with probability $p_C$; a Toffoli gate depolarises its qubits with probability $p_T$; all events are independent, and a depolarised set of qubits is replaced by a uniform mixture of the computational basis. $p_{\text{out}}(p_0,p_I,p_C,p_T)$ is the expected number of errors on the outputs divided by the number of outputs.

The question (Section 3.2):

> We conjecture that it should be possible to prove monotonicity under some reasonable set of conditions. For instance, suppose that $\big|\binom n 0 + \cdots + \binom n e\big| = 2^{n-k}$ and $p_0 < 0.5$. Is $p_{\text{out}}(p_0,p_I,p_C,p_T)$ an increasing function of $p_0$, $p_I$, $p_C$ and $p_T$? We leave this as an open question.

## Verified locator

Source: https://arxiv.org/abs/2209.05391v3
- DOI: https://doi.org/10.22331/q-2023-05-04-994 (Quantum 7, 994 (2023); author list, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/2209.05391v3 (the e-print is a gzipped tar archive; member `purification.tex`, 1111 lines, md5 `f2d9d11afbfb0d5a6c11340b0a183f5c`):
  - purification circuits, l. 203;
  - the existence criterion, l. 262–270;
  - the error model, l. 217–243;
  - $p_{\text{out}}$, l. 711–713;
  - the monotonicity question, l. 859–862.
- The arXiv version dates are from the arXiv metadata.

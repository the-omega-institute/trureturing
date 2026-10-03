---
bibkey: klimov2023wstate
authors: Petr Klimov; Richik Sengupta; Jacob Biamonte
year: 2023
title: "On Translation-Invariant Matrix Product States and advances in MPS representations of the W-state"
doi: 10.48550/arXiv.2306.16456
url: https://arxiv.org/abs/2306.16456v2
claim: "A TI MPS representation with PBC of bond dimension d of the W-state of order n is a pair of complex d x d matrices A_0, A_1 with Tr(A_{i_1} ... A_{i_n}) = 1/sqrt(n) when exactly one i_j is 1 and 0 otherwise. Theorem 1 gives such a representation of bond dimension floor(n/2) + 1 for every n. The paper conjectures that no TI MPS representation with PBC of the W-state of order n has bond dimension smaller than floor(n/2) + 1, and asks whether d(n) = floor(n/2) + 1."
strata_touched:
  - D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension
license: citation-only
triage: anchor
---

# On Translation-Invariant Matrix Product States and advances in MPS representations of the W-state

Petr Klimov, Richik Sengupta, Jacob Biamonte, arXiv:2306.16456v2
[quant-ph, math.RA] (2023). Quotations are from the arXiv source.

The normalized $W$-state (Section 2; the `align` environment around the
formula omitted):

> The $W$-state of order $n$ is defined as $\ket{W_n} = \frac{1}{\sqrt n}\sum\limits_{(i_1,\ldots,i_n) \in \{0, 1\}^n : \sum\limits_{j=1}^n i_j = 1} \ket{i_1\ldots i_n}$

The representations (Section 2):

> TI MPS representation with PBC of bond dimension $d$ for the $W$-state are pair of complex matrices $A_0$ and $A_1$ such that

$\operatorname{Tr}(A_{i_1} A_{i_2} \ldots A_{i_n})$ is $0$ for every
$(i_1, \ldots, i_n) \in \{0, 1\}^n$ with $\sum_j i_j \ne 1$ and
$\frac{1}{\sqrt n}$ for every $(i_1, \ldots, i_n) \in \{0, 1\}^n$ with
$\sum_j i_j = 1$.

After Theorem 1 (Section 3), which gives a representation of bond
dimension $\lfloor n/2 \rfloor + 1$:

> These experiments lead us to conjecture that the representation obtained in Theorem \ref{W state representation} could be optimal both in terms of asymptotics and the constant factor or in other words it is impossible to come up with a TI MPS representation with PBC with bond dimension smaller than $\floor*{\frac{n}{2}}+1$ for the $W$-state of order $n$.

Section 4 lists computed values of the minimal bond dimension $d(n)$, with
$d(7) = 4$, and asks:

> Is the estimate obtained in Theorem \ref{W state representation} optimal? Or, in other words, is it true that $d(n)=\floor*{\frac{n}{2}}+1$ for the $W$-state? In particular, is it true that $d(6)=4?$

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2306.16456 (arXiv-issued; the arXiv
  record lists no journal reference).
- URL: https://arxiv.org/abs/2306.16456v2 (source `W_eng_final.tex`, md5
  `7ca3ea38231607a509cbbc09602101f3`): the $W$-state (l. 180–184), the
  representations (l. 189–197), the conjecture (l. 414), the table of
  $d(n)$ (l. 750–768) and the problem (l. 772–774).

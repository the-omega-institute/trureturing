---
bibkey: gudder2021mutuallyunbiasedobservables
authors: Stan Gudder
year: 2021
title: "Mutually Unbiased Quantum Observables"
doi: 10.48550/arXiv.2110.03099
url: https://arxiv.org/abs/2110.03099v1
claim: "The paper defines sequential products A∘B=A^{1/2}BA^{1/2} of effects on a finite-dimensional Hilbert space, finite observables, sequential products of observables and the conditioned observable (B|A)_y=Σ_x A_x∘B_y, introduces uniform attenuation (Condition (1)) and conditional randomness (Condition (2)) of two observables, proves that Condition (1) implies Condition (2) and that the two are equivalent for sharp observables, and states that it does not know whether the converse of Theorem 2.1(i) or (ii) holds."
strata_touched:
  - D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation
license: citation-only
triage: anchor
---

# Mutually Unbiased Quantum Observables

S. Gudder, arXiv:2110.03099v1 (only version). Quotations are from the v1 TeX source; displayed macros are expanded without changing the wording.

Effects and the sequential product (Section 1):

> if $0\le A\le I$ where $0,I$ are the zero and identity operators, respectively, we call $A$ an *effect*

> For $A,B\in\mathcal E (H)$ we define their *sequential product* by $A\circ B=A^{1/2}BA^{1/2}$, where $A^{1/2}$ is the unique positive square-root of $A$

Observables and conditioning:

> An *observable* for a quantum system is represented by a finite set of effects $A=\{A_x\colon x\in\Omega _A\}\subseteq\mathcal E (H)$ where $\Omega _A$ is a finite set called the *outcome space* for $A$ and $\sum _{x\in\Omega _A}A_x=I$.

> We also define the observable $B$ *conditioned* by the observable $A$ to have outcome space $\Omega _B$ and to be given by $(B\mid A)_y=\sum _{x\in\Omega _A}A_x\circ B_y=\sum _{x\in\Omega _A}A\circ B_{(x,y)}$

The two conditions (Section 2), for observables with $|\Omega_A|=m$ and $|\Omega_B|=n$:

> Condition (1) is shorthand for $A_x\circ B_y=\tfrac{1}{n}\,A_x$ and $B_y\circ A_x=\tfrac{1}{m}B_y$ for all $x\in\Omega _A$, $y\in\Omega _B$ and Condition (2) is shorthand for $(B\mid A)_y=\tfrac{1}{n}\,I$ and $(A\mid B)_x=\tfrac{1}{m}\,I$ for all $x\in\Omega _A$, $y\in\Omega _B$.

Theorem 2.1:

> (i) Condition (1) implies Condition (2). (ii) If $A$ and $B$ are sharp, then Condition (1) and Condition (2) are equivalent.

The question (PDF p. 6):

> We do not know whether the converse of Theorem 2.1(i) or (ii) holds.

## Verified locator

Source: https://arxiv.org/abs/2110.03099v1
- URL: https://arxiv.org/abs/2110.03099v1 (the e-print is a single gzip file whose header names `MutualUnbiasedQO.tex`; md5 `ea23a0dd97764fa2b7444408b910866f`, 576 lines):
  - effects, sequential products, observables and conditioned observables, l. 95–124;
  - Conditions (1) and (2), l. 174–182;
  - Theorem 2.1, l. 184–188;
  - the question, l. 223.
- DOI: 10.48550/arXiv.2110.03099 (https://doi.org/10.48550/arXiv.2110.03099; DataCite lists this arXiv-issued DOI with creator Gudder, Stan, 2021). The arXiv record lists no journal reference and no publisher DOI.

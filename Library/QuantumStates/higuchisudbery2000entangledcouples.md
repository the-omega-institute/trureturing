---
bibkey: higuchisudbery2000entangledcouples
authors: A. Higuchi; A. Sudbery
year: 2000
title: "How entangled can two couples get?"
doi: 10.1016/S0375-9601(00)00506-4
url: https://arxiv.org/abs/quant-ph/0005013
claim: "Four-qubit marginal entropy: the Higuchi–Sudbery candidate, its known restrictions, and the unrestricted maximum question."
strata_touched:
  - D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1016/S0375-9601(00)00506-4

Source: https://arxiv.org/abs/quant-ph/0005013

# How entangled can two couples get?

## The average two-qubit entropy

Section 3, p. 5:

> Given that a four-qubit state cannot have maximal entropy of entanglement for every two-qubit subset, we now ask what is the greatest possible average for such entropies, i.e. we seek to maximise

$$\langle E_2\rangle=\frac16(E_{AB}+E_{AC}+E_{AD}+E_{BC}+E_{BD}+E_{CD})=\frac13(E_{AB}+E_{AC}+E_{AD}).$$

> The second equality holds because complementary pairs have equal entropy.

> We have not been able to solve this problem analytically. We will adopt a heuristic approach, using an (indefensible) analogy with the two-qubit system to obtain a candidate maximally entangled state and then showing that $\langle E_2\rangle$ is indeed stationary at this state and appears to be maximal.

The explicit candidate on p. 5 is

$$|M_4\rangle=\frac1{\sqrt6}\bigl[|0011\rangle+|1100\rangle+\omega(|1010\rangle+|0101\rangle)+\omega^2(|1001\rangle+|0110\rangle)\bigr],\qquad\omega=e^{2\pi i/3}.$$

Section 3, p. 6:

> Hence the entanglement entropies are

$$E_{AB}=E_{AC}=E_{AD}=1+\frac12\log_2 3.$$

Section 3, p. 7:

> We have searched numerically for states which maximise $\langle E_2\rangle$ starting from several arbitrarily chosen states. All the states we have obtained in this manner are locally equivalent to $|M_4\rangle$ or $|\overline M_4\rangle$.

The amplitude index is $8a+4b+2c+d$ for the ordered qubits $A,B,C,D$. The three literal flattenings retain $AB$, $AC$, and $AD$, respectively. The entropy is the repository's von Neumann entropy in natural logarithms divided by $\log 2$.

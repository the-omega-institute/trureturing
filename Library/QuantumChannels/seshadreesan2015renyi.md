---
bibkey: seshadreesan2015renyi
authors: K. P. Seshadreesan, M. Berta, M. M. Wilde
year: 2015
title: "Rényi squashed entanglement, discord, and relative entropy differences"
doi: 10.1088/1751-8113/48/39/395303
url: https://arxiv.org/abs/1410.1443v3
claim: "Conjecture 1 The Rényi conditional quantum mutual information obeys monotonicity with respect to CPTP maps on system A, i.e., for ρABE ∈ S(HABE) and α ∈ (0, 1) ∪ (1, 2], Iα(A; B|E)ρ ≥ Iα(A′; B|E)τ, where τA′BE ≡ MA→A′(ρABE) and MA→A′ is a CPTP map acting on system A alone."
strata_touched:
  - D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/1410.1443v3>.

- DOI: https://doi.org/10.1088/1751-8113/48/39/395303

*J. Phys. A: Math. Theor.* 48 (2015) 395303, §3, equation (3.18):

> Throughout this paper, we take our definition of Rényi conditional quantum mutual information for α ∈ (0, 1) ∪ (1, ∞) to be as follows [BSW15a, Definition 7]:

$$
I_\alpha(A;B|E)_\rho = \frac{\alpha}{\alpha-1}\log \operatorname{Tr}\Big\{\big(\rho_E^{(\alpha-1)/2}\operatorname{Tr}_A\{\rho_{AE}^{(1-\alpha)/2}\rho_{ABE}^{\alpha}\rho_{AE}^{(1-\alpha)/2}\}\rho_E^{(\alpha-1)/2}\big)^{1/\alpha}\Big\}
$$

§3, introduction to Conjecture 1:

> Some results in this paper rely on the following conjecture:

§3, Conjecture 1:

> Conjecture 1 The Rényi conditional quantum mutual information obeys monotonicity with respect to CPTP maps on system A, i.e., for ρABE ∈ S(HABE) and α ∈ (0, 1) ∪ (1, 2], Iα(A; B|E)ρ ≥ Iα(A′; B|E)τ, where τA′BE ≡ MA→A′(ρABE) and MA→A′ is a CPTP map acting on system A alone.

§2, discussion of local quantum operations:

> it was left as an open question to determine if the property holds for local quantum operations on the other system (with numerical evidence supporting a positive answer). Here, we assume the latter to hold.

## Mathematical scope

The definition is equation (3.18), with generalized inverse powers on the support.
Conjecture 1 concerns channels on $A$ for $0<\alpha<1$ and $1<\alpha\le2$.
The finite-dimensional reading uses positive semidefinite trace-one matrices and
finite Kraus families with $\sum_j K_j^\dagger K_j=1$.
The settlement fixes three qubits, a faithful state with classical $B$, complete
dephasing of $A$, and $\alpha=2$. It does not concern monotonicity on $B$.

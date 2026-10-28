---
bibkey: ballesterosetal2025qsymmetric
authors: Angel Ballesteros; Ivan Gutierrez-Sagredo; Jose de Ramón; J. Javier Relancio
year: 2025
title: "Deformations of the symmetric subspace of qubit chains"
doi: 10.1088/1751-8121/ae05da
url: https://arxiv.org/abs/2503.23554v3
claim: "The paper defines the q-symmetric subspace of an N-qubit chain through the coproduct of the quantum group U_q(su(2)), constructs q-Dicke states, and in its applications section conjectures that, as it asserts for two qubits, the closest product state to an arbitrary q-Dicke state in the geometric measure of entanglement is q-symmetric."
strata_touched:
  - D5/S3/Quantum/Entanglement/GeometricMeasure/QDickeClosestProductRefutation
license: citation-only
triage: anchor
---

# Deformations of the symmetric subspace of qubit chains

A. Ballesteros, I. Gutierrez-Sagredo, J. de Ramón and J. J. Relancio, arXiv:2503.23554v3 (11 March 2026; first version 30 March 2025); J. Phys. A 58(40) (2025), 405301. Quotations are from the v3 TeX source, with the macros `\up` and `\down` written as $\uparrow$ and $\downarrow$.

The q-number:

> $[x]_q=\frac{q^{\frac{x}{2}}-q^{-\frac{x}{2}}}{q^{\frac{1}{2}}-q^{-\frac{1}{2}}}.$

The q-symmetric subspace:

> Similar to the case of the symmetric group, we define the $q$-symmetric subspace $\text{Sym}_q \, \mathcal{H}$ as the subspace carrying the trivial representation of the Hecke algebra.

The q-Dicke states for three qubits (Example `ex:qDickeN3`), with $\ket{G}=\ket{D^0_3}_q=\ket{\downarrow\downarrow\downarrow}$:

> $\ket{D^1_3 }_q=\frac{1}{\sqrt{ {[3]_q}}}\left( q^{1/2}|\downarrow\downarrow\uparrow\rangle +|\downarrow\uparrow\downarrow\rangle+ q^{-1/2}|\uparrow\downarrow\downarrow\rangle\right)$, $\ket{D^2_3 }_q=\frac{1}{\sqrt{ {[3]_q}}}\left( q^{1/2} |\downarrow\uparrow\uparrow\rangle +|\uparrow\downarrow\uparrow\rangle + q^{-1/2}|\uparrow\uparrow\downarrow\rangle \right)$, $\ket{D^3_3 }_q= \ket{\uparrow\uparrow\uparrow}$, and thus $\mathrm{Sym}_q \, \mathcal{H} = \text{span } \{ \ket{D_3^0}_q, \ket{D_3^1}_q, \ket{D_3^2}_q, \ket{D_3^3}_q \}$.

The geometric measure of entanglement:

> $G[\ket{\Psi}]=\underset{\{\phi_i\}}{\text{max}}|\!\braket{\Psi|\{\phi_i\}}\!|$ where $\ket{\{\phi_i\}}=\ket{\phi_1}...\ket{\phi_N}$ are product states.

The conjecture:

> Therefore, the closest separable state to a $q$-symmetric state for two qubits is also $q$-symmetric. If we conjecture that a similar relation holds for arbitrary $q$-Dicke states, it would mean that we can construct whole new families of states whose multipartite entanglement has an analytic expression.

## Verified locator

Source: https://arxiv.org/abs/2503.23554v3
- URL: https://arxiv.org/abs/2503.23554v3 (the e-print is a tar archive; member `newsubmission__1_.tex`, md5 `18fa3b609df74e7f0e866cc4ee871711`, 1495 lines):
  - the q-number, l. 469;
  - the q-symmetric subspace, l. 532–535;
  - the three-qubit q-Dicke states and their span, l. 579–586;
  - the geometric measure of entanglement, l. 1232–1243;
  - the two-qubit discussion and the conjecture, l. 1249–1258.
- DOI: 10.1088/1751-8121/ae05da (https://doi.org/10.1088/1751-8121/ae05da; Crossref lists Journal of Physics A: Mathematical and Theoretical, volume 58, issue 40, published 30 September 2025).

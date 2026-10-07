---
slug: qian-wang-2025-separable-states-stab-local-unitaries
bibkey: qian2025nonlocalnonstabilizerness
doi: 10.1103/PhysRevA.111.052443
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction.result
---

## Problem

Qian and Wang, *Quantum non-local nonstabilizerness*, arXiv:2502.06393v4, Appendix F, conjecture that some separable multi-qubit states cannot be transformed into `STAB` using only local unitary transformations. Their statement is that they are unaware of a proof that every separable state can be so transformed and conjecture that this is false.

The settled two-qubit claim is the preregistered QW-F statement from GitHub issue #14115: for real parameters $0 < p < 1$, $c > 0$, $s > 0$, $c^2+s^2=1$, and $c^2 \ne 1/2$, let $b=c|0\rangle+s|1\rangle$ and
$$
\rho=p|00\rangle\langle00|+(1-p)|bb\rangle\langle bb|.
$$
Then no $U_A\otimes U_B$ with single-qubit local unitaries sends $\rho$ into the full convex stabilizer hull `STAB`.

## Motivation

The source defines separable states as convex hulls of pure product states and `STAB` as the convex hull of pure stabilizer states. Appendix F gives the example
$$
\rho_0=\tfrac12|\phi_0\phi_0\rangle\langle\phi_0\phi_0|+\tfrac12|00\rangle\langle00|,
\qquad
|\phi_0\rangle=\cos(\pi/8)|0\rangle+\sin(\pi/8)|1\rangle.
$$
Issue #14115 records the exact QW-F family, the binding Lean conventions, and the preregistered route.

## Gap

The source leaves open whether every separable state is locally unitarily equivalent to a state in `STAB`. The settlement proves an infinite rank-two family outside every local-unitary stabilizer frame. It does not settle higher-rank states, more than two qubits, or qudits, and it does not certify the source's numerical robustness value.

## Route

The Lean module defines literal signed Hermitian two-qubit Pauli products, normalized pure stabilizer vectors fixed by two independent commuting generators, the real convex hull `STAB`, local-unitary conjugation, product-state projectors, separability, and the preregistered claim. The settling theorem
`D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.result`
uses the family theorem on its live proof path.

The decisive mechanism is rank-two support rigidity. The range of $\rho$ has exactly two product rays, $u=|00\rangle$ and $v=|bb\rangle$, and its only maximally entangled ray is proportional to $(v-u)/(\sqrt{2}s)$. Product vectors and maximal entanglement are preserved by local unitaries. After the stabilizer classification, every positive-weight stabilizer vector in a pulled-back ensemble is therefore one of the two product rays; positivity forces both rays to occur. Their single-qubit squared overlap is $c^2$, while Pauli eigenprojectors have overlap spectrum $\{0,1/2,1\}$, giving the contradiction under $c^2\ne1/2$.

## Falsifier

An exact pair of local unitaries and a valid `STAB` ensemble for one parameter triple satisfying the QW-F hypotheses would refute the corresponding universal nonmembership statement. An exact proof that every separable state has a local-unitary representative in `STAB` would refute the source's conjecture. A numerical robustness value without an exact certificate is not a falsifier.

## Evidence

The sole public settling theorem is `result : claim`. Its private `family_result : FamilyClaim` proves the full parameter family and is consumed by `result`. The axiom closure of every public declaration is contained in $\{\text{propext},\ \text{Classical.choice},\ \text{Quot.sound}\}$; the module has no `sorry`. The Scribe result node is attached to this dossier with `OpenProblemResolutionClaim` of kind `Proved`. The Library note `qian2025nonlocalnonstabilizerness` records the DOI, arXiv locator, Appendix F conjecture, the separable and `STAB` definitions, and the $\rho_0$ example.

## Triage

### What the settlement shows

- **Proved — mechanism:** Rank-two support rigidity gives exactly the product rays $u$ and $v$ and the sole maximally entangled ray proportional to $(v-u)/(\sqrt{2}s)$; single-qubit Pauli eigenstates have overlap spectrum $\{0,1/2,1\}$. Evidence kind: kernel-checked declaration `result` and its live family proof, with the paper argument stated in the Route.
- **Proved — authors' $\rho_0$:** With $p=1/2$, $c=\cos(\pi/8)$, and $s=\sin(\pi/8)$, the half-angle identity gives $c^2=(2+\sqrt2)/4\ne1/2$ and $c,s>0$. The identity $\cos^2(\pi/8)+\sin^2(\pi/8)=1$ supplies the remaining parameter condition, so the family theorem covers the authors' state. Evidence kind: paper specialization of the kernel-checked private `family_result`; no separate Lean trigonometric instance is delivered.
- **Proved — boundary $c^2=1/2$:** Taking $c=s=1/\sqrt2$ gives $b=|+\rangle$, so $\rho$ is already a convex mixture of the product stabilizer projectors $|00\rangle\langle00|$ and $|++\rangle\langle++|$; the identity local unitary suffices. Evidence kind: paper argument from the source definitions. The strict family obstruction intentionally excludes this boundary.
- **Proved — strict positivity of LU-minimized robustness:** The local-unitary group is compact, and its orbit is the continuous image of that group. There are finitely many pure two-qubit stabilizer projectors, so their convex hull `STAB` is compact. The family nonmembership theorem makes these compact sets disjoint, hence their trace-norm distance has a strictly positive minimum $\delta$. In any signed stabilizer decomposition of an orbit state with total negative weight $t$, write $\rho=(1+t)\sigma_+-t\sigma_-$ with $\sigma_+,\sigma_-\in\mathrm{STAB}$ when $t>0$. Then $\|\rho-\sigma_+\|_1=t\|\sigma_+-\sigma_-\|_1\le2t$, so $t\ge\delta/2$. The stabilizer robustness, whose coefficient norm is $1+2t$, is therefore uniformly greater than one on the orbit, and its logarithmic magic measure is strictly positive. Evidence kind: paper corollary of `family_result`, compactness, and the signed-ensemble norm estimate; no Lean robustness theorem is delivered.
- **Open — numerical robustness certification:** The source's reported LU-minimized value $0.0703$ is not certified here. Evidence kind: literature reading in Appendix F; no exact optimization certificate is delivered.
- **Open — higher rank, more qubits, and qudits:** The result is rank two for two qubits and supplies no uniform extension to higher rank, additional qubits, or qudit systems. Evidence kind: open boundary of the kernel-checked statement.

The settlement supplies an explicit infinite family witnessing the source's conjectured failure of universal local-unitary reachability. It leaves the neighboring higher-dimensional and robustness-certification questions open.

Appendix F's numerical example is consequently a member of a proved obstruction family. The settlement verifies the qualitative conclusion supported there by numerical evidence; it makes no additional claim about the source's other quantitative results or about exact robustness minimizers.

## ASSUMED-UNVERIFIED

Literature coverage is bounded by Qian–Wang (arXiv:2502.06393v4; Physical Review A 111, 052443 (2025)) and the preregistration issue #14115. Information-escape registration is paused under CLAUDE.md section 3.9.

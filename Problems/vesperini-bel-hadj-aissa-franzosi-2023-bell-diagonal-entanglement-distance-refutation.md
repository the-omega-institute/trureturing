---
slug: vesperini-bel-hadj-aissa-franzosi-2023-bell-diagonal-entanglement-distance-refutation
bibkey: vesperinibelhadjaissafranzosi2023entanglement
doi: 10.1038/s41598-023-29438-7
url: https://arxiv.org/abs/2205.07143v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.result
---

# Bell-diagonal entanglement distance is not twice the squared concurrence

## Problem

A. Vesperini, G. Bel-Hadj-Aissa and R. Franzosi, *Entanglement and Quantum Correlation Measures from a Minimum Distance Principle*, arXiv:2205.07143v2; published as *Entanglement and quantum correlation measures for quantum multipartite mixed states*, Sci. Rep. 13, 2852 (2023), DOI 10.1038/s41598-023-29438-7. In Applications, “Bell diagonal states”, the v2 source `QCDED-V4.tex`, line 368, states:

> We were not able to find a simple analytic solution of the minimization procedure for the most general case of BD states. However, numerical minimization provided us with empirical evidence that the procedure (22) also leads for these states to the squared concurrence, as shown in figure \ref{figBD_ED}, which represent a face of the tetrahedral domain of BD states.

This is a reported numerical belief, rather than a proved identity. The source read is the arXiv v2 TeX, MD5 `232776c9cef202cc624a80958cb4c818`. Its figure caption at line 372 plots $E[\rho_{BD}]/2$; the Werner-state formula at lines 396–400 is described as “twice the square of the concurrence”. These fix the factor-two reading registered in issue [#20089](https://github.com/the-omega-institute/trureturing/issues/20089).

Let $B_0,B_1,B_2,B_3$ be the projectors onto $(|00\rangle+|11\rangle)/\sqrt2$, $(|00\rangle-|11\rangle)/\sqrt2$, $(|01\rangle+|10\rangle)/\sqrt2$ and $(|01\rangle-|10\rangle)/\sqrt2$, respectively. For $p_\alpha\ge0$ and $\sum_{\alpha=0}^3p_\alpha=1$, put $\rho_{BD}(p)=\sum_\alpha p_\alpha B_\alpha$ and $c(p)=\max(0,2\max_\alpha p_\alpha-1)$. Here $c$ denotes Bell-diagonal concurrence; $C_\mu$ below denotes site quantum correlation distance (QCD).

The registered claim is that $E(\rho_{BD}(p))=2c(p)^2$ for every such probability vector, where $E$ minimizes the site QCD of locally rotated mixtures over all finite density-matrix decompositions and component-dependent local rotations, summing both sites. This claim is refuted.

## Motivation

The source proposes the regularization of QCD as a measure of mixed-state entanglement. Bell-diagonal states provide an explicit test family: concurrence depends only on the largest Bell weight, whereas the proposed ED involves an optimization over decompositions and rotations. Agreement would identify that optimization with a familiar entanglement quantity. A counterexample tests whether component-dependent rotations preserve the entanglement information that the regularization is intended to extract.

The definitions and source locators are collected in [the literature note](../Library/QuantumContext/vesperinibelhadjaissafranzosi2023entanglement.md).

## Gap

Issue #20089 records the bounded literature check before any Lean:

- The orchestrator checked the arXiv v2 source and the 2023 journal HTML and reported that both retain the numerical claim.
- The orchestrator checked the later authors' paper by Vesperini, Bel-Hadj-Aissa, Capra and Franzosi, arXiv:2307.16835, Front. Phys. 19, 51204 (2024), and recorded no Bell-diagonal derivation there.
- Semantic Scholar listed 24 citing works. Inspection of the accessible citing works found no correction or counterexample; this inspection is search-seat-reported in the issue. One 2026 citing paper was unreadable.
- The orchestrator's web and repository searches found no correction, counterexample or existing repository record.

`not-found-in-searched-scope`. This is a bounded search result, not an exhaustive novelty claim.

## Route

1. **The state and a different decomposition.** Take $p=(16/25,9/25,0,0)$. Define $q_\pm=(7\pm24i)/25$ and $P_\pm=|v_\pm\rangle\langle v_\pm|$, where $|v_\pm\rangle=(|00\rangle+q_\pm|11\rangle)/\sqrt2$. The proof checks that $P_\pm$ are positive semidefinite with trace one and that $\rho_{BD}(p)=(P_++P_-)/2$. Its only nonzero entries are $\rho_{00,00}=\rho_{11,11}=1/2$ and $\rho_{00,11}=\rho_{11,00}=7/50$.
2. **The rotations.** Use $U_1=\operatorname{diag}((4+3i)/5,(4-3i)/5)$ on $P_+$ and $U_2=\operatorname{diag}((3+4i)/5,(3-4i)/5)$ on $P_-$. Both matrices are certified members of $SU(2)$. On either chosen site they send the respective projectors to $B_0$ and $B_1$, so the rotated mixture is $\chi=\operatorname{diag}(1/2,0,0,1/2)$.
3. **The site supremum.** For either site, $\operatorname{Re}\operatorname{tr}(\chi^2)=1/2$ and $\operatorname{Re}\operatorname{tr}(\chi H_\mu(n)\chi H_\mu(n))=n_z^2/2$, where $H_\mu(n)=\sum_i n_i\sigma_i^\mu$. On the real unit sphere the quadratic form is at most $1/2$ and attains $1/2$ at $n=(0,0,1)$. The proof supplies both nonemptiness and an upper bound for this supremum, obtaining $C_\mu(\chi)=0$.
4. **The contradiction.** Each inner infimum has an actual zero-valued rotation candidate. The outer infimum has the displayed admissible two-component decomposition. The private helper `ed_witness_le_zero` obtains $E(\rho_{BD}(p))\le0$ through `Real.sInf_nonpos'`. But $c(p)=7/25$, so the claimed equality would require $E(\rho_{BD}(p))=98/625>0$. The public theorem is `result : ¬ claim`.

## Falsifier

The correspondence with the source is part of the reading being settled:

- `onSite` places a two-dimensional matrix on the selected factor of the two-qubit product basis; `sitePauli` selects the existing $X,Y,Z$ Pauli matrices. `siteQCD` is $\operatorname{Re}\operatorname{tr}(\sigma^2)$ minus the supremum of $\operatorname{Re}\operatorname{tr}(\sigma H_\mu(n)\sigma H_\mu(n))$ over real unit vectors $n$.
- `rotated` conjugates each ensemble component by its own local $SU(2)$ matrix and then averages. `ED` takes an outer infimum over finite ensembles with nonnegative weights summing to one, positive semidefinite trace-one components, and exact reconstruction of the input. For that same ensemble it sums two independent inner infima, one for each site. It does not average the QCD values of the individual components and does not impose the Bell eigen-decomposition.
- The source's site-QCD and regularization formulas are at TeX lines 207–231 and 242–269. The printed ED sum starts at $\mu=1$, although sites elsewhere run from $0$ to $M-1$. The module includes both sites to match the figure's $E/2$ and the twice-squared-concurrence normalization. Both rotated site QCDs vanish in the certificate; the same certificate therefore also obstructs a positive squared-concurrence formula with only one site, as an unformalized consequence.
- The Bell-projector order and the probability hypotheses are exactly those used by `claim`. The input components $P_\pm$ are pure; restricting decompositions to pure states does not exclude this certificate.

The infimum argument has a specific scope. The proof establishes nonemptiness of the inner and outer sets used at the witness. It does not use an unrestricted rule that a real `sInf` is below every member without a lower-boundedness hypothesis. Instead, `Real.sInf_nonpos'` gives the required nonpositive bound from a nonpositive member, including the mathlib convention that the real infimum of a set unbounded below is zero. The module does not prove a global lower bound for ED, its exact value at this witness, or existence of minimizers for arbitrary states. Those statements must not be read into `result`.

## Evidence

The canonical source is `D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.lean` (295 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/EntanglementDistanceBellDiagonalRefutation.lean.json`, statement `sha256:5829ec9444b870fb4cb20dd368bd1210c619e999658e7fcb840abea615336c3e`.

Declaration statements:

- `result`: `sha256:b049060fa3faaf39d873d43fde21f741d18e1bc80d84c84b930f6673ef4440b7`;
- `claim`: `sha256:0b132b00244834779d02f181f9009ab93a2ec420f11d94549fb97178a85e3f8c`.

## Triage

Tier 1: a published numerical belief of a 2022 preprint and 2023 journal paper, preregistered in issue #20089 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed, and the per-declaration proof shapes are listed in the delivery PR. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that every nonnegative probability vector on the four specified Bell projectors, with weights summing to one, satisfies $E(\rho_{BD}(p))=2c(p)^2$ for the module's ED and concurrence definitions.

**Computed, not formalized** (exact rational and complex arithmetic, SymPy 1.14.0):

- The matrices at $p=(16/25,9/25,0,0)$ reproduce the Bell-diagonal identity, the two special-unitary certificates, both rotated mixtures, and $A^\mu(\chi)=\operatorname{diag}(0,0,1/2)$. These are independent computations of identities also used by the Lean proof.
- The eigenvalues of $\rho(\sigma_y\otimes\sigma_y)\overline{\rho}(\sigma_y\otimes\sigma_y)$ are $256/625,81/625,0,0$, whose square roots have difference $16/25-9/25=7/25$, agreeing with the defined concurrence. The partial-transpose eigenvalues are $1/2,1/2,7/50,-7/50$.
- The unrotated witness has $\operatorname{tr}(\rho^2)=337/625$ and $A^\mu(\rho)=\operatorname{diag}(0,0,288/625)$ on both sites. Its total QCD is consequently $98/625$.
- For a separate tested example, the equal-weight ensemble with both components equal to $B_0$ becomes $\chi$ on either site when its components are rotated by $I$ and $i\sigma_z$, respectively. This calculation evaluates the displayed candidate, not an infimum over all ensembles.

**Argued, not formalized.**

- *Mechanism.* The optimization permits different rotations of different components before averaging. Such an operation can erase the phase coherence of the mixture even when every component remains entangled. It is not a single unitary conjugation of the input state. The certified decomposition uses distinct, nonorthogonal pure components, so neither purity of components nor exclusion of repeated components alone repairs the conjecture. Restricting to the spectral decomposition would remove this particular decomposition, but would change the optimization; correctness of the corresponding restricted identity remains open here.
- *Lower bounds for the ordinary infima.* For Hermitian $\sigma$ and a Hermitian involution $H$, expanding the Hilbert–Schmidt norm gives $\operatorname{tr}(\sigma^2)-\operatorname{Re}\operatorname{tr}(\sigma H\sigma H)=\tfrac12\|[\sigma,H]\|_{HS}^2\ge0$. A unit Pauli direction gives such an $H$. Its quadratic form is continuous on the nonempty compact unit sphere, so the site supremum is finite and $C_\mu(\sigma)\ge0$. Every admissible rotated density matrix is Hermitian. Identity rotations make each inner set nonempty, and every site-QCD value is nonnegative, so each inner infimum is nonnegative. A density matrix has the singleton decomposition, making the outer set nonempty; all outer objective values are nonnegative. This supplies ordinary lower-boundedness and $E(\rho)\ge0$ for two-qubit density matrices, by an argument not present as a Lean theorem in this module.
- *A broader degeneracy under the admitted ensembles.* Repeated components are allowed by `ED`. For any two-qubit density matrix $\rho$, choose $\rho_1=\rho_2=\rho$ with weights $1/2$, and choose rotations $I$ and $i\sigma_z\in SU(2)$ on site $\mu$. The rotated mixture is $D_\mu(\rho)=(\rho+\sigma_z^\mu\rho\sigma_z^\mu)/2$. It commutes with $\sigma_z^\mu$, so the $z$ direction attains $\operatorname{tr}(D_\mu(\rho)^2)$ in the site supremum. The preceding upper bound on that supremum gives $C_\mu(D_\mu(\rho))=0$. The same ensemble works for both independent site optimizations. Thus there is a zero objective, and the preceding nonnegativity argument yields $E(\rho)=0$ for every two-qubit density matrix under these unrestricted ensembles. This is a full algebraic argument, not the type or an additional consequence formally certified by `result`.
- *Nearby statements.* Vanishing site QCD for a state commuting with a local Pauli observable survives by the same calculation. The implication from separability to vanishing ED also survives under the unrestricted ensembles, but gives no distinction from entangled inputs. The separately defined pure-state measure of the source is not the mixed-state optimization checked by this module. Whether a different optimization with additional restrictions recovers concurrence requires a separate statement and proof.
- *Effect on the source.* At TeX line 368 the paper states that “the ED of any given state indeed equates the QCD of the closest point located on a hinge of $\mathcal{T}$, hence the closest mixture of only two Bell states.” The witness already is a two-Bell mixture; its positive unrotated QCD and nonpositive ED obstruct that identification for the unrestricted optimization. The source also states at line 279, “Reciprocally, if $E(\rho) =0$, then $\rho$ is separable.” Combining the unformalized nonnegativity argument with the certificate gives zero ED at the witness, while the computed negative partial-transpose eigenvalue excludes separability: a separable state's partial transpose is a sum of positive semidefinite transposed product states. Thus that converse is also contradicted at the level of this algebraic argument. The formal theorem alone does not settle the Werner subfamily. The broader repeated-component argument gives zero there as well, so under the same unrestricted ensembles it conflicts with the positive values of the source's $E(\rho_W(p))=2\Theta(1/2-p)(1-2p)^2$ at $0\le p<1/2$ (lines 396–400). The original QCD definition and the separate pure-state definition do not rely on the Bell-diagonal equality; their remaining assertions are not settled by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The journal HTML, the later authors' paper arXiv:2307.16835, the accessible citing works, and the web and repository searches are readings reported in #20089 and are not independently reproduced here. The issue identifies Han, Xing, Wu, Li and Huang, Physica A (2026), DOI 10.1016/j.physa.2026.131831, as unreadable; no conclusion about its contents is available. The source text directly checked for this dossier is arXiv:2205.07143v2, not a separate verification of the journal version.

All claims in “Computed, not formalized” and “Argued, not formalized” carry those limits. In particular, global ED nonnegativity, the exact value zero at the witness, universal vanishing under repeated-component ensembles, and the consequences for faithfulness, the hinge description and the Werner formula are not additional Lean results. The calculations do not evaluate the full optimization or establish a numerical statement for untested families. The interpretation of the printed site-index discrepancy, the separately modified one-site claim, and the finite-ensemble versus more general ensemble correspondence are not formalized. The displayed finite certificate is admissible in the finite optimization and in any extension retaining it, but no such extension is a compiled declaration here. A successful repair of the conjecture by restricting the admissible decompositions or rotations remains open here.

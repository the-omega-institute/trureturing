---
slug: song-li-2022-dequantumness-power-strict-gap
bibkey: songli2022dequantumness
doi: 10.3390/e24081146
url: https://europepmc.org/article/PMC/PMC9407519
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/DequantumnessPowerStrictGap.result
---

# Unrestricted two-state dequantumness power can exceed its maximal-quantumness restriction

## Problem

H. Song and N. Li, *Quantumness and Dequantumness Power of Quantum Channels*, Entropy 24(8), 1146 (2022), DOI [10.3390/e24081146](https://doi.org/10.3390/e24081146), Section 3, page 5 of the [publisher PDF](https://mdpi-res.com/d_attachment/entropy/entropy-24-01146/article_deploy/entropy-24-01146.pdf), in the paragraph following the amplitude-damping calculation:

> Though $D_2(\Lambda)=D_2'(\Lambda)$ in this case, we conjecture this equality may fail in certain cases. But we have not found the counterexample satisfying $D_2(\Lambda)>D_2'(\Lambda)$ yet.

For a two-state qubit ensemble $\mathcal E=\{(p,\rho),(1-p,\sigma)\}$, let $p\in[0,1]$ and let $\rho,\sigma$ be positive semidefinite complex two-by-two matrices of trace one. Equation (1), on page 2, specializes to

$$Q(\mathcal E)=-\sum_{i,j=1}^2p_ip_j\operatorname{tr}[\rho_i,\rho_j]^2.$$

In the module, `quantumness` takes the real part of each trace. With all suprema below over these two-state ensembles, its definitions are

$$Q_{\max,2}=\sup_{\mathcal E}Q(\mathcal E),\qquad D_2(\Lambda)=\sup_{\mathcal E}\bigl(Q(\mathcal E)-Q(\Lambda(\mathcal E))\bigr),$$

$$D_2'(\Lambda)=\sup_{\mathcal E:\,Q(\mathcal E)=Q_{\max,2}}\bigl(Q(\mathcal E)-Q(\Lambda(\mathcal E))\bigr).$$

This is the two-ingredient reading used in the source's page-5 calculation, where the maximal initial quantumness is $1/4$; it does not optimize over ensembles of arbitrary size. The definitions and source locations are also given in [the literature note](../Library/Entropy/songli2022dequantumness.md).

Issue [#22778](https://github.com/the-omega-institute/trureturing/issues/22778) fixes `claim` as universal equality: every completely positive trace-preserving complex-linear qubit map satisfies $D_2=D_2'$. The resolution `refuted` negates that equality claim and supplies the strict separation sought by the authors; it confirms their quoted conjecture.

## Motivation

The restriction defining $D_2'$ simplifies optimization by selecting inputs with the greatest initial quantumness. Equality with $D_2$ would justify that simplification for every qubit channel. A strict separation means that an input with slightly less quantumness can lose more quantumness under the same channel.

## Gap

The bounded literature check recorded in #22778 reports:

- the GPT Pro search ask found no settlement in title and conjecture-wording searches on Zenodo, ResearchGate, SSRN and GitHub;
- the orchestrator's issue and repository searches found no existing treatment of this functional; `CoPRelativeQuantumnessRefutation` concerns a different functional.

The publisher PDF retains the quoted question. An independent exact-title arXiv API query returned zero records; no versioned arXiv identifier was located.

`not-found-in-searched-scope`.

## Route

Write $B(r)=(I+r\cdot\boldsymbol\sigma)/2$ for the Bloch matrix of a real three-vector, and set

$$\Lambda_*(X)=\frac12X+\frac12\operatorname{tr}(X)\operatorname{diag}(3/4,1/4),\qquad f(r)=\frac12r+\frac14e_z.$$

The following are private lemmas on the proof path of `result`.

1. **Ensembles and Bloch coordinates.** `two_state_ensemble_iff`, for every real $p$ and every pair of complex two-by-two matrices, identifies `IsEnsemble` with $0\le p\le1$ and both matrices being density matrices. `density_bloch`, for a qubit density matrix, supplies $\rho=B(r)$ with $r\cdot r\le1$. For every real $p$ and arbitrary real Bloch vectors $r,s$, `quantumness_bloch` gives $Q=p(1-p)\lVert r\times s\rVert^2$. `cross_bounds` requires $r\cdot r\le1$ and $s\cdot s\le1$; `quantumness_bounds` consequently gives $0\le Q\le1/4$ for every valid two-state ensemble.
2. **The restricted domain.** `maximizing_ensemble` constructs a valid equal-weight ensemble with $\rho=\operatorname{diag}(1,0)$ and $\sigma=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix}$ attaining $Q=1/4$. Together with the upper bound, this establishes nonemptiness and boundedness of the quantumness-value set, and `max_quantumness` gives $Q_{\max,2}=1/4$. `maximal_bloch` requires both a valid two-state ensemble and $Q=Q_{\max,2}$; it then supplies $p=1/2$, $r\cdot r=s\cdot s=1$ and $r\cdot s=0$.
3. **The channel.** `channel_cptp` certifies complete positivity of the fixed map $\Lambda_*$ by five Kraus matrices and verifies trace preservation. `channel_bloch`, for every real Bloch vector $r$, gives $\Lambda_*(B(r))=B(f(r))$.
4. **Restricted losses.** `orthonormal_cross_lower` requires real three-vectors satisfying $r\cdot r=s\cdot s=1$ and $r\cdot s=0$. For the fixed $f$ above it gives $\lVert f(r)\times f(s)\rVert^2\ge\tfrac14(\tfrac12-\tfrac{\sqrt2}{4})^2$, by projection onto the unit vector $r\times s$ and Cauchy–Schwarz. `restricted_loss`, requiring a valid ensemble and $Q=Q_{\max,2}$, therefore bounds its loss under $\Lambda_*$ by $U=(29+2\sqrt2)/128$.
5. **An unrestricted witness.** `witness_loss` constructs $p=1/2$ and

   $$\rho_\pm=\frac1{34}\begin{pmatrix}5&\pm\sqrt{145}\\\pm\sqrt{145}&29\end{pmatrix}.$$

   Their Hermitian, idempotent and trace-one certificates satisfy all hypotheses of `projection_density`. They form a valid ensemble whose loss under $\Lambda_*$ is $L=1329215/5345344$.
6. **The suprema and separation.** `power_lower` proves $L\le D_2(\Lambda_*)$: the witness contributes a loss value, and all unrestricted losses are bounded above by $1/4$, using the input bound and nonnegativity of output quantumness. `restricted_power_upper` proves $D_2'(\Lambda_*)\le U$; its restricted loss set is nonempty by `maximizing_ensemble` and `max_quantumness`, and every member is bounded by `restricted_loss`. `strict_comparison` gives $U<L$. Thus the fixed CPTP channel contradicts universal equality through $D_2'(\Lambda_*)\le U<L\le D_2(\Lambda_*)$.

## Falsifier

The refutation would not answer the source's question if it changed the functional, the admissible states or the maximal-quantumness restriction. `IsDensity` means positive semidefiniteness and trace one, `IsEnsemble` requires nonnegative normalized weights and such matrices, and `IsCPTP` requires complete positivity and trace preservation of a complex-linear map. The restriction is equality to `maxQuantumness`, not an assumed numerical threshold. The real-part convention agrees with the source on density matrices because their commutators are anti-Hermitian and the traces of their squares are real.

The source writes maxima, whereas the module uses real `sSup`; the ordinary compactness argument relating them is given below. The module also admits $p=0,1$, whereas the source's page-2 parametrization uses $p\in(0,1)$. At either endpoint both input and output quantumness are zero, so those endpoints cannot account for the positive separating witness or enter the maximal-quantumness domain.

## Evidence

The canonical source is `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumChannels/DequantumnessPowerStrictGap.lean.json`.

Declaration statements:

- `result`: `sha256:3aa9163832d4a8fab6fe377ef629381c2621e45ebdb0c272221a899cf7d8d89a`;
- `claim`: `sha256:ae6428ff2a9e708a4c348f36a82c292bf4bd44cc52ab67a67db804335474e02f`.

## Triage

Tier 1 conjecture of a 2022 Entropy paper, preregistered in issue #22778 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that every completely positive trace-preserving complex-linear qubit map has equal two-state dequantumness powers when optimized over all valid input ensembles and when restricted to ensembles of maximal initial quantumness.

**Computed, not formalized:** a floating-point evaluation of the witness loss by the dossier seat, and the random sample of orthonormal pure pairs recorded by the orchestrator in #22778, agree with the formal strict inequality.

**Argued, not formalized.**

- *Failure mechanism.* The witness has unit Bloch vectors $r_\pm=(\pm\sqrt{145}/17,0,-12/17)$ with $r_+\cdot r_-=-1/289$, and equal weights. Its initial quantumness is $(1-1/83521)/4$, slightly below the maximum. The channel's translation permits enough reduction of the output cross product to compensate for this initial deficit, as the fixed-channel bounds `restricted_power_upper`, `strict_comparison` and `power_lower` certify. Thus purity and equal weights alone do not make an input optimal for dequantumness power; the orthogonality requirement of the restricted domain excludes this witness.
- *Sharpness of the restricted bound.* Take equal weights and the orthonormal unit vectors $r=(1,0,-1)/\sqrt2$, $s=(-1,0,-1)/\sqrt2$. These give valid pure-state inputs with $Q=1/4$. Their output cross product has squared norm $\tfrac14(\tfrac12-\tfrac{\sqrt2}{4})^2$, so the loss is exactly $U$. Combined with the fixed-channel lemma `restricted_power_upper`, this supplies an argument for $D_2'(\Lambda_*)=U$. The module formalizes the upper bound, not this attainment argument or equality; it does not determine the exact value of $D_2(\Lambda_*)$.
- *A surviving equality case.* For a CPTP qubit map whose Bloch action is the homogeneous scalar contraction $r\mapsto ar$, with $|a|\le1$, the output cross product is $a^2(r\times s)$. Thus the loss is $(1-a^4)Q$, a nonnegative multiple of initial quantumness. Its maximum over all valid inputs is attained at equal weights and orthonormal unit Bloch vectors, so $D_2=D_2'=(1-a^4)/4$ in this case. This sufficient condition removes the translation used by the counterexample; no criterion for all affine channels follows from `result`.
- *Maxima and suprema.* The qubit density matrices form a compact set in finite-dimensional real matrix coordinates: positivity and the trace-one condition are closed, and the nonnegative eigenvalues summing to one give boundedness. With $p\in[0,1]$, the ensemble parameter space is compact, and quantumness and the loss under any fixed complex-linear map are continuous. The maximal-quantumness level set is closed and is nonempty by `maximizing_ensemble` and `max_quantumness`. Both loss suprema therefore have maximizing inputs on these domains. For $\Lambda_*$ the positive witness loss rules out an endpoint weight as an unrestricted maximizer, so the source's open-interval convention gives the same answer for this separation.
- *Effect on the paper.* The settlement supplies the example requested in the quoted conjecture. It does not contradict the source's separate amplitude-damping observation. No subsequent result in Sections 4–5 uses the strict-gap conjecture as a premise: the dynamical comparisons use quantumness directly. Those comparisons and the further questions in Section 5 are not settled by `result`.

## ASSUMED-UNVERIFIED

The literature search is bounded and does not establish exhaustive worldwide novelty or priority. The preregistration's reported external literature readings, settlement searches and historical repository-search readings were not independently reproduced. No arXiv record was found by the exact-title query; the front-matter URL identifies the verified journal full text.

The approximate numerical readings are not formalized, and the orchestrator's original eigenvalue-tolerance readings and random sample were not reproduced. The arguments about the mechanism, exact attainment of the restricted bound, homogeneous scalar contractions, compactness, endpoint conventions and consequences for the source are not additional Lean conclusions. The exact unrestricted power, a strict-gap criterion for other translated contractions, larger ensembles, higher dimensions and other quantumness measures are not determined by this module.

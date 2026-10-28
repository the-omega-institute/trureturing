---
slug: song-li-2022-dequantumness-power-strict-gap
bibkey: songli2022dequantumness
doi: 10.3390/e24081146
url: https://doi.org/10.3390/e24081146
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/DequantumnessPowerStrictGap.result
---

# Two-state dequantumness power can strictly exceed its maximal-quantumness restriction

## Problem

Hongting Song and Nan Li, *Quantumness and Dequantumness Power of Quantum Channels*, Entropy 24(8), 1146 (2022), DOI 10.3390/e24081146, Section 3, page 5, after Example 1:

> Though $D_2(\Lambda)=D'_2(\Lambda)$ in this case, we conjecture this equality may fail in certain cases. But we have not found the counterexample satisfying $D_2(\Lambda)>D'_2(\Lambda)$ yet.

This quotation is from the [published PDF](https://mdpi-res.com/d_attachment/entropy/entropy-24-01146/article_deploy/entropy-24-01146.pdf), page 5. For a two-state qubit ensemble $\mathcal E=\{(p,\rho),(1-p,\sigma)\}$, the source's Equation (1) defines

$$Q(\mathcal E)=-\sum_{i,j}p_ip_j\,\operatorname{tr}[\rho_i,\rho_j]^2.$$

Section 3, pages 3–5, defines the unrestricted dequantumness power by maximizing $Q(\mathcal E)-Q(\Lambda(\mathcal E))$, and its modified version by restricting the inputs to maximal initial quantumness. Here $D_2$ and $D'_2$ denote these optimizations over two-state ensembles. The corresponding definitions and source locators are in [the literature note](../Library/Entropy/songli2022dequantumness.md).

Issue [#22778](https://github.com/the-omega-institute/trureturing/issues/22778) fixes the formal claim as the universal equality: every completely positive, trace-preserving complex-linear qubit map satisfies $D_2(\Lambda)=D'_2(\Lambda)$. Refuting this claim supplies the strict separation sought by Song and Li; it confirms their existential conjecture.

## Motivation

The two powers distinguish the largest possible destruction of ensemble quantumness from the destruction achievable when the initial quantumness is maximal. Equality would justify restricting the optimization to maximally quantum inputs. A strict gap means that accepting a smaller initial quantumness can produce a larger decrease, so the restriction can miss the dequantumness power even for a qubit channel with two input states.

## Gap

Issue #22778 records the bounded literature check before any Lean:

- The published source states the conjecture explicitly; the conjecture is also present in the published PDF, Section 3, page 5.
- The oracle-reported searches of Zenodo, ResearchGate, SSRN and GitHub by the title and conjecture wording found no settlement.
- The orchestrator's repository and issue searches found no matching settlement; `CoPRelativeQuantumnessRefutation` concerns a different functional.

`not-found-in-searched-scope`.

## Route

All lemma names below refer to `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.lean`; the supporting lemmas are private. Write $B(r)=(I+r\cdot\boldsymbol\sigma)/2$ for the qubit Bloch matrix.

1. **Valid inputs and their maximum.** `two_state_ensemble_iff`, for every real $p$ and every pair of complex $2\times2$ matrices $\rho,\sigma$, identifies the ensemble condition with $0\le p\le1$ and both matrices positive semidefinite of trace one. `density_bloch`, for a matrix satisfying `IsDensity`, supplies $\rho=B(r)$ with $r\cdot r\le1$. `quantumness_bloch`, for every real $p$ and every pair of real three-dimensional Bloch vectors $r,s$, gives $Q=p(1-p)\|r\times s\|^2$. For $r\cdot r\le1$ and $s\cdot s\le1$, `cross_bounds` bounds the squared cross product between zero and one. Thus `quantumness_bounds`, for a valid ensemble, gives $0\le Q\le1/4$. `maximizing_ensemble` supplies an ensemble attaining $1/4$; `max_quantumness` uses this nonempty, bounded set to prove `maxQuantumness` is $1/4$.
2. **The channel.** The private `channel` is

   $$\Phi(X)=\frac12X+\frac12\operatorname{tr}(X)\begin{pmatrix}3/4&0\\0&1/4\end{pmatrix}.$$

   `channel_cptp` proves `IsCPTP channel`, using a Kraus representation for complete positivity and a trace calculation for trace preservation. `channel_bloch`, for every real three-dimensional Bloch vector $r$, gives $\Phi(B(r))=B(f(r))$, where $f(r)=r/2+e_z/4$ and $e_z=(0,0,1)$.
3. **The restricted upper bound.** `maximal_bloch` applies to a valid ensemble satisfying $Q=\texttt{maxQuantumness}$; it supplies $p=1/2$ and Bloch vectors with $r\cdot r=s\cdot s=1$ and $r\cdot s=0$. Under exactly these three orthonormality hypotheses, `orthonormal_cross_lower` proves

   $$\|f(r)\times f(s)\|^2\ge\frac14\left(\frac12-\frac{\sqrt2}{4}\right)^2.$$

   `restricted_loss`, for a valid ensemble with $Q=\texttt{maxQuantumness}$, therefore bounds its loss by $U=(29+2\sqrt2)/128$. `restricted_power_upper` bounds the real supremum by $U$, with nonemptiness supplied by `maximizing_ensemble` and `max_quantumness`.
4. **An unrestricted witness.** The construction in `witness_loss` uses $p=1/2$ and

   $$\rho_\pm=\frac1{34}\begin{pmatrix}5&\pm\sqrt{145}\\\pm\sqrt{145}&29\end{pmatrix}.$$

   Both matrices are Hermitian idempotents of trace one; `projection_density` requires all three conditions and concludes `IsDensity`. `witness_loss` supplies a valid ensemble whose loss is $L=1329215/5345344$. In `power_lower`, every unrestricted loss for this particular channel is bounded above by $1/4$, because valid inputs have $Q\le1/4$ and the output Bloch expression is nonnegative. The witness belongs to this bounded loss set, so `power_lower` proves $L\le D_2(\Phi)$.
5. **Strict separation.** `strict_comparison` proves $U<L$. Together, `power_lower` and `restricted_power_upper` give $D'_2(\Phi)\le U<L\le D_2(\Phi)$. Applying the universal equality to `channel_cptp` contradicts these inequalities, yielding `result : ¬ claim`.

## Falsifier

The settlement would not answer the source question if it changed the quantumness functional, allowed nonphysical inputs or channels, or treated a real supremum without the required existence and boundedness conditions.

The module uses the negative weighted real traces of squared commutators from Equation (1), complex-linear maps on $2\times2$ matrices, and the ordinary density-matrix and complete-positivity conditions. The restriction is to ensembles attaining the supremum of initial two-state quantumness, not to arbitrary pure inputs. The explicit maximizing ensemble and the boundedness arguments in the Route prevent empty-set or unbounded-supremum conventions from producing the separation.

The source writes maxima, whereas the module uses real suprema. For two-state qubits the density-matrix domain and the closed probability interval are compact, and the loss is continuous, so the suprema are attained. Section 2's open probability interval excludes only the endpoints, whose losses are zero; zero is also obtained at an interior probability by taking identical states. The maximal-quantumness restriction has $p=1/2$. These observations explain the correspondence of the two formulations; the compactness and endpoint correspondence are not additional Lean declarations in this module.

## Evidence

The canonical source is `D5/S3/QuantumChannels/DequantumnessPowerStrictGap.lean`.

- **Proof.** It proves `result : ¬ claim`, where `claim : Prop` is universal equality of the two real suprema for CPTP qubit maps.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumChannels/DequantumnessPowerStrictGap.lean.json`.

Declaration statements:

- `result`: `sha256:3aa9163832d4a8fab6fe377ef629381c2621e45ebdb0c272221a899cf7d8d89a`;
- `claim`: `sha256:ae6428ff2a9e708a4c348f36a82c292bf4bd44cc52ab67a67db804335474e02f`.

## Triage

Tier 1 explicit conjecture of a 2022 paper, preregistered in issue #22778 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that every completely positive, trace-preserving complex-linear map on complex $2\times2$ matrices has equal unrestricted and maximal-initial-quantumness-restricted two-state dequantumness powers.

**Computed, not formalized:** a floating-point evaluation of the witness loss and a random sample of orthonormal pure pairs by the dossier seat agree with the formal strict inequality.

**Argued, not formalized.**

- *Mechanism and the missing structure.* The witness's Bloch vectors are $r_\pm=(\pm\sqrt{145}/17,0,-12/17)$, with unit norm and inner product $-1/289$. Consequently its input quantumness is $20880/83521=1/4-1/334084$, and its output quantumness is $7105/5345344$. Their difference is $L$. For this channel the restricted bound is attained: choose $r=(1/\sqrt2,0,-1/\sqrt2)$ and $s=(-1/\sqrt2,0,-1/\sqrt2)$ with equal weights. They are orthonormal, and $f(r)\times f(s)$ has only its $y$ component nonzero, equal to $1/4-\sqrt2/8$, so the loss is $U$. `restricted_power_upper` supplies the matching upper bound, hence $D'_2(\Phi)=U$. The nonmaximal witness sacrifices $1/334084$ of initial quantumness while reducing the output quantumness by more than that amount. The translation makes output quantumness depend on the vectors' positions relative to $e_z$, so maximizing initial quantumness alone does not maximize the loss. The module proves the upper bound needed for refutation; the attaining pair and exact restricted value are the argument given here.
- *A sufficient structure that preserves equality.* For any CPTP qubit channel whose Bloch action is $r\mapsto ar$ with real $|a|\le1$, the cross product scales by $a^2$, hence $Q(\Lambda(\mathcal E))=a^4Q(\mathcal E)$. The loss is $(1-a^4)Q(\mathcal E)$ with nonnegative coefficient. Since $Q\le1/4$ and $1/4$ is attained by a valid two-state ensemble, both powers equal $(1-a^4)/4$. This includes the identity channel. It identifies a sufficient condition; it does not classify all channels with equality.
- *The weaker comparison survives.* For any CPTP qubit map, the restricted ensembles form a nonempty subset of all ensembles, and input and output quantumness lie in $[0,1/4]$. Both loss sets are therefore nonempty and bounded, and inclusion gives $D'_2\le D_2$. The settlement makes this inequality strict for the displayed channel.
- *Effect on Song and Li (2022, DOI 10.3390/e24081146).* The existential conjecture on page 5 receives the requested counterexample. Their amplitude-damping equality is a separate statement about that family; a different channel does not refute it. No subsequent result in Sections 4–5 or Appendix A uses the existence of the conjectured gap as a premise, so this settlement replaces no conjecture-dependent proof there. It does not settle their questions about non-unital channels without quantumness power or convex combinations of completely dequantumness dynamics.

## ASSUMED-UNVERIFIED

The bounded literature check in #22778 does not establish exhaustive worldwide novelty or priority. The oracle-reported external searches and the orchestrator's repository and issue searches were not reproduced here; their no-settlement readings remain attributed reports. No arXiv version is identified in the issue or Library note, so the front-matter URL identifies the published paper by DOI.

The numerical samples are not a proof over all orthonormal pairs. The exact witness calculations, the compactness and endpoint correspondence, the restricted bound's attainment, the structural explanation, the equality argument for scalar Bloch contractions, the general subset comparison and the assessment of the paper's dependencies are not additional formalized results of this module. The argument for the restricted value uses the module's upper bound together with the explicitly evaluated attaining pair.

The exact unrestricted power of the displayed channel, a classification of all CPTP qubit channels with equality or strict inequality, and the oracle's proposed criterion for a whole family of translated contractions remain open here. Ensembles with more than two ingredients, other Hilbert-space dimensions, other quantumness measures and quantumness-power claims are outside the formal statement.

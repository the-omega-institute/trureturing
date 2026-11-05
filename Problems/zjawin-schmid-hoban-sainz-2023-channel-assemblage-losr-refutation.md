---
slug: zjawin-schmid-hoban-sainz-2023-channel-assemblage-losr-refutation
bibkey: zjawinschmidhobansainz2023channel
doi: 10.22331/q-2023-10-10-1134
url: https://arxiv.org/abs/2209.10177v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.result
---

# The controlled-rotation channel assemblages do not obey the proposed LOSR angle ordering

## Problem

B. Zjawin, D. Schmid, M. J. Hoban and A. B. Sainz, *The resource theory of nonclassicality of channel assemblages*, Quantum 7, 1134 (2023), arXiv:2209.10177v3, Conjecture 3:

> Let the two resources $\In^{\,\theta_1}_{\A|\X}$ and $\In^{\,\theta_2}_{\A|\X}$ belong to the infinite family of assemblages $\FA$. Then, the conversion $\In^{\,\theta_1}_{\A|\X} \overset{\text{LOSR}}{\longrightarrow} \In^{\,\theta_2}_{\A|\X}$ is possible if and only if $\theta_1 \geq \theta_2$.

This is the verbatim text of `channel-quantum.tex`, line 354, in the [v3 source](https://arxiv.org/src/2209.10177v3), md5 `1478712c3cb6058c040039d9ae9978e6`. The source macros `\FA`, `\In`, `\A` and `\X` denote $\mathsf R$, $\mathbf I$, $\mathbb A$ and $\mathbb X$. The definitions and locators are also in [the literature note](../Library/QuantumContext/zjawinschmidhobansainz2023channel.md).

The family has binary outcomes and settings, $a,x\in\{0,1\}$, and angles $\theta\in(0,\pi/2]$. Alice and Bob share $|\phi\rangle=(|00\rangle+|11\rangle)/\sqrt2$. Bob applies the controlled gate $|0\rangle\langle0|_B\otimes I+|1\rangle\langle1|_B\otimes U_\theta$, where $U_\theta$ has rows $(\cos(\theta/2),-\sin(\theta/2))$ and $(\sin(\theta/2),\cos(\theta/2))$. The construction traces out $B$, applies Alice's effect $M_{a|0}=(I+(-1)^a\sigma_z)/2$ or $M_{a|1}=(I+(-1)^a\sigma_x)/2$, and traces out $A$ (Eqs. `eq:CR` and `eq:CRfam`, TeX lines 316–333).

Issue [#21490](https://github.com/the-omega-institute/trureturing/issues/21490) fixes the reading: for every pair of angles in $(0,\pi/2]$, LOSR conversion between these literal assemblages is possible exactly when the source angle is at least the target angle. The conjecture is refuted.

## Motivation

The paper uses LOSR convertibility to compare the nonclassicality of channel assemblages. Its controlled-rotation family supplies an infinite quantum-realizable example whose proposed ordering is indexed by the angle. An angle criterion would turn this part of the resource preorder into a scalar comparison. The refutation tests whether the stated family actually retains the nonclassical correlations needed for that ordering.

## Gap

Issue #21490 records the bounded literature check before any Lean:

- the v3 source contains Conjecture 3 and its supporting SDP observations; its text has been checked against the downloaded source;
- the search contributor reports screening the Crossref/ADS and INSPIRE citing records, comprising 11 arXiv papers and one thesis, with no settlement found, and reports no entry in MathDB or `google-deepmind/formal-conjectures`;
- the orchestrator reports an OpenAlex count of nine citing works and no existing repository issue, module, Library note or Problems dossier for this source at preregistration.

`not-found-in-searched-scope`. The reported citation screens and repository search are not an exhaustive literature search.

## Route

All lemma names below refer to the canonical module; the helpers are private.

1. **Expand the literal family.** `free_form` holds for every real $\theta$, every binary $a,x$, and every complex $2\times2$ matrix $\rho$, without a positivity or normalization hypothesis. It gives
   $\mathcal I^\theta_{0|0}(\rho)=\rho/2$,
   $\mathcal I^\theta_{1|0}(\rho)=U_\theta\rho U_\theta^\dagger/2$, and
   $\mathcal I^\theta_{a|1}(\rho)=(\rho+U_\theta\rho U_\theta^\dagger)/4$ for both outcomes. The computational-basis expansion includes the trace over $B$.
2. **Certify the fixed processing maps.** The pre-map $E(\rho)=|0\rangle\langle0|\otimes\rho$ stores the input in a qubit memory. Put $V_0=I$ and $V_1=U_{\pi/2}$. The post-map is $F_b(\tau)=V_b\operatorname{tr}_{B_{out}}(\tau)V_b^\dagger$. `pre_cptp` proves `IsCPTP preMap` with no additional hypotheses; `post_cptp` proves `IsCPTP (postMap b)` for every $b\in\mathrm{Fin}\,2$. Their Kraus operators satisfy $\sum_k K_k^\dagger K_k=I$. Here `IsCPTP` means complete positivity at every finite amplification and preservation of the trace of every matrix.
3. **Evaluate the memory bypass.** `memory_action` holds for every complex linear qubit matrix map $\Phi$, every binary $b$, and every complex $2\times2$ matrix $\rho$, without assuming $\Phi$ is positive or trace preserving. It states
   $F_b((\Phi\otimes\mathrm{id})(E(\rho)))=\operatorname{tr}(\Phi(|0\rangle\langle0|))V_b\rho V_b^\dagger$.
   `source_branch_trace` gives $\operatorname{tr}(\mathcal I^\theta_{a|0}(|0\rangle\langle0|))=1/2$ for every real $\theta$ and every binary $a$, at the fixed setting $x=0$ and fixed input $|0\rangle\langle0|$.
4. **Assemble the conversion at the witness angles.** Use a uniform shared pair $(b,r)\in\{0,1\}^2$. Alice queries $x=0$, ignores the source outcome $a$, and outputs $a'=b$ at $x'=0$ and $a'=r$ at $x'=1$. Her conditional probabilities are nonnegative, normalized over $(a',x)$ for every shared pair, $a$ and $x'$, and have a marginal over $a'$ independent of $a$. `conversion_identity` verifies the resulting equality for every binary $a',x'$ and every complex $2\times2$ matrix $\rho$, with source angle fixed to $\pi/3$ and target angle fixed to $\pi/2$. `conversion` combines that identity and the probability and CPTP certificates into `LOSRConvertible (assemblage (Real.pi / 3)) (assemblage (Real.pi / 2))`.
5. **Contradict the angle criterion.** `witness_angles` proves that $\pi/3$ and $\pi/2$ both lie in $(0,\pi/2]$ and that $\pi/3<\pi/2$. The forward implication of `claim` would apply to `conversion` and give the opposite weak inequality. `result` concludes $\neg\mathrm{claim}$.

## Falsifier

The refutation would not settle the source's conjecture if either the generated maps or the permitted operations differed from its definitions. The module uses:

- the Bell density, the half-angle rotation with $B$ as control, the trace over $B$, and Alice's Pauli-$z$ and Pauli-$x$ effects from Eqs. `eq:CR` and `eq:CRfam`;
- finite shared randomness, nonnegative normalized conditional probabilities with no retrocausation, and Bob's CPTP pre- and post-maps with a finite quantum side channel, as in Eq. `eq:LOSRtrans-channel` (TeX lines 246–265);
- equality of the transformed maps on every complex $2\times2$ matrix, rather than on a sample of states.

The witness uses only four shared values and a qubit side channel. The abstract type `Assemblage` is merely a binary family of complex linear qubit matrix maps; the claim concerns the specifically defined `assemblage θ`, not every inhabitant of that carrier. Neither an angle outside the source interval nor a restriction on Bob's memory is used to obtain the contradiction.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.lean` (268 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Definitions.** `claim` uses `assemblage` and `LOSRConvertible`; these use the half-angle `rotationY`, the binary `Assemblage` carrier and `IsCPTP` as described above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom. Importing the compiled module and running `#print axioms` on `result` reports exactly these three axioms; the source scan finds none of the three prohibited forms.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.lean.json`, statement `sha256:421563d4f5bec76e6459d0c14b6227f1ffdababf4424d4702c64888f894ae0dc`.

Declaration statements:

- `result`: `sha256:002cdde22afd5de2acc84d4d179d332dfbfdaa4a5b4a3fc1739dea9b1967f42f`;
- `claim`: `sha256:edb203f1d6e503d6a721ccca3abefae2a34ee0cf489a3ce77b322711f80ef150`.

## Triage

Tier 1 conjecture of a 2023 journal paper, supported by SDP observations, preregistered in issue #21490 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every real $\theta_1,\theta_2\in(0,\pi/2]$, `LOSRConvertible (assemblage θ₁) (assemblage θ₂)` is equivalent to $\theta_1\ge\theta_2$, with precisely the definitions above. The universal statement is negated; `result` does not state a universal freeness or interconvertibility theorem.

**Computed, not formalized** (exact symbolic matrix calculation with SymPy 1.14.0; the four branch formulas and the four converted target maps were reproduced by the orchestrator with an independent script):

- Expanding the source's $8\times8$ construction with an arbitrary complex input matrix and real symbolic rotation entries $c,s$ gives zero residual in every entry of all four branch formulas in `free_form`.
- At source angle $\pi/3$ and target angle $\pi/2$, explicit Kraus matrices satisfy the pre-map and both post-map completeness identities. Enumerating Alice's binary indices verifies normalization and no retrocausation. Applying the source maps tensored with the memory identity gives zero residual in all four target maps for arbitrary complex input entries. These are symbolic checks of this construction, not a numerical survey of other families or a reproduction of the paper's SDP runs.

**Argued, not formalized.**

- *Mechanism and freeness.* Put $U_0=I$ and $U_1=U_\theta$. The evolved operator is $\frac12\sum_{b,c}|b\rangle\langle c|_A\otimes|b\rangle\langle c|_B\otimes U_b\rho U_c^\dagger$. The trace over $B$ removes every term with $b\ne c$. Consequently the remaining branches have the free decomposition $\mathcal I^\theta_{a|x}(\rho)=\frac12\sum_b p(a|x,b)U_b\rho U_b^\dagger$, with $p(a|0,b)=\delta_{a,b}$ and $p(a|1,b)=1/2$. These are conditional probabilities, and each conjugation is CPTP because $U_\theta^\dagger U_\theta=I$, by $\cos^2(\theta/2)+\sin^2(\theta/2)=1$. This supplies the decomposition of the source's Eq. `eq:free-channel` for every allowed angle. The coherent correlation with the discarded control does not survive as a nonfree assemblage.
- *A surviving statement and the wider scope.* The decomposition also gives an explicit conversion for any allowed source and target angles $\alpha,\beta$. Store the new input in qubit memory, feed $|0\rangle\langle0|$ through source setting zero, and discard its output and Alice's outcome. Their summed trace is one. Shared uniform bits $(b,r)$ let Alice output $b$ at setting zero and $r$ at setting one; Bob applies $V_0=I$ or $V_1=U_\beta$ to the stored input according to $b$. The resulting target branches have weights $1/2$ at setting zero and $1/4$ for each conjugation at setting one. Both maps are CPTP: the pre-map is an isometry, and the post-map has Kraus operators $\langle k|\otimes V_b$ with $\sum_k K_k^\dagger K_k=I$. Thus the sufficient direction $\alpha\ge\beta$ survives in this algebraic argument, while the necessary direction has no angle-order content. This extension to arbitrary target angle is not the statement of the module's fixed-angle `conversion` lemma.
- *Missing structure and possible repairs.* With this free decomposition, restricting to any angle set containing two distinct values cannot restore the proposed necessary condition. A nontrivial angle ordering would require different generated maps or different permitted operations. Whether a modified construction retaining coherence, or a restriction on the side-channel operations, supports such an ordering is open; neither modification is the conjecture settled here.
- *Effect on the source and Conjecture 4.* The general freeness argument replaces the proposed angle hierarchy in the quantum-realizable-family discussion by a single free equivalence class. The source's two analogous controlled-$x$ and controlled-$z$ families (TeX lines 357–360) have the same traced-control expansion, with a different unitary in the $b=1$ branch. The same probability decomposition and memory preparation apply. This gives an unformalized argument for the fixed-angle, cross-axis equivalence of Conjecture 4, and also for conversions between different allowed angles across those literal families. The larger-to-smaller conversions in the source's conversion diagram remain possible, but do not exclude reverse conversions. The module does not settle the correctness of the general SDP formulation or the later comparisons of different post-quantum assemblages. It does not identify whether the reported numerical ordering arose from different input assemblages, implementation choices or numerical errors; that discrepancy remains open.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The citation screens, database absence reports, OpenAlex count and repository search recorded in #21490 have not been independently reproduced. The search contributor's report about the other arXiv versions and retention of the conjecture in the journal version has not been separately checked against those versions; the source text checked here is arXiv:2209.10177v3.

The statements in "Computed, not formalized" are independent symbolic computations, not additional Lean declarations. The general freeness, arbitrary-angle conversions, cross-axis extension, repair discussion and consequences for the source in "Argued, not formalized" are not formalized by this module. The paper's Matlab/CVX/SeDuMi/QETLAB computations and the orchestrator's reported reading of the authors' code have not been reproduced. Their discrepancy with the literal-family calculation and the behaviour of modified families or restricted operations remain open.

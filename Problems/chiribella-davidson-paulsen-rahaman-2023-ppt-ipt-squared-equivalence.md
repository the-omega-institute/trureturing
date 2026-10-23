---
slug: chiribella-davidson-paulsen-rahaman-2023-ppt-ipt-squared-equivalence
bibkey: chiribelladavidsonpaulsenrahaman2023real
doi: 10.1007/s00023-023-01325-x
url: https://arxiv.org/abs/2207.02510v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.result
---

# PPT-squared and IPT-squared equivalence

## Problem

G. Chiribella, K. R. Davidson, V. I. Paulsen and M. Rahaman, *Positive maps and entanglement in real Hilbert spaces*, arXiv:2207.02510v2, Ann. Henri Poincaré 24 (2023), DOI 10.1007/s00023-023-01325-x, Section 9.2, asks:

> We do not know if these conjectures are equivalent.

The source defines PPT-squared over complex matrices and IPT-squared over real and complex matrices. The source implications are $\mathrm{PPT}^2(\mathbb C) \Rightarrow \mathrm{IPT}^2(\mathbb C) \Rightarrow \mathrm{IPT}^2(\mathbb R)$.

### Statement echo

The source conventions are represented by the public definitions `SEP`, `IsEB`, `ptFirst`, `IsPPT`, `IsIPT`, `PPT2C`, `IPT2` and `claim` in `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.lean`. Amplification and complete positivity use `MatrixMap.kron` and `MatrixMap.IsCompletelyPositive` from `FiniteKrausChannel`; the consumed `kron_id_apply` proves the source coordinate formula. The input-first Choi expression is `MatrixMap.choi_matrix` from `FiniteKrausRepresentation`, with `submatrix Prod.swap Prod.swap`; its entries are exactly the source formula. Thus the claim remains $(\mathrm{PPT2C}\leftrightarrow\mathrm{IPT2}(\mathbb C))\land(\mathrm{IPT2}(\mathbb C)\leftrightarrow\mathrm{IPT2}(\mathbb R))$. The settling declaration is `result : claim`. The matrix indices use `Fin`, scalars are generic over `[RCLike 𝕜]`, and the flag identification is `(finCongr (Nat.mul_comm 2 n)).trans finProdFinEquiv.symm`.

## Motivation

The settling declaration `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.result` proves the equivalence question unconditionally. It does not prove the PPT-squared conjecture itself. The settlement has admission basis `open-problem-resolution` (#15391; Proved), and the delivered module uses `utility: none` with generality `G`.

The source's Choi and measure-and-prepare characterization is used to transport entanglement breaking through the flag construction. The flag device is related to Huber, Lami, Lancien and Müller-Hermes, Lemma III.1, in the cited Library note; the map lift, composition law and recovery are the result's argument.

## Gap

The source left the equivalence of the three conjectures open. The proof in `result` closes that equivalence while preserving the source's fixed-dimension forward implications. The reverse transfer uses dimension $2n$ for the IPT hypothesis.

The public result is positive and is an escape-audit target. The audit is unfinished: [#15525](https://github.com/the-omega-institute/trureturing/issues/15525) records the concrete template gap, namely that no faithful enrolled template currently supplies the joint-source reconstruction, lawful readout and realization bridge for this conjunction of global channel-conjecture equivalences, including the required DependentFamily positivity, variation, sensitivity and observational-dependence evidence. No Reg file and no `declared_validated` status are claimed.

## Route

The proof uses the following chain.

1. Define the two-dimensional conjugate flag maps $B_+$, $B_-$, $E$ and $D$, and set $\Gamma_\Phi=D\Phi E/2$.
2. Expand $2\Gamma_\Phi$ into four completely positive branches. For a complex PPT map, the lift is completely positive, invariant under input transpose and invariant under output transpose, hence IPT over $\mathbb C$.
3. Restrict the lift to real matrices and complexify it back; the restriction is real IPT.
4. Prove $\Gamma_\Psi\Gamma_\Phi=\Gamma_{\Psi\Phi}$ and recover $\Phi^2/2$ by completely positive insertion and compression.
5. Use the Choi and measure-and-prepare characterization to transfer entanglement breaking through completely positive pre- and post-composition and through real complexification.
6. Combine the new reverse transfers with the source implications to obtain both equivalences in `result`.

## Falsifier

A counterexample to any identity in the flag construction, a failure of complete positivity for one of its four branches, or a map satisfying an IPT-squared premise whose recovered square is not entanglement breaking would refute the formal statement. The open PPT-squared conjecture itself is not a falsifier for this equivalence theorem, because the theorem asserts only equivalence.

## Evidence

The kernel-checked settling declaration is `D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.result`. Its axiom closure is contained in \{propext, Classical.choice, Quot.sound\}. The public surface consists of the eight definitions named in the statement echo and the sole public theorem `result`; private helpers are consumed on the live proof path. The corresponding Scribe node carries one `OpenProblemResolutionClaim` with `ResolutionKind.Proved`.

The literature source is `Library/QuantumChannels/chiribelladavidsonpaulsenrahaman2023real.md`. The flag precedent is `Library/QuantumChannels/huberlamilancienmullerhermes2018ppt.md`.

The independent numerical check is published in [the experiments repository](https://github.com/the-omega-institute/trureturing-experiments/tree/691133b13524e26bcc338c76d989b798bb190273/docs/reports/chiribella-davidson-paulsen-rahaman-2022-ipt-ppt-squared-equivalence) at commit `691133b13524e26bcc338c76d989b798bb190273`. The command `python3 check.py` exited 0, its script SHA-256 is `4774275c78ddfe252c60a22564839c3c9f04b070b2196f196a5915b741b3e57e`, and the final reading is `bad= 0` for random $n=3$ instances, recovery powers $1,2,3$, the fixed $n=2$ PPT/non-IPT example and the fixed $n=4$ lift.

## Triage

### What the settlement shows

- **Proved, kernel-checked mechanism.** The flag lift $\Gamma_\Phi=D\Phi E/2$ turns every complex PPT map into a complex IPT map and, after restriction, a real IPT map. The lift is compatible with composition, and completely positive insertion and compression recover $\Phi^2/2$ from $\Gamma_\Phi^2$. Evidence: the kernel-checked helpers `gamma_ipt`, `gamma_real_ipt`, `gamma_comp` and `recovery` in `D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence`; these are used by `result`.
- **Proved in prose, dimension-by-dimension reverse transfers.** For $\mathbb K\in\{\mathbb R,\mathbb C\}$, IPT$^2(\mathbb K)$ in dimension $2n$ implies PPT$^2(\mathbb C)$ in dimension $n$. The proof is the flag restriction, real-to-complex entanglement-breaking transfer and recovery in the preceding bullet.
- **Proved in prose, source implications.** PPT$^2(\mathbb C)$ in dimension $n$ implies IPT$^2(\mathbb C)$ in dimension $n$, and IPT$^2(\mathbb C)$ in dimension $n$ implies IPT$^2(\mathbb R)$ in dimension $n$, by the source's implication argument formalized in `result`.
- **Literature reading.** Chen, Yang and Tang, arXiv:1807.03636v2, Theorem 3 gives the complex PPT-squared conclusion for $n=3$; its Section II recalls the $n=2$ case from the Peres-Horodecki criterion. Proposition 9.9 of the primary source transfers those fixed-dimension conclusions to IPT$^2$ over both fields. These citations establish only the stated dimensions; no uniform extension is claimed.
- **Computed.** The experiment entry above computes `bad= 0` over its exact random and fixed-instance scope. It is a numerical check, not a universal proof.
- **Open.** The PPT-squared conjecture itself remains open; the equivalence theorem does not decide whether any of the three conjectures is true.
- **Open.** Whether the dimension doubling in the flag lift can be avoided remains open.
- **Effect on source results.** The source's forward implications remain valid dimension by dimension. Its PPT-squared and IPT-squared conjectures remain unresolved as truth claims, while their equivalence is now proved. The fixed $n=2$ and $n=3$ results retain their stated scopes.

## ASSUMED-UNVERIFIED

Exhaustive worldwide novelty and priority beyond the bounded literature screen recorded in preregistration #15391 are not established. The unfinished escape audit and its concrete template gap are recorded in #15525. The numerical experiment is evidence for its tested instances only.

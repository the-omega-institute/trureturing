---
slug: nandi-2025-mub-correlation-locc-refutation
bibkey: nandi2025genuine
doi: 10.48550/arXiv.2509.24045
url: https://arxiv.org/abs/2509.24045v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.result
---

# A local measure-and-reset refutes the LOCC monotonicity of the MUB correlation $I_2$

## Problem

S. Nandi, *Genuine multipartite entanglement detection with mutually unbiased bases (MUBs)*,
arXiv:2509.24045v1 (EPL 154 (2026)), §II, measures a bipartite state $\rho$ on
$\mathbb C^d\otimes\mathbb C^d$ in a basis $\{a_i\}$ for Alice and $\{b_i\}$ for Bob, and in
a second pair $\{a'_i\}$, $\{b'_i\}$ mutually unbiased to the first, and sets
$I_2=\sum_i\langle a_ib_i|\rho|a_ib_i\rangle+\sum_i\langle a'_ib'_i|\rho|a'_ib'_i\rangle$.
Its Conjecture states that "the quantity $I_2$ is monotonically non-increasing under LOCC
operations", tested in Eq. (10) on binary local instruments $E_1,E_2$ with
$E_1^\dagger E_1+E_2^\dagger E_2=I$: $I_2(\rho)-p_1I_2(\rho_1)-p_2I_2(\rho_2)\ge0$. The verbatim
statements are in [the literature note](../Library/QuantumStates/nandi2025genuine.md).

Issue [#13804](https://github.com/the-omega-institute/trureturing/issues/13804) fixes two
readings of "the quantity $I_2$", both for $d\ge2$: for every fixed pair of local MUB settings,
and for the supremum over settings (the paper evaluates $I_2$ of pure states in their Schmidt basis). The
conjecture is read as the disjunction of the two. Because $I_2$ is linear in $\rho$,
$p_kI_2(\rho_k)=I_2(\tau_k)$ with $\tau_k=(E_k\otimes I)\rho(E_k\otimes I)^\dagger$, which also
covers $p_k=0$.

## Motivation

The paper uses $I_2$ and its multipartite analogues as entanglement witnesses and compares
them with entanglement measures; the Conjecture is announced as "one of the central results",
and the conclusion states that the correlation "is convex, and non-increasing under LOCC".
`D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.result` shows that it is
not non-increasing in either reading, already for two qubits and a one-sided measurement.

## Gap

The bounded literature check in issue #13804 found no counterexample or correction in the
arXiv versions, the public EPL abstract, web searches, or Zenodo phrase searches ("mutual
predictability", "mutually unbiased" LOCC, the identifier). The paper's numerical check of
Eq. (10) (its Fig. 1) uses the Bell state only. `not-found-in-searched-scope`.

The other D5 MUB results concern tomography and basis compatibility, rather than this
correlation's LOCC monotonicity. The proof reuses the frozen unitary-norm theorem and
Hadamard matrix, and Mathlib's unitary entry bound, positive-semidefinite outer products
and conditionally complete supremum lemmas. No other D5 or pinned Mathlib declaration was
found that settles this claim.

## Route

Take $d=2$, $\rho=\tfrac12 I\otimes|0\rangle\langle0|$, $E_1=|0\rangle\langle0|$,
$E_2=|0\rangle\langle1|$ (measure Alice in the computational basis and reset outcome 1 to
$|0\rangle$). Then $\tau_1=\tau_2=\tfrac12|00\rangle\langle00|$.

1. **Every setting gives $I_2(\rho)=1$.** $\langle a_ib_i|\rho|a_ib_i\rangle
   =\tfrac12\|a_i\|^2|\langle b_i|0\rangle|^2=\tfrac12|\langle b_i|0\rangle|^2$, and
   $\sum_i|\langle b_i|0\rangle|^2=1$ because Bob's basis is orthonormal. Each of the two sums
   is $\tfrac12$. Hence the supremum over settings is also $1$.
2. **The branches.** In the computational/Hadamard setting
   ($a=b=\{|0\rangle,|1\rangle\}$, $a'=b'=\{|\pm\rangle\}$),
   $I_2(\tfrac12|00\rangle\langle00|)=\tfrac12(1+\tfrac12)=\tfrac34$, so the branches sum to
   $\tfrac32>1$.
3. **The supremum.** $I_2^{s}(\tau)\le2$ for every setting, so the supremum over settings of
   each branch is finite and at least $\tfrac34$; the branches again sum to at least
   $\tfrac32>1$.

## Falsifier

The formal refutation concerns fixed-setting values and their supremum. It does not settle
Eq. (10) with branch-wise minima over settings. Restricting the operation class to exclude
measure-and-reset instruments would change the claim. The instrument used here satisfies
$E_1^\dagger E_1+E_2^\dagger E_2=I$, the completeness condition in Eq. (10).

## Evidence

The canonical source is
`D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.lean`. Its public
declarations are `Setting`, `prodVec`, `I2`, `I2max`, `branch`, `claimFixed`,
`claimOptimized`, `claim` and `result`. Its two imports are:

- `D5.S3.Weil.ZetaLinear.VonNeumann`, for
  `RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary` in `col_norm_sq` and `row_norm_sq`;
- `D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence`, for `hadamard` and `s2`
  in `hadamard_eq`.

It also uses Mathlib's `Matrix.unitaryGroup`, `Matrix.kronecker`, `Matrix.PosSemidef`,
`entry_norm_bound_of_unitary`, `ciSup_le`, `le_ciSup` and `le_ciSup_of_le`.
The axiom closure of `result` is exactly `propext`, `Classical.choice` and `Quot.sound`;
there is no `sorry`, `native_decide`, or new axiom in the module.
The module statement is `sha256:f2a1a70d6a8555fd81594dbf727d9d42999af8ed61675b42069927e8b36a5cde`,
the `result` statement `sha256:132905ada69324d38200d6c44277cc6336a4bd987db4228f75453d8f31a5382b` and the
`claim` statement `sha256:230f98303e86e0c110c320b98386c1d4440577dd7cb4f4ff15cf66fd254f3e41`. The Freeze
event is `sha256:b526a3e5a760af56c57ca370cf6128603623274e82cfcfbcfb07814f17c40b41`; its project-level
prerequisites are the frozen `VonNeumann` and `BinaryStabilizerLocalInequivalence`.

## Triage

Tier 1 conjecture of a 2025 paper (published 2026), with the reading specified in issue
#13804. Both `claimFixed` and `claimOptimized` quantify over dimensions $d\ge2$;
`claim` is their disjunction, and `result` refutes it. `theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The private theorems (`col_norm_sq`, `row_norm_sq`, `rho0_mulVec`, `rho0_expect`, `i2_rho0`,
`hadamard_eq`, `half_sqrt_two_sq`, `hadamard_unitary`, `hadamard_mub`,
`branch_first`, `branch_second`, `rhoP_mulVec`,
`rhoP_expect`, `i2_standard_branch`, `i2_standard_rhoP`, `rho0_vec`, `rho0_state`,
`instrument_complete`, `not_claimFixed`, `normSq_entry_le_one`,
`i2_rhoP_le_two`, `i2max_rho0`, `i2max_rhoP_ge`, `not_claimOptimized`) are bind-only and are
used on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is
`certified-instance` with basis `refutes` of `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the conjecture fails in the fixed-setting reading and in the
optimized reading, for $d=2$ and a binary instrument acting on Alice only.

**Established inside the proof.** For every pair of qubit MUB settings,
$I_2(\tfrac12I\otimes|0\rangle\langle0|)=1$ (`i2_rho0`); every value $I_2^{s}$ of the
branch state is at most $2$ (`i2_rhoP_le_two`), which bounds the supremum.

**Argued, not formalized.**

- *Mechanism.* $I_2^{s}$ is not invariant under local unitaries, and a local reset can move
  the state into a position aligned with the measured bases. A function that does not increase
  under all LOCC maps, including discarding a state and preparing a separable one, must be
  constant on separable states: each separable state can be prepared from any other. $I_2^{s}$
  is not: it equals $2/d$ at the maximally mixed state $I/d^2$ for every setting, and
  $1+1/d$ at $|a_0b_0\rangle$. So for every $d\ge2$, every fixed setting and the supremum over
  settings, preparing $|a_0b_0\rangle$ from $I/d^2$ raises $I_2$ from $2/d$ to at least
  $1+1/d$.
- *The minimum over settings fails too, under full LOCC.* At $d=2$, $\min_sI_2^{s}(I/4)=1$,
  while the setting $a=\{|0\rangle,|1\rangle\}$, $b=\{|1\rangle,|0\rangle\}$, $a'=b'=\{|\pm\rangle\}$
  gives $I_2^{s}(|00\rangle\langle00|)=0+\tfrac12$. Replacing $|00\rangle$ by $I/4$, a local
  operation, raises the minimum from at most $\tfrac12$ to $1$. This channel is not a single
  binary instrument on one side, and Eq. (10) with branch-wise minima is not addressed by this
  example.
- *What survives.* $I_2^{s}\le1+1/d$ on separable states is the separability criterion the
  paper takes from its reference [1huber], and the paper's tripartite and quadripartite bounds
  are stated as upper bounds over biseparable states; their proofs as given do not cite the
  Conjecture. $I_2$ therefore remains an entanglement witness; it is not an entanglement
  monotone.

**Open.** Whether some LOCC-monotone quantity is obtained from $I_2$, for example
$\max\{0,\,I_2^{\max}-(1+1/d)\}$, is not settled here.

**Effect on the paper.** The Conjecture and the sentence of the conclusion that the
correlation is non-increasing under LOCC are false under the two specified readings.
The separability and multipartite witness bounds do not rely on this conjecture in the
paper's arguments; this Lean result neither proves nor refutes those bounds.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or
the absence of an independent counterexample.

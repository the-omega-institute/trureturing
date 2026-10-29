---
slug: sanz-wolf-perez-garcia-cirac-2009-spin-three-halves-u1-injective-mps
bibkey: sanzwolfperezgarciacirac2009mps
doi: 10.1103/PhysRevA.79.042308
url: https://arxiv.org/abs/0901.2223v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/FourLevelU1SymmetricInjectiveMPS.result
---

# Four physical levels admit a $U(1)$-symmetric injective matrix-product family

## Problem

M. Sanz, M. M. Wolf, D. Pérez-García and J. I. Cirac, *Matrix product states: Symmetries and two-body Hamiltonians*, Phys. Rev. A 79, 042308 (2009), arXiv:0901.2223v1, Section IV, `Symmetries191208.tex`, lines 748–751:

> Let us remark that this counter-example is applicable to spin $\ge
> \frac{5}{2}$. Indeed, one can prove Theorem \ref{} for $U(1)$ and
> spin $\frac{1}{2}$, which is the content of the following
> proposition. The case of spin $3/2$ remains an open question.

The preceding example, lines 726–746, uses general generator eigenvalues, all nonzero, at physical dimension $d=D^2-D$ with bond dimension $D\ge3$. The question concerns the remaining four-level case. Issue [#23698](https://github.com/the-omega-institute/trureturing/issues/23698) fixes its general-generator reading as follows.

For $D\in\mathbb N$, let $A:\mathrm{Fin}\,4\to\mathcal M_D(\mathbb C)$, let $W$ be a unitary $4\times4$ matrix, and let $\lambda:\mathrm{Fin}\,4\to\mathbb R$. Define

$$u(\varphi)=W\operatorname{diag}(e^{i\varphi\lambda_k})W^\dagger,\qquad
\Psi_N(w)=\operatorname{tr}(A_{w_0}\cdots A_{w_{N-1}}).$$

`IsSymmetric` means that for every real $\varphi$ and every positive $N$ there is a real $\theta$, allowed to depend on both, with $u(\varphi)^{\otimes N}\Psi_N=e^{i\theta}\Psi_N$. `IsInjective` means that for some natural block length $n$ the map

$$\Gamma_n:X\longmapsto\bigl(w\longmapsto\operatorname{tr}(XA_{w_0}\cdots A_{w_{n-1}})\bigr)$$

is injective on $\mathcal M_D(\mathbb C)$. These are the trace-amplitude, symmetry and injectivity conventions of the source at lines 222–237, 134–140 and 267–276, respectively; [the literature note](../Library/StatisticalMechanics/sanzwolfperezgarciacirac2009mps.md) records the locators.

`claim` asserts universally in $D,A,W,\lambda$ that if every $A_k\ne0$, $\sum_kA_kA_k^\dagger=I_D$, every $\lambda_k\ne0$, at least two charges differ, and `IsSymmetric` holds, then `IsInjective` does not hold. This assertion is refuted. The specified reading concerns four physical levels with general charges; it does not identify their generator with the usual spin-$3/2$ matrix $J_z$.

## Motivation

The source studies which restrictions a symmetry places on a single translationally invariant matrix-product state. Its Section IV theorem assumes an irreducible $SU(2)$ representation of even physical dimension and concludes noninjectivity, with a consequence for uniqueness of frustration-free ground states. The surrounding $U(1)$ examples and question distinguish restrictions coming from the symmetry representation from restrictions coming merely from the number of physical levels. A four-level injective example with nonzero charges answers the preregistered question without providing an $SU(2)$-symmetric example.

## Gap

Issue #23698 records the bounded literature check before any Lean:

- The orchestrator screened the titles of 85 citing records listed by INSPIRE; Crossref listed 78.
- The orchestrator searched the TeX of arXiv:2412.20765, 2405.14929, 0908.1674, 2111.02457 and 1301.0746 for the four-level question and the source citation, and reported no settlement in those five works.
- GPT Pro reported searches of Zenodo, ResearchGate, SSRN and GitHub without finding a settlement, and pointed to Ahrens, Schadschneider and Zittartz (2002), arXiv:cond-mat/0206537, as related constructional prior art with a fifth, zero-charge component.
- The preregistration reports no existing repository treatment of this question.

`not-found-in-searched-scope`. The citation screening, five-paper reading and GPT Pro reports are attributed checks, not independently reproduced literature results.

## Route

All named helpers below are private declarations of the canonical module and concern its fixed witness unless an argument is explicitly quantified. With matrix units indexed by $0,1,2$, take bond dimension three, $W=I_4$, and

$$A_0=\tfrac35(E_{01}+E_{12}),\quad
A_1=\tfrac45(E_{10}+E_{21}),\quad
A_2=\tfrac45E_{02},\quad
A_3=\tfrac35E_{20},\qquad
\lambda=(-1,1,-2,2).$$

1. **The hypotheses.** `kraus_nonzero` proves that each of these four matrices is nonzero. `kraus_normalized` proves $\sum_kA_kA_k^\dagger=I_3$. `charges_nonzero` proves that all four displayed charges are nonzero, and `charges_distinct` proves the existence of two unequal charges.
2. **Symmetry.** For every real $\varphi$, set $V(\varphi)=\operatorname{diag}(1,e^{i\varphi},e^{2i\varphi})$. `gauge_inverse` proves the inverse identity for this diagonal matrix. For every real $\varphi$ and every $k\in\mathrm{Fin}\,4$, `charge_conjugation` proves $VA_kV^{-1}=e^{i\varphi\lambda_k}A_k$. `conjugation_words` extends this identity to every finite list of physical labels at that $\varphi$, and `trace_words` proves that the product of its scalar phases fixes the trace of that word. For every real $\varphi$, natural $n$, amplitude function $\psi$ and word $w\in(\mathrm{Fin}\,n\to\mathrm{Fin}\,4)$, `diagonal_tensor_action` identifies the action at $W=I_4$ with multiplication by $\prod_i e^{i\varphi\lambda_{w_i}}$. Consequently `kraus_symmetric` proves `IsSymmetric` for the fixed witness, choosing $\theta=0$ for every real $\varphi$ and every positive chain length.
3. **Injectivity.** For the fixed witness, `two_products` gives nonzero scalar multiples of all six off-diagonal matrix units and of $E_{00},E_{22}$ as length-two products, and gives $A_0A_1-A_2A_3=(12/25)E_{11}$. For any complex $3\times3$ matrix $X$, `trace_kernel` assumes $\operatorname{tr}(XA_iA_j)=0$ for every $i,j\in\mathrm{Fin}\,4$ and concludes $X=0$: the product identities and $\operatorname{tr}(XE_{ij})=X_{ji}$ force each entry to vanish. `kraus_injective` applies this to $X-Y$ when $\Gamma_2(X)=\Gamma_2(Y)$, proving injectivity at block length two.
4. **Refutation.** `result` applies the universal assertion `claim` to bond dimension three, these matrices, the identity unitary and these charges. Its conclusion of noninjectivity contradicts `kraus_injective`.

## Falsifier

The source-to-formalization boundary matters in three places:

- `u1Rep` accepts arbitrary real charges and a real parameter; its definition does not impose periodicity. The witness has integer charges, so its exponentials are $2\pi$-periodic and define an actual circle action by the elementary exponential identities. This periodicity observation is not a separate Lean declaration. The spectrum is not the usual spin-$3/2$ spectrum.
- Normalization here is the Kraus identity $\sum_kA_kA_k^\dagger=I_D$, not unit norm of every finite-chain vector. `IsSymmetric` does not require $\Psi_N\ne0$ at every positive length.
- `IsInjective` quantifies over all natural block lengths, including zero. The proof supplies the positive block length two, and uses the source's boundary trace map rather than injectivity of a transfer operator or of a single local matrix.

Thus the formal counterexample answers the preregistered general-charge obstruction. A claim specifically requiring the usual spin generator, full $SU(2)$ symmetry, or nonzero periodic vectors at every positive length has additional hypotheses and is not this `claim`.

## Evidence

The canonical source is `D5/S3/Quantum/SpinChains/FourLevelU1SymmetricInjectiveMPS.lean`.

- **Proof.** It proves `result : ¬ claim`; the compiled definition of `claim` has type `Prop`. A scratch file importing the module checked `result` and printed `claim`, `amplitude`, `u1Rep`, `IsSymmetric` and `IsInjective` successfully.
- **Axioms.** `#print axioms` on `result` reports only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; the module source contains no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/SpinChains/FourLevelU1SymmetricInjectiveMPS.lean.json`.

Declaration statements:

- `result`: `sha256:22a6051ac678362f08900a3c3ca25aaccac55890f029a8de40047c69d7cc4280`;
- `claim`: `sha256:e5172971e49123232162fee932d40d0b30e8a74f1d0f74b06de75c5ddef5d08d`.

## Triage

Tier 1: an explicitly stated open question in a 2009 Phys. Rev. A paper, preregistered in issue #23698 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal assertion that every normalized four-component family with nonzero local matrices, nonzero real charges with at least two unequal values, a unitary spectral basis and symmetry up to phase at every positive chain length is noninjective is false, where injectivity means injectivity of $\Gamma_n$ for some natural $n$.

**Computed, not formalized** (dossier seat, exact rational arithmetic): the witness's periodic amplitudes at small lengths, consistent with the symmetry and injectivity proved by `result`.

**Argued, not formalized.**

- *Mechanism.* The virtual levels $0,1,2$ allow two nearest-neighbour transitions of the same charge to share one physical matrix, while the transitions between the endpoints carry charges of magnitude two. Four physical matrices therefore suffice even though the source's example assigns a separate physical label to every ordered pair of distinct virtual levels. Here the length-two identities in `two_products`, for exactly the displayed family, recover every matrix unit; `trace_kernel` makes the recovery precise for every $X\in\mathcal M_3(\mathbb C)$ whose sixteen pair traces vanish. Counting physical labels alone misses this shared charge structure.
- *A surviving sufficient obstruction.* Suppose $D\ge1$, at least one $A_k$ is nonzero, and a physical transformation acts as $-I_4$ and fixes every periodic vector exactly, with phase one, at every positive length. Every odd-length trace is then zero. At an odd block length $n$, $\Gamma_n(I_D)=0$; at an even block length $n$, including zero, $\Gamma_n(A_k)=0$ for a nonzero $A_k$, because its entries are traces of words of odd length $n+1$. In either case a nonzero boundary matrix lies in the kernel, excluding injectivity at every block length. This argument explains a parity obstruction under the stated exact-invariance hypothesis. The usual half-integer spin generator produces $-I_4$ at angle $2\pi$, but symmetry up to an unrestricted scalar phase does not supply that hypothesis: the phase can compensate the sign.
- *Effect on the source.* Sanz, Wolf, Pérez-García and Cirac (2009), arXiv:0901.2223v1, state the four-level case as a question, not as a premise of the following two-level proposition or the subsequent $SU(2)$ Hamiltonian construction. The witness rules out an affirmative extension of noninjectivity to the preregistered general-charge four-level setting. It supplies no contradiction to their irreducible $SU(2)$ theorem, whose symmetry hypothesis is stronger, or to their two-level proposition, whose physical dimension differs. Their larger-dimensional examples are compatible with the four-level construction. No Hamiltonian uniqueness or spectral-gap assertion is formalized by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check in #23698 does not establish exhaustive worldwide novelty or priority. Its citation counts, title screening and reading of the five cited preprints were not reproduced here. GPT Pro's wider search, its comparison with Ahrens, Schadschneider and Zittartz (2002), arXiv:cond-mat/0206537, and its report that Mikel Sanz's 2011 thesis repeats the question in Section 9.5 remain unverified source readings. The source text independently checked for this dossier is `Symmetries191208.tex` from arXiv:0901.2223v1, md5 `54c705c1d4b5323bbd6f9276ee90e022`.

The items under “Computed, not formalized” and “Argued, not formalized” are not additional Lean theorems. In particular, periodicity of the witness's circle action, the parity obstruction under exact invariance, and the consequences for the source's arguments are not formalized. The physical interpretation of four levels as a spin-$3/2$ system with an arbitrary chosen $U(1)$ action is distinct from imposing the usual spin generator. The odd-bond-dimension family and even-bond-dimension obstruction mentioned as GPT Pro suggestions in #23698 were not verified and remain open here. Minimal bond dimension and generalizations to other charge spectra are not settled by `result`.

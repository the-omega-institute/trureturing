---
slug: tononi-lewenstein-2025-temporal-bell-contraction-identity
bibkey: tononilewenstein2025temporalbell
doi: 10.1088/2058-9565/adcbce
url: https://arxiv.org/abs/2409.17290v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.result
---

# The temporal Bell endpoint contraction identity for every open XX chain

## Problem

Andrea Tononi and Maciej Lewenstein, *Temporal Bell inequalities in non-relativistic many-body physics*, Quantum Science and Technology 10 (2025), arXiv:2409.17290v4, Methods, “Derivation of Eq. `ICHexact`”, conjecture in `arxiv.tex`, lines 343–353 (md5 `225051e786fe4712ac07f5226a0a99ac`):

> However, we conjecture that
>
> $\text{Re}\big[ \bra{0} f_N f_1 \sigma^x_{N}(t) f_1^\dagger \ket{0} + \bra{0} f_N f_1 \sigma^x_{N}(t) f_N^\dagger \ket{0} \big] = \text{Re}\big[G_{NN}(t) - G_{1N}(t) \big]$,
>
> and
> we verified \cite{sneg} that the exact analytical form of the left- and right-hand sides coincides for $2\leq N \leq 5${, and with exact numerics} up to $N=8$ \cite{mullerrigat2025}.
> In the absence of a general proof, we assume the relation to hold for any value of $N$.

The quotation preserves the TeX wording and citation keys, with display delimiters and the equation label omitted. The source's references identify `sneg` as R. Žitko's SNEG package (2011) and `mullerrigat2025` as preliminary results of G. Müller-Rigat, M. Płodzień, D. Farina, M. Lewenstein and A. Tononi (2025).

Issue [#21106](https://github.com/the-omega-institute/trureturing/issues/21106) fixes the reading: for every integer $N\ge2$ and every real $J,\mu,t$, use the Jordan–Wigner annihilators $f_j$ on the full occupation space $(\mathbb C^2)^{\otimes N}$, its empty vacuum $|0\rangle$, and

$H=-J\sum_{j=1}^{N-1}(f_j^\dagger f_{j+1}+f_{j+1}^\dagger f_j)-\mu\sum_{j=1}^N f_j^\dagger f_j$,

$h_{jj}=-\mu$, $h_{j,j+1}=h_{j+1,j}=-J$, with all other entries zero, and $G(t)=e^{ith}$.

The observable is $\sigma_N^x=\big[\prod_{j<N}(1-2f_j^\dagger f_j)\big](f_N^\dagger+f_N)$, with its prefix product in increasing site order, and $\sigma_N^x(t)=e^{itH}\sigma_N^xe^{-itH}$. With these definitions, the displayed real-part identity is proved.

The source introduces $G$ through the relation $f_j^\dagger(t)=\sum_iG_{ij}(t)f_i^\dagger$ (`arxiv.tex`, lines 153–154 and 291). The settlement follows this relation. Its matrix exponential is not identified with the source's printed spectral formula containing $(-1)^{j-1}$ in $u_{jk}$; the sign distinction is addressed below. The source quotations and bibliography are also in [the literature note](../Library/QuantumContext/tononilewenstein2025temporalbell.md).

## Motivation

The paper evaluates temporal Clauser–Horne probabilities for a Bell pair at the endpoints of an open XX chain. The conjectured sum is the remaining contraction in the probability difference $p_{11}(A_2,B_1(t))-p_{11}(A_2,B_2(t))$. Its all-$N$ identity supplies the conjectural step in the paper's derivation of its analytic CH expression, whose main-text description explicitly depends on Eq. `conjecture` (`arxiv.tex`, lines 158–167).

## Gap

The bounded literature check recorded before any Lean in #21106 reports:

- The orchestrator read the v4 source, which retains the conjecture and its finite-size checks.
- The quick-track search seat reports that OpenAlex work `W4409354437` lists two citing works, arXiv:2507.03440 and arXiv:2512.19260; its reading of their full texts found no treatment of this identity. It also reports no entry in MathDB or `google-deepmind/formal-conjectures`.
- The orchestrator reports no existing repository issue, module or `Problems/` dossier settling this identity. Existing Jordan–Wigner and number-parity declarations provide reusable infrastructure.

`not-found-in-searched-scope`. These reports are bounded search evidence, not an exhaustive novelty claim.

## Route

The module indexes sites by $\mathrm{Fin}\,N$, from $0$ to $N-1$; these correspond to the source's sites $1$ to $N$. Write $f_j=\texttt{fullC}\,j$, $P=\texttt{numberParity}\,N$, $h=\texttt{hopping}\,N\,J\,\mu$ and $H=\texttt{hamiltonian}\,N\,J\,\mu$. Its `vacuumIndex N` is the all-false occupation configuration, and `FullOperator N` is the complex matrix algebra on these configurations.

1. **Creation and annihilation evolution.** For any natural $N$, real $J,\mu$ and $j\in\mathrm{Fin}\,N$, `quadratic_commutator` gives $[H,f_j^\dagger]=\sum_i h_{ij}f_i^\dagger$. For any additional real $t$, `creation_evolution` gives $e^{itH}f_j^\dagger e^{-itH}=\sum_iG_{ij}(t)f_i^\dagger$. Its proof differentiates $e^{-zH}L(e^{zh})e^{zH}$ for complex $z$, where $L(M)=\sum_iM_{ij}f_i^\dagger$; the commutator relation makes the derivative zero. For any natural $N$ and real $J,\mu$, `hamiltonian_hermitian` establishes Hermiticity. For real $J,\mu,t$ and any $A\in\texttt{FullOperator}\,N$, `evolve_adjoint` establishes preservation of adjoints. Consequently `annihilation_evolution`, for any such $N,J,\mu,t,j$, gives $e^{itH}f_je^{-itH}=\sum_i\overline{G_{ij}(t)}f_i$.
2. **Parity removes the string.** For any natural $N$ and $j\in\mathrm{Fin}\,N$, `parity_odd` gives anticommutation of $P$ with both $f_j$ and $f_j^\dagger$. For $N>0$, `sigmaXLast_parity` gives $\sigma_N^x=P(f_{N-1}-f_{N-1}^\dagger)$ in the module's indexing. For every natural $N$ and all real $J,\mu,t$, `parity_stationary` gives $e^{itH}Pe^{-itH}=P$. Thus `evolved_endpoint`, with hypotheses $N>0$ and real $J,\mu,t$, expresses the evolved observable as $P\big(\sum_i\overline{G_{i,N-1}}f_i-\sum_iG_{i,N-1}f_i^\dagger\big)$.
3. **Vacuum contraction.** For any natural $N$ and any $a,b,k,r\in\mathrm{Fin}\,N$, `vacuum_four` gives $\langle0|f_bf_af_k^\dagger f_r^\dagger|0\rangle=\delta_{ak}\delta_{br}-\delta_{bk}\delta_{ar}$, and `vacuum_annihilation_contraction` gives $\langle0|f_bf_af_kf_r^\dagger|0\rangle=0$. For $a,b\in\mathrm{Fin}\,N$ with $a\ne b$ and arbitrary coefficient functions $u,v:\mathrm{Fin}\,N\to\mathbb C$, `vacuum_contractions` gives the sum of contractions of $P(\sum_i u_if_i-\sum_i v_if_i^\dagger)$ with left bra $\langle0|f_bf_a$ and the two right-hand kets $f_a^\dagger|0\rangle,f_b^\dagger|0\rangle$ as $v_b-v_a$. Its proof moves $P$ through the two left annihilators and uses the vacuum's even parity.
4. **Endpoints.** For $N\ge2$ and real $J,\mu,t$, `complex_identity` applies that contraction lemma with the distinct indices $a=0$, $b=N-1$, $u_i=\overline{G_{i,N-1}(t)}$ and $v_i=G_{i,N-1}(t)$. It establishes the complex-valued sum before taking real parts. `result : claim` takes `Complex.re` of that identity under exactly these hypotheses.

The named proof lemmas in this route are private helpers of the canonical module.

## Falsifier

A proof using the opposite hopping sign, the opposite Heisenberg convention, a differently ordered Jordan–Wigner string, or an assumed contraction identity would not establish the preregistered statement. The module defines its Hamiltonian as $\sum_{ij}h_{ij}f_i^\dagger f_j$, fixes the hopping entries to $-J$, defines evolution by $e^{itH}Ae^{-itH}$, and defines the endpoint string explicitly. Its imported `fullC` has occupation-basis coefficient $(-1)^{\#\{i<j:s_i=1\}}$ when removing an occupied site $j$, and zero otherwise. The vacuum matrix element is the all-false row and column. No contraction identity is a premise of `claim`.

The printed spectral expression is a distinct reading of the source's $G$. Neither agreement at small $N$ nor the settlement for $e^{ith}$ certifies that expression as the propagator of the printed Hamiltonian. The separation matters for the individual conjectured contractions even though the final CH expression is insensitive to the resulting endpoint sign.

## Evidence

The canonical source is `D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.lean` (504 lines).

- **Proof.** It proves `result : claim`. A scratch file importing the module checked that exact application and printed the compiled declarations.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom. The imported `result` has this `#print axioms` reading. The source scan `grep -n "sorry\|native_decide\|^axiom" D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.lean` returned no matches.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/SpinChains/TemporalBellContractionIdentity.lean.json`, statement `sha256:610dc9eee73e7aa134d0177d816a5172af2d9f4d25de3448054e17d04f925c4c`.

Declaration statements:

- `result`: `sha256:26ac9f17f68b0440f7568dce1f1995646883deae93ffe9cac54053a336063011`;
- `claim`: `sha256:b65ad5785ca8a934c61650b8d13cecd3adccaaf14dffd89be4b665a6c7d28086`.

## Triage

Tier 1 conjecture of the 2025 source version of a 2024 preprint, preregistered in issue #21106 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every integer $N\ge2$ and all real $J,\mu,t$, the real part of the sum $\langle0|f_Nf_1\sigma_N^x(t)f_1^\dagger|0\rangle+\langle0|f_Nf_1\sigma_N^x(t)f_N^\dagger|0\rangle$ equals $\operatorname{Re}(G_{NN}(t)-G_{1N}(t))$, with precisely the open-chain Hamiltonian, vacuum, endpoint observable and matrix-exponential propagator defined in “Problem”.

**Argued, not formalized.**

- *Decisive mechanism and boundary.* For every natural $N$, `parity_odd` applies to each $j\in\mathrm{Fin}\,N$, so its two sign changes let parity pass through the two left annihilators. For distinct $a,b\in\mathrm{Fin}\,N$ and arbitrary complex coefficient functions $u,v$, `vacuum_contractions` removes the annihilation coefficients and selects $v_b-v_a$. For $N\ge2$ and real $J,\mu,t$, the private `complex_identity` supplies the stronger complex equality used by `result`; the public result states only its real part. There is no asymptotic or nonzero-coupling restriction. If the endpoints are separately identified at $N=1$, the left-hand sum vanishes because $f_1^2=0$, and the right-hand difference is $G_{11}-G_{11}=0$; this degenerate observation is outside `claim`.
- *Extension beyond the uniform chain.* For a finite $N\ge2$ and an arbitrary Hermitian one-particle matrix $q$, put $H_q=\sum_{ij}q_{ij}f_i^\dagger f_j$ and $G_q=e^{itq}$ for real $t$, keeping the same vacuum and last-site string. The CAR calculation gives $[H_q,f_j^\dagger]=\sum_iq_{ij}f_i^\dagger$, so the derivative cancellation in the creation-evolution argument still applies. Hermiticity gives the adjoint evolution; every quadratic term commutes with number parity because it contains two odd factors. For distinct endpoints the unchanged vacuum calculation selects $(G_q)_{NN}-(G_q)_{1N}$. This gives a full algebraic argument for the complex extension to nonuniform or long-range number-conserving hopping. The module has no declaration parameterized by arbitrary $q$. Pairing terms and interactions require different evolution formulas and remain open here.
- *The printed spectral sign.* In source indexing let $v_j(k)=U_{j-1}(\cos k)/[\sum_lU_{l-1}^2(\cos k)]^{1/2}$ with $k=\pi m/(N+1)$, $1\le m\le N$. The sine recurrence $v_{j-1}+v_{j+1}=2\cos(k)v_j$, with $v_0=v_{N+1}=0$, gives $hv=(-2J\cos k-\mu)v$; finite sine orthogonality supplies an orthonormal eigenbasis. The source prints $u=Dv$ with the same eigenvalues (`arxiv.tex`, lines 151–154). Its spectral sum is therefore $\widetilde G=DGD$, equivalently the exponential of $DhD$, which has hopping $+J$. Thus $\widetilde G_{NN}=G_{NN}$ and $\widetilde G_{1N}=(-1)^{N+1}G_{1N}$: the endpoint entry changes sign for even $N$. This general sign calculation is not part of `result`.
- *Effect on the paper.* The source's other two contractions in this probability difference are $G_{NN}^*$ and $G_{1N}^*$ (`arxiv.tex`, lines 339–340). Adding their real parts to the settled real-part sum gives $2\operatorname{Re}G_{NN}$. Under the source's unformalized projector reduction at lines 330–336, multiplication by $\sqrt2/8$ yields its Eq. `p11A2B1minusp11A2B2`, $p_{11}(A_2,B_1(t))-p_{11}(A_2,B_2(t))=(\sqrt2/4)\operatorname{Re}G_{NN}$. Combining this with the other two probability formulas at lines 312–324 gives its Eq. `ICHexact`, $I_{CH}^{(N)}(t)=1/2+(\sqrt2/4)(|G_{NN}|^2+|G_{1N}|^2+\operatorname{Re}G_{NN})$. The conjectural contraction step in that derivation is therefore supplied for the defining propagator. The displayed CH expression is invariant under $G\mapsto DGD$, since the last diagonal entry and both endpoint absolute squares are unchanged. The sign issue consequently does not alter that expression. The probability reductions, Bell-violation intervals, revival estimates, thermodynamic claims and Lieb–Robinson interpretation are not conclusions of the Lean module.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The OpenAlex citation inventory, the two citing-paper readings, the MathDB and `google-deepmind/formal-conjectures` searches, and the preregistration's historical repository search are attributed reports from #21106 and were not independently reproduced. The v4 TeX quotation and its hash were independently checked. The paper's symbolic checks through $N=5$ and exact numerical checks through $N=8$, including the cited preliminary results, were not reproduced.

All extensions, spectral-sign calculations and source-probability deductions in “Argued, not formalized” are outside the type of `result`. In particular, the arbitrary-Hermitian-hopping extension, the $N=1$ observation, and the full CH formula are not formalized by this settlement. No general result for pairing Hamiltonians, interacting chains, other states or other measurement choices is claimed. The source's remaining probability/projector calculations and its physical or asymptotic interpretations have not received Lean verification here.

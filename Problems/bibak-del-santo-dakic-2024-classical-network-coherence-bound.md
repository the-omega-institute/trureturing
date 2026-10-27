---
slug: bibak-del-santo-dakic-2024-classical-network-coherence-bound
bibkey: bibakdelsantodakic2024coherence
doi: 10.1103/PhysRevLett.133.230201
url: https://arxiv.org/abs/2407.11122v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.result
---

# The classical network coherence maximum is $1/4$ for every $n\ge2$

## Problem

F. Bibak, F. Del Santo and B. Dakić, *Quantum coherence in networks*, arXiv:2407.11122v1 [quant-ph]; Phys. Rev. Lett. 133, 230201 (2024), subsection "Generalization of the inequality to $n$ parties", `main.tex`, lines 277–278:

> We obtained classical bound $C_n^{\text{cl}}$ by substituting $p_{\text{cl}}$ (Eq.~\eqref{pncl}) into the expression for $C_n$ and performing extensive numerical optimization. For all tested values of $n \in \{2, \ldots, 10\}$, we consistently obtained $\text{max}(C_n^{\text{cl}}) = \frac{1}{4}$. Consequently, we conjecture that $\text{max}(C_n^{\text{cl}}) = \frac{1}{4}$ for all $n$.

The quotation preserves the source's words and mathematical content, with inline TeX math delimiters rendered as dollar delimiters and the source line break joined. The source read is `main.tex` from the v1 source archive, md5 `c47930e35162d18bc08d65fb1201100d`.

Issue [#21125](https://github.com/the-omega-institute/trureturing/issues/21125) fixes the reading: for every integer $n\ge2$, maximize over $\gamma\in[0,1]$ and binary probability laws $p_i,q_i$ the merit of

$r(a)=\gamma\prod_{i=0}^{n-1}p_i(a_i)+(1-\gamma)\prod_{i=0}^{n-1}q_i(a_i).$

Each local law is nonnegative and sums to one. This is the mathematical mixture in the source's equation `pncl`, lines 248–253. Define $E=\{a:\sum_i a_i\equiv0\pmod2\}$ and $O=\{a:\sum_i a_i\equiv1\pmod2\}$. The reading of equation `cn`, lines 263–271, is

$C_n(r)=\frac12\left|\sum_{\substack{a,b\in E\\a\ne b}}r(a)r(b)-\sum_{\substack{a,b\in O\\a\ne b}}r(a)r(b)\right|.$

The pairs are ordered, and both strings in each pair have the stated parity. The factor $1/2$ counts each unordered pair once. The conclusion is an attained maximum of $1/4$, as expressed by `IsGreatest`, rather than an unevidenced supremum. The restriction $n\ge2$ is explicit: at $n=1$, each parity class has only one string and the merit is zero.

The source definitions and quotations are also collected in [the literature note](../Library/QuantumContext/bibakdelsantodakic2024coherence.md).

## Motivation

The bound supplies an exact classical threshold for the source's nonlinear witness of coherence in a postselected ring network. It applies to every mixture of two binary product laws, without imposing parity support on the mixture. Its sharpness prevents lowering the threshold within this model. Comparing that threshold with the source's proposed quantum distribution gives the party-number dependence of the witness gap; the physical realization of that distribution is a separate claim.

## Gap

The literature check recorded in #21125 has the bounded status `not-found-in-searched-scope`:

- The v1 source explicitly states the conjecture and reports numerical optimization only for $n\in\{2,\ldots,10\}$.
- The preregistration reports an OpenAlex listing of 10 citations and an APS count of 11. It reports reading the citing works with arXiv identifiers 2609.10624, 2604.17196, 2512.17535, 2512.13357, 2512.09144, 2509.15002, 2507.09261, 2506.14115, 2506.11254 and 2406.15853 without finding an all-$n$ bound. The journal-only citing work, DOI 10.1016/j.physleta.2026.131466, was inaccessible with HTTP 429.
- It reports no entry in MathDB or `google-deepmind/formal-conjectures`, and no repository issue, module or dossier for this bound. It identifies `D5/S3/TotalVariation/ParityKernelMasses.lean` as related infrastructure.

The v1 source and its conjecture are independently checked here. The other reported literature readings do not constitute an exhaustive novelty or priority claim.

## Route

Write $\chi(a)=(-1)^{\sum_i a_i}$.

1. **Parity reduction (`parity_reduction`).** For every natural $n$ and every real function $r$ on binary strings satisfying $\sum_a r(a)=1$, put $T=\sum_a\chi(a)r(a)$ and $U=\sum_a\chi(a)r(a)^2$. Then $C_n(r)=|T-U|/2$. No nonnegativity hypothesis is needed for this lemma. Its finite-set identity `off_diagonal` holds for any finite set in a type with decidable equality and any real function: the distinct ordered-pair sum is the square of the total minus the sum of squares. The two parity masses sum to one.
2. **Product factorization (`signed_product`, `mixture_factorization`).** For every natural $n$ and arbitrary real local functions $w_i$, `signed_product` factors $\sum_a\chi(a)\prod_iw_i(a_i)$ as $\prod_i(w_i(0)-w_i(1))$. For every natural $n$, $\gamma\in[0,1]$ and local probability laws $p_i,q_i$, `mixture_factorization` gives

   $C_n(r)=\frac{\gamma(1-\gamma)}2|A+B-2D|,$

   where $x_i=p_i(0)-p_i(1)$, $y_i=q_i(0)-q_i(1)$, $A=\prod_i x_i$, $B=\prod_i y_i$ and $D=\prod_i\frac{x_i+y_i}{2}$. Local normalization is essential to the square and mixed-product identities in this calculation.
3. **Uniform bound (`cube_bound`, `upper_bound`).** For every natural $n$ and $x,y:\mathrm{Fin}\,n\to\mathbb R$ satisfying $x_i,y_i\in[-1,1]$ for every $i$, `cube_bound` proves $|A+B-2D|\le2$. Its finite-coordinate induction starts from zero. If $P,Q,D_s$ are the partial products, $F=P+Q-2D_s$, $u=(1+x_i)/2$ and $v=(1+y_i)/2$ at a coordinate $i$ outside the finite set of partial-product coordinates, the new expression is

   $uvF+u(1-v)(P-Q)+(1-u)v(Q-P)+(1-u)(1-v)(-F).$

   The coefficients are nonnegative and sum to one. The induction hypothesis bounds $|F|$ by two, while the coordinate bounds give $|P|,|Q|\le1$, hence $|P-Q|,|Q-P|\le2$. For every natural $n$, $\gamma\in[0,1]$ and local probability laws $p_i,q_i$, `upper_bound` combines the factorization and cube bound with $\gamma(1-\gamma)\le1/4$ to prove $C_n(r)\le1/4$.
4. **Attainment (`attainment`).** For every natural $n$ with $2\le n$, take $\gamma=1/2$, all $p_i=\delta_0$, and $q_0=q_1=\delta_1$, with $q_i=\delta_0$ for $i\ge2$. These are probability laws; $A=B=1$ and $D=0$, giving $C_n(r)=1/4$. The resulting distribution has equal mass on $0^n$ and $110^{n-2}$. `result` combines this nonempty attainable set with `upper_bound` to establish `claim`.

## Falsifier

A settlement requires both a bound on every admissible mixture and attainment in that same class. An admissible mixture with merit above $1/4$, or a dimension $n\ge2$ with no attaining mixture, would contradict `claim`.

Source fidelity requires the binary alphabet, two product components, local nonnegativity and normalization, $\gamma\in[0,1]$, ordered distinct pairs, both parity restrictions and the prefactor $1/2$. The module implements these through `Probability`, `windowLaw`, `occupationCount`, `parity`, `classicalMixture` and `coherenceMerit`, with `false` representing zero and `true` representing one. It does not identify arbitrary classical network correlations with this two-component class; the source's physical reduction to that class is outside the Lean statement.

## Evidence

The canonical source is `D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.lean` (297 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/NetworkCoherenceClassicalBound.lean.json`, statement `sha256:3be3b3d7d9e625740e7f30dcef7f49b31e71b3ea4fea9c089bf9b62c7de4519d`.

Declaration statements:

- `result`: `sha256:2e24701d86d0d44e1c465fef4f9aff454b418d75bcde6d27e33f876cbae3456c`;
- `claim`: `sha256:d943804b22fc39e21b1d424a3bf0946bf6205a7b6e8eb5a63c57efda33a4d6f8`.

## Triage

Tier 1: an explicit conjecture of a 2024 paper, supported there numerically for $2\le n\le10$, preregistered in issue #21125 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge2$, the set of merits of mixtures $\gamma\prod_i p_i+(1-\gamma)\prod_i q_i$, over $\gamma\in[0,1]$ and nonnegative normalized probability laws $p_i,q_i$ on the binary alphabet at every coordinate, has greatest element $1/4$. Thus $1/4$ is attained and bounds every member of this set.

**Argued, not formalized.**

- *Decisive mechanism and sharpness.* For every natural $n$, $\gamma\in[0,1]$ and local binary probability laws, `mixture_factorization` reduces the merit to $\gamma(1-\gamma)|A+B-2D|/2$. For every natural $n$ and coordinate values $x_i,y_i\in[-1,1]$, `cube_bound` bounds the last absolute value by two, independently of dimension. These two lemmas yield the finer bound $C_n\le\gamma(1-\gamma)$. For $n\ge2$, the deterministic local laws in `attainment`, with an arbitrary fixed $\gamma\in[0,1]$, have $A=B=1,D=0$ and therefore attain this finer bound. Thus the fixed-weight maximum is also determined by the same argument; that parameterized maximum is not a separate statement of `result`.
- *Small dimensions.* At $n=0$ there is only one string; at $n=1$ each parity class contains one string. Neither dimension has a distinct same-parity pair, so the merit is zero for every real function on strings. The conjecture's unqualified phrase "for all $n$" must retain the preregistered restriction $n\ge2$.
- *More product components.* At $n=3$, the equal mixture of the four deterministic even strings has twelve ordered distinct pairs, each contributing $1/16$, and no odd contribution. Its merit is $\tfrac12\cdot12/16=3/8>1/4$. Consequently, extending the same bound to arbitrary finite mixtures of product laws is false. The sharp maximum for exactly three product components is not determined here and remains open in this dossier.
- *Effect on the paper.* The source states at `main.tex`, line 278: "This result implies that the discrepancy between quantum and classical correlations increases with the number of parties, reaching a maximum value of $\frac{1}{4}$ in the limit as $n$ approaches infinity." Its quantum value is displayed at lines 272–276 as $C_n^Q=1/2-2^{-n}$. For $n\ge2$, the uniform even distribution described at line 239 has $m=2^{n-1}$ support strings of mass $1/m$, so its ordered-pair merit is $m(m-1)/(2m^2)=1/2-2^{-n}$. Combining this evaluation with the proved classical maximum gives a gap $\Delta_n=1/4-2^{-n}$ for $n\ge2$: it is zero at $n=2$, positive for $n\ge3$, increases by $2^{-(n+1)}$ from $n$ to $n+1$, and tends to $1/4$ without attaining that limit at finite $n$. This supplies the classical bound needed for the quoted comparison. The quantum realization, global logical optimality and physical interpretation are not conclusions of `result`.

## ASSUMED-UNVERIFIED

The bounded literature check in #21125 does not establish exhaustive worldwide novelty or priority. Its citing-paper readings, database searches, citation counts and repository search were not independently reproduced. The downloaded arXiv abstract page confirms the DOI and shows only v1 in its submission history. The journal-only citing work with DOI 10.1016/j.physleta.2026.131466 was not read; the preregistration records HTTP 429. The journal text was not compared with the downloaded v1 TeX, and the source's numerical optimization was not reproduced.

The fixed-weight refinement, small-dimension analysis, four-component example and gap calculation are not additional conclusions of `result`. The three-component optimum remains open here. The physical derivation of the two-product model, the quantum state's preparation and postselection, and the source's claim of a global logical maximum are not formalized by this module. Only the stated classical attainable maximum is the settlement.

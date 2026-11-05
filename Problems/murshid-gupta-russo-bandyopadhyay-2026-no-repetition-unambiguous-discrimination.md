---
slug: murshid-gupta-russo-bandyopadhyay-2026-no-repetition-unambiguous-discrimination
bibkey: murshidguptarussobandyopadhyay2026nonlocality
doi: 10.22331/q-2026-07-23-2174
url: https://arxiv.org/abs/2506.20560v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.result
---

# Optimal unambiguous discrimination without repetition for equal-overlap states

## Problem

S. Murshid, T. Gupta, V. Russo and S. Bandyopadhyay, *Quantum nonlocality without entanglement and state discrimination measures*, arXiv:2506.20560v3; Quantum 10, 2174 (2026), consider the uniform ensemble $\mathcal E_{N,k}$ of ordered products of $k$ distinct members of $N$ normalized states $\psi_i\in\mathbb C^N$ with $\langle\psi_i,\psi_j\rangle=s\in(0,1)$ for $i\ne j$.

Their conjecture appears in the TeX source `revised_02.tex`, lines 970–984, subsection “Conjecture for multipartite systems”. The quotations retain the source macro `\E`, meaning $\mathcal E$, and its equation reference; the displays are written inline.

> For the family of ensembles of multipartite pure product states $\E_{N,k}$ given by Equation \eqref{eq:gensemble} the following holds for all $N \geq 3$ and $2 \leq k \leq N$

> $p_{_{L}}^{me}\left(\E_{N,k}\right) <p_{_{G}}^{me}\left(\E_{N,k}\right),$
>
> $p_{_{L}}^{ud}\left(\E_{N,k}\right) =p_{_{G}}^{ud}\left(\E_{N,k}\right).$

> Moreover, the optimal unambiguous discrimination probability of $\E_{N,k}$ is given by

> $p_{_{G}}^{ud}\left(\E_{N,k}\right) = \begin{cases} (1-s)^k, & \text{ when } k < N \\ (1-s)^{N-1}(1+\left(N-1\right)s), & \text{ when } k=N. \end{cases}$

T. Gupta, S. Murshid and S. Bandyopadhyay, *Unambiguous discrimination of sequences of quantum states*, arXiv:2402.06365v2; Phys. Rev. A 109, 052222 (2024), pose the earlier no-repetition question in `GMBjournal-revision-02.tex`, lines 883–903:

> In our scenario, as well as in more general ones (which we could not solve), repetitions of states are allowed in a sequence. The third problem considers the situation where it is not. Restrict $k<N$ and by $S'_{N,k}$ denote the set of sequences of length $k$, where no element is repeated.

> Now assume that the inner products of the states $\left|\psi_{i}\right\rangle$ are equal and positive, say, $s>0$. Then $S_{N,k}^{\prime}\subset S_{N,k}$, where $S_{N,k}$ is the set of sequences considered in this paper. Under these restricted conditions, numerical experiments ($N=3$, $k=3$) still suggest that the optimal probability for distinguishing between the elements of $S_{N,k}^{\prime}$ unambiguously once again obeys $(1-s)^{k}$. However, for arbitrary values of both $N$ and $k$, whether one could benefit from collective measurements in this scenario is an interesting problem to consider in the future.

The source definitions and locators are also recorded in [the 2026 literature note](../Library/QuantumContext/murshidguptarussobandyopadhyay2026nonlocality.md) and [the 2024 literature note](../Library/QuantumContext/guptamurshidbandyopadhyay2024sequences.md).

Issue [#21233](https://github.com/the-omega-institute/trureturing/issues/21233) fixes the settlement as the unambiguous clauses of the conjecture, together with the 2024 question for $2\le k<N$ under these hypotheses. These are proved. The minimum-error clause of the conjecture is not settled by this result.

## Motivation

The 2026 paper studies whether nonlocality without entanglement depends on the discrimination measure: local operations and classical communication (LOCC) can attain the global optimum for unambiguous discrimination even when they are suboptimal for minimum-error discrimination. For the no-repetition family, an exact unambiguous optimum separates this part of the question from the minimum-error problem. It also determines whether the correlations imposed by distinct labels create an advantage for collective unambiguous measurements, the question raised by Gupta, Murshid and Bandyopadhyay (2024).

## Gap

Issue #21233 records the bounded literature check before any Lean:

- The two source versions retain the question and conjecture. The 2026 source proves the $\mathcal E_{3,2}$ unambiguous case and supplies numerical Gram spectra for $\mathcal E_{3,3}$, $\mathcal E_{4,2}$ and $\mathcal E_{4,3}$ (`revised_02.tex`, lines 947–966).
- The search report cited in the issue records readings of arXiv:2603.05452, 2510.20311, 2511.07848, 2508.05050, 2409.13379, 2608.22393 and 2605.09710v2, and the abstract of DOI 10.1007/s10773-026-06362-w, without a general no-repetition settlement. It identifies arXiv:2409.08705 as addressing sequences with repetitions.
- The preregistration records no earlier repository issue, module, Library note or Problems dossier for either source.

`not-found-in-searched-scope`.

## Route

Let $I=\mathrm{Label}\,N\,k$ be the injective maps from $k$ positions to $N$ labels, $\phi_x=\mathrm{productState}\,\psi\,x$, and $K_{xy}=\prod_j(1\text{ if }x_j=y_j\text{, otherwise }s)$. Write $v=\mathrm{value}\,N\,k\,s$, with the two branches quoted above on $k\le N$. All helper names below refer to the private declarations of the settlement module.

1. **Gram reduction.** For any natural $N,k$, real $s$ and $\psi$ satisfying `IsEquiangular ψ s`, `product_gram` identifies the Gram matrix of $\phi$ with $K$. For any family $\phi$ and effects $E,E_0$ satisfying `IsUnambiguousMeasurement φ E E₀`, `measurement_gram_bound` proves $\mathrm{Gram}(\phi)-\operatorname{diag}(q)\succeq0$, where $q_x=\operatorname{Re}\langle\phi_x,E_x\phi_x\rangle$. Its hypothesis includes positivity of every effect, completeness and zero probability of every erroneous output. Positivity turns the no-error condition into $E_x\phi_y=0$ for $y\ne x$, so compression of the inconclusive effect gives this matrix inequality.
2. **Symmetrization.** For $k\le N$, any real $s$ and $q:I\to\mathbb R$ satisfying $K-\operatorname{diag}(q)\succeq0$, `symmetrized_bound` proves $K-\bar q I\succeq0$, where $\bar q=|I|^{-1}\sum_xq_x$. Relabelling by permutations preserves $K$ and is transitive on $I$. The condition $k\le N$ supplies an injection and hence $|I|>0$, so the averaging denominator is nonzero.
3. **A nonzero determinant eigenvector.** Put $G=(1-s)I+sJ$, with $J$ the all-ones matrix. For any natural $N,k$, real $s$, vectors $u_i\in\mathbb C^N$ and complex numbers $\lambda_i$ satisfying $Gu_i=\lambda_i u_i$ for every $i\in\mathrm{Fin}\,k$, `alternant_kernel` proves that $w(x)=\det(u_i(x_j))_{j,i}$ satisfies $Kw=(\prod_i\lambda_i)w$. The determinant vanishes on tuples with repeated labels; this permits restriction from all tuples to $I$. Nonzeroness is supplied separately: for $k<N$ and any real $s$, `short_eigenvector` uses the $k$ differences $e_i-e_k$ (indices starting at zero), whose determinant on the injection listing the first $k$ labels is one. For every natural $n$ and real $s$, `full_eigenvector` treats $N=k=n+1$ using $n$ differences and the constant-one vector. Their eigenvalues give $(1-s)^k$ and $(1-s)^{N-1}(1+(N-1)s)$, respectively.
4. **The global bound.** For real $s,a,v$, if $K-aI\succeq0$ and $w\ne0$ satisfies $Kw=vw$, `eigenvalue_bound` gives $a\le v$ by evaluating the quadratic form on $w$. Combining the preceding steps, `upper_bound` assumes $N\ge3$, $2\le k\le N$, real $s$, `IsEquiangular ψ s` and an unambiguous measurement on `productState ψ`, and bounds its uniform average success by `value N k s`.
5. **Attainment by independent measurements.** For any natural $N$, $0<s<1$ and `IsEquiangular ψ s`, `single_system_measurement` constructs a positive POVM $F$ summing to the identity with $\langle\psi_j,F_i\psi_j\rangle=(1-s)\delta_{ij}$ and $\langle\psi_j,F_?\psi_j\rangle=s$. In coordinates, if $A$ has columns $\psi_i$ and $B=A^{-1}$, its effects are $B^*H_oB$, where $H_i=(1-s)e_ie_i^*$ and $H_?=sJ$; the positive-definite Gram matrix makes $A$ invertible. For any $\psi,F,s$ with these outcome probabilities, positive effects and $\sum_oF_o=I$, `short_product_attainment` assumes $k<N$ and accepts only fully conclusive patterns. Under the same POVM and probability hypotheses, `full_product_attainment` assumes $1\le N$ and $k=N$ and also accepts every pattern with exactly one inconclusive position. For $x,y:\mathrm{Label}\,N\,N$ and $j\in\mathrm{Fin}\,N$, `full_label_eq_off` shows that agreement at every position other than $j$ implies $x=y$; this is the uniqueness needed for that recovery rule. The full-sequence probability is $(1-s)^N+Ns(1-s)^{N-1}=v$. Under $N\ge3$, $2\le k\le N$, $0<s<1$ and `IsEquiangular ψ s`, `product_attainment` combines the two constructions, and `result` pairs attainment with the global bound.

## Falsifier

A bound for a different ensemble or an unattainable success value would not settle the question. The compiled definitions fix the correspondence:

- `Label N k` consists of ordered injective maps, so every distinct-label sequence is present. `IsEquiangular` requires unit vectors and equal real inner products, not merely equal absolute values of inner products.
- `productState` uses the tensor-product coordinate basis. `IsUnambiguousMeasurement` requires positive conclusive and inconclusive effects summing to the identity and zero erroneous probability for every pair of different labels.
- `averageSuccess` is the finite uniform average of the real quadratic-form readouts. The label set is nonempty when $k\le N$.
- `IsProductProtocol` applies one fixed POVM $F$, with $N$ conclusive outcomes and one inconclusive outcome, at every position, and sums its product effects over the fibers of a classical decision rule. `result` asserts both that the induced measurement is unambiguous and that it attains $v$.

The theorem states a bound for every feasible measurement and supplies a feasible attaining measurement. It does not define an optimum by an unchecked infimum or supremum. The LOCC interpretation is the argument below; LOCC is not a separate predicate in `claim`.

## Evidence

The canonical source is `D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.lean` (929 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** The scratch import and `#print axioms` report only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/PureState/NoRepetitionSequenceUnambiguousDiscrimination.lean.json`, statement `sha256:85f5086471c373e44b3d0b65548bc0e009d8f52c5e27a0308ea9c26fa387e968`.

Declaration statements:

- `result`: `sha256:bafaeaf92ec4d4042fdd6819a5cecd2a5ad4c0bbcff3e7585aba373eb4c95a8c`;
- `claim`: `sha256:7e19a5ff0a878db727b4aa56ce72b724368c5827e804201c50f2a4f04248de48`.

## Triage

Tier 1: the explicit no-repetition question of a 2024 paper and the unambiguous clauses of an explicit conjecture of a 2026 journal paper, preregistered in issue #21233 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $N\ge3$, $2\le k\le N$, real $0<s<1$ and $N$ vectors $\psi_i\in\mathbb C^N$ with $\langle\psi_i,\psi_i\rangle=1$ and $\langle\psi_i,\psi_j\rangle=s$ for $i\ne j$, every unambiguous measurement on their distinct-label product sequences has uniform average success at most $v(N,k,s)$, and there exist a single-system POVM, a classical decision rule and induced conclusive and inconclusive effects forming an unambiguous product protocol with uniform average success exactly $v(N,k,s)$. Here $v(N,k,s)=(1-s)^k$ for $k<N$, and $v(N,N,s)=(1-s)^{N-1}(1+(N-1)s)$.

**Argued, not formalized.**

- *Decisive mechanism and sharpness.* For any natural $N,k$, real $s$, vectors $u_i\in\mathbb C^N$ and complex $\lambda_i$ satisfying $Gu_i=\lambda_i u_i$ for every $i$, `alternant_kernel` restricts the determinant eigenvector to injective labels. For $k<N$ and real $s$, `short_eigenvector` supplies a nonzero vector with eigenvalue $(1-s)^k$; for $N=k=n+1$ with $n\in\mathbb N$ and real $s$, `full_eigenvector` supplies a nonzero vector with the full-sequence value. Thus the proof needs no full diagonalization. Under all the hypotheses of `result`, attainment makes the global average bound sharp for every allowed $N,k,s,\psi$; there is no slack to remove by a better collective measurement.
- *The LOCC and supremum bridge.* Under those same hypotheses, each party can perform the POVM supplied by `result` on its own subsystem, send its outcome to a classical processor, and apply the supplied decision rule. The choices of local measurement need no messages or adaptation. This is an LOCC implementation of the induced effects. Consequently both the LOCC and unrestricted sets of feasible unambiguous success values contain $v$, and both are bounded above by $v$. Their suprema are therefore $v$, giving the source's $p_L^{ud}=p_G^{ud}=v$ and answering the 2024 question in the stated range. The nonemptiness and boundedness here follow from the attained value and universal bound; the module does not formalize these supremum definitions or LOCC membership.
- *Why the branch changes at $k=N$.* For any natural $N$, $0<s<1$ and $\psi:\mathrm{Fin}\,N\to\mathbb C^N$ satisfying `IsEquiangular ψ s`, `single_system_measurement` supplies the POVM described in the Route. Every pattern matching the input's conclusive labels has positive probability. If $k<N$ and one position is inconclusive, the other $k-1$ labels leave $N-k+1\ge2$ possible labels for that position. If $k=N$ and $r$ positions are inconclusive, there are $r!$ completions. Thus exactly one erased label is recoverable in the full-sequence case, whereas two erased labels remain ambiguous. This counting argument describes the limit of classical recovery from this POVM's outcomes, not a classification of all optimal measurements. The 2024 numerical suggestion at $N=k=3$, quoted above, lies outside its declared $k<N$ restriction: the settled full-sequence value is $(1-s)^2(1+2s)$, exceeding $(1-s)^3$ by $3s(1-s)^2>0$ for $0<s<1$.
- *Ambient-dimension extension.* For $N\ge3$, $2\le k\le N$ and normalized states in any finite-dimensional complex Hilbert space with the same real overlap $0<s<1$, their Gram matrix is positive definite because $z^*Gz=(1-s)\|z\|^2+s|\sum_i z_i|^2>0$ for $z\ne0$. Their span therefore has dimension $N$. Choosing an orthonormal basis identifies it isometrically with $\mathbb C^N$. Compressing any global POVM to the tensor power of this span preserves positivity, completeness and all relevant probabilities, so `result` bounds its success there. Conversely, extend the attaining single-system POVM from the span by assigning the orthogonal complement to the inconclusive effect. This preserves its probabilities on the given states and yields the same product attainment. This extension is a prose argument; `result` itself quantifies over $\mathbb C^N$.
- *Effect on the source and neighbouring questions.* The unambiguous equality and exact value in the conjecture, and the unambiguous part of the multipartite research direction in the 2026 Discussion (`revised_02.tex`, line 1027), are settled under the stated hypotheses. The proposed measure-dependent nonlocality of the whole family still requires its separate strict minimum-error inequality. The Discussion's PPT-versus-LOCC minimum-error comparison, reversed separation between discrimination measures, and removal of equiangularity (lines 1029–1035) are not settled. Nonuniform priors, incomplete subsets of injective labels, unequal or nonreal overlaps, $k=1$, $N<3$ and the endpoints $s=0,1$ are outside `claim`.

## ASSUMED-UNVERIFIED

The literature check is bounded by the report in #21233 and does not establish exhaustive worldwide novelty or priority. Its citing-work readings, abstract reading, citation counts and earlier repository-search results have not been independently reproduced. MathDB and google-deepmind/formal-conjectures were not reported as checked. The two primary TeX sources were read directly: `revised_02.tex` from arXiv:2506.20560v3 has MD5 `1f552f21910a72e61d78246fe6c76ee9`; `GMBjournal-revision-02.tex` from arXiv:2402.06365v2 has MD5 `a3c17bf5369a6647a1dc646ac2ba07da`. The source papers' original numerical spectra and SDP experiments, including the 2024 reported $N=k=3$ experiment and the minimum-error comparisons, were not reproduced as those experiments.

The statements labelled “Argued, not formalized” are not additional compiled conclusions of `result`. In particular, the explicit LOCC implementation and supremum interpretation, completion-count argument, arithmetic comparison with the 2024 numerical suggestion, and extension to other ambient dimensions have no separate Lean declarations in this settlement. No minimum-error claim or generalization beyond the hypotheses of `claim` is attributed to the formal result.

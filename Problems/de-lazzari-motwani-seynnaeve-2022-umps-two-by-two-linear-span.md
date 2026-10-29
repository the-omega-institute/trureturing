---
slug: de-lazzari-motwani-seynnaeve-2022-umps-two-by-two-linear-span
bibkey: delazzarimotwaniseynnaeve2022umpsspan
doi: 10.3842/SIGMA.2022.099
url: https://arxiv.org/abs/2204.10363v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.result
---

# The exact linear-span dimension of binary bond-two uniform matrix product states

## Problem

Claudia De Lazzari, Harshit J. Motwani and Tim Seynnaeve, *The Linear Span of Uniform Matrix Product States*, SIGMA 18 (2022), 099, DOI 10.3842/SIGMA.2022.099; arXiv:2204.10363v3, Conjecture 3.8 (`sigma22-099.tex`, lines 540–547):

> **Conjecture 3.8 (Corollary of Conjecture 3.7).**
>
> $$
> \dim\langle\operatorname{uMPS}(2,2,d)\rangle=\begin{cases}
> \displaystyle\frac{1}{192}\big(d^4-4d^2+192d+192\big)&\text{for }d\text{ even,}\\
> \displaystyle\frac{1}{192}\big(d^4-10d^2+192d+201\big)&\text{for }d\text{ odd.}
> \end{cases}
> $$

The quotation expands the source's operator macro. Definition 2.1, lines 214–225, takes the closure of the image of the map sending a pair of complex $2\times2$ matrices $X,Y$ to the tensor with coefficient $\operatorname{tr}(A_{i_1}\cdots A_{i_d})$, where $A_0=X$ and $A_1=Y$. Both the bond dimension and the physical dimension are two; $d$ is the number of sites.

Issue [#23810](https://github.com/the-omega-institute/trureturing/issues/23810) fixes the reading for every positive length. In Lean the length is named $n$. Write $S_n$ for the complex linear span of `UniformMPSExpectedDimensionRefutation.uMPS 2 2 n`: this set is the image of `traceWord 2 2 n`, whose coefficient at $i:\mathrm{Fin}\,n\to\mathrm{Fin}\,2$ is the trace of the ordered product of the selected matrices. The proposition `claim` asserts the displayed formula for $\dim_{\mathbb C}S_n$ for every $n\in\mathbb N$ with $1\le n$, with the dimension and polynomial evaluated in $\mathbb Q$. It is proved.

The source's closure and the module's image have the same linear span by the argument under Triage. The source definitions and locator are also recorded in [the literature note](../Library/Geometry/delazzarimotwaniseynnaeve2022umpsspan.md).

## Motivation

The source studies which linear equations vanish on uniform matrix product states. The case of two matrices of size two is its smallest nontrivial case: determining the span dimension measures the linear constraints left beyond the tensor parametrization. The question concerns the dimension of a vector space, rather than the Krull dimension of the parametrized variety. The exact formula replaces finite-length computations and a leading-term upper estimate by an equality at every positive length.

## Gap

The bounded literature check is recorded in #23810:

- De Lazzari, Motwani and Seynnaeve's v3 source states Conjecture 3.8 as a consequence of the stronger weight-space Conjecture 3.7; Section 4 proves the latter only for weights $0,1,2,3$ and gives an asymptotically matching upper bound for the total dimension.
- Tim Seynnaeve, *Matrix product states, geometry, and invariant theory*, arXiv:2212.13806v2 (2023 version), `MatrixProductStatesInvariantTheory.tex`, lines 460–466, retains a representation-decomposition problem and says that its solution “would solve Conjectures 3.7 and 3.8”. This passage was checked directly in that source.
- The orchestrator's searches of the authors' arXiv listings, the 40 most recent arXiv abstracts matching uniform matrix product states, web results, and repository issues and pull requests returned no settlement of this conjecture within their searched scope.
- The doctoral thesis and citation-list checks were incomplete: the thesis request returned HTTP 403, and the OpenAlex citing-work list and Semantic Scholar requests returned HTTP 429.

`not-found-in-searched-scope`.

## Route

All matrices in this route are complex $2\times2$ matrices. Put $s=\operatorname{tr}X$, $t=\operatorname{tr}Y$, $u=\det X$, $v=\det Y$, $w=\operatorname{tr}(XY)$ and $C=XY-YX$. The helper module `UniformMPSTwoByTwoTraceWords` defines these five functions as `invariants`, their monomials as `mon`, their weighted degree as `degree`, and

$$
\delta=w^2-stw+s^2v+t^2u-4uv.
$$

For $e\in\mathbb N^5$, write $m_e=s^{e_0}t^{e_1}u^{e_2}v^{e_3}w^{e_4}$ and $q(e)=e_0+e_1+2e_2+2e_3+2e_4$; these are precisely `mon e` and `degree e`. Let $R_k$ be the span of the $m_e$ with $q(e)=k$, and zero for negative integer $k$, as in `graded`.

1. **Evaluation bridge.** For every natural length $n$, `UniformMPSTwoByTwoLinearSpan.evaluation_bridge` equates $\dim_{\mathbb C}S_n$ with the dimension of the span of the coordinate functions $(X,Y)\mapsto\operatorname{tr}(A_{i_1}\cdots A_{i_n})$. Its linear map sends a functional on the tensor space to its composition with `traceWord`; its image is the coordinate span and its kernel is the annihilator of $S_n$.
2. **Commutator multiples.** For every pair $(X,Y)$, `UniformMPSTwoByTwoTraceWords.commutator_square` gives $C^2=\delta I$, including pairs for which $C$ or $\delta$ vanishes. For every $e\in\mathbb N^5$, `invariant_multiple` constructs a finite complex linear combination of binary words, all of length $q(e)+2$, whose value at every matrix pair is $m_eC$. Consequently, `delta_monomial_mem`, for every such $e$, puts $\delta m_e$ in the trace-coordinate span at length $q(e)+4$.
3. **A basis of functions.** For every $n\in\mathbb N$, `coordinates_upper` bounds the coordinate span by the span of the $n+1$ functions $\operatorname{tr}(X^aY^{n-a})$, $0\le a\le n$, together with $\delta R_{n-4}$. The definitions `ordered` and `normalFamily`, and the lemmas `normal_span` and `normal_independent`, each at every natural $n$, give equality and linear independence of the family consisting of these ordered traces and the functions $\delta m_e$ with $q(e)+4=n$. In the independence argument, `scalar_delta` applies to $(X,Y)=(xI,I)$ for every $x\in\mathbb C$, and `scalar_ordered` gives $2x^a$ there for every $n$ and $a:\mathrm{Fin}(n+1)$. The invariant-polynomial evaluation map is injective by `invariant_polynomial_injective`; its auxiliary `invariants_attained` realizes every quintuple $(s,t,u,v,w)\in\mathbb C^5$ satisfying $s^2\ne4u$. That condition restricts this auxiliary construction, not the pairs in the coordinate span. Thus `coordinate_dimension`, for every natural $n$, gives

   $$
   \dim_{\mathbb C}S_n=n+1+\#\{e\in\mathbb N^5:q(e)+4=n\}.
   $$

   Here `coordinate_dimension` gives the coordinate dimension, and the equality for $S_n$ also uses `evaluation_bridge`; the definition `extraIndex` bounds every exponent by $n$, and `index_unbounded` removes that bound for every natural $n$.
4. **Exact count.** In `UniformMPSTwoByTwoLinearSpan`, `compositions_card` counts five nonnegative integers of sum $k$ as $\binom{k+4}{4}$ for every $k\in\mathbb N$. For every natural $k$, `odd_equiv` identifies the exponent set at length $2k+5$ with two copies of those compositions of $k$, while `even_equiv` identifies the set at length $2k+6$ with compositions of $k+1$ or $k$. The separate lemmas `small_count` for $n<4$ and `count_four` cover the remaining lengths. For every $k\in\mathbb N$, `monomial_count_even` and `monomial_count_odd` give the two parity counts at lengths $2k$ and $2k+1$. Finally `normal_count`, with its hypothesis $1\le n$, adds $n+1$ and yields `result : claim`.

## Falsifier

A different tensor parametrization, an unordered matrix product, a change of field, or a restriction to generic matrix pairs would change the problem. The module uses all pairs of complex $2\times2$ matrices and the ordered-product trace, and its final statement covers every positive natural length. Singular matrices, zero matrices and length one are included. The span lives in the finite-dimensional coordinate space $((\mathrm{Fin}\,n\to\mathrm{Fin}\,2)\to\mathbb C)$, identified with the tensor space by its binary-word basis. The equality between image and closure spans is an ordinary linear-algebraic bridge, not an additional clause of `claim`.

Finite-field ranks of sampled tensors alone could not establish the asserted dimension over $\mathbb C$ at all lengths. The proof instead uses the spanning and independence statements for functions on all complex matrix pairs.

## Evidence

The canonical source is `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.lean.json`.

Declaration statements:

- `result`: `sha256:efb69fb47d7d2bb25abbbc3e4b96fb87b7ec5c79aad1f44eb723d7b2791c98a7`;
- `claim`: `sha256:53251a790f94fbd4e7da1cf9dc3ed53a3b70b6880539bafca3ed51dece6edd63`.

## Triage

Tier 1 conjecture of a 2022 SIGMA paper, retained as a target in Seynnaeve's later notes, preregistered in issue #23810 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural length $n\ge1$, the complex linear span of the image `uMPS 2 2 n` has dimension $(n^4-4n^2+192n+192)/192$ for even $n$ and $(n^4-10n^2+192n+201)/192$ for odd $n$, as an equality in $\mathbb Q$ after casting the natural-number dimension.

**Computed, not formalized** (orchestrator, recorded in #23810): exact finite-field ranks of sampled trace tensors at small lengths, consistent with the dimension proved by `result`.

**Argued, not formalized.**

- *Mechanism and exactness.* The mechanism supplies both directions of the dimension count. For each natural length $n$, `normal_span` and `normal_independent` provide a spanning, independent family of trace functions on all complex matrix pairs. The ordered traces distinguish the $n+1$ exponents on the scalar slice $(xI,I)$, where `scalar_delta` vanishes and `scalar_ordered` equals $2x^a$ for $a:\mathrm{Fin}(n+1)$. The commutator sector is independent as a family of polynomial functions, rather than at each individual matrix pair; `commutator_square` applies to every pair and permits $\delta=0$. Thus the exact formula does not require a nonvanishing-commutator hypothesis on the parametrization.
- *Closure bridge.* If $T$ is the trace-parametrization image, its span $S$ is a linear subspace of a finite-dimensional complex vector space. It is cut out by linear equations, so it is Zariski closed. Hence $T\subseteq\overline T\subseteq S$, giving $\operatorname{span}(\overline T)=S$. This identifies the module's span with the span in the source's Conjecture 3.8; the topological closure statement is not formalized in `result`.
- *Linear equations.* Write $D_n$ for the dimension supplied by `result`. A homogeneous linear equation vanishes on the source variety exactly when its linear functional annihilates $S_n$. The ambient space has its $2^n$ binary-word basis, so the annihilator dimension formula gives $2^n-D_n$ independent linear equations for each $n\ge1$. This counts the degree-one equations without specifying generators or higher-degree equations.
- *Length zero and scope.* The final type requires $n\ge1$. At length zero, the empty matrix product is $I_2$, its trace is $2$, and the coordinate space has one coordinate; the image therefore spans a one-dimensional space, agreeing with the even expression at zero. This argument is not a clause of `result`. No extension to other bond or physical dimensions or other fields is asserted; deriving such extensions by this method is open here.
- *Effect on dependent statements.* Conjecture 3.8, presented in the source as a corollary of Conjecture 3.7, receives an independent total-dimension proof. The equality supplies the exact dimension whose leading term is compared with the Section 4 upper bound (`sigma22-099.tex`, lines 752–772). A total dimension does not determine the individual weight dimensions, so `result` does not settle Conjecture 3.7 or the representation-decomposition problem in Seynnaeve's arXiv:2212.13806v2. The source's proofs for weights $0,1,2,3$ and its higher-degree-equation algorithm are independent of assuming Conjecture 3.8; their correctness is not certified by this settlement.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The author-listing, arXiv-abstract, web and repository searches reported by the orchestrator in #23810 were not independently reproduced. The thesis was not read, and absence of a proof in it is unverified; the unavailable citing-work lists leave a further literature gap. The primary paper's quoted conjecture and the later notes' cited passage were read directly.

The finite-field rank computations and the formula evaluations attributed to the orchestrator were not rerun. They are finite computations, not evidence for untested matrix samples or lengths. The closure and tensor-coordinate identifications, the dimension count for linear equations, the length-zero extension, and the implications for neighbouring source questions are arguments outside the type of `result`; no separate Lean verification of them is claimed. The full weight-space formula, representation decomposition, higher-degree equations and parameter extensions are not settled by `result`.

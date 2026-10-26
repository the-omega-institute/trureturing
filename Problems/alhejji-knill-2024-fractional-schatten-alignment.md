---
slug: alhejji-knill-2024-fractional-schatten-alignment
bibkey: alhejjiknill2024spinalignment
doi: 10.1007/s00220-024-04980-1
url: https://arxiv.org/abs/2307.06894v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.result
---

# Word-trace domination does not control fractional Schatten norms

## Problem

M. A. Alhejji and E. Knill, *Towards a resolution of the spin alignment problem*, arXiv:2307.06894v3, Commun. Math. Phys. 405, 119 (2024), Section VI, Concluding remarks, item 1 (PDF p. 30; TeX `main.tex`, line 759), ask:

> (**Schatten norms of non-integer order**) We used Cor. IV.6 to resolve the spin alignment problem for Schatten norms of integer order. It is of interest to know if a similar approach can be used in cases where the order of the norm is not an integer. Suppose that $A_{0}, A_{1}, B_{0}, B_{1} \geq 0$ satisfy $\lambda(A_{0}) = \lambda(B_{0})$, $\lambda(A_{1}) = \lambda(B_{1})$. For a string $s \in \{0, 1\}^{*}$, define the ordered products $\Pi_s(A_{0}, A_{1}) := \Pi_{i \in [|s|]} A_{s(i)}$ and $\Pi_s(B_{0}, B_{1}) := \Pi_{i \in [|s|]} B_{s(i)}$. If for all strings $s$, $\operatorname{tr}(\Pi_s(A_{0}, A_{1})) \geq |\operatorname{tr}(\Pi_s(B_{0}, B_{1}))|$, does it hold that $\lVert A_{0} + A_{1} \rVert_{p} \geq \lVert B_{0} + B_{1} \rVert_{p}$ for all $p \in [1,\infty)$? If so, then the overlap lemma may be used to prove the spin alignment conjecture for all Schatten norms, and by extension for the von Neumann entropy as well.

The quotation follows the PDF, with mathematical notation typeset in Markdown. The source defines $\lambda$ using eigenvalues with multiplicity (`main.tex`, line 117), and defines $\lVert R\rVert_p=(\operatorname{tr}|R|^p)^{1/p}$ with $|R|=\sqrt{R^*R}$ (lines 274–278). See [the literature note](../Library/Eigenstructure/alhejjiknill2024spinalignment.md).

Issue [#21843](https://github.com/the-omega-institute/trureturing/issues/21843) fixes the reading: for every natural size $d$, four positive semidefinite complex $d\times d$ matrices with $A_0$ and $B_0$ having equal characteristic polynomials, and likewise $A_1$ and $B_1$, satisfy the norm comparison for every real $p\ge1$ whenever every ordered-word trace of the $A$ pair is real and dominates the absolute value of the corresponding $B$ trace. The universal implication is refuted.

## Motivation

The proposed implication would extend the paper's use of the overlap lemma from integer Schatten orders to every real order at least one. The quoted conditional explicitly connects that extension to the spin alignment conjecture and von Neumann entropy. The issue is whether fixed individual spectra and domination of every ordered-product trace supply enough information about a fractional power of the sum.

## Gap

The bounded literature check preregistered in #21843 records:

- verification that the v3 TeX retains the question;
- a web search for the non-integer Schatten question with “counterexample” and a Zenodo search for “spin alignment” and Schatten, with no settlement found;
- a repository search with no existing issue, module, Library note or dossier for this paper;
- additional-paper and MathDB checks with no reported settlement of this mixed-word question. The recorded OpenAlex enumeration failed with HTTP 429.

The recorded status is `not-found-in-searched-scope`.

## Route

All lemma names below refer to the private helpers in the canonical module.

1. **The matrices.** Set $A_0=B_0=\operatorname{diag}(0,1,1,2)$, $A_1=\operatorname{diag}(1,0,1,2)$ and $B_1=\operatorname{diag}(0,1,2,1)$, as complex matrices of size four. For these specific matrices, `witness_psd` proves positive semidefiniteness of $A_0,A_1,B_1$, and `witness_spectra` proves $A_1.\mathrm{charpoly}=B_1.\mathrm{charpoly}$. The remaining positivity and characteristic-polynomial equality use $B_0=A_0$.

2. **Ordered products.** For every natural size $d$, complex diagonals $x_0,x_1:\operatorname{Fin}(d)\to\mathbb C$ and Boolean list $s$, `word_diagonal` proves that the ordered product is diagonal with entry $x_0(k)^m x_1(k)^n$, where $m$ counts false and $n$ counts true. There is no positivity or nonempty-word hypothesis. The empty word gives the identity. For the displayed matrices and every Boolean list, `trace_forms` gives
   $\operatorname{tr}\Pi_s(A_0,A_1)=0^m+0^n+1+2^{m+n}$ and
   $\operatorname{tr}\Pi_s(B_0,B_1)=0^{m+n}+1+2^m+2^n$,
   with the natural-number expressions included in $\mathbb C$ and $0^0=1$.

3. **All words.** For every $m,n\in\mathbb N$, `nat_gap` compares the second natural-number expression with the first. If either count is zero they agree. If both are positive, $2^m,2^n\ge2$ imply $2^m+2^n\le2^m2^n$; the positive powers of zero vanish. For the displayed matrices and every Boolean list $s$, `word_bounds` consequently proves that the $A$ trace has imaginary part zero and that the complex norm of the $B$ trace is at most the real part of the $A$ trace.

4. **The fractional norm.** For every natural size $d$, real diagonal $x:\operatorname{Fin}(d)\to\mathbb R$ with $x(k)\ge0$ for every $k$, and real $p$, `norm_diagonal` identifies the repository's `schattenNorm` with $(\sum_k x(k)^p)^{1/p}$, using Lean's real-power conventions. It uses functional calculus on the diagonal matrix with entries $x(k)^2$. For the specific witness, `norm_reverse` proves
   $\lVert A_0+A_1\rVert_{3/2}<\lVert B_0+B_1\rVert_{3/2}$.
   The sums have diagonals $(1,1,2,4)$ and $(0,2,3,3)$. Their $3/2$-power sums are $10+2\sqrt2$ and $2\sqrt2+6\sqrt3$. The strict comparison reduces to $10<6\sqrt3$, using $\sqrt3\ge0$ and $(\sqrt3)^2=3$; the outer power $2/3>0$ preserves it.

5. **Contradiction.** `result` applies `claim` at size four, these matrices and $p=3/2\ge1$. The resulting weak inequality contradicts `norm_reverse`.

## Falsifier

The refutation would miss the question if the encoded positivity, spectra, ordered products or Schatten norms differed from the source's. The module uses:

- `Matrix.PosSemidef`, which includes Hermitian symmetry and nonnegative quadratic forms;
- equality of characteristic polynomials, expressing equality of spectra with multiplicity for these Hermitian matrices;
- `wordProduct`, with false selecting subscript zero, true selecting subscript one, multiplication preserving word order, and the empty product equal to the identity;
- the realness condition $\operatorname{Im}\operatorname{tr}\Pi_s(A)=0$ and $|\operatorname{tr}\Pi_s(B)|\le\operatorname{Re}\operatorname{tr}\Pi_s(A)$ for every finite word;
- `schattenNorm` from `D5/S3/Quantum/Schatten/Holder.lean`, defined by the real part of the trace of $(R^*R)^{p/2}$ and the outer power $1/p$.

The universal dimension includes zero; the counterexample uses dimension four. The exponent is the real number $3/2$. No conclusion about every non-integer order is needed to negate the universal implication.

## Evidence

The canonical source is `D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.lean` (154 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Schatten/FractionalSchattenAlignmentRefutation.lean.json`, statement `sha256:ba30835e753b17e3871f4bfc693c43b3dbf6d97869f65a9837c68e207030e1a1`.

Declaration statements:

- `result`: `sha256:d54afeb32b269c255b1a852fbd5399af4c5c771e33d4fc26898adfa4923e40de`;
- `claim`: `sha256:e5d103ebdb9f50df3d8cb58c5787c2e048c2dc63c2f072f14dd951c8cc376cef`.

## Triage

Tier 1: an explicit question in the concluding list of a 2024 journal article, preregistered in issue #21843 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal implication in `claim` is false. Positive semidefiniteness, the two characteristic-polynomial equalities, and domination of every word trace in the stated realness-and-absolute-value sense do not imply the Schatten-norm comparison for every real $p\ge1$.

**Computed, not formalized**. Exact enumeration of the displayed quadruple found no word-bound violation and no mismatch with the trace formulas among all 511 words of lengths zero through eight. An 80-digit evaluation at $p=3/2$ gave power sums approximately $12.82842712474619$ and $13.22073197015945$, and norms approximately $5.48002165014139$ and $5.59118248657337$, respectively. These computations concern this tested quadruple and finite word range.

**Argued, not formalized**.

- *Mechanism and interval.* Commutativity alone cannot repair the implication: all four witness matrices are diagonal. Define $f_p(x)=x^p$ on $[0,\infty)$ and $\Delta^2 f_p(c)=f_p(c+2)-2f_p(c+1)+f_p(c)$. For this quadruple the difference between the two power sums is
  $S_A(p)-S_B(p)=2+4^p-2\cdot3^p=\Delta^2 f_p(2)-\Delta^2 f_p(0)$ for $p>0$.
  If $1<p<2$, then $f_p''(x)=p(p-1)x^{p-2}$ is strictly decreasing for $x>0$. The identity
  $\Delta^2 f_p(c)=\int_0^1\int_0^1 p(p-1)(c+u+v)^{p-2}\,du\,dv$
  gives $\Delta^2 f_p(2)<\Delta^2 f_p(0)$. The integral at $c=0$ is finite because $p-2>-1$; its value at the single corner $u=v=0$ is immaterial. Thus the same quadruple reverses the norm comparison for every $1<p<2$. At $p=1$ and $p=2$ the displayed difference is zero; for $p>2$ the increasing second derivative gives the opposite sign for this quadruple. Only $p=3/2$ is certified by the module's norm-comparison helper.

- *A weaker conclusion survives.* Under all the hypotheses of `claim`, every positive integer order $k$ satisfies the proposed comparison: expansion gives
  $\operatorname{tr}((B_0+B_1)^k)=\sum_{|s|=k}\operatorname{tr}\Pi_s(B)$.
  Taking real parts, bounding each by its absolute value, and using the word bounds gives at most $\sum_{|s|=k}\operatorname{tr}\Pi_s(A)=\operatorname{tr}((A_0+A_1)^k)$. Positivity of the sums and monotonicity of the $k$th root give the norm inequality. At $p=1$ the individual spectral equalities give equality of traces. This polynomial expansion does not extend word by word to a non-integer power.

- *The missing order structure.* The ordered eigenvalue lists of the witness sums are $(4,2,1,1)$ and $(3,3,2,0)$, with cumulative sums $(4,6,7,8)$ and $(3,6,8,8)$. Neither majorizes the other. A sufficient additional condition is a doubly stochastic matrix $D$ relating the sum spectra by $b=Da$, with $a=\lambda(A_0+A_1)$ and $b=\lambda(B_0+B_1)$. For $p\ge1$, Jensen's inequality gives $b_i^p\le\sum_jD_{ij}a_j^p$; summing and using the column sums of $D$ gives $\sum_i b_i^p\le\sum_j a_j^p$. Taking $p$th roots restores the desired comparison. The word bounds do not supply this condition, as the witness demonstrates.

- *Effect on the paper.* The conditional extension quoted in Problem cannot use this general mixed-word implication to reach all real Schatten orders or von Neumann entropy. The overlap lemma and Corollary IV.6 are not contradicted; the integer-order argument of Theorem IV.7 (PDF pp. 22–23) does not use the refuted implication. The witness does not establish a violation within the paper's constrained tensor-product spin-alignment family. Whether those additional constraints permit a different extension remains open here; the original and strong spin alignment conjectures are not settled by `result`.

## ASSUMED-UNVERIFIED

The literature check is bounded and establishes no exhaustive worldwide novelty or priority. The web, Zenodo, historical repository, additional-paper, MathDB and Crossref readings reported in #21843 were not independently reproduced; its OpenAlex enumeration has no successful reading. The source question, spectrum convention and norm definition were checked directly in v3 `main.tex`, and the question and integer-order argument were also read in the PDF.

The numerical enumeration and evaluations in “Computed, not formalized” are computations, not formal proofs. The interval argument, integer-order consequence, majorization analysis, sufficient additional condition and implications for the source's proof strategy in “Argued, not formalized” are not additional compiled declarations. No minimum counterexample dimension, classification of all failing exponents for arbitrary quadruples, or settlement of the constrained spin alignment problems is claimed.

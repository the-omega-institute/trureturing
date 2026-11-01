---
slug: sp322844-serpentine
bibkey: spezia2018a322844
doi: null
url: https://oeis.org/A322844
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/SpeziaSerpentineSecondExteriorTrace.result
---

# The second exterior trace of Spezia’s serpentine matrix

## Problem

Stefano Spezia, OEIS A322844, COMMENTS revision 68, states:

> For n > 1, a(n) is the absolute value of the trace of the 2nd exterior power of an n X n square matrix M(n) defined as M[i,j,n] = j + n*(i-1) if i is odd and M[i,j,n] = n*i - j + 1 if i is even (see A317614). Equivalently, a(n) is the absolute value of the coefficient of the term [x^(n-2)] in the characteristic polynomial of the matrix M(n), or the absolute value of the sum of all principal minors of M(n) of size 2.

The matrix definition is shared with A317614 revision 194. With one-based indices $1\leq i,j\leq n$, its integer entries are $M_{ij}=j+n(i-1)$ for odd $i$ and $M_{ij}=ni-j+1$ for even $i$. Put $\varepsilon=n\bmod 2$ and

$$
a(n)=\frac{n^2}{12}\bigl(3(1+n^2)-2(2+n^2)\varepsilon\bigr).
$$

### Statement echo

| Source clause or convention | Lean counterpart | Fidelity |
| --- | --- | --- |
| One-based integer serpentine entries | `SpeziaSerpentineSecondExteriorTrace.M` | `Fin n` indices are increased by one; entry arithmetic is integer arithmetic. |
| Source rational expression for $a(n)$ | `SpeziaSerpentineSecondExteriorTrace.a` | Rational division and natural remainder; no truncated rational quotient. |
| Second exterior trace, characteristic coefficient, principal-minor sum | `SpeziaSerpentineSecondExteriorTrace.traceExt` | The binding convention uses $(-1)^k[x^{n-k}]\chi_M$ for $k\leq n$ and zero for $k>n$. It does not construct an exterior-power linear map. |
| First conjecture, every $n>1$ | `SpeziaSerpentineSecondExteriorTrace.claim`, `result` | Integer absolute value, cast to the rationals, equals $a(n)$. |
| Second conjecture, every $n$ and $k>2$ | `SpeziaSerpentineHigherExteriorTrace.claim`, `result` | Includes $n<k$, including the empty matrix, using the zero exterior-space convention. |
| Centered coordinates and two rectangular factors | `w`, `u`, `U`, `V` in the second-trace module | Auxiliary constructions, not additional hypotheses on either claim. |

All declaration names in this table have prefix `D5.S3.Quantum.Matrix.`. The source calls the two coefficient/minor descriptions equivalent views of the first conjecture. No additional source conjecture is counted from those equivalent descriptions.

## Motivation

The two conjectures ask for uniform identities across every matrix order. A common two-dimensional factorization explains both the second coefficient and the disappearance of all higher coefficients. The settlements correspond to preregistrations #21795 and #21796.

## Gap

The source labels the two statements conjectures. No settlement was located in the readable literature scope recorded in those preregistrations. Literature completeness is ASSUMED-UNVERIFIED. The formal statements use the preregistered characteristic-coefficient convention, rather than a separately constructed exterior-power operator or a separately formalized trace/minor equivalence.

## Route

Over $\mathbb Q$, set $w_i=i-(n+1)/2$, $u_i=ni-(n-1)/2$, and $s_i=(-1)^{i+1}$ for source indices $i=1,\ldots,n$. Let the $i$th row of $U$ be $(u_i,s_i)$ and the $j$th column of $V$ be $(1,w_j)$. The entry identity $M=UV$ is the private `factorization` lemma of the second-trace module. The public `charpoly_factor` applies `Matrix.charpoly_mul_comm_of_le` to give, for $n\geq2$,

$$
\chi_{M_{\mathbb Q}}(x)=x^{n-2}\chi_{VU}(x).
$$

The private centered-moment lemmas evaluate the four entries of $VU$ as

$$
VU=\begin{pmatrix}
 n(n^2+1)/2 & \varepsilon\\
 n^2(n^2-1)/12 & -n(1-\varepsilon)/2
\end{pmatrix}.
$$

The private `small_det` and `coefficient_two` give $[x^{n-2}]\chi_M=-a(n)$, after the rational scalar map. The private `a_nonneg` gives $a(n)\geq0$. The first `result` therefore proves the absolute-value formula. The second `result` uses `charpoly_factor` and `Polynomial.coeff_X_pow_mul'` to annihilate every coefficient indexed by $k>2$ with $k\leq n$; for $k>n$ the defining zero branch applies.

## Falsifier

A counterexample to the first binding claim would have $n>1$ and an integer second trace whose absolute value, cast to $\mathbb Q$, differs from $a(n)$. A counterexample to the second would have natural $n,k$ with $k>2$ and nonzero binding exterior trace. The two universal `result` theorems exclude these counterexamples within the stated convention.

## Evidence

Settlement: **Proved**, by `D5.S3.Quantum.Matrix.SpeziaSerpentineSecondExteriorTrace.result`. The companion settlement is the other module's `result`. Both modules have `generality: I` and `utility: none`: their assertions quantify unbounded orders and contain no fixed numerical certificate.

The public theorem surface is the second-trace module's `charpoly_factor` and `result`, and the higher-trace module's `result`. Every other lemma is private. The escape audit of these three original theorem statements is unfinished and tracked in [issue #21995](https://github.com/the-omega-institute/trureturing/issues/21995). No validated four-slot registration is asserted.

### Exact finite computation

The immutable experiment is [spezia-a322844 at commit 72e99409d60c1747efec95cc67de4f5dd612c133](https://github.com/the-omega-institute/trureturing-experiments/tree/72e99409d60c1747efec95cc67de4f5dd612c133/docs/reports/spezia-a322844). The implementation seat verified the committed `check.py` bytes and ran `python3 /Users/auric/.sshx/2ca24994250d0563baab9783/attempt-1/check.py`, exit 0, final verdict `ALL_CHECKS_OK`. Script SHA-256: `2573b4928f9051382c4692a3d3d1680b30d477d8d5d8c898145398a8d08f5159`.

The exact tested scope is $0\leq n\leq40$ and $3\leq k\leq42$: 10,660 principal two-minors, 101,270 principal three-minors, 741 higher coefficients, and all 1,816 principal minors of order at least three for $n\leq10$. Exact ranks in this range are $\min(n,2)$. These computations are finite evidence, separate from the universal Lean theorems.

## Triage

1. **Proved (kernel-checked): centered rational factorization.** The second-trace module's private `factorization` proves $M_{\mathbb Q}=UV$ for every $n$, with dimensions $n\times2$ and $2\times n$.
2. **Proved (kernel-checked): the second coefficient and absolute-value claim.** Its private `coefficient_two` gives $[x^{n-2}]\chi_M=-a(n)$ for $n\geq2$, its private `a_nonneg` gives $a(n)\geq0$, and its public `result` gives exactly the first binding claim.
3. **Proved (kernel-checked): every higher exterior trace vanishes.** `D5.S3.Quantum.Matrix.SpeziaSerpentineHigherExteriorTrace.result` covers every natural $n$ and $k>2$, including $n<k$.
4. **Computed: the exact finite checks.** The experiment entry above records the command, exit 0, script hash, `ALL_CHECKS_OK`, and the complete tested scope and all four counts. It also checks rank $\min(n,2)$ for $0\leq n\leq40$; no uniform exact-rank theorem is inferred from this computation.
5. **Open (formalization boundary): separate exact rank and complete expanded characteristic polynomial.** Neither a separate uniform exact-rank theorem nor a separately expanded full characteristic-polynomial theorem is delivered. These are neighbouring formalization tasks, not assertions that the corresponding elementary mathematical facts are unknown.

### What the settlement shows

**Proved (kernel-checked):** the decisive mechanism is factorization through dimension two, followed by the signed coefficient identity and the nonnegativity needed for absolute value. The companion higher-trace settlement follows from the same public `charpoly_factor`; it needs no bound on $n$ and includes $n<k$. The first claim retains the source's $n>1$ guard.

**Computed:** exact ranks are $\min(n,2)$ for $0\leq n\leq40$, with evidence in the experiment entry. **Open (formalization boundary):** a uniform exact-rank theorem, a separately expanded full characteristic polynomial, and an exterior-power operator realization are outside this delivery.

The source identifies no further theorem conditional on these two conjectures. The result changes their status in the characteristic-coefficient formulation; it makes no claim about unrelated Spezia matrix families or a new general rectangular-product identity.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The preregistrations report readable OEIS, arXiv metadata, Crossref, MathOverflow, Math StackExchange, repository and GitHub-code scopes without a located settlement. OpenAlex and Semantic Scholar requests returned HTTP 429, arXiv full-text and general-web searches were unavailable or unusable, and the later-author bibliography was incomplete. No exhaustive citation inventory, priority claim, or identification of the OEIS contributor with a same-named paper author is asserted. No source DOI, arXiv manuscript or journal version is identified.

The standard exterior-power/coefficient interpretation is the binding source convention. A constructed exterior-power linear map and a separate formal equivalence to its trace are not supplied. The unfinished audit in #21995 concerns registration evidence, not the kernel-checked mathematical proof.

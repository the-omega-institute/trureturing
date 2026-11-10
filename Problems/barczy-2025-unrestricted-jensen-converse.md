---
slug: barczy-2025-unrestricted-jensen-converse
bibkey: barczypales2025jensen
doi: null
url: https://arxiv.org/abs/2510.03715v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/BarczyPalesJensenConverse.result
---

# The unrestricted rank-only Jensen converse is false

## Problem

Mátyás Barczy and Zsolt Páles, *Jensen convex functions and doubly stochastic matrices*, arXiv:2510.03715v1, Remark 2.2(i), ask:

> However, we do not know whether the assertion in part (i) of Theorem 2.1 holds for every doubly stochastic matrix having rank at least 2. We leave this question as an open problem.

The referenced assertion is Theorem 2.1(i), equation (2.1), with Jensen convexity defined in Definition 1.1. The complete target is the following closed universal assertion:

For every positive integer $n$, every nonempty open real interval $I$ (including unbounded intervals and $I=\mathbb R$), every arbitrary function $f:I\to\mathbb R$, and every real $n\times n$ matrix $P=(p_{ij})$ satisfying

$$
p_{ij}\geq0,\qquad \sum_jp_{ij}=1,\qquad
\sum_ip_{ij}=1,\qquad \operatorname{rank}_{\mathbb R}P\geq2,
$$

does

$$
f\!\left(\frac1n\sum_{j=1}^n x_j\right)
\leq\frac1n\sum_{i=1}^n f\!\left(\sum_{j=1}^np_{ij}x_j\right)
\qquad\text{for every }(x_1,\ldots,x_n)\in I^n
$$

imply

$$
f\!\left(\frac{u+v}{2}\right)\leq\frac{f(u)+f(v)}2
\qquad\text{for every }u,v\in I?
$$

The rank condition replaces the original special column-span premise; it is not conjoined with it. There is no continuity, measurability, boundedness, rational-entry or rational-input assumption. The function is defined on the original interval itself, with no ambient-extension datum. Convexity of the interval puts each mean and each matrix row output in its domain.

The answer is negative. The exact result is the negation of this whole universal assertion:

$$
\neg\Bigl[\forall n\in\mathbb N_{>0}\;\forall I\subseteq\mathbb R
\text{ nonempty open interval}\;\forall f:I\to\mathbb R\;
\forall P\in\mathbb R^{n\times n},\quad
\bigl(P\text{ doubly stochastic}\ \land\ \operatorname{rank}_{\mathbb R}P\geq2\bigr)
\Longrightarrow
\Bigl(\bigl[\forall x\in I^n,\ f(\tfrac1n\sum_jx_j)
\leq\tfrac1n\sum_i f(\sum_jp_{ij}x_j)\bigr]
\Longrightarrow
\bigl[\forall u,v\in I,\ f(\tfrac{u+v}2)\leq\tfrac{f(u)+f(v)}2\bigr]\Bigr)\Bigr].
$$

## Motivation

The question asks whether the dimension of the image of a stochastic matrix alone can force a functional inequality back to midpoint convexity. Theorem 2.1(i) gives such a converse under a specific geometric condition on its column span. Replacing that geometry by rank would enlarge the class of matrices substantially. A counterexample must therefore keep the actual real matrix, its nonnegative stochastic entries, its real rank, and the comparison at every input together.

## Gap

The published v1 question is explicitly open. The bounded qualification found no earlier verified equal-or-stronger settlement in the sources checked. Niezgoda (2013), DOI `10.7153/mia-16-16`, supplies forward convexity results; the later expected-loss paper arXiv:2606.22183 assumes convexity with additional probabilistic or generator conditions. Those cited scopes do not supply the unrestricted converse. Their earlier reading is retained qualification evidence, not a new rereading here.

Burai–Makó–Szokol (2019) and the complete *Functions Generating Strongly Schur-Convex Sums* chapter remain unread. The search supports only `not-found-in-searched-scope`, with no global novelty, priority, or exhaustive citation claim. The original source identity and qualification boundary are recorded in [the Library note](../Library/QuadraticForms/barczypales2025jensen.md).

## Route

Put $s=\sqrt3$ and realize $K=\mathbb Q(s)$ as the actual field `QuadraticAlgebra ℚ 3 0`, with $\omega=(0,1)$ and $\omega^2=3$. The rational nonsquare theorem supplies its field structure. The quadratic lift

$$
\iota:K\hookrightarrow\mathbb R,\qquad \iota(a+b\omega)=a+bs
$$

is injective. Give all of $\mathbb R$ its induced $K$-vector-space structure. The vector-space linear splitting theorem supplies a total $K$-linear map $L:\mathbb R\to K$ with $L(\iota(z))=z$ for every $z\in K$. Classical choice constructs this map; no finite-dimensionality of $\mathbb R$ over $K$ and no assumed retraction are introduced.

Define the actual real function

$$
F(x)=\bigl(N(L(x)):\mathbb R\bigr),\qquad
N(a+b\omega)=a^2-3b^2.
$$

The rational norm is signed. The projection $L$ is used as a linear map, with no assertion of multiplicativity. Set $I=\mathbb R$, $n=3$, and take $f$ on the interval subtype to be $x\mapsto F(x.\mathrm{val})$.

Use the same literal real matrix throughout:

$$
P=\frac1{12}\begin{pmatrix}
5&3&4\\
s+2&6-s&4\\
5-s&3+s&4
\end{pmatrix}.
$$

The bounds $1<s<2$ make all entries nonnegative, and every row and every column sums to one. The actual top-left minor is

$$
\det P_{\{1,2\},\{1,2\}}=\frac{3-s}{18}>0,
$$

so this real matrix has rank at least two.

For every real triple $x$, including all degenerate inputs, set

$$
m=\frac{x_1+x_2+x_3}{3},\qquad t=\frac{x_1-x_2}{12}.
$$

Direct multiplication gives

$$
Px=(m+t,\ m+(s-2)t,\ m+(1-s)t).
$$

For arbitrary $A,B\in K$, the quadratic coordinate identity is

$$
N(A+B)+N(A+(\omega-2)B)+N(A+(1-\omega)B)=3N(A).
$$

Apply this with $A=L(m)$ and $B=L(t)$. Genuine $K$-linearity transports the three real row outputs to the three arguments in this identity. Casting the resulting rational equality into $\mathbb R$ gives

$$
\sum_{i=1}^3F((Px)_i)=3F(m)\qquad\text{for every }x\in\mathbb R^3.
$$

Thus the source comparison holds with equality for every legal input. Retraction gives

$$
F(s)=F(-s)=-3,\qquad F(0)=0.
$$

Midpoint convexity at $u=s$, $v=-s$ would require $0\leq-3$. This legal all-real witness refutes the entire universal claim.

## Falsifier

The refutation would fail to answer the source if the open question retained its old column-span premise or imposed regularity, if the all-input identity held only on $K$ or rational inputs, if the projection were merely assumed, or if stochasticity and rank belonged to a different matrix. The complete claim and its witness preserve these distinctions: the original interval/function quantifiers are literal, the projection is total on $\mathbb R$, and the literal real matrix is used for both the comparison and the rank proof. A verified earlier full settlement or a competing exact registration would change the qualification or ownership conclusion, without changing the kernel theorem.

## Evidence

The canonical source is [BarczyPalesJensenConverse.lean](../D5/S3/QuadraticForms/BarczyPalesJensenConverse.lean), with [its full Blueprint exposition](../Blueprint/D5/S3/QuadraticForms/BarczyPalesJensenConverse.md). The public definition `D5/S3/QuadraticForms/BarczyPalesJensenConverse.claim` has literal compiled type `Prop`. The public theorem `D5/S3/QuadraticForms/BarczyPalesJensenConverse.result` has literal compiled type `Not claim`.

| Original clause | Exact formal counterpart |
| --- | --- |
| Every positive $n$ | `n : ℕ`, `hn : 0 < n` in `claim` |
| Every nonempty open real interval, including the full line | `I : Set ℝ`, `I.Nonempty`, `IsOpen I`, `hI : Convex ℝ I` |
| Arbitrary function on that interval | `f : I → ℝ`, without regularity or extension premises |
| Actual nonnegative real doubly stochastic matrix | `P : Matrix (Fin n) (Fin n) ℝ`, `hP : P ∈ doublyStochastic ℝ (Fin n)` |
| Real rank at least two | `2 ≤ P.rank` |
| Comparison at every legal input | `∀ x : Fin n → I`, with subtype-valued `intervalMean` and `intervalRow` |
| Midpoint convexity at every pair | `∀ u v : I`, the two-input subtype mean and the corresponding inequality |
| Whole negation | `result : ¬ claim`, instantiated at `n=3`, `I=Set.univ` |

The claim declaration has statement identity `sha256:888b9c47bcf7d75d9a89d6dd89230a3623c7b4ad70e2c15ed48f4275e4806c54`; the result declaration has statement identity `sha256:35548343af610ba735b7310c748b65e389a37a7c73c2f65928e6ec243d770a9d`. These are declaration identities, distinct from the host module pin `sha256:5a8531be5ae0ccfbc94e281d1ecabeb75558e4936a9b433f1f8a441db05ac8b3` in `Golden/Frozen/state/D5/S3/QuadraticForms/BarczyPalesJensenConverse.lean.json`.

All 45 compiled declaration closures use only `Classical.choice`, `Quot.sound`, and `propext`. There is no `sorry`, additional axiom, free assumption in the closed result, or direct frozen D5 declaration dependency. The 21 authored declarations comprise the public claim/result and private consumed supports; generated and equational declarations are not additional authored results. The implementation reuses pinned mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679` for the field, embedding, splitting, convex-combination membership, stochastic predicate, and determinant/rank APIs. No experimental program or finite sample substitutes for the universal identity.

The original v1 TeX has SHA-256 `e1fc8837e6a539035540c729f237a359f2dcb72b5500bc3a42173cbe16bacdc1`. Its exact target is Remark 2.2(i), read with Theorem 2.1(i), equation (2.1), Definition 1.1, and the global notation that $\mathbb N$ denotes positive integers.

## Triage

Tier 1 external explicitly posed open problem, preregistered in [issue #23083](https://github.com/the-omega-institute/trureturing/issues/23083). The single resolution is `Refuted` for the complete unrestricted v1 question. The proof is conservatively classified `bind-only`, with `admission_basis: open-problem-resolution`; no content or escape witness is claimed. The utility is a certified instance refuting the exact closed claim, with `claim` and `result` as its typed endpoints. The designated refutation result is the sole new public theorem; its private supports are consumed in its proof.

### What the settlement shows

**Proved (Lean, `D5/S3/QuadraticForms/BarczyPalesJensenConverse.result`):** real rank at least two and the all-input comparison do not suffice for midpoint convexity. The failure occurs on the entire real line already in dimension three, with a genuine real doubly stochastic matrix and an actual function satisfying the comparison with equality everywhere.

**Mechanism (the implemented witness inside `result`):** a signed quadratic norm can cancel along the matrix's three row deviations while remaining negative at the embedded field element $s$. The matrix rank certifies independent real directions but does not supply the special column-span geometry used by the positive theorem. The total linear splitting extends this cancellation from the quadratic field to every real input.

**Surviving source statements (literature-attested, not newly formalized here):** Theorem 2.1(i) retains the premise that, for some disjoint nonempty $A,B\subseteq\{1,\ldots,n\}$, the vector $|A|^{-1}\sum_{\alpha\in A}e_\alpha-|B|^{-1}\sum_{\beta\in B}e_\beta$ lies in the column span of $P$. Remark 2.2(i) notes that invertibility supplies that premise. The refutation removes neither premise from those statements. Their proofs and the source's separately stated forward implications and circulant results retain their own hypotheses; the false rank-only extension supplies no premise for them.

**Open:** regularity-restricted rank-only converses, stronger classifications of matrices that force midpoint convexity, and additional neighbouring questions are not settled by this result. No such statement is added to the settling module or assigned this problem's admission basis.

## ASSUMED-UNVERIFIED

The bounded literature and ownership searches do not establish exhaustive absence of an earlier settlement or global priority. Burai–Makó–Szokol (2019), the full strongly-Schur-convex-sums chapter, and other uninvoked bibliography originals remain unread. No fresh Niezgoda or expected-loss rereading is claimed. The full original TeX review is retained at its matched hash; the PDF was not read. This theorem settles the unrestricted v1 mathematical assertion, not publication priority or any regularity-restricted variant.

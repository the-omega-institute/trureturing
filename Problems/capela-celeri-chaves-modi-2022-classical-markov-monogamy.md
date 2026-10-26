---
slug: capela-celeri-chaves-modi-2022-classical-markov-monogamy
bibkey: capelacelerichavesmodi2022markov
doi: 10.1103/PhysRevA.106.022218
url: https://arxiv.org/abs/2108.11533v4
triage: theorem
motivation_gids:
  - D5/S3/Entropy/MarkovMonogamyPermutationInequality.result
---

# Classical Markov monogamy for every finite alphabet and every permutation

## Problem

M. Capela, L. C. Céleri, R. Chaves and K. Modi, *Quantum Markov monogamy inequalities*, Phys. Rev. A 106, 022218 (2022), arXiv:2108.11533v4, Section II, Conjecture 1 (`PRA-v1.tex`, lines 153–159):

> Consider the Markovian process $X_n \rightarrow \cdots \rightarrow X_1 \rightarrow Y_1 \rightarrow \cdots \rightarrow Y_n$. The variables $X_1$ and $Y_1$ are to be interpreted as input and output of a given channel, respectively. The variables  $X_i$ and $Y_i$, with $i=2,\dots,n$, are interpreted as pre-processed and post-processed variables, respectively. Then for any bijective function $f \colon \{1,\dots,n\} \rightarrow \{1,\dots,n\}$, it holds that
>
> $\sum_{i=1}^{n} I(X_i:Y_i) \geq \sum_{i=1}^{n} I(X_i:Y_{f(i)}),$
>
> where $I(X:Y)$ denotes the mutual information of random variables $X$ and $Y$.

The source reports at line 161:

> The conjecture above has been checked for $n$ up to 4, that is, Markov chains with 8 random variables

Here $I(X:Y)=H(X)+H(Y)-H(X,Y)$, with Shannon entropy. The definitions and source locators are in [the literature note](../Library/Entropy/capelacelerichavesmodi2022markov.md).

Issue [#22399](https://github.com/the-omega-institute/trureturing/issues/22399) fixes the finite-alphabet reading. The module proves it for every $n\in\mathbb N$, including $n=0$ with empty sums: choose finite alphabets $\alpha_t$, a nonnegative initial mass $p:\alpha_0\to\mathbb R$ with $\sum_xp(x)=1$, and matrices $k_t:\alpha_t\to\alpha_{t+1}\to\mathbb R$ satisfying $k_t(x,y)\ge0$ and $\sum_y k_t(x,y)=1$ whenever $t+1<2n$. For every permutation $f$ of $\mathrm{Fin}\,n$, the sum paired by $f$ is at most the diagonal sum.

Precisely, `composedTransition` is the identity at equal positions and the product of successive matrices for ordered positions $s\le t$; write it as $K_{s,t}$. The definitions `mixture` and `mixtureJoint` give $p_s(x)=\sum_zp(z)K_{0,s}(z,x)$ and $q_{s,t}(x,y)=p_s(x)K_{s,t}(x,y)$. For $i\in\mathrm{Fin}\,n$, position $n-1-i.val$ represents $X_{i.val+1}$ and position $n+i.val$ represents $Y_{i.val+1}$. Each summand in `claim` is `mutualInformation` of the corresponding $q_{s,t}$, defined as its KL divergence from the product of its marginals, in nats.

## Motivation

Conjecture 1 constrains how mutual information can be distributed among pairs across a channel and its pre-processing and post-processing stages. A proof for arbitrary length supplies a family of necessary conditions for a finite stochastic process to be Markovian: a violation of any permutation inequality excludes that representation. It also identifies the ordered diagonal pairing as a maximizer among all bijective pairings, beyond the source's checked range.

## Gap

The bounded literature check recorded in #22399 reports:

- arXiv:2108.11533v4 states Conjecture 1 and reports checks only through $n=4$;
- web searches for the conjecture and Markov monogamy inequalities found the source papers and no later proof for all $n$, and a Zenodo search returned no record;
- readings of the eight citing works arXiv:2204.08298, 2206.10800, 2312.10147, 2405.19108, 2407.15712, 2411.05559, 2503.09693 and 2505.13681 found no proof; MathDB and formal-conjectures had no match;
- no repository issue, module, literature note or dossier already settled the conjecture at preregistration.

`not-found-in-searched-scope`.

## Route

1. **Four-position information rectangle (`four_point_rectangle`).** For four finite alphabets, a nonnegative normalized initial mass $p$, and three nonnegative transition matrices $u,v,w$ with every row summing to one, form the joint law $p(a)u(a,b)v(b,c)w(c,d)$ of $A\to B\to C\to D$. The lemma proves $I(B:C)+I(A:D)\ge I(B:D)+I(A:C)$. It applies `conditional_mutual_information_nonneg` to this normalized nonnegative law regrouped as $((A,D),(B,C))$. That lemma requires a finite, nonnegative joint mass of total mass one. Its entropy defect is $H(ABD)+H(ACD)-H(ABCD)-H(AD)$. The channel entropy expansions identify this defect with the rectangle difference.

2. **Ordered positions of one chain (`chain_rectangle`).** For a family of finite alphabets, a nonnegative normalized $p$, indices $a\le b\le c\le d$, and nonnegative unit-row-sum $k_u$ for every $u<d$, the lemma gives the same rectangle for positions $A=Z_a,B=Z_b,C=Z_c,D=Z_d$. The composite transitions are stochastic by `composed_stochastic`, whose hypotheses are $s\le t$ and nonnegative unit-row-sum $k_u$ for every $s\le u<t$. Thus consecutive positions and strictly positive masses are unnecessary; equal positions are allowed.

3. **Common-marginal supermodularity (`monge_permutation`).** For any $n\in\mathbb N$, real matrix $m:\mathrm{Fin}\,n\to\mathrm{Fin}\,n\to\mathbb R$ satisfying $m(i,a)+m(j,b)\ge m(i,b)+m(j,a)$ for every $i<j$ and $a<b$, and every permutation $f$, the lemma proves $\sum_i m(i,f(i))\le\sum_i m(i,i)$. At size zero both sums are empty. For $n>0$, apply the frozen `common_marginal_supermodular_le_diagonal` with $C=\mathrm{Fin}\,n$, the nonnegative probability law assigning mass $1/n$ to each point $(i,f(i),i,f(i))$, and the test $F(x)=m(x_0,x_1)$. The points are distinct, so the law has total mass one. All four marginals are uniform: coordinates zero and two read $i$, and coordinates one and three read the bijection $f(i)$. The rectangle hypothesis gives supermodularity of $F$ under pointwise minimum and maximum by the relative orders of the two coordinates, with equality when an index coincides. The frozen theorem bounds the weighted permutation sum by the weighted diagonal sum; cancel the positive factor $1/n$.

4. **Application (`result`).** For every $n$, finite alphabet family, nonnegative normalized $p$, and matrices nonnegative with unit row sums whenever $t+1<2n$, set $m(i,a)=I(X_{i.val+1}:Y_{a.val+1})$ using the pair laws above. For $i<j$ and $a<b$, apply `chain_rectangle` at positions $n-1-j.val\le n-1-i.val\le n+a.val\le n+b.val$. The last position is less than $2n$, so all transitions required by that lemma satisfy the stated stochasticity condition. The matrix therefore meets every hypothesis of `monge_permutation`, for every $f$.

## Falsifier

The proof would not answer the stated reading if its information quantities or pair laws differed from the source's. The module uses finite classical mutual information of normalized joint masses, with natural logarithms; changing to another logarithm base greater than one multiplies both sums by the same positive constant. The stochastic matrices need not be homogeneous, strictly positive, or between alphabets of equal size. Only transitions within the first $2n$ positions are constrained.

The connection from the source's conditional-probability definition of a finite Markov law to this transition representation is explained below; it is not a separately formalized equivalence. The claim concerns one initial law and one common sequence of transitions for all pairs. Independently specified pair laws are outside its hypotheses.

## Evidence

The canonical source is `D5/S3/Entropy/MarkovMonogamyPermutationInequality.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Entropy/MarkovMonogamyPermutationInequality.lean.json`.

Declaration statements:

- `result`: `sha256:ae2d24737b62b764d770c604ac32a275132af5341491ac16764e956ef2129408`;
- `claim`: `sha256:9951d7fc944c42c73d6b34363bccdfa2829ad9be43520bc726e953f728227783`.

## Triage

Tier 1 conjecture of a 2022 paper, preregistered in issue #22399 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $n\in\mathbb N$, every family of finite alphabets, every nonnegative initial mass of total mass one, every sequence of real transition matrices that are nonnegative with unit row sums whenever $t+1<2n$, and every permutation of $\mathrm{Fin}\,n$, the permuted sum of the pair-law mutual informations defined in `claim` is at most its diagonal sum, with positions ordered as $X_n,\ldots,X_1,Y_1,\ldots,Y_n$; at $n=0$ both sums are empty.

**Computed, not formalized.**

None.

**Argued, not formalized.**

- *Decisive mechanism.* For a four-variable finite Markov law with nonnegative normalized initial mass and three stochastic transitions, the defect in `four_point_rectangle` is $I(B:C\mid A,D)$. Indeed, expanding $H(ACD)$ and $H(ABCD)$ cancels their common $H(D\mid C)$ term, and expanding $H(ABD)$ and $H(ABC)$ leaves $H(BD)-H(BC)$; hence the conditional-information defect equals $H(BD)+H(AC)-H(BC)-H(AD)$, the rectangle difference. The assignment argument uses only the real-matrix rectangle hypothesis for all $i<j,a<b$, exactly as stated in `monge_permutation`; it requires no positivity of the matrix entries.
- *Finite Markov-law representation.* Given a joint finite Markov law, choose its initial marginal and its conditional transition rows at states of positive probability. At zero-probability states choose arbitrary probability rows on the next alphabet, which is nonempty because it carries a marginal of total mass one. The probability multiplication rule and the Markov property give the product representation on histories of positive probability. A zero-probability history has an earliest zero-probability extension, so that product is zero there too. Summing out intermediate variables gives exactly $p_s(x)K_{s,t}(x,y)$. Conversely, the product of a probability mass and stochastic rows has conditional next-step probabilities depending only on the current state on every history of positive probability. This supplies the finite-alphabet correspondence, including zero masses.
- *Sharpness.* Set every variable equal to one finite random variable $Z$, with identity transitions. Then $I(X_i:Y_a)=H(Z)$ for every pair, so both sums are $nH(Z)$ for every permutation. Thus a strict gap for nonidentity permutations requires extra hypotheses. A complete classification of equality cases is not supplied.
- *Quantum neighbour.* Capela, Céleri, Chaves and Modi (2022), arXiv:2108.11533v4, Theorem 1 (`PRA-v1.tex`, lines 271–278), states the four-time coherent-information inequality for any initial quantum state and any three quantum channels. For a finite-dimensional channel chain and $i<j,a<b$, take the initial density operator at $\rho_j$ and compose the completely positive trace-preserving channels from $\rho_j$ to $\rho_i$, from $\rho_i$ to $\sigma_a$, and from $\sigma_a$ to $\sigma_b$. The theorem gives $m(i,a)+m(j,b)\ge m(i,b)+m(j,a)$ for $m(i,a)=I_c(\rho_i:\sigma_a)$, using the paper's channel-composition definition at lines 439–443. These entries are finite real numbers. The application of the frozen `common_marginal_supermodular_le_diagonal` in `monge_permutation`, using the uniform law on $(i,f(i),i,f(i))$ and the supermodular test $F(x)=m(x_0,x_1)$ supplied by these ordered rectangles, therefore gives the finite-dimensional reading of Conjecture 2 (lines 445–454). This deduction uses the source's quantum theorem; it is not a conclusion of the classical Lean `result`.
- *Effect on the paper.* Conjecture 1's finite-alphabet necessary conditions for Markovianity now cover every even chain length $2n$, rather than only its reported checks through $n=4$. Violating any such inequality excludes a finite Markov representation by contraposition. No sufficiency criterion follows: the theorem assumes the representation and constrains its pair laws. The quantum deduction above supplies the analogous arbitrary-length inequalities conditional on the paper's Theorem 1, but does not formalize that theorem, the process-tensor construction, or non-Markovianity measures. The operational interpretation and recovery questions left in the paper's conclusion (`PRA-v1.tex`, lines 697–699) are not settled by this inequality.

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. Beyond the checked v4 source text and preregistration, the reported web and Zenodo searches, eight citing-work readings, MathDB and formal-conjectures searches, repository prior-art search, and comparison with Capela, Céleri, Chaves and Modi (2020), arXiv:1910.04236, were not independently reproduced.

The arguments about the conditional-information defect, the conditional-law/transition-law correspondence, logarithm-base conversion, equality examples, quantum extension and consequences for the paper are not separate formalized conclusions. In particular, the quantum argument relies on the source's Theorem 1 as a literature result, not a Lean verification. Equality classification, infinite-alphabet extensions, the process-tensor-to-classical-law bridge, and operational or recovery interpretations remain unverified here.

---
slug: makuta-kuzaka-augusiak-2023-stabilizer-commutation-rank
bibkey: makutakuzakaaugusiak2023fully
doi: 10.22331/q-2023-02-09-915
url: https://arxiv.org/abs/2203.16902v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.result
---

# The prime-dimensional stabilizer commutation-rank bound

## Problem

O. Makuta, B. Kuzaka and R. Augusiak, *Fully non-positive-partial-transpose genuinely entangled subspaces*, arXiv:2203.16902v2; Quantum 7, 915 (2023), Section 3, Conjecture 1 (`final_5.tex`, lines 458–463):

> Given a stabilizer $\mathbb{S}=\langle G_{1},\dots,G_{k}\rangle$, if the local dimension $d$ is a prime number and the corresponding stabilizer subspace $V$ is genuinely entangled, then
>
> $\dim K(\mathbb{S}) \geqslant \left\lceil \frac{N-1}{d-1} \right\rceil.$

The source defines $K(\mathbb{S})$ using the local commutation exponents (lines 375–391). In the Lean coordinates, write the prime local dimension as $p$. A Pauli word is a phase residue together with $x,z:\mathrm{Fin}\,N\to\mathbb F_p$, acting as $\omega^{\mathrm{phase}}\bigotimes_n X^{x(n)}Z^{z(n)}$, with $\omega=\exp(2\pi i/p)$. For words $a,b$, the commutation vector has coordinates $z_a(n)x_b(n)-x_a(n)z_b(n)$; `commutationSpace G` is the $\mathbb F_p$-span of all generator-pair vectors.

`IsStabilizer G` requires pairwise commuting generator matrices and excludes every scalar matrix other than the identity from their generated matrix submonoid. `stabilizerSubspace G` is the intersection of the generators' fixed subspaces. `genuinelyEntangled G` says that every nonzero vector in this intersection fails to factor across every bipartition with two nonempty sides. Factorization means an amplitude of the form $u(x|_Q)v(x|_{Q^c})$; normalization is not required.

Issue [#20105](https://github.com/the-omega-institute/trureturing/issues/20105) fixes the statement for every $N\ge1$, prime $p$, and finite generator family. `claim` uses natural-number division:

$(N-1+(p-2))/(p-1)\le\operatorname{finrank}_{\mathbb F_p}(\operatorname{commutationSpace}G)$.

For $N\ge1$ and prime $p$, the left side is $\lceil(N-1)/(p-1)\rceil$. The conjecture is proved.

## Motivation

The commutation space records how global commutativity is assembled from local noncommutativity. A necessary lower bound on its dimension constrains the number of independent stabilizer generators and hence the possible size of a genuinely entangled stabilizer subspace. The source connects Conjecture 1 to its maximal-dimension Conjecture 2 in Section 3.1, lines 554–583.

The definitions and source locators are also recorded in [the literature note](../Library/QuantumContext/makutakuzakaaugusiak2023fully.md).

## Gap

The bounded literature check before any Lean is recorded in #20105:

- The source-reading author, the orchestrator, reports that arXiv v2 is the latest version and that the journal version retains the conjecture. The v2 TeX itself contains Conjecture 1 and the sentence at line 538: “However, since we were not able to prove Conjecture \ref{con_ge}, the actual value of $p(N,d)$ remains unknown.”
- The orchestrator reports a Semantic Scholar list of ten citing works and readings of the TeX sources of arXiv:2508.13734, 2503.22400, 2504.11525, 2509.26135, 2312.08474, 2301.03120 and 2211.03813, with no statement or proof of this commutation-rank bound. These are seven specified readings, not a claim that all ten citing works were checked.
- The issue records no matching entry on dev in `Problems/`, `Library/`, or an issue search for the arXiv identifier.

`not-found-in-searched-scope`.

## Route

Put $r=\dim_{\mathbb F_p}K$ and $m=N-1$.

1. **Nonzero fixed subspace.** The generated Pauli matrix submonoid $T$ is finite and consists of invertible matrices. Every nonidentity element has trace zero: a word with a nonzero displacement coordinate is traceless, while a scalar word in $T$ must be the identity. Thus $M=\sum_{A\in T}A$ has trace $p^N\ne0$. Each generator permutes $T$ by left multiplication, so a nonzero vector in the image of $M$ is fixed by every generator. Nontriviality of the stabilizer subspace is derived, not assumed.
2. **No vanishing coordinate subsum.** If a nonempty subset $Q$ of the first $N-1$ parties had zero coordinate sum for every vector in $K$, the generator restrictions to $Q$ would commute. The complementary restrictions commute as well, since the total commutation phases vanish. On the nonzero common fixed subspace, the commuting complementary actions have a common eigenvector. Taking two coordinate slices of this vector gives a nonzero product vector fixed by every generator. Since the last party is outside $Q$, this contradicts genuine entanglement across a nontrivial cut.
3. **Chevalley–Warning.** For a basis $u_1,\dots,u_r$ of $K$, suppose $m>r(p-1)$. The polynomials $f_i(x)=\sum_{j=1}^{m}u_i(j)x_j^{p-1}$ have degree sum at most $r(p-1)<m$. Mathlib's `char_dvd_card_solutions_of_sum_lt` makes the number of common zeros divisible by $p$. Zero is one solution, so another solution $x\ne0$ exists. Fermat's identity turns $x_j^{p-1}$ into the indicator of its support, yielding a forbidden nonempty coordinate subsum. Hence $N-1\le r(p-1)$, giving the ceiling bound, including $N=1$.

## Falsifier

A counterexample would be a finite Pauli generator family satisfying both stabilizer conditions, with every nonzero common fixed vector entangled across every nontrivial cut, but with commutation-space dimension below $\lceil(N-1)/(p-1)\rceil$.

Source fidelity requires the actual Pauli matrix actions, scalar exclusion, and the full common fixed subspace. The module defines all three explicitly. Its generated submonoid formulation uses finite products of actual matrices; finiteness and invertibility make this a group, so it does not weaken the source's generated-subgroup condition. The entanglement predicate excludes only nonzero product vectors and quantifies over every nontrivial bipartition. Its intersection of fixed submodules is not an optimization over possibly empty feasible sets, and the proof supplies a nonzero fixed vector.

## Evidence

The canonical source is `D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.lean` (706 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank.lean.json`, statement `sha256:c276c8afc2f5b7856b0fd2d053720e6b414e194a2fb8e7b7bc73bbaff8c95e77`.

Declaration statements:

- `result`: `sha256:071fd2667f70e4962ce0b3dce958f25f6375f7eec69a18bd2c985ed830fa5d35`;
- `claim`: `sha256:d78c47fe2507b744503a8c594633087b18ff6a8fb58a5c14b78b966c663971a0`.

## Triage

Tier 1 conjecture of a 2022 preprint published in Quantum in 2023, preregistered in issue #20105 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $N,p,k\in\mathbb N$ with $N\ge1$ and $p$ prime, and every family $G:\mathrm{Fin}\,k\to\operatorname{PauliWord}(N,p)$, if its generator matrices commute pairwise, its generated matrix submonoid contains no scalar matrix other than the identity, and every nonzero common fixed vector fails to factor across every bipartition with two nonempty sides, then

$\lceil(N-1)/(p-1)\rceil\le\operatorname{finrank}_{\mathbb F_p}(\operatorname{commutationSpace}G)$.

**Computed, not formalized.** Exact integer enumeration tests all unordered length-$m$ multisets of nonzero columns in $\mathbb F_p^r$, with no constraint on their total sum. A dynamic program retains the sums of all nonempty submultisets.

| $p$ | $r$ | $m$ | Multisets tested | Without a nonempty zero subsum |
| --- | --- | --- | --- | --- |
| 2 | 1 | 3 | 1 | 0 |
| 2 | 2 | 4 | 15 | 0 |
| 2 | 3 | 5 | 462 | 0 |
| 3 | 1 | 4 | 5 | 0 |
| 3 | 2 | 6 | 1716 | 0 |
| 5 | 1 | 6 | 84 | 0 |
| 7 | 1 | 8 | 1287 | 0 |

For these 3570 tested multisets, absence of a nonempty zero subsum was not observed. This checks only the listed finite families, not the Pauli-to-entanglement bridge or any untested parameters. The separate finite check reported by the codex-cli search author in #20105 is not used as reproduced evidence here.

**Argued, not formalized.**

- *Decisive mechanism and extent.* The degree $p-1$ makes a nonzero field coordinate contribute exactly one, converting a polynomial common zero into an ordinary subset, rather than a general linear dependence with arbitrary coefficients. The combinatorial argument applies to any subspace $K\subseteq\mathbb F_p^N$ for which every nonempty subset of the first $N-1$ coordinates has a nonzero coordinate-sum functional on $K$: choose a basis and apply the polynomials in the Route. The Pauli structure is used to obtain this condition from entanglement. For $p=2$ the bound specializes to $r\ge N-1$; for $N=1$ it is the zero lower bound. No composite-local-dimension conclusion follows, because the proof uses a field and Fermat's identity.
- *Why scalar exclusion matters.* With $N=2$, $p=2$, and the single generator $-I$, the fixed subspace is zero. The entanglement predicate is then vacuous and the commutation space has dimension zero, below the required bound one. This family is excluded by `IsStabilizer`. Thus nontriviality cannot simply be omitted from the bridge without deriving it from the stabilizer conditions.
- *Sharpness on an infinite family.* For any prime $p$, take $N=p$ and generators $X^{\otimes p}$ and $Z^{\otimes p}$. They commute, and a product $(X^{\otimes p})^a(Z^{\otimes p})^b$ is scalar only when $a=b=0$ modulo $p$: a nonzero $a$ shifts basis labels and a nonzero $b$ gives a nonconstant diagonal. The vector $\sum_{t\in\mathbb F_p}|t\rangle^{\otimes p}$ is a nonzero common fixed vector. If any nonzero common fixed vector factored across a cut of size $s$, each factor would be an eigenvector of both restricted generators. Indeed, equality of two nonzero simple tensors forces proportionality of their factors. But on a side of size $1\le s<p$ these restrictions commute with phase $\omega^{-s}\ne1$, which precludes a common nonzero eigenvector. Thus the whole fixed subspace is genuinely entangled. Its commutation vectors span the nonzero constant vector, giving $r=1=\lceil(p-1)/(p-1)\rceil$. This verifies sharpness for $N=p$ by an argument, not by `result`; attainment for every $N,p$ is not formalized here.
- *A surviving neighbouring distinction.* The rank bound is necessary, not sufficient. For $p=3$, $N=3$, the family $X\otimes Z\otimes I$, $Z\otimes X\otimes I$ is a stabilizer: its two nonzero local commutation exponents cancel, and a product is scalar only for zero exponents. Its commutation space has rank one, meeting the bound. The first two factors have the common fixed vector $\sum_{a,b\in\mathbb F_3}\omega^{ab}|a,b\rangle$: the two generator actions give amplitudes $\omega^b\omega^{(a-1)b}=\omega^{ab}$ and $\omega^a\omega^{a(b-1)}=\omega^{ab}$. Tensoring this vector with any nonzero third-party vector produces a product across the third-party cut. Hence satisfying the bound does not characterize genuine entanglement.
- *Effect on dependent statements.* In Section 3.1, line 563, the authors write: “Let us now provide a proof that Conjecture \ref{con_ge} implies Conjecture \ref{con_dim}.” Their Conjecture 2, lines 556–559, is:

  > If $d$ is prime then the maximal dimension of genuinely entangled, stabilizer subspace is given by $d^{N-k_{\min}(N)}$, where
  >
  > $k_{\min}(N,d)=\left\lceil \frac{1+\sqrt{1+8\lceil (N-1)/(d-1)\rceil}}{2} \right\rceil.$

  For $N\ge2$, put $R=\lceil(N-1)/(p-1)\rceil$. An independent generating set of size $s$ has at most $s(s-1)/2$ distinct nonzero generator-pair vectors spanning $K$: diagonal pairs vanish and reversing a pair negates its vector. The bilinearity of commutation exponents shows that changing between generating sets preserves that span. The settled bound therefore gives $s(s-1)/2\ge R$ and $s\ge\lceil(1+\sqrt{1+8R})/2\rceil$. The scalar-free abelian Pauli group generated by these independent elements has order $p^s$: each element has order dividing $p$, since its $p$th power is scalar and hence the identity. Its averaging projector has trace, and therefore fixed-space dimension, $p^N/p^s=p^{N-s}$. These steps give the upper bound in Conjecture 2. The matching lower bound still uses the source's recursive construction in Appendix D, beginning at $N=2$ (lines 968–1045). Accepting that construction and its independence and entanglement arguments supplies the matching dimension; its verification is outside `result`. Thus Conjecture 2's dependence on Conjecture 1 is discharged, while the complete maximal-dimension statement is not a compiled consequence delivered by this module. Likewise, the exact optimal threshold $p(N,d)$ discussed at line 538 requires an attaining construction in addition to this lower bound. At $N=1$ genuine entanglement is vacuous and the trivial stabilizer fixes the full $p$-dimensional space; the multipartite maximal-dimension formula is not extended to that case.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The latest-version and journal-status readings, the Semantic Scholar count, the seven citing-paper readings, and the dev/issue-search absence are reports by the preregistration's authors, not independently reproduced readings. The source independently read is arXiv:2203.16902v2, `final_5.tex`, 1184 lines, md5 `8b745e95a3a5cb115f40e13c86b1e06d`; its conjecture and dependent argument are located above.

All computations and arguments under those labels are outside the statement proved by `result`. The finite enumeration gives no conclusion beyond its tested parameters. The original search author's finite-check script and output were not reproduced. Universal attainment, the complete recursive construction and independence proof of Appendix D, the maximal-dimension formula, and an exact optimal threshold for every $N,p$ are not formalized here. The Appendix D construction is read as a source argument, not independently rederived or checked in full. Composite local dimensions and a general classification of equality cases remain open within this settlement.

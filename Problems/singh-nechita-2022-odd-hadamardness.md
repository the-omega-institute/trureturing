---
slug: singh-nechita-2022-odd-hadamardness
bibkey: singhnechita2022evolution
doi: 10.1088/1751-8121/ac7017
url: https://arxiv.org/abs/2112.11123v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.result
---

# Odd order does not ensure the conjectured minimum of Hadamardness

## Problem

S. Singh and I. Nechita, *Diagonal unitary and orthogonal symmetries in quantum theory II: Evolution operators*, J. Phys. A: Math. Theor. 55 (2022) 255302, arXiv:2112.11123v1, Section 6, `main.tex` line 848, immediately following Table 1:

> We note that for the odd values of $d$ considered above, $\min \mathfrak h(C) = d^3 + d(d-1)$, obtained for matrices $C$ with the property that all the scalar products between different works have absolute value $1$. We conjecture that this is the case for all odd integers $d$.

“Works” is the source's wording. The source defines its measure in Eq. `eq:Hada_measure`, `main.tex` lines 780–783. For a real sign matrix, write $G=CC^{\mathsf T}$ and $\mathfrak h(C)=\operatorname{Tr}(G^2)=\sum_{i,j}G_{ij}^2$; conjugate transpose and transpose coincide here. The source and its table are described in [the literature note](../Library/Eigenstructure/singhnechita2022evolution.md).

Issue [#22426](https://github.com/the-omega-institute/trureturing/issues/22426) fixes the reading encoded by `claim`: for every odd natural $d$, there exists an integer $d\times d$ matrix $C$ with every entry equal to $1$ or $-1$, such that $\mathfrak h(C)=v_d$ and every integer sign matrix $B$ of that order satisfies $v_d\leq\mathfrak h(B)$. Here $v_d=d^3+d(d-1)$ is evaluated in the natural numbers, including subtraction, and then embedded in the integers. Thus attainment and the lower bound are both explicit; no infimum convention is used. The conjecture is refuted, using order nine.

## Motivation

Section 6 connects Hadamardness to the entangling power of real dual orthogonal operators invariant under local diagonal unitary actions (LDUI). For $d>1$, the expressions in `main.tex` lines 757–771 specialize to $e_p(X)=(1-\mathfrak h(C)/d^4)/(1-1/d^2)$ for the corresponding sign matrix $C$. Maximizing this quantity requires minimizing Hadamardness. A lower bound alone does not determine that optimum unless an admissible sign matrix attains it.

## Gap

The bounded literature check recorded in #22426 reports:

- web searches for the conjecture and Hadamardness of sign matrices found no settlement in the inspected literature;
- Zenodo searches for Hadamardness and the source title returned no record;
- OpenAlex listed eleven citing works, six citing full texts were screened without finding a settlement, and MathDB and formal-conjectures had no match;
- no earlier repository settlement was found.

These are attributed search readings from #22426; the external searches and citing texts were not independently reproduced. The directly inspected arXiv v1 source contains the conjecture verbatim. The literature status is `not-found-in-searched-scope`.

## Route

Unqualified lemma names below refer to the canonical module; its auxiliary lemmas are private. Write $J$ for the all-ones matrix.

1. **Trace and entry bounds.** `hadamardness_sum` applies to every natural $d$ and every integer $d\times d$ matrix $C$, without a sign hypothesis, and gives $\mathfrak h(C)=\sum_{i,j}(CC^{\mathsf T})_{ij}^2$. For a $9\times9$ integer sign matrix $C$, `gram_diag` gives $G_{ii}=9$ for every $i$, and `gram_odd` gives $G_{ij}=1$ modulo $2$ for every $i,j$.
2. **Equality forces unit correlations.** For a $9\times9$ integer sign matrix $C$ with $\mathfrak h(C)=801$, `equality_forces_unit` gives $G_{ij}\in\{1,-1\}$ whenever $i\ne j$. The diagonal squares equal $81$ and the off-diagonal squares are at least $1$; their lower bounds sum to $801$, so equality of the total forces equality in each summand.
3. **Normalize the Gram matrix.** For a $9\times9$ integer sign matrix $C$ whose distinct-row inner products are all $1$ or $-1$, `normalize_gram` produces an integer $9\times9$ matrix $B$ with $BB^{\mathsf T}=8I+J$. Its construction uses $s_0=1$, $s_i=G_{i0}$ for $i\ne0$, and $B=\operatorname{diag}(s)C$. These multipliers are signs and the off-diagonal entries in column zero of $BB^{\mathsf T}$ become $1$. For every $9\times9$ integer sign matrix and all row indices $i,j,r$, `gram_triangle` gives $G_{ij}\equiv G_{ir}+G_{rj}-1\pmod4$. Applied to the constructed sign matrix $B$ with $r=0$, it excludes $-1$ for every remaining off-diagonal entry; the diagonal entries are $9$.
4. **Determinant obstruction.** For any integer $9\times9$ matrix $B$ satisfying $BB^{\mathsf T}=8I+J$, with no additional sign hypothesis, `gram_impossible` derives a contradiction. Map $B$ to $A$ over $\mathbb Z/3\mathbb Z$. The mapped Gram matrix is $2(I+uv^{\mathsf T})$, where every entry of $u$ is $2$ and every entry of $v$ is $1$. The identity `Matrix.det_one_add_replicateCol_mul_replicateRow`, applied to these length-nine vectors over $\mathbb Z/3\mathbb Z$ with the single column indexed by `Unit`, gives $\det(A)^2=2^9(1+\sum_i v_i u_i)=2$ in $\mathbb Z/3\mathbb Z$. The reused `D5.S3.Factorization.CubeGapFiveNoSquare.sq_mod_three_ne_two` says that $m^2\bmod3\ne2$ for every natural $m$; applying it to the natural representative of $\det(A)$ gives the contradiction.
5. **Negate the universal claim.** Its odd-order instance at $d=9$ would supply a sign matrix with $\mathfrak h(C)=9^3+9\cdot8=801$, contradicting the preceding lemmas. The lower-bound clause of `claim` is not needed for this contradiction.

## Falsifier

The formalization would miss the source conjecture if its matrix domain, trace, quantifier over odd orders, or meaning of minimum differed from the source's. `IsSignMatrix` requires every integer entry to be exactly $1$ or $-1$; it imposes no symmetry, invertibility, or dephasing condition. Every real sign matrix has the same entries as a unique integer sign matrix, and integer arithmetic preserves its Gram matrix and trace. `hadamardness` is exactly the trace of the squared row Gram matrix. `claim` requires an attaining matrix and a lower bound over all sign matrices for every odd natural order, including $d=1$. The obstruction is at $d=9$, within this domain. It concerns simultaneous realizability of all row correlations, rather than a failure to find a matrix numerically.

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/SinghNechitaOddHadamardnessRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:0dde2e29381886cb96eb9fb474561e7606a119779444cf6a02d777f163edae98`;
- `claim`: `sha256:899e1e445a87ac67d3de689fadb7548894a7058d22a0341d055c23078f9a19dc`.

## Triage

Tier 1 conjecture of a 2021 preprint published in 2022, supported in the source by enumeration at odd orders three and five, preregistered in issue #22426 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every odd natural $d$, there exists an integer sign matrix $C$ of order $d$ with $\mathfrak h(C)=v_d$ and every integer sign matrix $B$ of that order satisfies $v_d\leq\mathfrak h(B)$, where $v_d$ is the integer embedding of the natural number $d^3+d(d-1)$.

**Computed, not formalized**:

- Exact enumeration of dephased sign matrices gives minima $1$, $33$ and $145$ at orders $1$, $3$ and $5$, respectively.
- The core of the Sylvester Hadamard matrix of order eight has Hadamardness $385=7^3+7\cdot6$ and all distinct-row inner products equal to $-1$ at order seven.
- Exact determinant arithmetic at order nine gives $\det(8I+J)=285212672=17\cdot8^8\equiv2\pmod3$.

**Argued, not formalized**:

- *The lower bound survives.* For every odd natural $d$ and integer sign matrix $C$ of order $d$, diagonal Gram entries equal $d$, while every distinct-row inner product is an odd integer and has square at least $1$. Summing gives $\mathfrak h(C)\geq d^3+d(d-1)$, with equality precisely when all distinct-row inner products have absolute value $1$. There are finitely many sign matrices and the all-ones matrix supplies nonemptiness. Thus the issue is attainment, not existence of a minimum. At order nine the Route excludes equality, so the minimum is strictly greater than $801$; its exact value is not determined here.
- *Why oddness is insufficient.* Individual correlations can each have the smallest allowed absolute value without those choices forming a Gram matrix of integer sign rows. For a $9\times9$ integer sign matrix whose distinct-row inner products are all $1$ or $-1$, `normalize_gram` produces an integer $9\times9$ matrix $B$ with $BB^{\mathsf T}=8I+J$. For any integer $9\times9$ matrix $B$, `gram_impossible` excludes that Gram identity. The missing structure is a jointly realizable family of rows, not a stronger estimate on an individual odd inner product.
- *A necessary condition in other orders.* A separate argument applies to a sign matrix of natural order $d>1$ with $d\equiv1\pmod4$ that attains the lower bound. Negate each row having an odd number of negative entries; because $d$ is odd, each resulting row has an even number of negative entries. Two such rows have even Hamming distance $\delta$, so their inner product $d-2\delta$ is $1$ modulo $4$. Its absolute value is $1$, hence it equals $1$. The resulting Gram matrix is $(d-1)I+J$, with eigenvalue $2d-1$ on the all-ones vector and eigenvalue $d-1$ on its orthogonal complement. Its determinant is $(2d-1)(d-1)^{d-1}$. Since the determinant is the square of an integer and $(d-1)^{d-1}$ is a nonzero square, $2d-1$ must be a rational square, hence an integer square: a rational square root $p/q$ in lowest terms must have $q=1$, since $q^2$ divides $p^2$. In particular, attainment is excluded for every $d\equiv9\pmod{12}$, since $2d-1\equiv2\pmod3$. No sufficiency of the square condition is asserted.
- *A surviving sufficient construction.* If $d$ is an odd natural number and a real Hadamard matrix of order $d+1$ exists, normalize its first row and column to ones and delete them. Orthogonality of the original rows gives the core Gram matrix $(d+1)I-J$, so the core attains $d^3+d(d-1)$. This supplies a structural hypothesis under which the proposed minimum is correct. Row and column sign changes preserve squared row correlations and can dephase every sign matrix, so the finite enumerations above cover all matrices at their stated orders. Together with the order-seven core and the lower-bound argument, they establish minimality of order nine among odd counterexamples as an unformalized consequence.
- *Effect on the source.* In the inspected v1 text the conjecture closes Section 6; no subsequent proposition invokes it, and the conclusion explicitly leaves further analysis of Hadamardness as a question (`main.tex` line 945). The complex-Hadamard maximum immediately preceding the conjecture uses the separate trace bound $\operatorname{Tr}[(CC^\dagger)^2]\geq d^3$ for unit-modulus entries and complex Hadamard examples, independently of the odd-order sign-matrix claim (`main.tex` lines 750–776). For the real dual orthogonal LDUI class at $d=9$, the entangling-power formula in Motivation is strictly decreasing in $\mathfrak h$, so its optimum is strictly below the value obtained by substituting $801$. Determining that optimum, or the larger LDOI optimum asked about in the conclusion, is not settled here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The web and Zenodo searches, the OpenAlex citation count and six citing full-text readings, and the MathDB and formal-conjectures checks recorded in #22426 were not independently reproduced. The reported retention of the conjecture in the published journal text was not checked; the source read directly is arXiv:2112.11123v1, `main.tex`, whose conjecture is at line 848.

The integer-to-real identification and every statement in “Computed, not formalized” and “Argued, not formalized” are outside the formal conclusion of `result`. In particular, the general odd-order lower bound, the necessary square condition and its extension to other orders, the Hadamard-core construction, minimality of order nine, and the entangling-power consequences are not separate theorems of this module. The exact minimum at order nine, a classification of attaining odd orders, sufficiency of the square condition, and the larger LDOI optimization question remain open here.

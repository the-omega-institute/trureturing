---
slug: heimendahl-heinrich-gross-2022-affine-partition-flag
bibkey: heimendahlheinrichgross2022magic
doi: 10.1063/5.0085774
url: https://arxiv.org/abs/2011.11651v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.result
---

# The flag partition maximizes the squared sizes of affine parts outside the origin

## Problem

A. Heimendahl, M. Heinrich and D. Gross, *The axiomatic and the operational approaches to resource theories of magic do not coincide*, arXiv:2011.11651v3 (J. Math. Phys. 63, 112201, 2022), conjecture in the remark following Corollary `cor:SO-cap-AD`. The checked TeX member `paper_new.tex`, lines 1219–1227, reads:

> We conjecture that such a projective measurement which maximizes \eqref{eq:estimation-of-overlapII}
> has the following form:
>
> Measure the first qudit in the computational basis.
>
> If $ x \neq 0 $ is measured, do nothing.
> If $ 0 $ is measured, measure the second qudit in the computational basis.
> Continue in this fashion until all qubits are measured.
>
> If $ 0 $ has been measured on every qudit, apply a Hadamard gate to every qudit.

Write $p$ for the source's prime dimension $d$, and $V=\mathbb F_p^n$, represented by `Fin n → ZMod p`. An affine partition (`isAffinePartition`) is a finite set of nonempty affine subspaces, with distinct parts disjoint, such that a vector belongs to a part if and only if it is nonzero. Its objective is `sqSum`, namely $\sum_{K\in\mathcal K}|K|^2$.

The cells $K_{i,x}=\{v\in V:(\forall j<i,\ v_j=0),\ v_i=x\}$, for $0\le i<n$ and $x\in\mathbb F_p\setminus\{0\}$, form `flagPartition p n`. Put $S_p(n)=\sum_{k=0}^{n-1}(p-1)p^{2k}$, the definition `flagValue p n`.

Issue [#25329](https://github.com/the-omega-institute/trureturing/issues/25329) fixes the reading: for every prime $p$ and every $n\in\mathbb N$, the flag family is an affine partition, its objective equals $S_p(n)$, and every affine partition of $V\setminus\{0\}$ has objective at most $S_p(n)$. This is the proposition `claim`, proved by `result`.

## Motivation

The source compares stabiliser operations (SO), defined by Clifford gates, Pauli measurements and classical control, with completely stabiliser-preserving channels (CSP). Lemma `lem:so-in-ad` (TeX lines 986–994) expresses the relevant SO states through affine partitions of the nonzero vectors. Equation `eq:estimation-of-overlapII` (lines 1215–1217) bounds their overlap by $\langle+|\sigma|+\rangle\le\sum_{K\in\mathcal K}|K|^2/[p^n(p^n-1)]$. Maximizing the squared-size sum therefore supplies a quantitative upper bound for that comparison when $n\ge1$. The source's permitted partitions have additional tree structure; the formal statement bounds all affine partitions.

## Gap

The bounded literature check recorded in #25329 is attributed there to the orchestrator (Claude Code, Opus):

- The arXiv v3 source contains the conjecture; the journal text was not read.
- Citation-context and affine-subspace searches in arXiv:2311.06133, 2507.10851, 2610.38401, 2211.15678, 2202.07867, 2507.11793 and 2608.10202 found no settlement of this conjecture or bound on the squared-size sum.
- Zenodo, GitHub preregistration and repository searches found no existing settlement in their searched scope.

`not-found-in-searched-scope`. These searches do not establish worldwide novelty or priority.

## Route

The helper names below refer to private lemmas in the canonical module.

1. **Part cardinalities.** For prime $p$, natural $n$ and a nonempty affine subspace $K\subseteq\mathbb F_p^n$, `affine_card` gives $|K|=p^{\dim K.direction}$. For a finite family satisfying `isAffinePartition p n parts`, `partition_card` gives $\sum_{K\in\mathcal K}|K|=p^n-1$.
2. **Radix potential.** Define $h_p(s)$ by reading the base-$p$ digits of $s$ as base-$p^2$ digits (`radix`). For natural $p\ge2$ and natural $k,s$ with $p^k\le s$, `radix_power` gives $p^{2k}+h_p(s-p^k)\le h_p(s)$. For any type, finite index set $t$ and size function into $\mathbb N$ such that every indexed size is $p^k$ for some natural $k$, `power_family_bound`, assuming $p\ge2$, gives $\sum_{x\in t}size(x)^2\le h_p(\sum_{x\in t}size(x))$. For $p\ge2$ and every natural $n$, `radix_value` evaluates $h_p(p^n-1)=S_p(n)$. For prime $p$, natural $n$ and `isAffinePartition p n parts`, `partition_bound` combines these facts to bound `sqSum parts` by `flagValue p n`.
3. **Attainment.** For prime $p$, natural $n$, $i\in\mathrm{Fin}\,n$ and any $x\in\mathbb F_p$, including zero, `flag_cell_card` gives $|K_{i,x}|=p^{n-1-i}$. For prime $p$ and every natural $n$, `flag_partition` proves that the cells with $x\ne0$ form an affine partition, and `flag_sum` proves that their objective equals $S_p(n)$. Together with `partition_bound`, these are the three conjuncts of `claim`.

## Falsifier

The settlement would miss the source's question if the objective or admissible cells differed. The formal cells follow the measurement procedure: coordinates before the first nonzero outcome are fixed to zero, that outcome is fixed, and the remaining coordinates are free. With zero-based $i$, there are $n-1-i$ free coordinates. The source's display at TeX lines 1230–1232 instead uses $n-i$; its displayed affine set at $i=0$ would be the whole space and contain zero. The formal reading follows the procedure, not that inconsistent display. The prime-field scope follows the source's setup at lines 131–133; the isolated $\mathbb F_2^n$ in line 1218 does not restrict `claim` to qubits.

Bounding every affine partition also bounds the tree-structured subclass described by the source. Identifying the proposed procedure with a permissible stabiliser operation is a source-level bridge, not a Lean statement of this module. Neither quantum-state normalization nor attainment of the overlap bound is formalized here. The case $n=0$ is included in `claim` as an empty partition with objective zero; the overlap expression is used only for $n\ge1$, when its denominator is positive.

## Evidence

The canonical source is `D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Magic/AffinePartitionFlagMaximum.lean.json`.

Declaration statements:

- `result`: `sha256:6f6d034b48658a69f9ba3e6d0fde8826ac69f1f295e9b25b5316c8c0e09b77bc`;
- `claim`: `sha256:f01998ff2b176f3845f390fbc5e52ada71b92378f072ab5d5dde6e1d6050dd32`.

## Triage

Tier 1 conjecture of a 2020 preprint published in 2022, checked in arXiv v3, preregistered in issue #25329 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every prime $p$ and every natural $n$, `flagPartition p n` is a finite partition of $\mathbb F_p^n\setminus\{0\}$ into nonempty, pairwise disjoint affine subspaces, its squared-cardinality sum equals $S_p(n)$, and every such affine partition has squared-cardinality sum at most $S_p(n)$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Cardinality mechanism and equality profiles.* For any integer base $b\ge2$, consider a finite multiset of powers $b^j$ with total $b^n-1$, for natural $n$. Replacing $b$ copies of $b^j$ by one copy of $b^{j+1}$ preserves the total and increases the squared-size sum by $(b^2-b)b^{2j}>0$. Repeating terminates because the number of parts decreases. The final multiplicities are the base-$b$ digits of $b^n-1$: $b-1$ at each exponent below $n$, and zero elsewhere. Thus a maximizing size multiset has precisely that profile. This argument concerns cardinalities; the replacements need not be realizable as mergers of affine parts.
- *Extension and geometric sharpness.* The same cardinality argument applies over any finite field of size $q$, since each nonempty affine part has $q^r$ points and the punctured space has $q^n-1$ points; the coordinate flag cells provide $q-1$ parts of each size $q^j$ for $0\le j<n$. This extension beyond prime fields is not a statement of `result`. An invertible linear change of coordinates preserves affine parts, disjointness, the punctured space and cardinalities, so it preserves the maximum. A classification of all maximizing partitions, and whether every maximizer arises from a complete flag, remain open here.
- *Corrected arithmetic.* The source writes "$\sum_{K \in \mathcal{K}} |K|^2 = \sum_{k = 0}^{n-1}  (d-1) d^{2k} = (d-1) \frac{d^{2n-2}}{d^2-1}$" (TeX line 1235). For $p\ge2$ and natural $n$, telescoping gives $(p^2-1)\sum_{k=0}^{n-1}p^{2k}=p^{2n}-1$, hence $S_p(n)=(p^{2n}-1)/(p+1)$. For $n\ge1$, its normalized value is $S_p(n)/[p^n(p^n-1)]=(p^n+1)/[(p+1)p^n]$, tending to $1/(p+1)$ as $n$ grows with $p$ fixed. This corrects the source's "$\approx \frac{1}{d^3}$" at line 1241. The closed form and limit are not part of the Lean type of `result`.
- *Effect on the source's separation claim.* For prime $p$ and $n\ge2$, the corrected normalized value is at most $(p^2+1)/[(p+1)p^2]$, which is below $1/p$ by $(p-1)/[(p+1)p^2]>0$. Combining the partition bound with the source's overlap inequality therefore gives a positive separation uniform in $n\ge2$ under the source's state representation. At $n=1$ the normalized value equals $1/p$. This supplies the quantitative consequence sought in the conjectural remark for $n\ge2$, with corrected arithmetic. Corollary `cor:SO-cap-AD` already has an independent strict-inequality argument at lines 1197–1207. Neither that corollary, the SO/CSP channel representations, nor overlap attainment is proved by this module; no other source result is settled by `result`.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches reported in #25329; its seven citing-work readings, Semantic Scholar citation listing and Zenodo/GitHub search results were not independently reproduced. The journal text was not read, so retention of the conjecture and its displayed arithmetic in the journal version is unverified. The arXiv v3 TeX conjecture, surrounding partition lemma and quantitative remark were read directly.

The arguments under "Argued, not formalized" are not Lean conclusions of this module, including the equality-profile characterization, arbitrary finite-field extension, closed-form evaluation, asymptotic value and conditional quantum separation. The correspondence between source-admissible operations and partitions, the source's quantum overlap inequality, overlap attainment and classification of maximizing geometries are outside the formal statement; the last two remain open here.

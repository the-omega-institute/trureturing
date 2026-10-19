---
bibkey: dechter1996bucket
authors: Rina Dechter
year: 1996
title: 'Bucket elimination: A unifying framework for probabilistic inference'
doi: null
url: https://arxiv.org/pdf/1302.3572
claim: Elimination over an ordered decomposition combines local factors while retaining separator information, with exponential dependence on structural width.
strata_touched: []
license: citation-only
triage: anchor
---

# Explicit ordered-frontier compilation and complete overlap records

**Definition 1 (Source scope and constraint encoding).** The original UAI paper at https://arxiv.org/pdf/1302.3572, printed pp. 211–219, describes bucket elimination; §2 defines ordered graphs and induced width, and the inference sections analyze width-dependent elimination. The frontier construction below is a full elementary ordered dynamic-programming exposition. Its width is defined directly and is not silently equated with the source's induced width. Fixed-order residual sharing and order sensitivity are also classical [ordered Boolean graph][BRYANT] mechanisms. The equality example below is already a repository result in [minimal realization][MINIMAL], Theorem 22.

Input $x$ explicitly lists Boolean variables $V=\{v_1,\ldots,v_m\}$, their order, finite local scopes $S_j\subseteq V$, and ordinary finite Boolean circuits $C_j$ with their input wires assigned to $S_j$, $1\le j\le r$. Total bit length is $n$. The encoding lists every variable, scope and gate, so $m,r$ and total circuit evaluation work are bounded by a polynomial in $n$. The relation is

$$
R_x(w)=\bigwedge_{j=1}^r C_j(w|_{S_j}).
\tag{1}
$$

Let $P_i=\{v_1,\ldots,v_i\}$, $U_i=V\setminus P_i$, and

$$
B_i=\{v\in P_i:\exists j,\ v\in S_j,\ S_j\cap U_i\ne\varnothing\},
\qquad w(x,\prec)=\max_i|B_i|.
\tag{2}
$$

$B_i$ is the ordered frontier of already assigned variables still involved in an unfinished constraint. It is computable from scopes and order without knowing satisfiability.

## 1. Records, addresses and compilation cost

**Proposition 1 (Frontier sufficiency).** A prefix of length $i$ can be represented by a failure flag if a completed constraint is false, and otherwise by its joint assignment $\alpha\in\{0,1\}^{B_i}$. Appending one bit has a deterministic record update, and prefixes with the same record have the same accepting suffix language.

Proof. One has

$$
B_{i+1}\subseteq B_i\cup\{v_{i+1}\}.
\tag{3}
$$

Indeed an old variable still meeting an unassigned variable in a scope after step $i+1$ already had that property at step $i$. Moreover a constraint completed exactly when $v_{i+1}$ is assigned has all its old variables in $B_i$, because before the step they shared that unfinished scope with $v_{i+1}$.

At initialization evaluate all empty-scope constraints; a false one starts in failure, otherwise in the empty assignment. From normal $(i,\alpha)$ and bit $b$, evaluate every newly completed constraint on $\alpha$ together with $v_{i+1}=b$. If any fails go to the next-layer failure state; otherwise retain

$$
\beta=(\alpha\cup\{v_{i+1}\mapsto b\})|_{B_{i+1}}.
\tag{4}
$$

Failure propagates. Induction proves the flag means exactly a violated completed constraint and the normal assignment equals the prefix restriction. At layer $m$, $B_m=\varnothing$ and all constraints have been checked; the normal terminal accepts and failure rejects. Equal records follow identical transitions for every common suffix, giving equal final values. In particular a current record retains joint boundary assignments, not just the independent one-variable marginals. $\square$

**Proposition 2 (One uniform finite compiler).** There is a fixed deterministic compiler producing a layered DAG with exactly

$$
M=\sum_{i=0}^m(2^{|B_i|}+1)
\le(m+1)(2^w+1)
\tag{5}
$$

records, two successor addresses per nonterminal record, a completion bit and an optional next-bit strategy. Its total description length is

$$
O(M\log(M+2)+n),
\tag{6}
$$

and the construction, decision and witness-output work can be bounded by

$$
n^{O(1)}2^{O(w)}.
\tag{7}
$$

If the supplied order has $w=O(\log(n+2))$, all these operations take polynomial time.

Proof. At each layer enumerate the $2^{|B_i|}$ normal boundary assignments and one failure record. Define transitions by Proposition 1. Terminal completion bits are one on the normal empty assignment and zero on failure. Work backwards by

$$
H_i(z)=H_{i+1}(\Delta_i(z,0))\lor H_{i+1}(\Delta_i(z,1)).
\tag{8}
$$

Induction on remaining length, using frontier sufficiency, gives for every actual prefix $u$

$$
H_i(\sigma_i(u))=\mathbf1[\exists t,\ R_x(ut)=1].
\tag{9}
$$

Choose zero when its successor has bit one and one otherwise. If the current bit is one, this selects an accepting successor; if zero, both children are zero. Therefore on every record, not just positive instances,

$$
H_i(z)=H_{i+1}(\Delta_i(z,\pi_i(z))).
\tag{10}
$$

Starting at the actual initial record and appending the choices for $m$ steps yields a full assignment whose verification equals the root completion bit. A root one supplies a satisfying witness, while root zero decides impossibility. No certificate query remains after compilation.

Assign contiguous addresses to layer blocks, listing assignments in a fixed frontier-variable order. Their assignments need not be stored in every output record: the address offset decodes the enumerated bit string from the retained layer metadata. An address needs $O(\log(M+2))$ bits. Retain the original input rather than a second list of all frontier sets; each frontier and its fixed variable order can be regenerated by scanning the encoded scopes and order. Two addresses and constant flags per record, together with that original input, give (6). The description may retain the original input so that addresses can be interpreted and witnesses returned in the original coordinates.

Boundary computation, scope scans, constraint evaluation and restriction (4) all have polynomial cost in $n$. Enumerating a row takes at most polynomial work plus its table navigation. Sequential-tape access can be implemented by scans of the explicit table rather than a unit-cost random-access assumption. Even squaring or applying another fixed polynomial to $M$ multiplies the exponent of $2^w$ only by a fixed constant, so total work remains (7). Backward filling, outputting the literal addresses, scanning for successors and witness generation are all covered. With no variables, evaluate constant constraints directly; with no constraints, every normal state accepts. Empty scopes, unused variables, repeated scopes and unsatisfiable constraints all fit the same construction. Substituting logarithmic $w$ into (7) gives polynomial time.

An order not supplied as input requires a uniform algorithm producing a suitable order, with its computation charged. The theorem does not solve that order-finding task. $\square$

## 2. Complete overlaps and the repository gluing theorem

**Proposition 3 (Path bags and valid gluing premises).** For $1\le i\le m$ put

$$
J_i=B_{i-1}\cup\{v_i\}.
$$

Then every nonempty constraint lies in the bag where its last variable enters, each variable's bag-occurrence set is an interval, and

$$
J_i\cap J_{i+1}=B_i.
\tag{11}
$$

These scope identities alone do not ensure consistency of arbitrary local rows. If the global satisfying relation $Q$ is nonempty and $\Gamma_i=\operatorname{pr}_{J_i}Q$, then the $\Gamma_i$ are nonempty and have equal complete projections on every adjacent overlap. They satisfy the premises of the existing finite-tree extension theorem `local_row_extends_raw_join` in [RunningIntersectionRecords][GLUING].

Proof. A constraint's old variables all lie in $B_{i-1}$ when its last variable $v_i$ enters, by Proposition 1. A variable $v_j$ first occurs at $J_j$ and stays through the last bag index of any constraint containing it; (2) gives consecutive occurrence and no later return. Equation (3) gives $B_i\subseteq J_i$, while $J_{i+1}=B_i\cup\{v_{i+1}\}$ and $v_{i+1}\notin J_i$, proving (11).

For the pruned relations $\Gamma_i$, both adjacent projections to $B_i$ equal $\operatorname{pr}_{B_i}Q$. This is equality of sets of full assignments on the whole overlap, not merely equality of separate coordinate projections. All are nonempty because $Q$ is. These are precisely the complete edge-projection consistency and running-intersection conditions of the cited Lean declaration, together with finite tree and nonempty rows. This exposition does not report a new Lean application or compilation.

For completeness, the general finite-tree extension argument is as follows. Choose a row at a root. Grow a connected processed subtree by one adjacent child. Any variable in that child and an earlier bag must occur throughout the connecting path by running intersection, so in particular in the parent–child overlap. Complete projection equality gives a child row agreeing simultaneously on that whole overlap with the selected parent row. It is consistent with every previously assigned variable. Repeating over the finite tree glues a global row extending the chosen root row. Merely checking individual overlap marginals would not provide a child row meeting all requirements together.

The pruning can also be realized by the compiler, rather than assumed available for an algorithm. Let $F_i(z)$ be the forward reachability bit from the actual initialization. Then

$$
F_i(z)\land H_i(z)=1
\quad\Longleftrightarrow\quad
\exists\text{ satisfying full assignment passing through }z.
\tag{12}
$$

The forward half supplies a prefix reaching $z$, the backward half an accepting suffix; Proposition 1's residual sufficiency permits concatenation. Conversely every satisfying path supplies both bits. A bag assignment at step $i$ extends globally precisely when its parent record has $F_{i-1}=1$, its bit transition is normal and its successor has $H_i=1$. Enumerating these transitions computes exactly $\operatorname{pr}_{J_i}Q$. If the root bit is zero, $Q$ is empty and the nonempty-row gluing theorem is not invoked. Thus complete projection consistency is established after appropriate global pruning, not inferred from bag geometry alone. $\square$

## 3. Order sensitivity and program cost

**Proposition 4 (Existing equality-order example, with selector distinction).** Let

$$
E_k(a,b)=\bigwedge_{j=1}^k(a_j\leftrightarrow b_j).
\tag{13}
$$

The grouped order $a_1,\ldots,a_k,b_1,\ldots,b_k$ has $2^k$ different exact residuals at its middle cut. The alternating order $a_1,b_1,\ldots,a_k,b_k$ has frontier width one and $O(k)$ layered records. Both scale statements reuse MINIMAL Theorem 22 and classical ordered-graph ideas; a polynomial-time next-bit completion selector exists even for the grouped order.

Proof. After reading all $a$, the accepting suffix language is the singleton $\{a\}$; distinct $a$ give different residuals. The exact middle quotient therefore has $2^k$ states. In alternating order, only a just-seen $a_j$ must be retained until $b_j$ arrives. The frontier alternates sizes one and zero, and Proposition 2 gives linearly many records. To preserve the full derivation, the two claims have been verified directly rather than counted as new results.

In grouped order a selector first checks whether any already assigned equality pair mismatches. If so every extension rejects and an arbitrary next bit preserves completion zero. Otherwise while assigning $a$ it may choose zero, since each unassigned partner remains freely selectable; while assigning $b_j$ it copies the retained corresponding $a_j$. This preserves completion one whenever possible and uses only polynomial input scans. Thus number of distinct explicit residuals, bits describing the currently selected residual, and selector-program runtime differ: they are respectively $2^k$, $k$ and polynomial here. An exponential explicit table lower bound is not a lower bound for every succinct program computing its entries. $\square$

## 4. Faithful auxiliary extensions

**Definition 2 (Uniform faithful extension).** For a family $R_x(y)$ with polynomially bounded witness length, an auxiliary extension adds variables $z$ and a Boolean constraint system $F_x(y,z)$ satisfying

$$
R_x(y)=1\quad\Longleftrightarrow\quad\exists z,\ F_x(y,z)=1
\tag{14}
$$

for every $x,y$. Uniformity means one fixed finite algorithm constructs the entire encoded system and the stated variable order from $x$; polynomial size and construction time refer to $|x|$, including all new variables, scopes and circuits. Faithfulness concerns projection to the original witness, not merely equisatisfiability without a witness map.

**Proposition 5 (A sufficient route to polynomial compilation).** Suppose such a uniform polynomial-time construction gives polynomial output length and an order of width $O(\log(|x|+2))$. Then $\exists y\,R_x(y)$ is decidable in polynomial time, and a witness $y$ is output in polynomial time when one exists.

Proof. From (14), $\exists y\,R_x(y)$ is equivalent to $\exists y,z\,F_x(y,z)$. Apply Proposition 2 to the constructed input. Its length is polynomial in $|x|$, and its width is logarithmic in $|x|$, so (7) is polynomial in $|x|$. A satisfying full assignment yields $y$ by projection, and faithfulness gives the original relation; root rejection rules out every original witness. Both compilation and projection are charged.

Auxiliary variables can enlarge total variable count while reorganizing unfinished dependencies across a cut. This is a sufficient condition only; Proposition 4 gives simple selectors without a small grouped-order explicit table. Applying this route to all NP verification tasks would establish the closure condition in [bounded certificate completion][COOK], but the existence of the required uniform constructions has not been proved by defining auxiliary variables or a completed semantic table. Hidden-world target recovery and computation on a fully supplied formula have different inputs: in the latter the formula already determines truth semantically, while the resource claim concerns uniformly computing it from its finite encoding. $\square$

[BRYANT]: bryant1986boolean.md
[MINIMAL]: ../../docs/develop/theory/OBSERVATION_BOUNDARY_ALGEBRA_MINIMAL_REALIZATION.md
[GLUING]: ../../D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.lean
[COOK]: cook2006pversusnp.md

## 追加锚（本行以下为增补区）

# Critical eight-input lower bound under the original two caps

This companion fixes the original finite Boolean control model and its supplied native interface. Its new conclusion is the unrestricted critical-instance bound

$$
 n=8,\quad k=4\quad\Longrightarrow\quad m\ge 18,
$$

for every complete correct graph satisfying both original whole-run caps. The general grid bound and the exact critical minimum remain open below.

## 1. Original model and the supplied interface

The source domain is the complete unbounded fiber

$$
\mathcal U_* = \{u\in\mathcal T:R_{\{L,R\}^3}(\rho u)=R_*\},
$$

where

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad \rho(\alpha)=\beta,
\qquad \rho(\beta)=\langle\beta,\alpha\rangle,
$$

and $\rho$ acts homomorphically on pairs. The fixed row $R_*$ has equality classes

$$
\{LLL,LRL\}=a,\quad \{LLR\}=b_1,\quad \{LRR\}=b_2,
\quad \{RLL,RRL\}=c,\quad \{RLR\}=b_3,\quad \{RRR\}=b_4,
$$

with distinct classes distinct. A complete predecessor row retains its ordered exterior, all occurrences, the canonical equality partition, disequalities, and strict-prefix guards.

For distinct positive positions $s_1<\cdots<s_n$, put

$$
 w_i=L^{s_i}R,\qquad a_i=LLLw_i,\qquad c_i=s_i+4,\qquad W=\sum_{i=1}^n c_i.
$$

The Boolean execution graph has a finite installed running-state set $Q$, two distinct terminals $\mathsf 0,\mathsf 1$, a fixed start, one fixed queried coordinate $i(q)\in[n]$ at every $q\in Q$, and fixed successors $\delta(q,0),\delta(q,1)$. Its only changing configuration is the current state. On an input $\theta\in\{0,1\}^n$, a visit to $q$ queries $\theta_{i(q)}$, costs one query and $c_{i(q)}$ letters, and follows the corresponding successor. Every installed state, including an unused state and a state reached only after certification, contributes to

$$
 m=|Q|.
$$

A complete correct graph terminates on every input, returns $\mathbf 1_{\{|\theta|\ge k\}}$, and obeys on every same actual run

$$
 t_P(\theta)\le n,\qquad J_P(\theta)\le W. \tag{1}
$$

Arbitrary adaptive coordinate choices, sharing, repeated queries, paid post-certificate traffic, and syntactic cycles with actual termination are allowed. No history, counter, clock, computed address, phase, or other changing register is supplied.

The supplied native correspondence is

$$
\mathsf N_{A,k,r}(H,p,\ell)
\Longleftrightarrow
\mathsf B_{c,k}(H-4-r,p-1,\ell-3). \tag{2}
$$

It installs the Boolean graph at the literals $a_i$, adds the two original profile states and the original entry latches, and applies on all of $\mathcal U_*$. Thus a Boolean lower bound is a conditional installed-control lower bound through (2). Source binding, the fixed register, acquired same-version data, authentication, permission, export, access isolation, code-only handoff, lawful complete entry, and stationary service are separate supplied assumptions. Boolean installed-state count does not assert physical acquisition, time, memory, or any other native resource law.

## 2. Live incidence and the supplied local facts

For the critical instance set

$$
 n=8,\qquad k=4,\qquad K=4,\qquad L=5,\qquad
 V=\{0,1,2,3\}\times\{0,1,2,3,4\},\qquad G=KL=20.
$$

A history is an actual finite run prefix immediately before a query. Its support $S$ is the set of queried coordinates; write $h$ for its number of exposed ones and $z$ for its number of exposed zeros. It is live exactly when $(h,z)\in V$. For $p\in V$, let $F_p$ be the set of installed states ending actual live histories of count cell $p$, and set

$$
 b_p=|F_p|,\qquad e_p=b_p-1.
$$

At depth $d$ write $V_d=\{(h,z)\in V:h+z=d\}$ and $e_d=\sum_{p\in V_d}e_p$.

We use the following supplied interfaces, with their stated scope and attribution to PCA Theorems 34.3 and 35.1, PE Lemma 4.1, and WTF Convention 6.1 and Theorem 9.1:

1. Every $F_p$ is nonempty; every live query is fresh; both axes have one support and one host, so $e_p=0$ whenever $h=0$ or $z=0$.
2. At one installed state, equal-support histories with unequal hit counts cannot coexist, properly nested live supports cannot coexist, and distinct hosted count cells satisfy, after orienting $h<g$,
   
   $$
   g-h\ge2,\qquad z-w\ge2. \tag{3}
   $$

3. A depth is common-support precisely when every cell at that depth has one support. A consecutive common-support cut interval $B=(a,b)$ has no common-support internal depth, hence $e_d\ge1$ for every $a<d<b$. Live sharing is confined to one such interior pool; cut hosts are disjoint from other count cells.
4. For a consecutive interval $B=(a,b)$, let $D_B$ count duplicate count-cell incidences in the pool and let $E_B=\sum_{a<d<b}e_d$. Let $E_{\rm cut}$ be the sum of the excesses at all common-support cuts and let $u$ be the number of installed states that are not live in any count cell. The exact same-graph identity is

   $$
   m-G=E_{\rm cut}+u+\sum_B(E_B-D_B). \tag{4}
   $$

5. The supplied short-interval compensation gives $D_B\le E_B$ for every consecutive interval of span at most four. The supplied right-cut separation gives, for a shared pair in an interval ending at $b$,

   $$
   g-h\ge\max(2,9-b),\qquad z-w\ge\max(2,9-b). \tag{5}
   $$

   In particular $D_B=0$ whenever $b\le5$.

These are interfaces about actual histories of one complete graph. They do not replace actual support by abstract count labels, do not delete certified traffic, and do not authenticate any nested supplier beyond its displayed conditional statement.

For completeness, (4) is finite incidence counting. If $Q_{\rm live}=\bigcup_{p\in V}F_p$, put

$$
D=\sum_{q\in Q_{\rm live}}\bigl(|\{p:q\in F_p\}|-1\bigr),\qquad
E=\sum_{p\in V}(b_p-1).
$$

Then $\sum_pb_p=|Q_{\rm live}|+D=G+E$ and $m=|Q_{\rm live}|+u$, so $m-G=E-D+u$. The common-support cut decomposition separates all these incidences into the cut pools and the interior pools, yielding (4).

## 3. Four critical lemmas

### Lemma 3.1 (three antichains obstruct two consecutive five-depth windows)

If $m\le17$, neither all depths $2,3,4,5,6$ nor all depths $3,4,5,6,7$ can be noncommon-support.

**Proof.** Consider

$$
\begin{aligned}
\mathcal A_0&=(\{0,1\}\times\{0,1,2,3,4\})\cup(\{2,3\}\times\{3,4\}),\\
\mathcal A_1&=(\{1,2\}\times\{0,1,2,3,4\})
 \cup(\{0\}\times\{0,1\})\cup(\{3\}\times\{3,4\}),\\
\mathcal A_2&=(\{2,3\}\times\{0,1,2,3,4\})
 \cup(\{0,1\}\times\{0,1\}).
\end{aligned} \tag{6}
$$

Each set has fourteen cells. Each is an antichain for the comparison (3). For $\mathcal A_0$, a possible comparison between its two horizontal strips has lower zero count at most $4$ and higher zero count at least $3$, so the required zero decrease is at most one. For $\mathcal A_1$, the low strip has zero count at most $1$, the middle strip has hit counts $1,2$, and the high strip has zero count at least $3$; every cross-strip comparison again has a required gap at most one. For $\mathcal A_2$, the same argument applies to its low strip against its middle strip. Within a strip the hit difference is at most one or the hit counts agree. Thus no two cells in any $\mathcal A_j$ satisfy (3).

Hosts of cells in an antichain are disjoint. Therefore

$$
\sum_{p\in\mathcal A_j}e_p\le m-14\le3\qquad(j=0,1,2). \tag{7}
$$

The axis excesses vanish. The non-axis cells and their multiplicities in the three antichains are

$$
\begin{array}{c|c|c}
d&\text{non-axis cells}&\text{multiplicity in }(\mathcal A_0,\mathcal A_1,\mathcal A_2)\\ \hline
2&(1,1)&3\\
3&(1,2),(2,1)&2,2\\
4&(1,3),(2,2),(3,1)&2,2,1\\
5&(1,4),(2,3),(3,2)&2,3,1\\
6&(2,4),(3,3)&3,3\\
7&(3,4)&3.
\end{array} \tag{8}
$$

Consequently, summing (7), the contribution of depths $2$ through $6$ is at least

$$
3e_2+2e_3+e_4+e_5+3e_6,
$$

and the contribution of depths $3$ through $7$ is at least

$$
2e_3+e_4+e_5+3e_6+3e_7. 
$$

If the first five depths are all noncommon, each relevant $e_d\ge1$, so the first expression is at least $10$, contradicting the sum of the three upper bounds in (7), which is at most $9$. If the second five depths are all noncommon, the second expression is at least $10$ and gives the same contradiction. \(\square\)

### Lemma 3.2 (a gap ending at six cannot carry a deficit)

If $B$ is consecutive, ends at $b=6$, and has span at least five, then

$$
D_B\le2<E_B.
$$

**Proof.** By (5), a shared pair has both oriented gaps at least three. Since hit counts lie in $\{0,1,2,3\}$, its lower hit count is $0$ and its higher hit count is $3$. The lower cell has the form $(0,z)$ with $z\ge3$, hence is $(0,3)$ or $(0,4)$; both are axis cells and each has exactly one host.

No installed state can host three distinct count cells: their hit counts would be three distinct elements of $\{0,1,2,3\}$, pairwise separated by at least two, which is impossible. Thus each shared state uses the unique host of one of those two axis cells, and $D_B\le2$. A span at least five has at least four internal depths, all noncommon by consecutivity, so $E_B\ge4$. \(\square\)

### Lemma 3.3 (the interval $(2,7)$ has deficit at most two)

For a consecutive gap $B=(2,7)$,

$$
D_B-E_B\le2. 
$$

**Proof.** The internal depths are $3,4,5,6$, so $E_B\ge4$. The only axis cells in this pool are $(0,3),(0,4),(3,0)$, each with one host. Hence at most three shared states have an axis endpoint.

For a shared pair with neither endpoint on an axis, (5) forces hit counts $1$ and $3$. The possible lower cells are $(1,2),(1,3),(1,4)$ and the possible higher cells are $(3,1),(3,2),(3,3)$. Requiring a zero decrease at least two leaves, among pairs with neither endpoint on an axis,

$$
((1,3),(3,1)),\quad ((1,4),(3,1)),\quad ((1,4),(3,2)). \tag{9}
$$

Let

$$
\ell=e_{(1,3)}+e_{(1,4)},\qquad
r=e_{(3,1)}+e_{(3,2)}.
$$

A shared state without an axis endpoint is counted at a lower endpoint in (9), so the number of such states is at most
$ b_{(1,3)}+b_{(1,4)}=2+\ell$ and at most $b_{(3,1)}+b_{(3,2)}=2+r$. Therefore

$$
D_B\le3+\min(2+\ell,2+r)=5+\min(\ell,r). \tag{10}
$$

The depths $3$ and $6$ are internal noncommon depths, while all other excesses are nonnegative. Hence

$$
E_B\ge \ell+r+e_3+e_6\ge \ell+r+2. \tag{11}
$$

If $\ell+r>0$, then $\max(\ell,r)\ge1$, and (10)–(11) give

$$
D_B-E_B\le3-\max(\ell,r)\le2.
$$

If $\ell=r=0$, then $D_B\le5$ and $E_B\ge4$, giving $D_B-E_B\le1$. \(\square\)

### Lemma 3.4 (the terminal interval $(3,8)$ has no deficit)

If $m\le17$ and $B=(3,8)$ is consecutive, then

$$
D_B\le E_B.
$$

**Proof.** The internal depths are $4,5,6,7$, so $E_B\ge4$, and $e_6,e_7\ge1$. By (5), every shared pair has a unique lower-hit endpoint with hit count at most one. The only such cells in this pool are $(0,4),(1,3),(1,4)$. Counting at the lower endpoint gives

$$
D_B\le b_{(0,4)}+b_{(1,3)}+b_{(1,4)}
 =3+e_{(1,3)}+e_{(1,4)}, \tag{12}
$$

because $(0,4)$ is an axis cell. The antichain $\mathcal A_0$ contains $(1,3)$, $(1,4)$, every non-axis cell at depths $6$ and $7$, and no negative excess. Equation (7) therefore gives

$$
 e_{(1,3)}+e_{(1,4)}+e_6+e_7\le3,
$$

so $e_{(1,3)}+e_{(1,4)}\le1$. Equation (12) yields $D_B\le4\le E_B$. \(\square\)

## 4. The unrestricted critical lower bound

### Theorem 4.1 (critical eight-input lower bound)

Every complete correct graph of the original model with $n=8$, $k=4$, and both caps (1) has

$$
 m\ge18. \tag{13}
$$

**Proof.** Suppose $m\le17$. Since $m<20$, (4) implies that some consecutive gap $B=(a,b)$ has $D_B>E_B$. Every gap of span at most four has $D_B\le E_B$, and every gap ending at $b\le5$ has $D_B=0$. Thus the positive-deficit gap has span at least five and ends at $b=6$, $7$, or $8$. Depth $1$ is a common-support cut, so $a\ge1$.

If $b=6$, Lemma 3.2 rules out the deficit. If $b=7$, then $a=1$ or $a=2$. For $a=1$, all depths $2,3,4,5,6$ are internal and noncommon, contradicting Lemma 3.1. For $a=2$, the gap is $(2,7)$ and Lemma 3.3 gives $E_B-D_B\ge-2$. There are no other interior depths in the complete cut list: the only remaining gaps are the span-one intervals between $0,1,2,7,8$. Hence (4) gives

$$
 m-20=E_{\rm cut}+u+E_B-D_B\ge-2,
$$

so $m\ge18$, contradicting $m\le17$.

If $b=8$, then $a=1,2,$ or $3$. For $a=1$ or $a=2$, all depths $3,4,5,6,7$ are internal and noncommon, contradicting Lemma 3.1. For $a=3$, Lemma 3.4 rules out the deficit. These cases exhaust every possible positive-deficit gap, proving (13). Every quantity in the argument belongs to the one original installed graph; no state is copied, unrolled, discarded after certification, or assigned to incompatible residual computations. \(\square\)

## 5. Credited upper and native consequence

### Proposition 5.1 (the twenty-state ordered grid)

There is a complete correct graph for $n=8,k=4$ with $m=20$ satisfying both caps and attaining $t=8$ and $J=W$ on one input.

**Proof.** Install a running state $q_{h,z}$ for each $0\le h\le3$ and $0\le z\le4$, and distinct terminals $\mathsf0,\mathsf1$. Start at $q_{0,0}$. State $q_{h,z}$ queries coordinate $h+z+1$. Its zero successor is $\mathsf0$ when $z=4$ and is $q_{h,z+1}$ otherwise. Its one successor is $\mathsf1$ when $h=3$ and is $q_{h+1,z}$ otherwise. These formulas specify every installed state and both successors.

Inductively, before visiting $q_{h,z}$ the run has queried the first $h+z$ coordinates, with exactly $h$ ones and $z$ zeros. A one edge at $h=3$ returns the correct positive answer. A zero edge at $z=4$ returns the correct negative answer, because five zeros leave at most three ones. If neither terminal condition has occurred, the next coordinate is fresh. At depth seven the only live cell is $(3,4)$, so the next reply reaches a terminal. Thus every input terminates correctly after at most eight queries, and every query is a distinct coordinate, so the letter charge is at most $W$ on the same run.

Choose an input whose first seven replies contain three ones and four zeros. Its run reaches $q_{3,4}$ and queries the eighth coordinate, attaining eight queries and the full charge $W$. There are $4\cdot5=20$ installed running states. \(\square\)

### Corollary 5.2 (native installed-control bound)

Under the supplied correspondence (2), any original native preparer for $n=8,k=4$ that is correct on all of $\mathcal U_*$ at native caps $9$ and $W+3$ has

$$
 H_P\ge22+r. \tag{14}
$$

The Boolean interval is therefore

$$
18\le m_{\rm exec}\le20,
$$

and the corresponding conditional native interval is $22+r\le H_P\le24+r$ when the credited grid lift is used.

**Proof.** The supplied projection of a native preparer has Boolean caps $8,W$ and at most $H_P-4-r$ running states. Theorem 4.1 gives $H_P-4-r\ge18$, proving (14). Proposition 5.1 gives the upper endpoint, and the supplied full-fiber lift through (2) adds the two profile states, two original-entry latches, and the $r$ mandated latches. The whole source fiber, all profiles, the prescribed pointwise code, literal complete entries, all four replies, and the separately priced eight-state predecessor-row reader remain part of that supplied lift. \(\square\)

## 6. Credit, new content, and exact remaining boundary

The local live-incidence facts, the common-support localization and identity (4), the short-interval compensation, and the right-cut separation are credited at the interfaces stated in Section 2. SI Definition 3.1 and Theorem 3.2 supply the three specialized antichains in (6), their antichain property and size fourteen, and the individual excess inequalities used in (7). The ordered grid in Proposition 5.1 is the credited full-domain upper. The new deductions in this companion are the critical membership-weight calculation and the two resulting noncommon-depth window obstructions (Lemma 3.1), the endpoint-six count (Lemma 3.2), the complete symbolic bound for the sole surviving interval $(2,7)$ (Lemma 3.3), the endpoint-eight bound under $m\le17$ (Lemma 3.4), and the exhaustive cut argument in Theorem 4.1. They establish a one-unit improvement over the supplied unrestricted lower endpoint $17$ without imposing an additional graph class or resource.

The exact critical minimum remains unresolved within

$$
18\le m_{\min}(8,4)\le20.
$$

No correct eighteen-state or nineteen-state graph is supplied, and optimality of the twenty-state grid is not proved. For general $\min(k,n-k+1)\ge4$, the unrestricted alternatives remain: prove

$$
 m\ge k(n-k+1)
$$

for every complete correct original graph at both caps, equivalently prove the supplied collective incidence inequality

$$
\sum_{B\in\mathcal L_*}(D_B-E_B)
\le E_{\rm cut}+u+\sum_{B\in\mathcal A_*}(E_B-D_B),
$$

where $\mathcal L_* =\{(a,b):b-a\ge5, b>\max(k,n-k+1)\}$ and $\mathcal A_*$ is its complement among consecutive cut intervals; or construct a complete correct strict-subgrid graph satisfying both original caps on every input. Neither alternative is settled here. Separate compensation in every remaining long pool is stronger than this collective target. The unrestricted budget minimum and fixed-specification attainment questions retain their separate meanings.

The native statement remains conditional on the supplied correspondence and service assumptions. The Boolean theorem concerns installed finite control states and does not imply native acquisition, physical memory, elapsed time, timing, or realization bounds.

## 追加锚（本行以下为增补区）

## 7. Critical sharing geometry and the axis fork

**Convention 7.1 (unchanged task and explicit reused interfaces).** Retain the complete model of Sections 1–2: one finite stationary graph, current state as its sole changing configuration, correctness and actual termination on every Boolean input, distinct original costs, and both caps $8,W$ on every same run. Adaptive coordinate choices, sharing, repeated queries, paid post-certificate traffic and syntactic cycles remain allowed. All installed states count. No order normalization, history, selector, counter, clock, phase, computed address or residual entry is added.

Use $V,F_p,b_p,e_p,e_d,E_B,D_B,E_{\rm cut},u$ from Section 2. The supplied interfaces there apply to every such competitor. In particular [SI, Theorem 2.2][SI19] gives nonempty host sets, fresh live queries, one support per fixed cell and host, unique axis hosts, and actual fixed live successors. Its successor assertion is

$$
p=(h,z),\quad p_\varepsilon=(h+\varepsilon,z+1-\varepsilon)\in V
\quad\Longrightarrow\quad
\delta(q,\varepsilon)\in F_{p_\varepsilon}.
\tag{15}
$$

For an actual occurrence with support $S$, the child in (15) has support $S\cup\{i(q)\}$. Each desired reply can be realized separately on a completion of that occurrence's exposed assignment. A reply word whose final counts lie in $V$ is actual and live throughout: each earlier count is bounded by its final live count, correctness forbids an earlier terminal, and freshness permits the next requested reply.

The equal-support, nested-support and equal-hit exclusions and count separation (3) retain exactly their stated conditional suppliers. The local diagonal argument of [SI, Theorem 4.1][SI19] has the following useful scope: a consecutive segment of cells on one diagonal, each with one support, has the same support throughout. Adjacent cells are the two live children of their common parent; (15) identifies their unique supports. No singleton premise is needed on that parent or outside the segment.

[SI, Theorems 5.2 and 9.3][SI19] supply the same-graph identity (4) and live-pool localization. [SI, Theorems 9.4 and 10.4][SI19] supply span-at-most-four compensation. [SI, Lemma 10.2][SI19] supplies right-cut separation (5), hence zero sharing for gaps ending at five or earlier. Every internal depth of a consecutive gap is noncommon and has $e_d\ge1$. Depths zero and one are common-support; eight is the formal endpoint. None of these interfaces asserts a free operation on the running graph or removes certified traffic.

**Lemma 7.2 (all possible critical sharing endpoints).** A live state hosts at most two distinct count cells, so $D_B$ is the number of states shared by two cells in its pool. Put

$$
\mathsf a=(1,3),\qquad \mathsf b=(1,4),\qquad
\mathsf c=(3,1),\qquad \mathsf d=(3,2).
\tag{16}
$$

Every sharing pair without an axis endpoint is one of

$$
\mathsf a\mathsf c,\qquad
\mathsf b\mathsf c,\qquad
\mathsf b\mathsf d.
\tag{17}
$$

The only axis cells that can participate in sharing are

$$
Z_2=(0,2),\quad Z_3=(0,3),\quad Z_4=(0,4),\quad
O_2=(2,0),\quad O_3=(3,0).
\tag{18}
$$

No depth-six or depth-seven cell can share with another count cell.

**Proof.** Distinct hosted cells have distinct hit counts with pairwise gaps at least two. Three such integers cannot lie in $\{0,1,2,3\}$: their extreme gap would be at least four. Thus a shared state contributes exactly one to $D_B$, independently of its number of histories in either cell.

For two non-axis endpoints, the oriented hit counts must be one and three. Their positive zero counts are at most four and decrease by at least two. The only ordered zero-count pairs are $(3,1),(4,1),(4,2)$, giving (17). An axis endpoint with zero hits must have at least two zeros; an axis endpoint with zero zeros must have at least two hits. This gives exactly the candidate list (18). These are necessary possibilities, with invalid pool endpoints omitted; no realizability of an abstract pair is asserted.

For completeness, a partner of $(0,z)$ has at most $z-2\le2$ zeros and at most three hits, hence depth at most five. A partner of $(h,0)$ has at most $h-2\le1$ hits and at most four zeros, also depth at most five. All endpoints in (16) and (18) themselves have depth at most five. This exhausts every pair and excludes sharing at depths six and seven. $\square$

**Lemma 7.3 (four axis-endpoint shared states force a mixed fork).** There are at most four shared states having an axis endpoint. If there are four, the unique hosts of $Z_2$ and $O_2$ coincide, and

$$
e_{(1,2)}\ge1,\qquad e_{(2,1)}\ge1,\qquad e_3\ge2.
\tag{19}
$$

**Proof.** Each of the five cells in (18) has exactly one host. A shared state with an axis endpoint uses at least one of these five axis incidences. The only partners of $Z_2$ are $O_2,O_3$, and the only partners of $O_2$ are $Z_2,Z_3,Z_4$, by (3). Both marked cells therefore require an axis partner. Five axis-endpoint shared states would use exactly one axis incidence each, contrary to this requirement for $Z_2$. Thus there are at most four.

If four occur, both $Z_2$ and $O_2$ participate. Otherwise at most four axis cells remain and each of the four states must use exactly one of them; the remaining marked cell, if present, cannot have its required axis partner, while if both are absent only three cells remain. There can be at most one state with two axis endpoints, since two such states among four would use at least six axis incidences. Both marked cells need axis partners, so they must share that same state $q$.

Let $x$ be the start coordinate, $y$ the next coordinate after first reply zero, and $v$ the next coordinate after first reply one. These queries exist and are live. The axis words $00,11$ end at $q$ with supports $\{x,y\},\{x,v\}$. Freshness gives $y,v\ne x$. Equal supports with unequal hits are forbidden, so $y\ne v$. Write $w=i(q)$; freshness for both occurrences gives $w\notin\{x,y,v\}$.

The actual word $001$ ends at the one successor of $q$ in cell $(1,2)$, with support $\{x,y,w\}$ omitting $v$. The actual live word $100$ ends in that same cell with support containing $v$. Thus it has at least two supports, and hence at least two hosts. Likewise $110$ ends at the zero successor of $q$ in cell $(2,1)$ with support $\{x,v,w\}$ omitting $y$, whereas the actual live word $011$ has support containing $y$. This forces two hosts at $(2,1)$. Every word used has final live counts and is actual by Convention 7.1. The two axis assignments need not agree, and no state is copied. This proves (19). $\square$

## 8. Complete critical window bounds

Throughout this section put

$$
\ell=e_{\mathsf a}+e_{\mathsf b},\qquad
r=e_{\mathsf c}+e_{\mathsf d}.
\tag{20}
$$

Both are nonnegative integers. For a specified pool let $A$ count shared states with an axis endpoint and $N$ those without. Lemma 7.2 gives $D_B=A+N$. Counting each non-axis shared state once at its lower endpoint and once at its upper endpoint in (17) gives

$$
N\le b_{\mathsf a}+b_{\mathsf b}=2+\ell,\qquad
N\le b_{\mathsf c}+b_{\mathsf d}=2+r.
\tag{21}
$$

These counts concern distinct states of one installed graph, not separately optimized histories or residual subgraphs.

**Lemma 8.1 (gaps starting at depth two).** If $B=(2,b)$ is consecutive and $b\in\{7,8\}$, then

$$
D_B-E_B\le8-b.
\tag{22}
$$

**Proof.** Set $E_*=e_3+e_4+e_5+e_6$. These four depths are internal and noncommon, so

$$
E_*\ge4,\qquad E_*\ge\ell+r+2.
\tag{23}
$$

The second inequality retains at least one excess at each of depths three and six. The pool's only candidate axis endpoints are $Z_3,Z_4,O_3$. Their unique hosts and (21) give

$$
A\le3,\qquad D_B\le5+\min(\ell,r).
\tag{24}
$$

Suppose $D_B-E_*\ge2$. From (23)–(24),

$$
2\le3-\max(\ell,r),
$$

so $\max(\ell,r)\le1$. If $\min(\ell,r)=0$, then $D_B\le5$ and $E_*\ge4$, contradicting a deficit of two. Consequently $\ell=r=1$, and the assumed deficit forces

$$
D_B=6,\quad E_*=4,\quad A=N=3,\quad
 e_3=e_4=e_5=e_6=1.
\tag{25}
$$

All excess at depths four and five outside the four cells (16) vanishes, because those four cells already contribute $\ell+r=2$. In particular

$$
b_{(2,2)}=b_{(2,3)}=1.
\tag{26}
$$

The three non-axis shared states use all three hosts counted at the lower endpoints in (21), and all three counted at the upper endpoints. Every host of $\mathsf a,\mathsf b,\mathsf c,\mathsf d$ is therefore in non-axis sharing. By Lemma 7.2 none can also participate in an axis-endpoint shared state. The three axis-endpoint shared states use the three axis incidences $Z_3,Z_4,O_3$ exactly once each, so no two of these axis cells share with each other.

The unique host of $Z_3$ must share with $(2,1)$. Its only possible higher partners within this pool are $(2,1),\mathsf c,O_3$: the hosts of $\mathsf c$ are exhausted by non-axis sharing, and an axis partner $O_3$ has just been excluded. Both $Z_3$ and $(2,1)$ have live zero children. Their actual fixed zero successor in (15) is therefore shared by

$$
Z_4=(0,4)\quad\hbox{and}\quad(2,2).
\tag{27}
$$

Let $X,Y,Z$ be the multiplicities of the three pairs in (17), in that order. Saturation of all endpoint hosts gives

$$
b_{\mathsf a}=X,\qquad b_{\mathsf b}=Y+Z,\qquad
b_{\mathsf c}=X+Y,\qquad b_{\mathsf d}=Z.
\tag{28}
$$

In particular $X,Z\ge1$. Equations (25)–(26), applied to depths four and five, give

$$
2X+Y=3,\qquad Y+2Z=3.
\tag{29}
$$

Nonnegative integral multiplicities force $X=Y=Z=1$. Thus $\mathsf a=(1,3)$ has one host and one support. The diagonal segment

$$
Z_4=(0,4),\quad\mathsf a=(1,3),\quad(2,2)
$$

consists entirely of cells with one support: $Z_4$ is an axis and (26) handles $(2,2)$. Their supports coincide by the local diagonal argument in Convention 7.1. Explicitly the parent $(0,3)$ identifies the first two supports, and the parent $(1,2)$ identifies the second and third. But (27) shares a state between the first and third cells, which have equal supports and unequal hits. This violates the supplied exclusion.

The contradiction proves $D_B\le E_*+1$. If $b=7$, then $E_B=E_*$, proving the deficit bound one. If $b=8$, then $E_B=E_*+e_7$ with $e_7\ge1$, proving compensation. No depth-seven sharing can add to $D_B$, by Lemma 7.2. All forced successor occurrences are separately realized live extensions of the original histories. $\square$

**Lemma 8.2 (gaps starting at depth one).** If $B=(1,b)$ is consecutive and $b\in\{7,8\}$, then

$$
D_B-E_B\le8-b.
\tag{30}
$$

**Proof.** Lemma 7.3 gives $A\le4$. Put $\kappa=1$ if $A=4$ and $\kappa=0$ otherwise. By (21) and the forced fork,

$$
D_B\le5+\kappa+\min(\ell,r),\qquad e_3\ge1+\kappa.
\tag{31}
$$

For $b=7$ the internal depths are two through six. Their noncommon-support condition, together with (20), gives both

$$
E_B\ge\ell+r+3+\kappa,\qquad E_B\ge5+\kappa.
\tag{32}
$$

The first retains $e_2,e_3,e_6$ outside the cells counted by $\ell+r$; the second retains at least one excess at every internal depth and the extra fork unit. If $\ell+r>0$, then

$$
D_B-E_B\le2-\max(\ell,r)\le1.
$$

If $\ell=r=0$, (31)–(32) give $D_B\le E_B$ directly.

For $b=8$ there is one more internal noncommon depth, seven. Hence

$$
E_B\ge\ell+r+4+\kappa,\qquad E_B\ge6+\kappa.
$$

If $\ell+r>0$, the deficit is at most $1-\max(\ell,r)\le0$. If both vanish, $D_B\le5+\kappa< E_B$. This exhausts both endpoints, both axis-count cases and all nonnegative excesses. The fork excess is an actual host requirement on this graph, not a separately allocated residual cost. $\square$

**Lemma 8.3 (the other long endpoints).** Every consecutive long gap ending at six is compensated, and so is the consecutive gap $(3,8)$.

**Proof.** For a gap ending at six, Lemma 3.2 already gives $D_B\le2<E_B$. Its argument uses the right-cut gap three, the two unique lower axis hosts $Z_3,Z_4$, and the four internal noncommon depths; it has no hypothesis $m\le17$ and is reused unchanged.

For $(3,8)$ the internal depths are four through seven and the only candidate axis endpoint is $Z_4$. Equations (20)–(21) give

$$
D_B\le3+\min(\ell,r),\qquad
E_B\ge\ell+r+e_6+e_7\ge\ell+r+2,\qquad E_B\ge4.
\tag{33}
$$

If $\ell+r>0$, then $D_B-E_B\le1-\max(\ell,r)\le0$. If $\ell=r=0$, then $D_B\le3<4\le E_B$. Thus the terminal gap is compensated without an assumed upper bound on $m$. $\square$

## 9. Nineteen lower bound, equality structure and remaining target

**Theorem 9.1 (unrestricted critical nineteen lower bound).** Every complete correct original graph for $n=8,k=4$ satisfying both caps $8,W$ on every actual input run has

$$
m\ge19.
\tag{34}
$$

**Proof.** Fix that one installed graph. Gaps of span at most four have $E_B-D_B\ge0$ by the reused short-gap theorem. Gaps ending at five or earlier have $D_B=0$. A potentially negative gap therefore has span at least five, lower endpoint at least one, and upper endpoint six, seven or eight; the lower-endpoint restriction follows from the common-support cut at depth one.

An endpoint-six gap is compensated by Lemma 8.3. An endpoint-seven long gap has lower endpoint one or two, and Lemmas 8.1–8.2 bound its deficit by one. An endpoint-eight long gap has lower endpoint one, two or three; Lemmas 8.1–8.3 compensate all three possibilities. These cases exhaust the integer endpoints. There is at most one consecutive gap ending at seven, since a cut has a unique preceding cut. Thus at most one pool term is negative, and that term is at least minus one.

The exact identity (4) now yields

$$
m-20=E_{\rm cut}+u+\sum_B(E_B-D_B)\ge-1.
$$

This proves (34). Unused states, certified-only states and all paid visits remain counted. Live sharing across depths, multiple histories at one cell and state, arbitrary adaptive orders and syntactic cycles are covered by the same actual-incidence interfaces; no arbitrary graph path is assumed realizable. $\square$

**Corollary 9.2 (necessary structure of a nineteen-state competitor).** If such a graph has $m=19$, its complete common-support cut list, including the formal endpoint, is exactly one of

$$
(0,1,7,8),\qquad(0,1,2,7,8).
\tag{35}
$$

Its sole long gap is respectively $(1,7)$ or $(2,7)$, and that gap has

$$
D_B-E_B=1,\qquad E_{\rm cut}=0,\qquad u=0.
\tag{36}
$$

In particular $b_{(3,4)}=1$; in the second case also $b_{(1,1)}=1$.

**Proof.** Equality $m-20=-1$ requires a negative pool contribution. Theorem 9.1's complete case analysis permits only $(1,7)$ or $(2,7)$, each with deficit at most one. All other pool contributions and $E_{\rm cut},u$ are nonnegative, so equality forces exactly (36) and zero contribution from every other gap. Consecutivity excludes every intervening cut. Together with depth one being common, the remaining integer depths outside the gap give precisely (35). Depth seven has only the cell $(3,4)$, whose zero cut excess makes its host unique. At depth two the only non-axis cell is $(1,1)$; in the second case it is a cut and has zero excess as well. The condition $u=0$ permits certified/live reuse, while requiring every installed state to be live somewhere. These are necessary conditions, with no nineteen-state table or attainment asserted. $\square$

**Corollary 9.3 (critical interval and conditional native consumer).** At both original Boolean caps,

$$
19\le m_{\min}(8,4)\le20.
\tag{37}
$$

Under exactly the supplied correspondence (2), equivalently (SI.5), and its source and service assumptions, the original preparation minimum at the fixed native caps $9,W+3$ satisfies

$$
23+r\le H_{\min}^{\,9,W+3}\le24+r.
\tag{38}
$$

The original eight-state complete predecessor-row reader remains separately priced.

**Proof.** Theorem 9.1 gives the lower endpoint in (37). The unchanged twenty-state grid of Proposition 5.1 gives the upper, with every-input correctness, actual termination and simultaneous charges at most $8,W$; one input attains both. Its complete fixed table and proof are reused directly.

For a native competitor, the supplied projection is a complete correct Boolean graph with both caps and at most $H_P-4-r$ running states. Thus Theorem 9.1 gives $H_P\ge23+r$. The unchanged full-fiber grid lift in Corollary 5.2 supplies the upper $24+r$, replacing the Boolean terminals by the two original entry latches, adding the two profile states and retaining all $r$ further mandated latches. Boolean terminals are not charged a second time. The selected route adds one call and three letters; the other profiles use at most two calls and six letters, within the same native caps.

The quantifier remains the entire unbounded original $\mathcal U_*$ of Section 1, with the original homomorphic $\rho$, current row, occurrences, repetitions, disequalities and guards. The pointwise code is precisely (SI.2): zero on $\Pi_1\cup\Pi_2$, one on $\Pi_3\cup\Pi_4$, the selected threshold on $Z_{b_3}$, and zero on the other zero profiles. Preparation produces the original $\widehat e_\sigma$ and hands off literally to the original complete $e_\sigma$ on the same source. Every original address and all four replies remain fixed; alpha, beta and absent use their separately installed Boolean-zero edges, and branch uses the Boolean-one edge. The upper covers arbitrary allowed noncomb images and absent selected nodes; the cube supplies lower witnesses and joint attainment, rather than replacing the source domain.

The independent reader retains its three running states and five whole-row halts, at most two fresh queries and six fresh letters. Its output remains the entire predecessor row: ordered exterior, occurrences, canonical equality partition, repetitions, disequalities and strict-prefix guards. All unused installed states and actual constant, repeated and post-certificate queries keep their charges. Source binding, the fixed register, acquired same-version row, authentication, permission, export, access isolation, code-only handoff, lawful complete entry and stationary continuity remain the original supplied service assumptions. Equation (38) is a conditional installed-control consequence, not an independently established original-Q bridge or physical acquisition, time, memory or realization theorem. $\square$

**Attribution and remaining boundary 9.4.** [This critical companion, Theorem 4.1][CE19] owns the earlier eighteen lower bound. Its Lemma 3.2 and Proposition 5.1 own the reused endpoint-six observation and explicit twenty-state upper. [SI, Theorems 2.2, 4.1, 5.2, 9.3–9.4 and 10.4, and Lemma 10.2][SI19] own the actual live-incidence, local diagonal, localization, short-gap and right-cut interfaces. Their nested PCA, PE and WTF suppliers remain exactly at the conditional interfaces of Section 2; (SI.5) owns the native correspondence. These earlier statements and the weaker intervals in Sections 4–6 remain valid.

The additional deductions are the critical sharing classification and four-axis forced fork, the fixed-zero-successor/singleton-segment contradiction in Lemma 8.1, the complete endpoint-one and terminal estimates without an assumed upper bound on $m$, and their exhaustive same-graph consequence (34) with equality conditions (35)–(36). They are ordinary symbolic deductions at the supplied interfaces. No kernel verification, external unrestricted lower-bound supplier, exhaustive search or worldwide priority is asserted. The count relaxation, both-conflict capacity, star and cyclic sufficient classes and above-grid inclusions of SI retain their separate scope and are not premises imposing a new class here.

The exact critical minimum is still either nineteen or twenty. No complete correct nineteen-state construction satisfying all original obligations is supplied, and no unrestricted twenty-state lower bound is proved. A nineteen-state construction must satisfy (35)–(36), actual support and successor compatibility, all-input correctness and termination, and both same-run caps; those necessary conditions alone are not a construction.

For general $\min(k,n-k+1)\ge4$, the original alternatives remain unresolved: prove $m\ge G=k(n-k+1)$ for every complete correct original graph at both caps, equivalently the same-graph collective inequality

$$
\sum_{B\in\mathcal L_*}(D_B-E_B)
\le E_{\rm cut}+u+\sum_{B\in\mathcal A_*}(E_B-D_B),
\tag{39}
$$

where $\mathcal L_*=\{(a,b):b-a\ge5,\ b>\max(k,n-k+1)\}$ and $\mathcal A_*$ is its complement among consecutive gaps; or construct one complete correct strict-subgrid graph satisfying both caps on every input. Neither general alternative follows from (34). Separate compensation in every late pool is stronger than (39). The unrestricted-budget minimum, fixed-specification attainment and the complete original native bridge retain their separate unresolved meanings. No quantum, calibration, stochastic timing, analytic or expanded-storage contract supplies an additional numerical or operational transfer here.

[SI19]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SUPPORT_INCIDENCE_AND_COUNT_RELAXATION.md
[CE19]: RECURSIVE_RELATIONAL_OBSERVATION_CRITICAL_EIGHT_INPUT_LOWER_BOUND.md

## 追加锚（临界十九下界；本行以下为增补区）

## 10. Actual-support forks and the surviving nineteen-state architecture

**Convention 10.1 (one original graph and the equality interfaces).**
Retain the entire model and both simultaneous caps of Sections 1–2 and
Convention 7.1. In particular there is one stationary finite installed
graph, with its current state as its sole changing configuration,
correctness and actual termination on every input, and costs at most
eight queries and the original distinct-cost sum $`W`$ on each same
run. All installed states count. Adaptive orders, multiple histories,
sharing, repeated queries, paid certified traffic and syntactic cycles
with actual termination remain allowed.

Let $`\mathcal S_p`$ be the family of supports of actual live histories
at cell $`p`$, and put $`a_p=|\mathcal S_p|`$. The supplied incidence
interface gives $`1\le a_p\le b_p`$ and one support for each fixed
cell and host. In addition to $`\mathsf a,\mathsf b,\mathsf c,\mathsf d`$
from (16), write

$$
\begin{gathered}
\mathsf P=(1,2),\quad \mathsf R=(2,1),\quad
\mathsf M=(2,2),\quad \mathsf N=(2,3),\\
\mathsf U=(2,4),\quad \mathsf V_6=(3,3),\qquad
Z_j=(0,j),\quad O_j=(j,0).
\end{gathered}
\tag{40}
$$

These cell names are unrelated to native row classes, coordinate names
or coordinate costs. Retain
$`\ell=e_{\mathsf a}+e_{\mathsf b}`$ and
$`r=e_{\mathsf c}+e_{\mathsf d}`$. For a specified long pool let
$`A`$ count shared states with an axis endpoint and $`N_{\rm sh}`$
count those with neither endpoint on an axis. Lemma 7.2 gives

$$
D_B=A+N_{\rm sh},\qquad
N_{\rm sh}\le 2+\min(\ell,r).
\tag{41}
$$

Its at-most-two-cell statement is essential: a state cannot be counted
as a non-axis sharing state and also as a sharing state with an
additional axis endpoint.

For clarity, the full possible partner lists for the five participating
axis cells, before restricting to a particular pool, are

| Axis cell | All possible distinct partner cells |
| --- | --- |
| $`Z_2`$ | $`O_2,O_3`$ |
| $`Z_3`$ | $`O_2,\mathsf R,O_3,\mathsf c`$ |
| $`Z_4`$ | $`O_2,\mathsf R,\mathsf M,O_3,\mathsf c,\mathsf d`$ |
| $`O_2`$ | $`Z_2,Z_3,Z_4`$ |
| $`O_3`$ | $`Z_2,Z_3,Z_4,\mathsf P,\mathsf a,\mathsf b`$ |

Indeed, a partner of $`Z_j`$ has hits two or three and zeros at most
$`j-2`$; a partner of $`O_2`$ has zero hits and at least two zeros;
a partner of $`O_3`$ has hits zero or one and at least two zeros.
Together with the rectangle bounds these give exactly the displayed
lists. With no axis endpoint the only pairs are
$`\mathsf a\mathsf c,\mathsf b\mathsf c,\mathsf b\mathsf d`$,
as credited in Lemma 7.2.

The following table gives both count children of every candidate pair.
An entry $`\mathsf C_0`$ means that this occurrence has reached five
zeros, and $`\mathsf C_1`$ means that it has reached four ones.
Neither symbol specifies a terminal or deletes any paid continuation.
When both entries in a child column are live cells, their actual
occurrences have the same fixed successor of the shared parent state,
by (15).

| Candidate pair, in displayed order | Zero children | One children |
| --- | --- | --- |
| $`Z_2,O_2`$ | $`Z_3,\mathsf R`$ | $`\mathsf P,O_3`$ |
| $`Z_2,O_3`$ | $`Z_3,\mathsf c`$ | $`\mathsf P,\mathsf C_1`$ |
| $`Z_3,O_2`$ | $`Z_4,\mathsf R`$ | $`\mathsf a,O_3`$ |
| $`Z_3,O_3`$ | $`Z_4,\mathsf c`$ | $`\mathsf a,\mathsf C_1`$ |
| $`Z_4,O_2`$ | $`\mathsf C_0,\mathsf R`$ | $`\mathsf b,O_3`$ |
| $`Z_4,O_3`$ | $`\mathsf C_0,\mathsf c`$ | $`\mathsf b,\mathsf C_1`$ |
| $`Z_3,\mathsf R`$ | $`Z_4,\mathsf M`$ | $`\mathsf a,\mathsf c`$ |
| $`Z_3,\mathsf c`$ | $`Z_4,\mathsf d`$ | $`\mathsf a,\mathsf C_1`$ |
| $`Z_4,\mathsf R`$ | $`\mathsf C_0,\mathsf M`$ | $`\mathsf b,\mathsf c`$ |
| $`Z_4,\mathsf M`$ | $`\mathsf C_0,\mathsf N`$ | $`\mathsf b,\mathsf d`$ |
| $`Z_4,\mathsf c`$ | $`\mathsf C_0,\mathsf d`$ | $`\mathsf b,\mathsf C_1`$ |
| $`Z_4,\mathsf d`$ | $`\mathsf C_0,\mathsf V_6`$ | $`\mathsf b,\mathsf C_1`$ |
| $`O_3,\mathsf P`$ | $`\mathsf c,\mathsf a`$ | $`\mathsf C_1,\mathsf M`$ |
| $`O_3,\mathsf a`$ | $`\mathsf c,\mathsf b`$ | $`\mathsf C_1,\mathsf N`$ |
| $`O_3,\mathsf b`$ | $`\mathsf c,\mathsf C_0`$ | $`\mathsf C_1,\mathsf U`$ |
| $`\mathsf a,\mathsf c`$ | $`\mathsf b,\mathsf d`$ | $`\mathsf N,\mathsf C_1`$ |
| $`\mathsf b,\mathsf c`$ | $`\mathsf C_0,\mathsf d`$ | $`\mathsf U,\mathsf C_1`$ |
| $`\mathsf b,\mathsf d`$ | $`\mathsf C_0,\mathsf V_6`$ | $`\mathsf U,\mathsf C_1`$ |

The tables are necessary implications for actual occurrences, not
realizations of abstract pairs. Each live child used below is separately
realized by fixing the fresh queried bit of its own parent history and
completing that exposed assignment. Two different parent histories need
not have compatible assignments or one common completing input.

Theorem 9.1 and Corollary 9.2 supply the already proved lower bound
nineteen and its necessary equality alternatives (35)–(36). They are
used only at that stated scope. In particular a nineteen-state
competitor has $`D_B=E_B+1`$ in its sole long pool,
$`E_{\rm cut}=u=0`$, and one of the two displayed cut lists.

**Lemma 10.2 (the shared $`Z_3,\mathsf R`$ support fork).**
If an installed state hosts both $`Z_3=(0,3)`$ and
$`\mathsf R=(2,1)`$, then

$$
a_{\mathsf N}\ge2,\qquad b_{\mathsf N}\ge2,\qquad
e_{\mathsf N}\ge1.
\tag{42}
$$

This assertion has no nineteen-state or equality hypothesis.

**Proof.** Choose actual live histories at their shared state $`q`$,
with respective supports $`S,T`$. Each has size three. Their unequal
hit counts forbid $`S=T`$. Put $`x=i(q)`$; freshness gives
$`x\notin S\cup T`$. Define

$$
A_*=S\cup\{x\},\qquad C_*=T\cup\{x\}.
$$

These are distinct size-four sets. The actual zero successor
$`q_0=\delta(q,0)`$ hosts $`Z_4,\mathsf M`$, with respective
supports $`A_*,C_*`$. The actual one successor
$`q_1=\delta(q,1)`$ hosts $`\mathsf a,\mathsf c`$, with those same
respective supports. All four child cells lie in the live rectangle.

Let $`u=i(q_0)`$, $`v=i(q_1)`$. Applying freshness at both
occurrences of each successor gives

$$
u,v\notin A_*\cup C_*.
$$

No assumption that $`u\ne v`$ is needed. From the $`\mathsf M`$
occurrence at $`q_0`$, take its live zero child at $`\mathsf N`$;
its support is $`C_*\cup\{u\}`$. From the $`\mathsf a`$
occurrence at $`q_1`$, take its live one child at $`\mathsf N`$;
its support is $`A_*\cup\{v\}`$. Choose $`j\in A_*\setminus C_*`$,
which exists since the two distinct sets have equal size. Then $`j`$
belongs to the latter support and not the former, because $`u\notin A_*`$.
Thus two distinct supports occur at $`\mathsf N`$.
One support per fixed cell and host gives $`b_{\mathsf N}\ge
a_{\mathsf N}\ge2`$, proving (42).

All the displayed children arise at the installed successors of the
chosen actual histories. Their separate realizations do not assert
realizability of an arbitrary syntactic path or agreement of the two
old assignments. $`\square`$

**Lemma 10.3 (an $`\mathsf a\mathsf c`$ host forces both last-layer
ambiguities when the outer supports are unique).**
Suppose a state hosts both $`\mathsf a=(1,3)`$ and
$`\mathsf c=(3,1)`$, and

$$
a_{\mathsf b}=a_{\mathsf d}=1.
$$

Then

$$
a_{\mathsf N}\ge2,\qquad
a_{\mathsf U}\ge2,\qquad a_{\mathsf V_6}\ge2,\qquad e_6\ge2.
\tag{43}
$$

The hypothesis concerns unique supports; unique hosts at
$`\mathsf b,\mathsf d`$ are sufficient but are not required.

**Proof.** Let $`q`$ be the shared $`\mathsf a,\mathsf c`$ state,
and let $`B_*,D_*`$ be the unique supports at $`\mathsf b,\mathsf d`$.
The fixed zero successor $`q_0=\delta(q,0)`$ hosts both these cells.
Their supports have size five, and equal-support unequal-hit exclusion
gives $`B_*\ne D_*`$. Its fixed query $`w=i(q_0)`$ is fresh at
both occurrences, so

$$
w\notin B_*\cup D_*.
\tag{44}
$$

The $`\mathsf a`$ occurrence at $`q`$, followed by reply one,
reaches $`\mathsf N`$ with support $`B_*`$: its zero sibling at
$`\mathsf b`$ has exactly that support, and the two children of one
history expose the same set. Independently choose any actual live
history at $`\mathsf M`$, which exists by the incidence interface.
Its one child at $`\mathsf d`$ has support $`D_*`$ by uniqueness,
so its zero child at $`\mathsf N`$ has support $`D_*`$ as well.
These children are all live. Thus $`\mathsf N`$ has the two distinct
size-five supports $`B_*,D_*`$.

Suppose first that $`\mathsf U`$ had one support $`T`$.
Every $`\mathsf N`$ occurrence has a live zero child at $`\mathsf U`$;
hence $`B_*,D_*\subset T`$, with $`|T|=6`$. If
$`|B_*\cup D_*|>6`$, this containment is already impossible.
Otherwise the distinct size-five sets have union of size at least
six, so their union must equal $`T`$. But the $`\mathsf b`$
occurrence at $`q_0`$ has its actual live one child at $`\mathsf U`$,
with support $`B_*\cup\{w\}`$. It follows that $`w\in T`$,
contradicting (44) and $`T=B_*\cup D_*`$.
Therefore $`a_{\mathsf U}\ge2`$.

Now suppose that $`\mathsf V_6`$ had one support $`T'`$.
Every $`\mathsf N`$ occurrence has a live one child at $`\mathsf V_6`$,
so $`B_*,D_*\subset T'`$, with $`|T'|=6`$.
A union of size greater than six is again immediately impossible;
otherwise $`T'=B_*\cup D_*`$. The $`\mathsf d`$ occurrence
at $`q_0`$ has its actual live zero child at $`\mathsf V_6`$,
with support $`D_*\cup\{w\}`$. This forces $`w\in T'`$,
again contrary to (44). Thus $`a_{\mathsf V_6}\ge2`$.

These are the two cells of depth six. Since $`b_p\ge a_p`$,
each contributes at least one excess, giving $`e_6\ge2`$.
The proof uses both actual live successors of $`\mathsf N`$, and the
one and zero successors of the two occurrences at the same installed
$`\mathsf b,\mathsf d`$ host. No new child host is chosen in place
of a fixed successor. $`\square`$

**Theorem 10.4 (exclusion of cut list $`(0,1,7,8)`$).**
No nineteen-state competitor in the original model has complete
common-support cut list $`(0,1,7,8)`$.

**Proof.** Suppose it did. Its long pool is $`B=(1,7)`$.
Put $`E=E_B`$, $`D=D_B=E+1`$. Depths two through six are
internal and noncommon. By Lemma 7.3, $`A\le4`$.
Define $`\kappa=1`$ when $`A=4`$ and $`\kappa=0`$ when $`A\le3`$.
The credited depth-two axis fork gives $`e_3\ge1+\kappa`$.
The axis and non-axis bounds therefore give

$$
D\le5+\kappa+\min(\ell,r),\qquad
E\ge5+\kappa,\qquad
E\ge\ell+r+3+\kappa.
\tag{45}
$$

The last estimate retains the depth-two, depth-three and depth-six
excesses outside $`\ell+r`$. In full, the excess decomposition is

$$
E=\ell+r+e_2+e_3+e_6+e_{\mathsf M}+e_{\mathsf N}.
\tag{46}
$$

Indeed the non-axis cells of depth four are
$`\mathsf a,\mathsf M,\mathsf c`$, and those of depth five are
$`\mathsf b,\mathsf N,\mathsf d`$; all axis excesses vanish.

Write $`s=\min(\ell,r)`$, $`t=\max(\ell,r)`$.
If $`s=0`$, the first two bounds in (45) contradict
$`D=E+1`$. If $`s>0`$, combining the first and third bounds with
$`D=E+1`$ gives
$`s+t+4+\kappa\le5+\kappa+s`$, hence $`t\le1`$.
Thus the branch $`t\ge2`$ is also impossible, and the only remaining
nonnegative integral case is

$$
\ell=r=1,\quad E=5+\kappa,\quad D=6+\kappa,\quad
A=3+\kappa,\quad N_{\rm sh}=3.
\tag{47}
$$

Here the value of $`E`$ follows from its lower bound and
$`E+1\le5+\kappa+s`$; the values of $`A,N_{\rm sh}`$
follow because their separate upper bounds sum to $`D`$.
Equation (46) and the retained positive excesses then force

$$
e_2=e_6=1,\quad e_3=1+\kappa,\qquad
e_{\mathsf M}=e_{\mathsf N}=0.
\tag{48}
$$

In particular $`\mathsf N`$ has just one host and one support.

The three non-axis shared states consume all
$`b_{\mathsf a}+b_{\mathsf b}=3`$ lower-endpoint hosts and all
$`b_{\mathsf c}+b_{\mathsf d}=3`$ upper-endpoint hosts in (41).
Every host of those four cells already shares with another of the
four. Since no state hosts three count cells, none of these hosts can
also share with an axis cell.

We next exclude every sharing possibility for $`Z_2,O_2`$, using
the complete partner lists in Convention 10.1.

* A $`Z_2,O_2`$ host has its actual fixed zero successor shared by
  $`Z_3,\mathsf R`$. Lemma 10.2 contradicts
  $`e_{\mathsf N}=0`$.
* A $`Z_2,O_3`$ host has its actual fixed zero successor shared by
  $`Z_3,\mathsf c`$. This contradicts the exhausted
  $`\mathsf c`$ hosts.
* A $`Z_3,O_2`$ host has its actual fixed one successor shared by
  $`\mathsf a,O_3`$. This contradicts the exhausted
  $`\mathsf a`$ hosts.
* A $`Z_4,O_2`$ host has its actual fixed one successor shared by
  $`\mathsf b,O_3`$. This contradicts the exhausted
  $`\mathsf b`$ hosts.

Each paired child just used is live. These four cases exhaust the
two partners of $`Z_2`$ and the three partners of $`O_2`$, with
their common pair counted once.

Only $`Z_3,Z_4,O_3`$ can consequently be axis endpoints.
Each has one host. If $`\kappa=1`$, (47) requires four
axis-endpoint shared states from these three axis incidences, an
immediate contradiction. If $`\kappa=0`$, (47) requires exactly
three. Each must then use exactly one of those three axis
incidences, so no two of $`Z_3,Z_4,O_3`$ share with each other.
The unique $`Z_3`$ host must participate. Its full partner list is
$`O_2,\mathsf R,O_3,\mathsf c`$. The first was excluded,
the third would use a second axis incidence at one shared state,
and the fourth has no host available for axis sharing.
Its partner must therefore be $`\mathsf R`$.
Lemma 10.2 again contradicts (48).

Both axis-count branches and all zero or positive endpoint-excess
branches have been exhausted. This proves the theorem on the one
original graph. $`\square`$

**Corollary 10.5 (a multiple-host endpoint in the surviving list).**
Every nineteen-state original competitor has complete cut list

$$
(0,1,2,7,8),
\tag{49}
$$

and its sharing endpoints satisfy

$$
\ell+r\ge1.
\tag{50}
$$

Equivalently, at least one of
$`\mathsf a,\mathsf b,\mathsf c,\mathsf d`$ has at least two
actual live hosts.

**Proof.** Corollary 9.2 and Theorem 10.4 leave only (49).
For its sole long pool $`B=(2,7)`$, equality still gives
$`D=E+1`$. Suppose first that $`\ell+r=0`$.
All four nonnegative endpoint excesses then vanish; the four
cells each have one host and one support.
Only $`Z_3,Z_4,O_3`$ can be axis endpoints in this pool,
so $`A\le3`$, while (41) gives $`N_{\rm sh}\le2`$.
The four internal noncommon depths give $`E\ge4`$. Consequently
$`D\le5`$ and $`D=E+1`$ force

$$
E=4,\quad D=5,\quad A=3,\quad N_{\rm sh}=2,\qquad
e_3=e_4=e_5=e_6=1.
\tag{51}
$$

The two non-axis shared states consume all four endpoint hosts.
The only non-axis partner of $`\mathsf a`$ is $`\mathsf c`$,
and the only one of $`\mathsf d`$ is $`\mathsf b`$.
Thus these two states must be an $`\mathsf a,\mathsf c`$
host and a $`\mathsf b,\mathsf d`$ host.
The cells $`\mathsf b,\mathsf d`$ have unique supports, so
Lemma 10.3 applies to the former host and gives $`e_6\ge2`$,
contrary to (51). The zero-excess branch is impossible.
In the remaining branch $`\ell+r>0`$, integrality gives (50);
no sufficiency or further realization is inferred from that branch.
$`\square`$

**Proposition 10.6 (the exact installed-state residual and its coordinate
blocks).**
A nineteen-state competitor, if one exists, has cuts (49),
$`D_B-E_B=1`$, $`E_{\rm cut}=u=0`$ and (50).
There are seven distinct cut hosts and exactly twelve interior hosts.
The latter host thirteen count cells:

$$
\begin{aligned}
V_3&=\{Z_3,\mathsf P,\mathsf R,O_3\},&
V_4&=\{Z_4,\mathsf a,\mathsf M,\mathsf c\},\\
V_5&=\{\mathsf b,\mathsf N,\mathsf d\},&
V_6&=\{\mathsf U,\mathsf V_6\}.
\end{aligned}
\tag{52}
$$

Write $`T_1=\{x\}`$, $`T_2=\{x,y\}`$,
and $`[8]\setminus T_7=\{j\}`$ for its common supports.
Every actual live run begins with the coordinates $`x,y`$ in that
order. Exactly one installed state queries $`x`$, exactly two query
$`y`$, exactly one queries $`j`$, and the other fifteen query
coordinates in $`T_7\setminus T_2`$.

**Proof.** The cut depths before the formal endpoint are zero, one,
two and seven, containing respectively one, two, three and one
count cells. Their excesses are zero by $`E_{\rm cut}=0`$.
Each cell therefore has one host, and the seven hosts are mutually
distinct and disjoint from the interior by the supplied localization.
The cells in (52) are exactly the internal diagonals of $`(2,7)`$;
they number $`4+4+3+2=13`$. Since $`u=0`$, every installed
state is live somewhere. The remaining $`19-7=12`$ states are
exactly its interior pool. This also agrees with
$`|Q_B|=|V_B|+E_B-D_B=13-1=12`$.

The supplied common-support envelope places the fixed label of every
live host in the coordinate block between its two surrounding cuts.
The four disjoint blocks for (49) are

$$
T_1=\{x\},\quad T_2\setminus T_1=\{y\},\quad
T_7\setminus T_2,\quad [8]\setminus T_7=\{j\}.
\tag{53}
$$

At the first depth, extension to the depth-one common support forces
the query $`x`$. At depth one, extension to the depth-two common
support forces the next query $`y`$. Freshness makes these different
coordinates. The half-open depth ranges $`[0,1),[1,2),[2,7),[7,8)`$
have respectively one, two, fifteen and one live states: the third
range consists of the three depth-two cut hosts and the twelve
interior hosts. Their fixed labels belong to the respective blocks
in (53). The blocks partition the coordinates, and $`u=0`$
leaves no further installed states to query any block. This proves
all four label-multiplicity assertions.

The conclusion describes installed labels and actual live prefixes.
It does not require certified traffic to follow those prefixes or
support envelopes, nor erase its original query and weighted charges.
$`\square`$

**Attribution and remaining boundary 10.7.**
The equality-residual arguments R1–R4 supply the four deductions
proved as Lemmas 10.2–10.3, Theorem 10.4 and Corollary 10.5.
The critical companion's Theorem 9.1 and Corollary 9.2 own the
nineteen lower bound and its two equality cut lists.
Its Lemmas 7.2–7.3 own the sharing classification, unique axis
incidences and the earlier depth-two axis fork. Its endpoint estimates
and twenty-state grid remain credited; the grid is not new progress.
The support-incidence source [SI][SI19], specifically Theorem 2.2,
the local diagonal argument of Theorem 4.1, Theorems 5.2 and 9.3,
the short-gap results and Lemma 10.2, owns the incidence, support,
localization and resource interfaces used here. The nested PCA, PE
and WTF statements retain their displayed conditional scope; no
unlisted supplier is authenticated by these deductions.

The additional content is necessary actual-support propagation:
the $`Z_3,\mathsf R`$ fork forces ambiguity at $`\mathsf N`$;
a shared $`\mathsf a,\mathsf c`$ host with unique outer supports
forces ambiguity at both depth-six cells; and these implications
exclude one full equality architecture and the all-singleton-endpoint
case of the other. No condition has been imposed as a new graph
class, and no separately optimized graphs or incompatible estimates
have been combined.

The exact numerical critical interval remains

$$
19\le m_{\min}(8,4)\le20.
\tag{54}
$$

The twelve-state interior in Proposition 10.6 remains to be realized
or excluded with globally compatible actual supports, fixed coordinate
labels and successors, all-input correctness, actual termination and
both original caps. At least one endpoint must have multiple hosts.
Lemma 10.2 can be paid by ambiguity at $`\mathsf N`$, and the
unique-support hypothesis of Lemma 10.3 need not hold.
The necessary conditions are not a nineteen-state construction.
No unrestricted twenty-state lower bound is established.

For every original instance with $`\min(k,n-k+1)\ge4`$, the original
all-size alternative remains unchanged: prove
$`m\ge G=k(n-k+1)`$ on every complete correct original graph at both
caps $`n,W`$, equivalently prove the collective inequality (39),
or construct one complete correct strict-subgrid graph satisfying
both caps on every input. Neither alternative follows from this
section. Separate compensation in each late pool remains stronger
than the collective target. The unrestricted-budget minimum and
fixed-specification attainment remain separate unresolved questions.

The entire original unbounded source fiber, homomorphism, eleven
profiles, prescribed pointwise code, original latches and literal
complete entries, all four replies, and the separately priced
eight-state whole-row predecessor reader are retained. Any native
consequence continues to depend on (2), equivalently (SI.5), and the
original source and service assumptions. In particular the existing
conditional interval $`23+r\le H_{\min}^{\,9,W+3}\le24+r`$
is unchanged. No complete original native acquisition/service bridge
is established here. These are ordinary symbolic conditional proofs;
there is no Lean or kernel verification, executed search,
physical-resource, general neural-network, empirical-learning,
worldwide-priority or programme-completion claim.

## 追加锚（临界十九等号剩余结构；本行以下为增补区）

## 11. Exact critical twenty from the remaining actual-history equality cases

**Convention 11.1 (original model and conditional interface scope).**
Fix one complete graph of Sections 1–2 and Convention 7.1, with
$n=8$, $k=4$, correctness and actual termination on every Boolean
input, and both original caps $t_P(\theta)\le8$ and
$J_P(\theta)\le W$ on every same run. Its sole changing configuration
is its current state. Every installed running state counts, including
unused and certified-only states. Adaptive coordinate orders, multiple
histories, sharing across counts or depths, repeated queries, paid
certified traffic and syntactic cycles remain permitted.

The conclusions below are ordinary symbolic deductions conditional on
the displayed SI interfaces already used in Sections 2, 7 and 10.
In particular we reuse actual live freshness, one support per fixed
cell and host, equal-support unequal-hit exclusion, properly nested
live-support exclusion, actual fixed live successors, the local
singleton-support diagonal argument, and the exact same-graph pool
identity and localization. No unlisted nested supplier is independently
authenticated. No abstract count incidence is presumed realizable.

Retain the cells $\mathsf a,\mathsf b,\mathsf c,\mathsf d$ of (16)
and $\mathsf P,\mathsf R,\mathsf M,\mathsf N,\mathsf U,\mathsf V_6$
of (40), together with the axis cells $Z_j,O_j$. Section 10 supplies
the following previously proved actual-history facts:

- A shared $Z_3,\mathsf R$ host forces
  $e_{\mathsf N}\ge1$ (Lemma 10.2, the R1 fork).
- A shared $\mathsf a,\mathsf c$ host, when
  $\mathsf b,\mathsf d$ each have one support, forces
  $e_6\ge2$ (Lemma 10.3, the R2 propagation).
- A nineteen-state graph cannot have cut list $(0,1,7,8)$
  (Theorem 10.4, R3).
- Every remaining nineteen-state graph has cut list
  $(0,1,2,7,8)$ and $\ell+r\ge1$
  (Corollary 10.5, R4).

These facts retain their complete proofs above and their original
conditional suppliers. The two new lemmas below concern actual
support families; singleton hosts are sufficient for their premises
because $1\le a_p\le b_p$.

**Lemma 11.2 (L1: the inner singleton-support obstruction).**
A state cannot host both $\mathsf a=(1,3)$ and
$\mathsf c=(3,1)$ if each of $\mathsf a,\mathsf M=(2,2)$ and
$\mathsf d=(3,2)$ has one exposed support.

**Proof.**
The adjacent singleton-support cells $\mathsf a,\mathsf M$ on
depth four have the same support $S$, of size four. Indeed, take an
actual history at their common parent $\mathsf P=(1,2)$; its zero
and one children are live and have equal supports, and the singleton
hypotheses identify those supports with the two unique ones.

Suppose $q$ hosts actual $\mathsf a,\mathsf c$ histories with
supports $S,T$. The supports both have size four. Equal-support
unequal-hit exclusion gives $T\ne S$. Put $x=i(q)$. Freshness at
both occurrences gives $x\notin S\cup T$. The actual zero child of
the $\mathsf c$ occurrence is a live $\mathsf d$ occurrence with
support $T\cup\{x\}$. Independently take an actual history at
$\mathsf M$. Its live one child is also at $\mathsf d$, and its
support contains $S$.

Let $D_*$ be the unique size-five support at $\mathsf d$. These two
actual children imply
$S\subseteq D_*$ and $D_*=T\cup\{x\}$.
In particular $x\in D_*\setminus S$. Since $|S|=4$ and $|D_*|=5$,
it follows that $D_*=S\cup\{x\}$. But $x\notin T$ and $|T|=4$,
so $T=D_*\setminus\{x\}=S$, a contradiction.

The two $\mathsf d$ children may be realized on different completing
inputs. Both are live children at their installed fixed successors;
no certified successor or common completion is required. $\square$

**Lemma 11.3 (L2: a host outside two exhausted families).**
If $\mathsf a,\mathsf M,\mathsf b=(1,4)$ and
$\mathsf N=(2,3)$ each have one exposed support, there is an actual
live $\mathsf d$ host outside
$F_{\mathsf b}\cup F_{Z_4}$.

**Proof.**
The axis cell $Z_4$ has its unique support. The consecutive
singleton-support diagonal segment $Z_4,\mathsf a,\mathsf M$ has a
common size-four support $S$. This follows by taking actual histories
at the common parents $Z_3$ and $\mathsf P$ and using their two
live children. Likewise the adjacent singleton-support cells
$\mathsf b,\mathsf N$ have a common size-five support $T$; an
actual parent at $\mathsf a$ identifies them.

Take an actual history at $\mathsf M$, whose support is $S$.
Its live zero child at $\mathsf N$ has support $T$, so
$S\subsetneq T$. Its live one child at $\mathsf d$ has that same
support $T$, since the two children of this particular query expose
the same new coordinate. Let $q_*$ be this actual one successor.

If $q_*\in F_{\mathsf b}$, the singleton-support premise at
$\mathsf b$ gives a $\mathsf b$ occurrence at $q_*$ with support
$T$. Its hit count is one, whereas the displayed $\mathsf d$
occurrence has three hits. Equal-support unequal-hit exclusion
forbids this. If $q_*\in F_{Z_4}$, that occurrence has support $S$,
properly contained in $T$, contradicting nested-support exclusion.
Thus the specific actual child $q_*$ lies outside the stated union.

This supplies one installed host on the original graph. It allocates
no independent residual graph or free state. $\square$

**Theorem 11.4 (exclusion of every twelve-state interior).**
No original nineteen-state graph can realize the thirteen cells in
(52) on the twelve interior states of Proposition 10.6.

**Proof.**
Assume such a graph exists. By Theorem 9.1, Corollary 9.2 and
Theorem 10.4, its sole long pool is $B=(2,7)$, and
$D_B=E_B+1$. Work throughout on that one installed graph. Write
$E=E_B$, $D=D_B$, and define the nonnegative integer excesses
and their sums by

$$
\begin{gathered}
a_0=e_{\mathsf a},\quad b_0=e_{\mathsf b},\quad
c_0=e_{\mathsf c},\quad d_0=e_{\mathsf d},\quad
\mu=e_{\mathsf M},\quad \nu=e_{\mathsf N},\\
t=e_3,\quad f=e_6,\quad w=\mu+\nu,\qquad
\ell=a_0+b_0,\quad \varrho=c_0+d_0,\\
E=\ell+\varrho+t+f+w,\qquad D=E+1.
\end{gathered}
\tag{55}
$$

Here $\varrho$ is the endpoint-excess sum denoted by $r$ in (20);
it is unrelated to the number of native mandated latches. The four
internal depths are noncommon-support. Since axis excesses vanish,
this gives

$$
t\ge1,\quad f\ge1,\quad
a_0+c_0+\mu\ge1,\quad b_0+d_0+\nu\ge1,\quad E\ge4.
\tag{56}
$$

Corollary 10.5 also gives $\ell+\varrho\ge1$.

Let $A$ count shared states having an axis endpoint and let
$N_{\rm sh}$ count shared states without one. Lemma 7.2 shows that
a state hosts at most two distinct count cells, so

$$
D=A+N_{\rm sh}.
\tag{57}
$$

Only $Z_3,Z_4,O_3$ can be axis endpoints inside this pool, and
each has one host. Therefore $A\le3$. If $A=3$, all three axes
participate in distinct shared states, with exactly one axis
incidence at each state. In particular the $Z_3$ host cannot
share with $O_3$: that would use two of the three available axis
incidences at one state. Its only possible partners are then
$\mathsf R$ or $\mathsf c$, by the full partner table in
Convention 10.1. The excluded axis $O_2$ lies at the cut, outside
the pool, and localization excludes cross-pool sharing.

Let $X,Y,Z$ be the respective numbers of non-axis shared states
of types $\mathsf a\mathsf c,\mathsf b\mathsf c,
\mathsf b\mathsf d$. These are the complete non-axis possibilities,
so

$$
\begin{gathered}
N_{\rm sh}=X+Y+Z,\\
X\le b_{\mathsf a},\quad
Y+Z\le b_{\mathsf b},\quad
X+Y\le b_{\mathsf c},\quad Z\le b_{\mathsf d},\\
N_{\rm sh}\le2+\ell,\qquad
N_{\rm sh}\le2+\varrho.
\end{gathered}
\tag{58}
$$

Whenever either final bound is an equality, every host on that
endpoint side is used by a non-axis shared state. None of those
hosts can also share with an axis cell, since it would host three
distinct cells. This is a count of distinct installed states, not
an addition of independently optimized witnesses.

The actual-successor table in Convention 10.1 supplies the following
implications on this graph. Every $\mathsf a\mathsf c$ host has its
zero successor at a $\mathsf b\mathsf d$ host. A shared
$Z_3,\mathsf R$ host has zero successor shared by $Z_4,\mathsf M$
and one successor shared by $\mathsf a,\mathsf c$. A shared
$Z_3,\mathsf c$ host has zero successor shared by $Z_4,\mathsf d$.
All children in these implications are live. Each is realized
separately by extending its actual parent history with the specified
fresh reply. No injectivity of the successor maps is assumed.

Put $s=\min(\ell,\varrho)$ and $H=\max(\ell,\varrho)$.
Equations (55), (57) and (58) imply

$$
E+1\le A+2+s,\qquad
H+t+f+w\le A+1\le4.
\tag{59}
$$

Thus $H\le2$. The already established
$\ell+\varrho\ge1$ excludes $H=0$. There are exactly the following
two possible positive values.

*Case 1: $H=2$.*
The second inequality in (59), with $t,f\ge1$, forces

$$
A=3,\qquad t=f=1,\qquad \mu=\nu=0.
\tag{60}
$$

In particular $\mathsf M,\mathsf N$ have one host each, and
(55), (57) give
$E=\ell+\varrho+2$ and $N_{\rm sh}=\ell+\varrho$.
Lemma 10.2 excludes a shared $Z_3,\mathsf R$ host because
$\nu=0$. Since $A=3$, the $Z_3$ host must therefore share with
$\mathsf c$. Its actual zero successor shares $Z_4,\mathsf d$.

These are two distinct axis shared states: coincidence would host
more than two cells. They use one $\mathsf c$ host and one
$\mathsf d$ host, neither of which can be a non-axis shared state.
Counting all these upper-endpoint hosts on the same graph gives

$$
N_{\rm sh}+2\le b_{\mathsf c}+b_{\mathsf d}=2+\varrho.
\tag{61}
$$

Together with $N_{\rm sh}=\ell+\varrho$, this forces $\ell=0$.
Consequently $\varrho=2$ and $N_{\rm sh}=2$.

The two lower-endpoint hosts, one at each of $\mathsf a,\mathsf b$,
are both exhausted by non-axis sharing. The $\mathsf a$ host must
be of type $\mathsf a\mathsf c$, and its zero successor is of
type $\mathsf b\mathsf d$. These states are distinct by the
two-cell limit. There are only two non-axis states in all, so

$$
X=Z=1,\qquad Y=0.
\tag{62}
$$

The non-axis $\mathsf a\mathsf c$ host and the axis
$Z_3,\mathsf c$ host require two distinct $\mathsf c$ hosts.
The non-axis $\mathsf b\mathsf d$ host and the axis
$Z_4,\mathsf d$ host likewise require two distinct
$\mathsf d$ hosts. Their total available capacity is
$2+\varrho=4$, so each cell has exactly two. In particular

$$
F_{\mathsf d}\subseteq F_{\mathsf b}\cup F_{Z_4}.
\tag{63}
$$

But $\ell=0$ and $\mu=\nu=0$ make
$\mathsf a,\mathsf b,\mathsf M,\mathsf N$ singleton-host,
hence singleton-support, cells. Lemma 11.3 supplies an actual
$\mathsf d$ host outside the union in (63), a contradiction.
This excludes every $H=2$ possibility, including either orientation
of its larger endpoint excess and the possibility
$\ell=\varrho=2$.

*Case 2: $H=1$.*
Equation (59) implies $A\ge2$, so $A$ is two or three.

*Case 2a: $A=2$.*
Equation (59) forces $t=f=1$ and $w=0$.
Then $E=\ell+\varrho+2\ge4$ and
$0\le\ell,\varrho\le1$, so

$$
\ell=\varrho=1,\qquad E=4,\qquad N_{\rm sh}=3.
\tag{64}
$$

Both endpoint sides have exactly three hosts, all in non-axis
sharing by (58). Because $\mu=\nu=0$, (56) shows that the
depth-four and depth-five excesses $a_0+c_0$ and $b_0+d_0$
are each positive. Their sum is $\ell+\varrho=2$, so each is
one. Endpoint saturation now gives

$$
b_{\mathsf a}=X,\quad b_{\mathsf b}=Y+Z,\quad
b_{\mathsf c}=X+Y,\quad b_{\mathsf d}=Z,
$$

and hence

$$
2X+Y=3,\qquad Y+2Z=3,\qquad X,Z\ge1.
\tag{65}
$$

The nonnegative integer solutions of these equations must have
$X=Z=1$ and $Y=1$: the first gives $X\le1$ and the second
gives $Z\le1$, after which both determine $Y$.
Thus $\mathsf a$ and $\mathsf d$ have one host, as does
$\mathsf M$. An $\mathsf a\mathsf c$ host exists, contrary to
Lemma 11.2. No $A=2$ possibility survives.

*Case 2b: $A=3$ and $\ell+\varrho=1$.*
Here $s=0$, so $N_{\rm sh}\le2$.
From $E+1=3+N_{\rm sh}$ and $E\ge4$ it follows that

$$
E=4,\qquad N_{\rm sh}=2,\qquad t+f+w=3.
\tag{66}
$$

The sum of the depth-four and depth-five excesses is
$\ell+\varrho+w=1+w$ and is at least two by (56).
Together with $t,f\ge1$, this forces $w=1$, $t=f=1$.
Each of those two layer excesses is exactly one.

First suppose $\ell=1,\varrho=0$. The two upper hosts,
one at each of $\mathsf c,\mathsf d$, are exhausted by the
two non-axis states. The $Z_3$ host cannot partner $\mathsf c$,
so it partners $\mathsf R$. Lemma 10.2 forces $\nu\ge1$;
as $w=1$, this means $\nu=1,\mu=0$.
The depth-five excess equation
$b_0+d_0+\nu=1$, with $d_0=0$, gives $b_0=0$.
Thus $\mathsf b,\mathsf d$ have one support each.
The one successor of the $Z_3,\mathsf R$ host is an actual
$\mathsf a\mathsf c$ host, so Lemma 10.3 forces $f\ge2$,
contrary to $f=1$.

Now suppose $\ell=0,\varrho=1$. The two lower hosts,
one at each of $\mathsf a,\mathsf b$, are exhausted by
non-axis sharing. The first must be an $\mathsf a\mathsf c$
host, whose zero successor is a $\mathsf b\mathsf d$ host.
Thus $X=Z=1,Y=0$. If $\nu=0$, then $\mu=1$.
The depth-five excess equation gives $d_0=1,c_0=0$.
Lemma 10.2 forbids the $Z_3,\mathsf R$ option, while the
$Z_3,\mathsf c$ option would require an additional
$\mathsf c$ host although its sole host is already the
non-axis $\mathsf a\mathsf c$ state. Both possible partners
are impossible. Therefore $\nu=1,\mu=0$.
The depth-four excess equation now forces $c_0=1,d_0=0$.
The cells $\mathsf a,\mathsf M,\mathsf d$ have one host,
and an $\mathsf a\mathsf c$ host exists. Lemma 11.2 again
gives a contradiction. This excludes both orientations in Case 2b.

*Case 2c: $A=3$ and $\ell=\varrho=1$.*
Now $N_{\rm sh}\le3$ and
$E=N_{\rm sh}+2\ge4$. Thus $E$ is four or five.

If $E=4$, (55) forces $t=f=1,w=0$, and
$N_{\rm sh}=2$. Since $\nu=0$, Lemma 10.2 excludes
$Z_3,\mathsf R$. As $A=3$, the axis host at $Z_3$
must share with $\mathsf c$, and its zero successor shares
$Z_4,\mathsf d$. These two distinct axis states, in addition
to the two non-axis states, require four distinct upper-endpoint
hosts. But $b_{\mathsf c}+b_{\mathsf d}=2+\varrho=3$.
This contradiction excludes $E=4$.

If $E=5$, then $N_{\rm sh}=3$, exhausting all three lower
and all three upper hosts. The $Z_3$ host therefore cannot
partner $\mathsf c$ and must partner $\mathsf R$.
Lemma 10.2 gives $\nu\ge1$. Since
$t+f+w=3$ and $t,f\ge1$, we obtain

$$
t=f=1,\qquad \mu=0,\qquad \nu=1.
\tag{67}
$$

Endpoint saturation yields

$$
X=1+a_0,\quad Z=1+d_0,\quad
X+Y=1+c_0,\quad Y+Z=1+b_0.
$$

With $a_0+b_0=c_0+d_0=1$, these imply

$$
a_0+d_0+Y=1.
\tag{68}
$$

All three summands are nonnegative integers. If $Y=1$, then
$a_0=d_0=0$ and $b_0=c_0=1$.
An $\mathsf a\mathsf c$ host exists, while
$\mathsf a,\mathsf M,\mathsf d$ have one host;
Lemma 11.2 excludes it.
If $a_0=1$, then $Y=d_0=b_0=0$ and $c_0=1$.
The cells $\mathsf b,\mathsf d$ have one support and
$X=2$ ensures an $\mathsf a\mathsf c$ host.
Lemma 10.3 gives $f\ge2$, contradicting (67).
If $d_0=1$, then $Y=a_0=c_0=0$ and $b_0=1$.
Equation (67) gives $\mu=0$, so
$a_0+c_0+\mu=0$, contrary to the noncommon depth-four
requirement in (56). These are all possibilities in (68).
Thus $E=5$ is impossible as well.

The nonnegative integer partition is exhaustive: $H=0$ was excluded
by R4, $H\ge3$ by (59), $H=2$ by Case 1, and $H=1$ by
Cases 2a–2c, which cover every allowed $A,\ell,\varrho,E$.
Every contradiction concerns actual histories or distinct installed
hosts of the alleged original graph. Consequently the thirteen-cell
interior cannot have twelve states. $\square$

**Corollary 11.5 (the unrestricted critical exact minimum at both caps).**
Conditional on the displayed SI interfaces, for every choice of the
original distinct positive positions $s_1<\cdots<s_8$,

$$
m_{\min}(8,4;\ t\le8,\ J\le W)=20.
\tag{69}
$$

Here $m$ counts running states; including the two distinct Boolean
terminals the corresponding installed total is twenty-two.

**Proof, lower bound.**
Theorem 9.1 gives $m\ge19$ in the full original graph class.
If $m=19$, Theorem 10.4 excludes the first equality cut list,
and Proposition 10.6 identifies the remaining cut list with precisely
the twelve-state interior excluded by Theorem 11.4.
Thus $m=19$ is impossible. Since $m$ is an integer, every competitor
has $m\ge20$.

**Proof, credited complete attaining graph.**
Reuse exactly the twenty-state ordered grid of Proposition 5.1.
For completeness its entire fixed graph is given by

$$
\begin{gathered}
Q=\{q_{h,z}:0\le h\le3,\ 0\le z\le4\},\qquad
q_{\rm start}=q_{0,0},\qquad i(q_{h,z})=h+z+1,\\
\delta(q_{h,z},0)=
\begin{cases}
\mathsf0,&z=4,\\
q_{h,z+1},&z<4,
\end{cases}
\qquad
\delta(q_{h,z},1)=
\begin{cases}
\mathsf1,&h=3,\\
q_{h+1,z},&h<3.
\end{cases}
\end{gathered}
\tag{70}
$$

There are no other running states, and $\mathsf0,\mathsf1$ are
distinct terminals. Immediately before $q_{h,z}$, induction gives
that exactly the first $h+z$ coordinates have been queried, with
$h$ ones and $z$ zeros. A one edge at $h=3$ certifies four
ones; a zero edge at $z=4$ certifies five zeros, leaving at most
three ones. Thus both terminal outputs are correct.
Every other edge preserves the invariant and increases the exposed
depth by one. The sole live cell at depth seven is $(3,4)$,
whose next query terminates. Hence every input terminates correctly
within eight queries. Each query is at a distinct coordinate,
so that same run pays at most the original $W$ letters.

The actual input $11100000$ reaches $q_{3,4}$ after its first
seven replies, queries coordinate eight, and returns zero.
It pays exactly eight queries and $W$ letters together.
All twenty installed running states count. This is the credited
upper, not a new construction. It attains the new lower bound
without restricting any competing graph to an ordered or read-once
subclass. $\square$

**Corollary 11.6 (conditional exact native installed-control consumer).**
Under precisely (2), equivalently (SI.5), and its original source and
service assumptions, at the fixed native caps nine queries and
$W+3$ letters the critical preparation minimum is

$$
H_{\min}^{\,9,W+3}=24+r.
\tag{71}
$$

The original eight-state whole-row reader remains separately priced.
This statement is a consumer of the supplied correspondence, not an
independently authenticated original-source or service bridge.

**Proof, lower bound.**
The supplied projection of any complete original native preparer is
a complete correct Boolean graph at both caps $8,W$, with at most
$H_P-4-r$ running states. Corollary 11.5 gives
$H_P-4-r\ge20$, so $H_P\ge24+r$.
This is the only Boolean-to-native lower transfer used.

**Proof, credited full-fiber attaining lift.**
Apply the supplied constructive direction of (SI.5) to exactly
(70). Each coordinate-$i$ row queries the fixed original literal
$a_i=LLL L^{s_i}R$, costing $c_i=s_i+4$ letters. Its four
separately installed successors in the order alpha, beta, branch,
absent are

$$
(\delta_0,\delta_0,\delta_1,\delta_0),
\tag{72}
$$

with the two Boolean terminals replaced by the two original-entry
latches $\widehat e_0,\widehat e_1$. Add the unchanged original
profile front:

| Profile state | Fixed literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D_0$ | $RLR$ | $\widehat e_1$ | $q_{0,0}$ | $T_0$ | $\widehat e_0$ |
| $T_0$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |

Start at $D_0$ and install all $r$ further mandated distinct
latches, including unused ones. There are twenty selected running
states, two profile states and $2+r$ latches, hence $24+r$
preparation states. Boolean terminals are replaced, not charged a
second time.

The full-fiber meaning is that of the supplied lift. The domain
remains every finite nonempty ordered alpha/beta tree in

$$
\mathcal U_*=\{u:R_{\{L,R\}^3}(\rho u)=R_*\},
$$

of unbounded size, depth and interior shape. The original
homomorphism satisfies $\rho(\alpha)=\beta$,
$\rho(\beta)=\langle\beta,\alpha\rangle$ and acts homomorphically
on pairs. The current row retains exactly the equality classes
$\{LLL,LRL\}=a$, $\{LLR\}=b_1$, $\{LRR\}=b_2$,
$\{RLL,RRL\}=c$, $\{RLR\}=b_3$, $\{RRR\}=b_4$,
with different classes disequal.

All eleven original profiles and the literal pointwise code (SI.2)
remain fixed: zero on $\Pi_1\cup\Pi_2$, one on
$\Pi_3\cup\Pi_4$, selected threshold four on $Z_{b_3}$,
and zero on the other zero profiles. Preparation produces the
original $\widehat e_\sigma$, and code-only handoff enters
literally the original complete $e_\sigma$ on that same source.
All original finite addresses and all four replies keep their
meaning and permission.

For every $Z_{b_3}$ source, its allowed arbitrary branch image
determines one fixed Boolean indicator vector. By the supplied
all-address occurrence identity, the entire selected run is (70)
on that vector, including alpha, beta and absent using their
separate zero edges. It is correct and costs at most eight queries
and $W$ letters. The profile front adds one paid call and three
letters on this route. The other ten profiles terminate through
the two displayed profile rows within two calls and six letters,
also within the fixed native caps. This reuses the supplier on
every allowed noncomb image and absent selected node; it is not a
cube-only upper. The supplied cube realizes $11100000$ by an
actual original source, so the two native maxima are attained
together on one source.

The independent original reader retains three running states and
five whole-row halts, hence eight separately priced states, with
at most two fresh calls and six fresh letters. It returns the
entire predecessor row: ordered exterior, every reached occurrence,
canonical equality partition, repetitions, disequalities and
strict-prefix guards. It is not included in the preparation count.

Source binding, the fixed register, acquired same-version row,
authentication, permission, same-source export, access isolation,
code-only handoff, lawful complete entry and stationary continuity
remain the separate supplied and priced services. All installed
running, output, latch and unused states, and every actual constant,
repeated and post-certificate invocation, retain their original
charges. The lift adds no free source copy, record, selector,
history, counter, clock, phase, computed address or work register.
These are conditional installed-control statements; no acquisition,
physical time, memory, permission or realization theorem is inferred.
$\square$

**Attribution and current boundary 11.7.**
The new numerical conclusion (69) explicitly replaces the unresolved
critical interval (54) and the twelve-state residual question in
Section 10.7. Those preceding necessary statements and lower bounds
remain valid, but the critical minimum at the two fixed original
caps is now exactly twenty, and its supplied conditional native
consumer is exactly $24+r$. The former native interval
$23+r\le H_{\min}^{\,9,W+3}\le24+r$ is correspondingly resolved
only through (SI.5) and its original assumptions.

The actual-history obstructions L1 and L2 and the symbolic equality
partition used in Theorem 11.4 are the additional deductions supplied
by the critical-twenty mathematics projection. R1–R4 are the earlier
Section 10 results, retained with their complete proofs and credits.
Theorems 4.1 and 9.1 own the earlier eighteen and nineteen lower
bounds; Lemmas 7.2–7.3 and Section 8 own the sharing classification,
axis fork and endpoint estimates; Corollary 9.2 owns the two equality
cut lists. Proposition 5.1 and the credited full-domain grid own
the unchanged attaining upper.

The support-incidence source [SI][SI19] owns the original graph model,
the actual-history and support interfaces, local singleton diagonal
argument, same-graph incidence and pool identities, localization,
short-gap compensation and right-cut separation. Its exact count
relaxation, classical all-history both-conflict capacity, star and
cyclic sufficient classes and complete above-grid inclusion families
remain credited at their separate scopes. None is imposed as a
necessary subclass or rebranded as this critical equality exclusion.
The nested PCA, PE and WTF results retain their stated conditional
interfaces. In particular (SI.5) owns the native correspondence;
this section supplies no independent authentication of its complete
original-source or operational service bridge.

The proof partitions the simultaneous integer constraints of one
alleged installed graph. Endpoint saturation consumes actual hosts
only once; the two-cell limit separates axis and non-axis uses.
Every successor implication is an actual live extension at its fixed
installed successor. The singleton arguments use full support
families, and do not replace multiple histories by representatives.
A certified visit to a state live elsewhere does not make that state
new or free. No normalization to an ordered, read-once, acyclic,
both-conflict, star or cyclic graph has been used.

For the original all-size range $\min(k,n-k+1)\ge4$, the unrestricted
alternatives remain unresolved: prove $m\ge G=k(n-k+1)$ for every
complete correct original graph at both same-run caps $n,W$, or
construct one complete correct strict-subgrid graph satisfying both
caps on every input. Equivalently, the general collective obligation
remains

$$
\sum_{B\in\mathcal L_*}(D_B-E_B)
\le E_{\rm cut}+u+\sum_{B\in\mathcal A_*}(E_B-D_B),
\tag{73}
$$

where $\mathcal L_*$ consists of consecutive common-support gaps
of span at least five whose endpoint is greater than
$\max(k,n-k+1)$, and $\mathcal A_*$ is its complement among
consecutive gaps. Separate compensation in every long pool is stronger
than this collective target. The critical case has been settled;
no all-size collective theorem, general strict-subgrid construction,
unrestricted representative injection or normalization follows.
The unrestricted-budget minimum and fixed-specification attainment
questions remain separate.

No external unrestricted lower-bound theorem or new literature
authentication is used. The source comparisons keep their hypotheses:
Bryant's ordered graphs require increasing variable indices;
Wegener's BP1 normalization uses realizability of every graph path;
acyclic semantic read-once suppliers have their own repetition
conditions; weak one-way conflicts differ from every ordered
off-diagonal intersection in the classical Bollobás supplier.
None provides a normalization of this arbitrary paid graph.
These are ordinary symbolic conditional proofs, with no Lean or
kernel verification, executed mathematics or exhaustive search,
empirical learning, general neural-network, physical-resource,
worldwide-priority or programme-completion claim. Installed control,
table and address representation, retained export alphabet,
workspace, acquisition, elapsed time and physical memory remain
distinct quantities. No quantum, calibration, stochastic timing,
analytic, conditional joint-interior/saturation or expanded-storage
contract supplies an additional numerical or operational transfer.

## 追加锚（临界二十精确结论；本行以下为增补区）

## 12. Twenty live hosts with arbitrary never-live installation

**Convention 12.1 (live count and unchanged conditional premises).**
Retain exactly Convention 11.1 and its displayed SI interfaces, on
one complete original eight-coordinate threshold-four graph. In
particular both caps are $8,W$ on every same complete input run,
all original distinct positive positions are allowed, and every
installed running state counts. Put

$$
Q_{\rm live}(4)=\bigcup_{p\in V}F_p,\qquad
v=|Q_{\rm live}(4)|,\qquad u=m-v.
\tag{74}
$$

Thus $u$ counts states with no live occurrence from the declared
start; a state live on one input and used after certification on
another belongs to $Q_{\rm live}(4)$, not to $u$. No condition
$u=0$ is imposed.

The distinction between local and installed conclusions is essential.
Lemma 7.2's two-cell limit and pair classification, Lemma 7.3's
axis fork, and Lemmas 8.1–8.3's pool estimates concern only live
incidences. Their proofs have no bound on $m$ or $u$. Lemma 3.2,
as used in Lemma 8.3, likewise has no such bound. Lemmas 10.2
and 10.3 propagate actual fixed live children and compare their
supports; Lemmas 11.2 and 11.3 use singleton support families and
actual fixed live children. None of these four support lemmas uses
a nineteen-state total or $u=0$. In each, one host implies one
support by $1\le a_p\le b_p$. The partner and live-child tables
of Convention 10.1 are the necessary consequences of the same
interfaces, independently of its later equality discussion.

By contrast, the installed-label multiplicities in Proposition 10.6
use $u=0$. They are not premises here. Nor do we substitute $v$
for $m$ in Corollary 11.5: deleting never-live states could change
actual paid certified continuations. The proof below keeps every
state and every successor of the original graph.

**Theorem 12.2 (conditional critical live bound).**
For every graph and every original position vector in Convention
12.1,

$$
|Q_{\rm live}(4)|\ge20,\qquad m\ge20+u.
\tag{75}
$$

**Proof: live incidence and the complete equality alternatives.**
Subtract $u$ from the exact same-graph identity (4), obtaining

$$
v-20=E_{\rm cut}+\sum_B(E_B-D_B).
\tag{76}
$$

The endpoint exhaustion in Theorem 9.1 uses only the pool estimates
identified in Convention 12.1: short gaps compensate; gaps ending
at five or earlier have no sharing; those ending at six compensate;
the only possible deficit is at most one in a gap $(1,7)$ or
$(2,7)$; and every long gap ending at eight compensates. There
is at most one gap ending at seven. Equation (76) therefore gives
$v\ge19$ without any assertion about $u$.

Suppose $v=19$. Equality in that same exhaustion forces
$E_{\rm cut}=0$, one deficit-one pool, and zero contribution from
every other pool. Consecutivity, the cuts zero and one and the
formal endpoint eight give exactly the lists

$$
(0,1,7,8)\quad\hbox{or}\quad(0,1,2,7,8).
\tag{77}
$$

For its long pool write $E=E_B$, $D=D_B=E+1$. Let $A$ count
axis-endpoint shared states and $N_{\rm sh}$ count non-axis shared
states. The two-cell limit gives $D=A+N_{\rm sh}$. Set
$\ell=e_{\mathsf a}+e_{\mathsf b}$ and
$\varrho=e_{\mathsf c}+e_{\mathsf d}$; the latter is unrelated to
the number of Native latches. The non-axis pairs are exactly
$\mathsf a\mathsf c,\mathsf b\mathsf c,\mathsf b\mathsf d$, so

$$
N_{\rm sh}\le2+\min(\ell,\varrho).
\tag{78}
$$

Equality on either endpoint side exhausts all its hosts in non-axis
sharing. No exhausted host can also host an axis cell, by the
two-cell limit. We now exclude both lists directly at live scope.

**Proof: the list $(0,1,7,8)$.**
For $B=(1,7)$ put $\kappa=1$ if $A=4$, and $\kappa=0$
otherwise. Lemma 7.3 gives $A\le3+\kappa$ and
$e_3\ge1+\kappa$. Internal depths two through six are noncommon,
and the live excess decomposition is

$$
\begin{gathered}
E=\ell+\varrho+e_2+e_3+e_6+e_{\mathsf M}+e_{\mathsf N},\\
D\le5+\kappa+\min(\ell,\varrho),\qquad
E\ge5+\kappa,\qquad E\ge\ell+\varrho+3+\kappa.
\tag{79}
\end{gathered}
$$

If $\min(\ell,\varrho)=0$, the first two bounds contradict
$D=E+1$. Otherwise the first and third imply
$\max(\ell,\varrho)\le1$. Thus necessarily

$$
\begin{gathered}
\ell=\varrho=1,\quad E=5+\kappa,\quad
A=3+\kappa,\quad N_{\rm sh}=3,\\
e_2=e_6=1,\quad e_3=1+\kappa,\quad
e_{\mathsf M}=e_{\mathsf N}=0.
\tag{80}
\end{gathered}
$$

The three non-axis states exhaust all hosts of
$\mathsf a,\mathsf b,\mathsf c,\mathsf d$. The live-child table
now excludes every use of $Z_2$ or $O_2$ in sharing. A
$Z_2,O_2$ host has a $Z_3,\mathsf R$ zero child, contradicting
Lemma 10.2 and $e_{\mathsf N}=0$. A $Z_2,O_3$ host has a
$Z_3,\mathsf c$ zero child, violating exhaustion of
$\mathsf c$. A $Z_3,O_2$ host has a $\mathsf a,O_3$ one
child, violating exhaustion of $\mathsf a$. A $Z_4,O_2$ host
has a $\mathsf b,O_3$ one child, violating exhaustion of
$\mathsf b$. These are all their partners.

Only $Z_3,Z_4,O_3$ remain as participating axes, each with one
host. Their three incidences cannot supply $A=4$. If $A=3$,
each shared state uses exactly one of these incidences. The
$Z_3$ host cannot partner $O_2$ (excluded), $O_3$ (two axis
incidences) or $\mathsf c$ (exhausted). Its partner must be
$\mathsf R$, again contradicting Lemma 10.2 and
$e_{\mathsf N}=0$. This excludes the first list.

**Proof: parameters for the list $(0,1,2,7,8)$.**
For $B=(2,7)$ define

$$
\begin{gathered}
a_0=e_{\mathsf a},\quad b_0=e_{\mathsf b},\quad
c_0=e_{\mathsf c},\quad d_0=e_{\mathsf d},\quad
\mu=e_{\mathsf M},\quad\nu=e_{\mathsf N},\\
t=e_3,\quad f=e_6,\quad w=\mu+\nu,\quad
\ell=a_0+b_0,\quad\varrho=c_0+d_0,\\
E=\ell+\varrho+t+f+w,\quad D=E+1,\\
t,f\ge1,\qquad a_0+c_0+\mu\ge1,\qquad
b_0+d_0+\nu\ge1.
\tag{81}
\end{gathered}
$$

In particular $E\ge4$. Only $Z_3,Z_4,O_3$ are possible axis
endpoints in this pool, so $A\le3$. If $A=3$, each uses a
distinct shared state with one axis incidence; the $Z_3$ partner
is then $\mathsf R$ or $\mathsf c$. Their actual zero children
are respectively $Z_4,\mathsf M$ or $Z_4,\mathsf d$; the
former parent also has an $\mathsf a,\mathsf c$ one child.

Let $X,Y,Z$ count the non-axis types
$\mathsf a\mathsf c,\mathsf b\mathsf c,\mathsf b\mathsf d$.
Then

$$
\begin{gathered}
N_{\rm sh}=X+Y+Z,\quad
X\le1+a_0,\quad Y+Z\le1+b_0,\\
X+Y\le1+c_0,\quad Z\le1+d_0.
\tag{82}
\end{gathered}
$$

Every $\mathsf a\mathsf c$ state has its fixed zero successor
of type $\mathsf b\mathsf d$. This does not assert injectivity
of that successor map.

First exclude $\ell=\varrho=0$. Equations (78), (81) and
$D=A+N_{\rm sh}=E+1$ force
$E=4,D=5,A=3,N_{\rm sh}=2,t=f=1$. The two non-axis states
exhaust the two hosts on each side. They must be one
$\mathsf a\mathsf c$ and one $\mathsf b\mathsf d$ state.
The unique supports at $\mathsf b,\mathsf d$ let Lemma 10.3
force $f\ge2$, a contradiction. This is the live argument
underlying Corollary 10.5; it uses no installed-state conclusion.

Put $H=\max(\ell,\varrho)\ge1$. From (78) and (81),

$$
H+t+f+w\le A+1\le4.
\tag{83}
$$

Thus $H$ is one or two. The following cases exhaust the remaining
nonnegative integers.

**Proof: $H=2$.**
Equation (83) forces $A=3,t=f=1,\mu=\nu=0$ and
$N_{\rm sh}=\ell+\varrho$. Lemma 10.2 excludes the
$Z_3,\mathsf R$ option, so $Z_3$ shares with $\mathsf c$,
and its zero child shares $Z_4,\mathsf d$. These two distinct
axis states consume two upper-endpoint hosts outside the non-axis
states. Hence $N_{\rm sh}+2\le2+\varrho$, giving
$\ell=0,\varrho=2,N_{\rm sh}=2$.

Lower saturation forces one $\mathsf a\mathsf c$ state and its
distinct $\mathsf b\mathsf d$ zero successor. Each upper cell
therefore needs one axis and one non-axis host. Their total capacity
is four, so each has exactly two, and
$F_{\mathsf d}\subseteq F_{\mathsf b}\cup F_{Z_4}$.
But $\mathsf a,\mathsf b,\mathsf M,\mathsf N$ each have one
host and support. Lemma 11.3 supplies an actual live
$\mathsf d$ host outside that union, a contradiction.

**Proof: $H=1$ and $A=2$.**
Equation (83) gives $t=f=1,\mu=\nu=0$. Since $E\ge4$,
necessarily $\ell=\varrho=1,E=4,N_{\rm sh}=3$. Both endpoint
sides are exhausted. The depth-four and depth-five excesses in
(81) are each one, so (82) becomes

$$
2X+Y=3,\qquad Y+2Z=3,\qquad X,Z\ge1.
\tag{84}
$$

The only nonnegative integral solution is $X=Y=Z=1$.
Consequently $\mathsf a,\mathsf M,\mathsf d$ have one host
and support, while $\mathsf a\mathsf c$ sharing occurs.
Lemma 11.2 excludes it.

**Proof: $H=1$, $A=3$ and $\ell+\varrho=1$.**
The bounds $N_{\rm sh}\le2$, $E\ge4$ and
$E+1=3+N_{\rm sh}$ force $E=4,N_{\rm sh}=2$.
The two middle layers each have positive excess; their total is
$1+w$. Together with $t,f\ge1$, this forces
$t=f=1,w=1$, with each middle-layer excess exactly one.

If $\ell=1,\varrho=0$, both upper hosts are in non-axis
sharing, so $Z_3$ must partner $\mathsf R$. Lemma 10.2
gives $\nu=1,\mu=0$. The depth-five equation then gives
$b_0=d_0=0$. Its $\mathsf a\mathsf c$ one child has singleton
supports at $\mathsf b,\mathsf d$, so Lemma 10.3 contradicts
$f=1$.

If $\ell=0,\varrho=1$, lower saturation forces one
$\mathsf a\mathsf c$ and one $\mathsf b\mathsf d$ state.
Were $\nu=0$, we would have $\mu=1,c_0=0,d_0=1$.
Lemma 10.2 would exclude $Z_3,\mathsf R$; its only other
option $Z_3,\mathsf c$ would need an additional $\mathsf c$
host beyond its sole exhausted one. Thus $\nu=1,\mu=0$.
The middle-layer equations give $c_0=1,d_0=0$, making
$\mathsf a,\mathsf M,\mathsf d$ singleton-support cells with
$\mathsf a\mathsf c$ sharing. Lemma 11.2 excludes this too.

**Proof: $H=1$, $A=3$ and $\ell=\varrho=1$.**
Here $E=N_{\rm sh}+2$ is four or five. If $E=4$, then
$t=f=1,\mu=\nu=0,N_{\rm sh}=2$. Lemma 10.2 forces the
$Z_3,\mathsf c$ option and its $Z_4,\mathsf d$ zero child.
These two axis states plus the two non-axis states need four upper
hosts, whereas $2+\varrho=3$.

If $E=5$, then $N_{\rm sh}=3$ exhausts both endpoint sides.
Thus $Z_3$ must partner $\mathsf R$, which gives
$t=f=1,\mu=0,\nu=1$. Saturation in (82) yields

$$
X=1+a_0,\quad Z=1+d_0,\quad
X+Y=1+c_0,\quad Y+Z=1+b_0,\quad a_0+d_0+Y=1.
\tag{85}
$$

Exactly one of the three final summands equals one. If $Y=1$,
then $a_0=d_0=0$, and Lemma 11.2 excludes the
$\mathsf a\mathsf c$ sharing with singleton
$\mathsf a,\mathsf M,\mathsf d$. If $a_0=1$, then
$b_0=d_0=0$, and Lemma 10.3 excludes it at $f=1$ using
singleton $\mathsf b,\mathsf d$. If $d_0=1$, then
$a_0=c_0=\mu=0$, contradicting the depth-four inequality in
(81). This exhausts (85).

For $H=1$, (83) requires $A\ge2$, and the preceding three
cases exhaust $A,\ell,\varrho$. Together with the zero-endpoint
case and $H=2$, they exclude the second list in (77). Hence
$v=19$ is impossible and (75) follows. All additional children
used are live; extra never-live installation cannot supply a missing
live incidence or invalidate these counts. Original certified
continuations and their charges remain in the graph. $\square$

**Corollary 12.3 (threshold-five transport).**
For every original eight-coordinate cost vector, every complete
threshold-five graph at both caps $8,W$ has at least twenty live
states from its declared start, under the transported conditional
interfaces of Convention 11.1. If $u_5$ is its never-live count,
then $m\ge20+u_5$.

**Proof.** Swap the two bit successors at every running state and
interchange terminal outputs. On input $y$ the resulting graph
follows exactly the old run on $1-y$, with the same visited
coordinates and both same-run charges. Its output is
$1-\mathbf1_{\{8-|y|\ge5\}}=\mathbf1_{\{|y|\ge4\}}$.
A live old prefix with counts $(h,z)$ becomes a live threshold-four
prefix with counts $(z,h)$, and conversely. Thus live and never-live
state sets have unchanged cardinalities. Apply Theorem 12.2 to this
threshold-four graph. This is a fixed table transformation in a
proof, not a free bit-complement port for an apparatus. $\square$

**Attribution and scope 12.4.**
Sections 7–11 own the critical geometry, pool estimates, support
forks, singleton obstructions and installed minimum twenty.
Theorem 12.2 extracts their live-scope consequence while retaining
arbitrary $u$ and all actual certified traffic. Its consumer is the
paid-root theorem in [Common Prefix, Section 7][CP12]: an adjacent
total threshold entry must sit outside a chosen live set. An
installed bound twenty alone does not supply that extra state.
This is repo-derived synthesis using mature incidence counting,
stationary continuation and Boolean complementation; no worldwide
originality or new Lean certification is claimed.

Convention 11.1's conditional SI hypotheses remain exactly the proof
boundary. The all-size collective obligation (73), original unrestricted
alternatives A/B, unrestricted-budget minimum and fixed-specification
attainment remain unresolved. The conditional critical installed
minimum and Native minimum of Section 11 are unchanged. The entire
actual full fiber, literal code and latches, complete separate $K=8$
reader, source and service assumptions of Sections 1 and 11.6 are
retained; [Common Prefix, Section 8][CP12] gives their parameter
map for the nine-coordinate consumer. No observation, acquisition,
selector, history store or inverse service is installed by (75),
and no four-view mutual recovery follows from counting live states.

[CP12]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_COMMON_PREFIX_MEMORY_FRONTIER.md

## 追加锚（临界二十精确结论；本行以下为增补区）

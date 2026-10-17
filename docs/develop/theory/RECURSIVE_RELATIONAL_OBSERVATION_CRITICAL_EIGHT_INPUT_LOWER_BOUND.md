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

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

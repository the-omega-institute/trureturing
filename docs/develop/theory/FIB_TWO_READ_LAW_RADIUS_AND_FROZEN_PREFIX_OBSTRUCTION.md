# FIB two-read law radius and frozen-prefix obstruction

Every lawful protocol with a hard total budget of two paid reads has an exact full-law representative within radius five of its original hidden endpoint. The radius five is sharp. A particular three-read law also shows that a valid two-read placement cannot always be frozen and extended: its prescribed first two placements preserve the target and prefix-reply law, but no continuation of that prefix preserves the complete target/output/return/count law.

These are ordinary mathematical proofs over the original stationary biased XOR source. The substantive increment is the universal two-read upper bound and the specified prefix-extension obstruction, as supplied in the two-read proposal and its independent mathematical check. The stopping-law lower bound, zero/one-budget values, and exponential upper bound retain their existing ownership. The universal polynomial-versus-superpolynomial radius question remains open.

**Reference convention.** This volume is mathematical reference input, without Lean-kernel certification. It uses the `generic-v1` text convention without asserting ingestion or a ledger state. Once integrated, its existing text is retained; additions and corrections belong after the terminal append anchor. The proofs below carry their conclusions directly.

## 1. The original source, endpoint, and universal objective

**Definition 1.1 (One stationary integer-clock law).** Fix a single real parameter and a single endpoint

$$
0<p<1,\qquad p\ne\tfrac12,\qquad j\in\{0,1\},\qquad
\pi_0=1-p,\quad\pi_1=p.
$$

Let $\varphi$ be uniform on $\{0,1\}$, independently of iid Bernoulli$(p)$ spins $(S_\ell)_{\ell\in\mathbb Z}$. On the original integer emitted-bit clock define the joint hidden-visible law $J_p$ by

$$
\begin{aligned}
H_{2\ell+\varphi}&=a_{S_\ell},&
H_{2\ell+\varphi+1}&=b_{S_{\ell+1}},\\
X_{2\ell+\varphi}&=S_\ell\mathbin\oplus S_{\ell+1},&
X_{2\ell+\varphi+1}&=0.
\end{aligned}
\tag{1.1}
$$

The hidden alphabet is $\mathcal A=\{a_0,a_1,b_0,b_1\}$. An active transition takes $a_s$ to $b_t$ with probability $\pi_t$ and emits $s\oplus t$; the next transition copies $b_t$ to $a_t$ and emits zero. Each $a_s,b_s$ has stationary mass $\pi_s/2$: incoming mass at $b_t$ is $\sum_s(\pi_s/2)\pi_t=\pi_t/2$, and copying gives the same incoming mass at $a_t$. Independence of the newly chosen spin gives these transition factors on every finite interval, including intervals beginning in either state class. Uniform phase and reindexing of the iid spins preserve their law under an integer shift. Thus (1.1) is the one original stationary law, including its separators and negative coordinates; in particular $X_tX_{t+1}=0$ for every integer $t$.

This source is inherited from *FIB harmonic-edge load: fixed-state tail nonuniformity and an erasure-risk jump*, Proposition 2.1 and (2.2), hereafter **Original**. Its realization is a description of the source, not an acquisition operation.

**Definition 1.2 (Actual endpoint).** The target remains the actual $H_j$. Write $H_j=h_{j,\varphi,S_{q_{j,\varphi}}}$. The complete table is

$$
\begin{array}{c|c|c|c|c}
j&\phi&q_{j,\phi}&h_{j,\phi,s}&B_{j,\phi}=2q_{j,\phi}+\phi\\ \hline
0&0&0&a_s&0\\
0&1&0&b_s&1\\
1&0&1&b_s&2\\
1&1&0&a_s&1
\end{array}
\tag{1.2}
$$

Hence $q_{j,0}=j$, $q_{j,1}=0$, and $B_{j,\phi}\in\{j,j+1\}$. For example, at $j=0,\phi=1$, coordinate zero is the separator after active address $-1$, so $H_0=b_{S_0}$. The table is Original (9.4). At fixed $j$, the endpoint's state class determines the phase as a mathematical event; a protocol does not observe that class or phase for free.

**Definition 1.3 (All lawful acquired-record rules).** Let $(\mathsf U,\mathcal U,\nu)$ be any given probability space independent of the entire source $J_p$, and set $\mathbb P_p=J_p\otimes\nu$. Keep the variable $u$ and its law unchanged. All internal randomness and random public data are included in this same independent variable. Fixed public data may include $p,j$ and the budget.

A finite acquired record is an ordered list

$$
r=((t_1,x_1),\ldots,(t_n,x_n))\in(\mathbb Z\times\{0,1\})^n,
\qquad n\in\mathbb N_0.
\tag{1.3}
$$

A measurable next-event rule uses only the public data, $u$, and that record. It chooses a read at an integer address, a finite return of a state in $\mathcal A$, or indefinite internal continuation with no further read or return. Finite events may follow internal waiting; their occurrence, kind, address or output, and finite waiting time are measurable functions of precisely those available data. Waiting supplies no additional source observation. A read at $t$ returns only the actual $X_t$ of (1.1).

Every actual call costs one, including every repeated address, separator zero, negative or positive address, remote address, and disconnected collection of reads. Ignoring a reply later does not remove its charge. Return before any read, wrong-phase output, and internal nonreturn after any finite read count, including zero, are allowed. Before a total cap is imposed, infinite-read nonreturn is also allowed. Null records and the usual measurable completion versions are included.

There is no new coin, phase oracle, hidden-state or spin read, half-line or tail observation, source-dependent seed or timing, reset, source switch, moving endpoint, or erased-coordinate substitution. There is no connectedness, consecutiveness, predetermined-address, or always-returning restriction. This is Original Definition 9.1 and *FIB paid reads: return mass and hidden-endpoint classification risk*, Definition 1.2, hereafter **Paid-return**.

**Definition 1.4 (Total cap and full preserved law).** Let $N$ count all actual reads and let $\tau$ be the return time, with $\tau=\infty$ on every nonreturn. These are different quantities. A pathwise hard total cap $k\in\mathbb N_0$ requires $N\le k$ on every execution, including nonreturns and exceptional source/seed paths. Set

$$
D=\mathbf1_{\{\tau<\infty\}},\qquad
O=\begin{cases}A&D=1,\\\bot&D=0,\end{cases}\qquad
Z=(H_j,O,D,N),\qquad\bot\notin\mathcal A.
\tag{1.4}
$$

Under the cap the alphabet is finite:

$$
\mathcal Z_k=\{(h,o,d,n):h\in\mathcal A,\ o\in\mathcal A\cup\{\bot\},
d=\mathbf1_{\{o\ne\bot\}},\ 0\le n\le k\}.
\tag{1.5}
$$

The objective is exactly equality of the joint law of $(u,H_j,O,D,N)$, including correlations with every measurable seed event. A nonreturn with $N=n$ keeps its $n$ paid calls and means internal continuation forever after them. A cap only on returns is insufficient: $k+1$ repeated reads followed by internal nonreturn obey every return-only cap but have an $N$-law impossible under total cap $k$.

Numerical return times, literal address names, acquired records, whole-tree signatures, and equality on each original source sample are not coordinates of this objective. A representative may change its tree, decisions, and records, and may use the single fixed public $p$.

**Definition 1.5 (Universal law radius).** A radius-$R$ rule uses only integer addresses $t$ with $|t-j|\le R$. Let $\rho_{\mathrm{law}}(k;p,j,\nu)$ be the least nonnegative integer radius sufficient to represent every lawful total-cap-$k$ input on this same given seed space, preserving the full law in Definition 1.4 and the total cap. The inherited exponential upper bound stated in Section 7 ensures finiteness. All parameter quantifiers in this definition and below retain the full range in Definitions 1.1–1.4.

## 2. Finite source sections and the unchanged seed

**Lemma 2.1 (Semantic trees with exact paid depths).** Every lawful total-cap-$k$ rule admits a measurable seed-dependent representation by finite binary read trees of height at most $k$. Read nodes carry integer addresses. Terminals carry one of the four return states or $\bot$, and their depths are the exact paid counts, also at $\bot$. Normalization preserves $Z$ and every actual read sequence; every formal binary branch can be capped too.

Proof. Replace numerical finite internal delays by fixed finite delays, keeping the distinction between a finite next event and indefinite internal continuation. At every formal record of length $k$, replace a further read request by internal nonreturn without making that call. Keep a return or existing internal nonreturn there. On an actual path already satisfying $N\le k$, no actual call or return is suppressed. A finite number of finite waits is finite, so $O,D,N$ are unchanged. Inconsistent formal branches are now capped as well.

At fixed $u$, unfold the resulting semantic rule. A read has two ordered children indexed by its reply. A return or internal nonreturn is a terminal. No read occurs at depth $k$, so the tree has at most $2^k-1$ read nodes for $k\ge1$ and none for $k=0$. Repeated addresses remain separate paid nodes; no terminal depth is padded.

The space $\mathcal T_k$ of these integer-labelled trees is countable and is given the discrete sigma-algebra: there are finitely many shapes and terminal-label patterns, with a finite integer tuple for each shape. To prove $u\mapsto T(u)$ measurable, construct the finitely many possible node positions in order of depth. Their preceding records have countable range. For any measurable action condition $F(u,r)$ and countably valued preceding record $r(u)$, evaluation has event

$$
\bigcup_r\bigl(\{u:r(u)=r\}\cap\{u:F(u,r)\}\bigr).
\tag{2.1}
$$

This is measurable. Induction gives the whole tree map, using a dummy label at absent positions. Finite-event versus indefinite-continuation type is measurably specified by the contract. For permitted completion versions choose versions together over the countably many records; null changes leave the product-measure identities below unchanged. This is a semantic representation, without a procedure for deciding divergence of arbitrary code. It is the inherited interface of Original Theorems 12.2–12.3. $\square$

**Lemma 2.2 (Source-section calculus and measurable lift).** For a fixed seed and a path of a normalized tree with record $r$, its source section is exactly the cylinder $\{X_{t_i}=x_i:1\le i\le n\}$ if its choices agree with the tree, and is empty otherwise. A terminal label and its paid depth determine $(O,D,N)$. If a specified map $C:\mathcal T_k\to\mathcal T_k$ preserves each tree's source law of $Z$, it produces one lawful representative on the unchanged seed space with the same full $(u,Z)$ law. Conversely, any full-law representative of a seed-ignoring witness has that witness's deterministic source law at almost every seed.

Proof. Fix the seed and a consistent record. The recorded replies force the successive choices on that path, including adaptive addresses and whether a finite terminal event occurs. Internal waiting imposes no further source condition, since it is already determined by the same seed and replies. This proves the cylinder assertion, including internal nonreturn terminals.

Write $a_{T,p}(z)=J_p(Z^T=z)$. Any specified map on the countable discrete tree space is measurable. Choose $C(T(u))$ at seed $u$ and execute that actual tree with actual source replies. On records inconsistent with it prescribe internal nonreturn. The countable measurable partition into selected trees and the finite record tests on each cell make this a total measurable next-event rule. Selection uses only the given seed and public data. If the image trees are capped on all formal branches, so is this rule. Independence of source and seed gives, for every $G\in\mathcal U$ and $z\in\mathcal Z_k$,

$$
\begin{aligned}
\mathbb P_p(u\in G,Z^{\mathrm{input}}=z)
&=\int_G a_{T(u),p}(z)\,d\nu(u)\\
&=\int_G a_{C(T(u)),p}(z)\,d\nu(u)\\
&=\mathbb P_p(u\in G,Z^{\mathrm{new}}=z).
\end{aligned}
\tag{2.2}
$$

The first equality uses Lemma 2.1. Since the $z$ alphabet is finite, these rectangles specify the full joint law.

For the converse let $w_z$ be the seed-ignoring witness's source masses and $a_z(u)$ a competitor's tree source masses. Full joint-law equality says

$$
\int_G(a_z(u)-w_z)\,d\nu(u)=0\qquad(G\in\mathcal U).
\tag{2.3}
$$

If $a_z-w_z$ were positive on a set of positive measure, it would exceed $1/n$ on such a set for some positive integer $n$, contradicting (2.3); apply the same argument to its negative. Thus $a_z=w_z$ almost everywhere. Intersect the finitely many equality sets over $z$ to obtain one full-measure set of good seeds. Every good seed has the exact deterministic witness law.

These are source-section integrals, without a regular conditional distribution given a singleton seed. They work for arbitrary atomic or nonstandard seed spaces, split no atoms, and introduce no randomizer. Completion-version null changes affect none of the integrals. These facts reproduce the needed same-seed reasoning of Original Theorem 12.3 and *FIB stopping-law rigidity and sharp linear address radius*, Lemma 2.2, hereafter **Stopping**. $\square$

## 3. One two-read tree within radius five

**Lemma 3.1 (The entire unordered two-edge domain).** Fix an integer target vertex $q$ and ordered queried edges $E,F$ of the integer spin line, each of the form $\{e,e+1\}$. The following table gives a new root edge $E'$ and new child edge $F'=\{f',f'+1\}$. Every old pair belongs to exactly one row. In every row the finite graph consisting of the two labelled unordered edges and the distinguished vertex $q$ is isomorphic to its displayed replacement, fixing $q$ and preserving which edge is the root and which the child.

| Target/root relation | Child relation | New root $E'$ | New child left endpoint $f'$ |
| --- | --- | --- | --- |
| $q\in E$ | $F=E$ | $\{q,q+1\}$ | $q$ |
| $q\in E$ | $E\cap F=\{q\}$ | $\{q,q+1\}$ | $q-1$ |
| $q\in E$ | $E\cap F$ consists of the other endpoint of $E$ | $\{q,q+1\}$ | $q+1$ |
| $q\in E$ | $E\cap F=\varnothing$ | $\{q,q+1\}$ | $q+2$ |
| $q\notin E$ | $F=E$ | $\{q+1,q+2\}$ | $q+1$ |
| $q\notin E$ | $\lvert E\cap F\rvert=1$, $q\in F$ | $\{q+1,q+2\}$ | $q$ |
| $q\notin E$ | $\lvert E\cap F\rvert=1$, $q\notin F$ | $\{q+1,q+2\}$ | $q+2$ |
| $q\notin E$ | $E\cap F=\varnothing$, $q\in F$ | $\{q+1,q+2\}$ | $q-1$ |
| $q\notin E$ | $E\cap F=\varnothing$, $q\notin F$ | $\{q+1,q+2\}$ | $q-2$ |

Proof. Two integer-line edges are equal, meet at exactly one vertex, or are disjoint. When $q\in E$, a meeting vertex is $q$ or the other root endpoint, and a disjoint child cannot contain $q$. These are exactly the first four cases. When $q\notin E$, an equal child excludes $q$; a meeting child either contains $q$ at its nonshared endpoint or excludes it; and a disjoint child either contains $q$ or excludes it. These are exactly the last five cases, covering every integer placement and both orientations.

For an equal pair, map the two endpoints to those of $E'$, fixing $q$ if incident and keeping the isolated $q$ otherwise. For a meeting pair, map the shared vertex and the two edge-labelled outer endpoints to the corresponding displayed vertices. The first meeting case has $q$ in the middle, the next has $q$ at the root-side end; the two detached-root meeting cases put $q$ at the child-side end or isolate it. Thus the distinguished position is preserved. For disjoint pairs, map each edge's two endpoints to its displayed edge's endpoints, fixing $q$ on its incident edge when applicable and keeping it isolated otherwise. In the last row the new edges are $\{q+1,q+2\}$ and $\{q-2,q-1\}$ with isolated $q$; in the target-touching-root disjoint row they are $\{q,q+1\}$ and $\{q+2,q+3\}$. These vertex sets have precisely the required disjointness. An unqueried adjacency between distinct vertices imposes no equality on iid spins. These maps give the claimed isomorphisms. $\square$

**Theorem 3.2 (Universal two-read upper bound).** Every lawful total-cap-two input has a lawful representative on its unchanged given seed space with every address in $[j-4,j+5]\cap\mathbb Z$ and the same full law of $(u,H_j,O,D,N)$. More specifically, a supplied normalized tree of height at most two has one relabelling independent of $p$ which retains its ordered shape, all terminal labels, and every terminal paid depth. The same relabelling of that fixed tree works for every allowed $p$ simultaneously.

Proof. Work first with one supplied finite tree. Keep any immediate terminal. Otherwise let its root address $t$ have parity $\alpha$ and active edge $E=\{e,e+1\}$, where $e=(t-\alpha)/2$. Put $q=q_{j,\alpha}$ and $B=2q+\alpha$. Give the root the single new edge left endpoint

$$
e'=\begin{cases}q&q\in E,\\q+1&q\notin E,\end{cases}
\qquad t'_{\mathrm{root}}=2e'+\alpha.
\tag{3.1}
$$

This choice is made once, before either root-reply branch. In phase $\alpha$, a target-touching edge, in either direction, has conditional reply $S_q\oplus V$ with $V$ an independent Bernoulli$(p)$ spin. A detached edge has the XOR of two fresh Bernoulli$(p)$ spins independently of $S_q$. Formula (3.1) has the respective same laws. In the other phase both old and new root bits are separator zeros. Thus the complete target/root-reply marginal is preserved.

Keep each terminal child at depth one, including $\bot$. Consider each reading child separately, retaining its two terminal labels at depth two. If its parity $\beta$ differs from $\alpha$, put $q_\beta=q_{j,\beta}$ and replace its active edge left endpoint by $q_\beta$ when its old edge contains $q_\beta$, and by $q_\beta+1$ otherwise. Its actual new address is twice that endpoint plus $\beta$. In phase $\alpha$ this child is a separator and the root/target marginal has already been preserved. In phase $\beta$ the root is a separator and the touching/detached argument preserves the child/target marginal. Consequently the target/root/that-child potential-reply triple has the same law, after averaging the original phase weights $1/2,1/2$.

If the child has parity $\alpha$, use Lemma 3.1 for its old edge $F$, giving actual new address $2f'+\alpha$. In phase $\alpha$ take the lemma's vertex bijection. Each spin assignment on the finite occupied vertex set has mass

$$
\prod_v\pi_{s(v)}.
\tag{3.2}
$$

Transporting the assignment along the bijection preserves all its factors, the target spin, and both edge XORs. The XOR is symmetric, so unordered edges suffice. Summing over assignments proves equality of the joint target/root/that-child potential-reply triple. In the opposite phase both addresses are separators. Averaging gives the unconditional triple identity too.

This constructs actual addresses for one tree, for both parities and both mutually exclusive child branches. The root is always the same (3.1) in the two child arguments. The abstract spin bijections used to prove their respective marginal identities may differ. Each identity is nevertheless a marginal of the genuine law of this one constructed tree; no joint identity of the two siblings' potential replies is needed.

To see execution explicitly, let $x$ denote the root reply. For a terminal child with label $\ell_x$, the event of reaching it jointly with $H_j=h$ has the preserved mass $J_p(H_j=h,X_{\mathrm{root}}=x)$. For a reading child, let $y$ be its reply and $\ell_{x,y}$ its terminal label. The corresponding mass is exactly

$$
J_p(H_j=h,X_{\mathrm{root}}=x,X_{\mathrm{child}\ x}=y),
\tag{3.3}
$$

which is the triple coordinate just proved equal. These terminal events partition actual execution, including any zero-mass events. Their kept labels and depths give $O,D,N$. Summing their masses proves the entire $Z$-law identity. A $\bot$ label at depth zero, one, or two retains internal nonreturn with exactly that many paid calls. No samplewise coupling or record preservation has been imposed.

Every same-parity table endpoint $f'$ is between $q-2$ and $q+2$, so its address is between $B-4$ and $B+4$. Root and opposite-parity child addresses are their own $B_{j,\gamma}$ or $B_{j,\gamma}+2$. By (1.2) every base is $j$ or $j+1$. All actual addresses therefore lie in $[j-4,j+5]$, within radius five. Keeping the shape retains the cap on every formal branch, including impossible replies and every nonreturn depth.

The specified construction defines a map $C_j$ on the countable discrete tree space. Lemmas 2.1–2.2 now yield the measurable same-seed rule and equality (2.2) for every seed event and every $z$. No new randomness or source observation is involved. Geometry and $j$ alone determine $C_j$, and the product identity (3.2) holds at every allowed $p$. If an input itself uses public $p$, apply the construction to its tree at that fixed $p$; joint measurability in a varying parameter is not required. $\square$

## 4. The inherited lower five and the exact universal value

**Proposition 4.1 (The two-read stopping witness, inherited).** Put

$$
\psi=1-j,\qquad q=j,\qquad 2q+\psi=j+1,\qquad
d=p(1-p),\qquad c=\pi_0^2+\pi_1^2=1-2d,
\qquad T_3=\pi_0^3+\pi_1^3=1-3d.
\tag{4.1}
$$

Ignore $u$, read $j+3$, return $a_1$ on one, and on zero read $j+5$, returning $a_1$ on one and $a_0$ on zero. This lawful always-returning cap-two witness has, for each $s\in\{0,1\}$, exactly the following nonzero source masses:

$$
\begin{aligned}
J_p(H_j=b_s,O=a_1,D=1,N=1)&=\tfrac{\pi_s}{2}\,2d,\\
J_p(H_j=b_s,O=a_1,D=1,N=2)&=\tfrac{\pi_s}{2}\,d,\\
J_p(H_j=b_s,O=a_0,D=1,N=2)&=\tfrac{\pi_s}{2}\,T_3,\\
J_p(H_j=a_s,O=a_0,D=1,N=2)&=\tfrac{\pi_s}{2}.
\end{aligned}
\tag{4.2}
$$

Each mass with $u\in G$ is its displayed value times $\nu(G)$. Every lawful full-law representative, on any unchanged given seed space and at this single fixed $p$, needs radius at least five. This is the $k=2$ instance of Stopping Theorems 3.2, 4.1, and 5.1; the following proof supplies the complete instance used here.

Proof. In phase $\psi$ the actual endpoint is $b_{S_q}$ and the two active edges have left endpoints $q+1,q+2$. Their three spins are independent of $S_q$. The first one has probability $2d$. Zero followed by one means the first two spins agree and the third differs, with probability $\pi_0^2\pi_1+\pi_1^2\pi_0=d$. Both zeros force all three spins equal, with probability $T_3$. These probabilities sum to one. In the opposite phase the actual endpoint has class $a$ and both reads are separators, so the output is $a_0$ at count two. The phase weight $1/2$ and independent target mass $\pi_s$ give (4.2). The rule is finite, measurable, and capped on every formal branch. Seed independence gives the rectangle masses.

Consider any full-law representative, initially allowing all lawful trees, nonreturn, public-$p$ dependence, and arbitrary measurable use of $u$. By Lemma 2.2, at almost every good seed its normalized deterministic source law is exactly (4.2). Fix such a seed. Refer to phase $\psi$ as phase $B$ and its opposite as phase $A$; these are mathematical conditionings identified by the preserved endpoint classes. Phase $A$ must return $a_0$ at count two surely. Phase $B$ has positive $a_1$ masses at counts one and two. Both phases have return probability one and no count-zero mass.

The root must read. If its parity were opposite to $\psi$, phase $B$ would have root reply zero surely. Its required count-one $a_1$ mass would force that zero child's next event to be an $a_1$ return. In phase $A$ the root would instead be active, with zero probability $c>0$. The same zero child would return $a_1$ on that positive-mass phase-$A$ event, contradicting (4.2). Hence the root parity is $\psi$.

Its zero child is reached surely in phase $A$, so it must make a second read. Its one child is the only possible source of the required positive phase-$B$ count-one mass; it must return $a_1$ there at count one. If the second read had parity opposite to $\psi$, phase $B$ would get second reply zero. The required positive $a_1$ mass at count two would force an $a_1$ return on that zero child. Phase $A$ has seen only its root separator, so the newly active edge has zero probability $c>0$ there. This would again produce a forbidden $a_1$ return in phase $A$. Thus the second parity is also $\psi$. Its zero child is reached surely in phase $A$ and returns $a_0$; its one child must supply the positive phase-$B$ count-two $a_1$ mass and return $a_1$. Nonreturn on any of these positive sections would violate $D=1$. This derives the stopping tree from the full law itself.

Let $e_1,e_2$ be the derived continuing-branch spin-edge left endpoints, and write

$$
C_r=\{S_{e_i}=S_{e_i+1}:1\le i\le r\}\qquad(r=1,2).
\tag{4.3}
$$

In phase $B$, $C_1$ is the event $N=2$, and $C_2$ is the event $O=a_0$. Summing (4.2) at each target value gives

$$
J_p(C_1\mid\varphi=\psi,S_q=s)=c,\qquad
J_p(C_2\mid\varphi=\psi,S_q=s)=T_3
\quad(s=0,1).
\tag{4.4}
$$

Both conditionings have positive mass. Averaging over the target gives the same unconditional probabilities within phase $B$.

Two integer-line edges either repeat, share one endpoint, or are vertex-disjoint. Repetition would give $J_p(C_2\mid\varphi=\psi)=c>T_3$, since $c-T_3=d>0$. Disjoint edges would give $c^2$, while

$$
T_3-c^2=d(1-4d)>0.
\tag{4.5}
$$

The inequality is strict at every single allowed biased $p$, because $0<d<1/4$. Only two distinct edges sharing one endpoint remain. They form a consecutive two-edge path on three vertices, whose both-zero probability is exactly $T_3$.

If $q$ were on that path, $C_2$ would force its other two spins to equal $S_q$, yielding conditional probability $\pi_s^2$ in (4.4). Those two probabilities differ, since $\pi_0\ne\pi_1$ and both are positive. They cannot both equal the required $T_3$. Thus $q$ is outside the path. If its vertices are $[L,L+2]\cap\mathbb Z$, either $L\ge q+1$ or $L+2\le q-1$. The first case has a queried left endpoint at least $q+2$ and hence an actual address at least

$$
2(q+2)+\psi=j+5.
\tag{4.6}
$$

The second case has a queried left endpoint $L\le q-3$ and hence an actual address at most

$$
2(q-3)+\psi=j-5.
\tag{4.7}
$$

These are actual positive-mass reads: in phase $A$ both zero-branch calls are executed surely; in phase $B$ the first call is sure and the second is reached with probability $c>0$. The remote call is therefore not an unreachable formal-node artifact. Integrating the good-seed sections rules out radius below five for every unchanged independent seed law. The witness itself uses radius five. No signature, acquired-record, or samplewise-preservation requirement entered the lower bound. $\square$

**Theorem 4.2 (Exact universal two-read law radius).** For every fixed $0<p<1$, $p\ne1/2$, either actual endpoint $j\in\{0,1\}$, and every given independent probability seed space with unchanged law $\nu$,

$$
\rho_{\mathrm{law}}(2;p,j,\nu)=5.
\tag{4.8}
$$

Proof. Theorem 3.2 supplies radius five for every lawful cap-two input with the full original interface. Proposition 4.1 supplies one such input for which every lawful full-law representative needs at least five. The upper and lower bounds have the same quantifiers, so they give (4.8). The lower is inherited; the new universal upper makes it matching. $\square$

## 5. A three-read law and an equivalent two-read prefix

**Proposition 5.1 (The bridge witness and its complete full law).** Keep $\psi,q,d,c$ from (4.1), and put $B=2q+\psi=j+1$. Define a seed-ignoring rule $V_j$ as follows: first read $j+7$; on one return $a_0$ at count one; on zero read $j+3$; on its one return $a_0$ at count two; on two zeros read $j+5$, returning $a_1$ on one and $a_0$ on zero. Fixed finite waits make this a lawful rule, always returning with cap three on every formal branch. For each $s\in\{0,1\}$ its complete nonzero source masses are

$$
\begin{aligned}
J_p(H_j=b_s,O=a_0,D=1,N=1)&=\tfrac{\pi_s}{2}\,2d,\\
J_p(H_j=b_s,O=a_0,D=1,N=2)&=\tfrac{\pi_s}{2}\,2dc,\\
J_p(H_j=b_s,O=a_1,D=1,N=3)&=\tfrac{\pi_s}{2}\,2d^2,\\
J_p(H_j=b_s,O=a_0,D=1,N=3)&=\tfrac{\pi_s}{2}\,(c^2-2d^2),\\
J_p(H_j=a_s,O=a_0,D=1,N=3)&=\tfrac{\pi_s}{2}.
\end{aligned}
\tag{5.1}
$$

Every other tuple has mass zero. For every $G\in\mathcal U$, the corresponding joint mass with $u\in G$ is the displayed mass times $\nu(G)$.

Proof. In phase $\psi$, the three queried edges, in execution order along zeros, are

$$
\{q+3,q+4\},\qquad \{q+1,q+2\},\qquad \{q+2,q+3\}.
\tag{5.2}
$$

The first two are disjoint pairs and are detached from the target $S_q$. Each pair has XOR-one probability $2d$ and zero probability $c$. Thus stopping at count one has probability $2d$ and stopping at count two has probability $2dc$. On the two-zero event, each pair is constant. The third, bridging edge is one precisely when the pairs have opposite constant spins. Each of the two such assignments has mass $\pi_0^2\pi_1^2=d^2$, giving the count-three $a_1$ mass $2d^2$. All three zeros force all four spins equal, with mass

$$
\pi_0^4+\pi_1^4=(\pi_0^2+\pi_1^2)^2-2\pi_0^2\pi_1^2=c^2-2d^2>0.
\tag{5.3}
$$

All events use spins disjoint from $S_q$, giving independence from the target. Their probabilities sum to $2d+2dc+c^2=1$, because $c+2d=1$. In the opposite phase every queried address is a separator; the rule returns $a_0$ at count three surely. Multiplication by the original phase weights and target probabilities proves (5.1), including its zero coordinates. Seed independence gives all rectangle masses. The rule's own radius is seven, attained at its first call. This last fact is a property of the displayed rule, without a lower-bound claim about its law. $\square$

**Proposition 5.2 (The specified frozen prefix preserves its complete prefix law).** Replace the first read of $V_j$ by $j+3$ and its second read on root zero by $j-3$. The resulting two-read prefix has exactly the same joint law of the actual target and its two potential replies as the original first two addresses. It consequently preserves the stopped prefix consisting of the target, first reply, whether the second read occurs, and its reply when acquired. Literal address names are excluded from this prefix statistic. These are precisely the placements from Theorem 3.2 for this two-edge prefix.

Proof. In phase $\psi$ the new pair of edges is

$$
E=\{q+1,q+2\},\qquad F=\{q-2,q-1\}.
\tag{5.4}
$$

They are disjoint from each other and from $q$, just as the first two edges in (5.2). Conditional on either target value $S_q=s$, both the old and new potential-reply pairs are independent pair XORs, each with probabilities $c,2d$ for zero and one. In the opposite phase all four addresses are separators, so both pairs are deterministically zero. The same actual endpoint table and the phase weights $1/2,1/2$ give equality of the complete target/potential-reply-pair laws. Applying the rule that omits the second reply on root one gives the stopped-prefix identity, and independence supplies every seed rectangle.

The old root edge $\{q+3,q+4\}$ excludes $q$, so (3.1) places it at left endpoint $q+1$, actual address $B+2=j+3$. Its old second edge is disjoint from the root and excludes $q$, so the last row of Lemma 3.1 places that child at left endpoint $q-2$, actual address $B-4=j-3$. This applies the two-edge placement to the prefix; it makes no claim that the height-three tree itself lies in the height-two theorem's domain. $\square$

## 6. No full-law continuation of that frozen prefix

**Theorem 6.1 (Frozen-prefix extension obstruction).** Fix any allowed $p,j,\nu$. No lawful total-cap-three representative of the full $(u,H_j,O,D,N)$ law (5.1) can have first query $j+3$ and next query on its zero reply $j-3$. Subsequent integer addresses are unrestricted, and arbitrary measurable use of the unchanged seed and the fixed public bias is allowed. The conclusion also holds if those prescribed prefix actions are required only at almost every seed.

Proof. Suppose such a rule exists. Apply Lemmas 2.1–2.2, obtaining a full-measure set of good seeds at which its normalized deterministic source law equals (5.1). If necessary intersect with the full-measure seed set where its prescribed actions hold. Fix one good seed. As before, call phase $\psi$ phase $B$ and its opposite phase $A$. In phase $A$ the law requires $O=a_0,D=1,N=3$ surely. In phase $B$ it prescribes all four positive masses in the first four lines of (5.1), conditionally on either target value.

First derive the stopping decisions from that law. Phase $A$ sees a root separator zero, so the root-zero child cannot terminate at count one or internally diverge. In phase $B$ root one has probability $2d$, and the required count-one mass is exactly $2d$, all with output $a_0$. A count-one return can occur only on the root-one child. Its next event, fixed by this seed and record, must therefore be a finite $a_0$ return. A further read or internal nonreturn there would give no count-one mass. In particular no root-one mass can be diverted to later counts.

On root zero the second query is prescribed. It is also a separator in phase $A$, so its zero child must make a third read to achieve the required count three. In phase $B$, the first two edges (5.4) are independent; zero then one has probability $2dc$, exactly the required count-two mass. Since the root-one branch has already returned and the second-zero branch must read in phase $A$, the second-one child is the only possible source of this mass and must return $a_0$ at count two. Thus phase-$B$ count three is exactly

$$
C=\{S_{q+1}=S_{q+2},\ S_{q-2}=S_{q-1}\},\qquad
J_p(C\mid\varphi=\psi,S_q=s)=c^2\quad(s=0,1).
\tag{6.1}
$$

On the common zero-zero record the third address is a single fixed integer at this seed. The third read is forced by the phase-$A$ count, a fourth call is disallowed by the cap, and positive-probability internal nonreturn is disallowed by $D=1$.

If the third address had parity opposite to $\psi$, it would be active in phase $A$. That phase has acquired only separator replies so far, so both replies have positive probability, $c$ and $2d$, there. Both terminal actions must return $a_0$ at count three. In phase $B$ this third address would be a separator zero, with the same $a_0$ terminal action. Earlier branches also return $a_0$, leaving no $a_1$ mass, contrary to (5.1). Hence the third address has parity $\psi$.

Its zero child is now reached surely in phase $A$ and must return $a_0$. To supply the positive $a_1$ mass, its one child must be reachable in phase $B$ and return $a_1$. If unreachable, the contradiction already follows. Writing $Y$ for the third active XOR, the full target law (5.1), divided by the positive probability $c^2$ in (6.1), therefore requires

$$
J_p(Y=1\mid\varphi=\psi,S_q=s,C)=\delta,
\qquad \delta=\frac{2d^2}{c^2},\qquad s=0,1.
\tag{6.2}
$$

This requirement has been deduced only from the full output/return/count/target law and the prescribed query actions. No acquired-record or signature preservation is being assumed.

Compute now the actual conditional spin law on $C$. Its constraints involve two disjoint pairs. Each pair is constant, with common spin Bernoulli$(r)$, where

$$
r=\frac{p^2}{c},\qquad 1-r=\frac{(1-p)^2}{c}.
\tag{6.3}
$$

The two common spins, $S_q$, and every outside spin are independent apart from the within-pair equalities. All outside spins retain their original Bernoulli$(p)$ laws. Indeed the conditioning indicator factors into the two pair-equality indicators on disjoint iid coordinates, so dividing their finite product probabilities by $c^2$ gives exactly these independent conditional factors. Conditioning further on $S_q=s$ merely fixes that independent coordinate. As $p\ne1/2$, $r\ne1-r$.

For every possible third active edge $\{e,e+1\}$, its conditional one-probabilities given phase $B$, $C$, and the two target values are as follows:

| Third left endpoint $e$ | Relation to conditioned vertices | Given $S_q=0$ | Given $S_q=1$ |
| --- | --- | --- | --- |
| $q-2$ or $q+1$ | Repeats $F$ or $E$ | $0$ | $0$ |
| $q-1$ or $q$ | Joins the target to an inner pair endpoint | $r$ | $1-r$ |
| $q-3$ or $q+2$ | Joins an outer pair endpoint to a fresh spin | $d/c$ | $d/c$ |
| $e\le q-4$ or $e\ge q+3$ | Two fresh outside spins | $2d$ | $2d$ |

For a repeated edge equality is already imposed on $C$, yielding zero. A target-touching edge has the fixed target on one end and an independent Bernoulli$(r)$ pair spin on the other, yielding $r,1-r$. An outside extension has an independent Bernoulli$(r)$ pair spin and Bernoulli$(p)$ fresh spin, so its probability is

$$
p(1-r)+(1-p)r
=\frac{p(1-p)^2+(1-p)p^2}{c}
=\frac d c.
\tag{6.4}
$$

An outside edge has two fresh iid spins, yielding $2d$. For exhaustiveness, the conditioned vertices are $q-2,q-1,q+1,q+2$ and the distinguished vertex is $q$. The six consecutive left endpoints $q-3,q-2,q-1,q,q+1,q+2$ are exactly the exceptional edges listed. Every other edge has two outside vertices. In particular there is no single edge bridging the two conditioned pairs: the closest vertices $q-1,q+1$ have $q$ between them. This covers negative, remote, repeated, disconnected, and target-touching choices without an address-radius restriction.

At every fixed allowed biased $p$ one has $0<d<1/4$ and $c=1-2d>1/2$, hence $c>2d$ and

$$
0<\delta=\frac{2d^2}{c^2}<\frac d c<2d.
\tag{6.5}
$$

The first strict comparison follows by the ratio $2d/c<1$, and the second by the ratio $1/(2c)<1$. Thus repeats, outer extensions, and fresh edges cannot give (6.2). A target-touching edge gives the unequal pair $r,1-r$, whereas (6.2) requires the same $\delta$ at both target values, each of positive probability. It cannot work either. Every third address is excluded at the fixed good seed.

The good-seed set has measure one, so this contradiction excludes the proposed measurable rule on every unchanged seed space. Even an atomless seed cannot supply a mixture to repair it: preserving the seed coordinate already forced the exact witness source law at almost every seed by (2.3). Finite waits provide no extra observation or choice beyond the fixed seed and acquired record. This proves the obstruction. $\square$

## 7. Inherited comparisons and the unchanged open target

**Proposition 7.1 (Existing general bounds and small budgets).** In the original interface, the inherited values and bounds are

$$
\begin{aligned}
\rho_{\mathrm{law}}(0;p,j,\nu)&=0,\\
\rho_{\mathrm{law}}(1;p,j,\nu)&=3,\\
2k+1\ \le\ \rho_{\mathrm{law}}(k;p,j,\nu)&\ \le\ 2^{k+1}-1\qquad(k\ge1).
\end{aligned}
\tag{7.1}
$$

The lower and small-budget conclusions are owned by Stopping Corollary 6.1 and Theorem 6.2. The upper is owned by *FIB finite paid reads: explicit address compression and the exact whole-signature radius*, Theorem 4.1, hereafter **Address**. The following ordinary arguments retain that ownership.

Proof. For the general lower let $T_m=\pi_0^m+\pi_1^m$ for $m\ge1$, so $T_1=1$, and let $d_i=T_i-T_{i+1}=\pi_0^i\pi_1+\pi_1^i\pi_0>0$. With $\psi=1-j,q=j$, read $j+2i+1$ along zeros for $1\le i\le k$, return $a_1$ at the first one, and $a_0$ after $k$ zeros. In phase $\psi$ these are $k$ consecutive edges detached from $q$. Their first $r$ zeros have probability $T_{r+1}$ independently of $S_q$. Thus the complete phase-$\psi$ masses given $S_q=s$ are $d_i$ for $(a_1,1,i)$ and $T_{k+1}$ for $(a_0,1,k)$. In the other phase $(O,D,N)=(a_0,1,k)$ surely. Multiply by $\pi_s/2$ and by $\nu(G)$ for each seed rectangle. Telescoping $\sum_i d_i+T_{k+1}=1$ verifies normalization.

Lemma 2.2 reduces any full-law representative to those same source masses at each good seed. Its root must read. Inductively suppose its first $i-1$ continuing calls have parity $\psi$ and their one children have returned $a_1$. The opposite phase has seen only separators and must reach count $k$, so call $i$ is forced. If it had opposite parity, its phase-$\psi$ reply would be zero; the positive prescribed $a_1$ mass at count $i$ would force an $a_1$ return on that zero child. In the opposite phase that newly active edge has positive zero probability $c$, contradicting the required $a_0$ output. Thus call $i$ has parity $\psi$. Its zero child is surely reached in the opposite phase and cannot return $a_1$; its one child must supply the positive count-$i$ $a_1$ mass and return immediately. For $i<k$ the zero child continues to read, and at $i=k$ it returns $a_0$. This completes the induction.

For these derived edges, let $C_r$ be the first $r$ zero constraints. For $r<k$ it is the phase-$\psi$ event $N>r$ and for $r=k$ it is $O=a_0$. The prescribed full target law gives

$$
J_p(C_r\mid\varphi=\psi,S_q=s)=T_{r+1}\qquad(1\le r\le k,\ s=0,1).
\tag{7.2}
$$

Starting with one edge, suppose the first $i-1$ distinct edges form a consecutive path. A further integer edge repeats, extends the path, or is disjoint. Repetition leaves probability $T_i>T_{i+1}$. Disjointness gives $cT_i$, and with $a=\max(p,1-p)>b=\min(p,1-p)>0$,

$$
T_{i+1}-cT_i=ab(a-b)(a^{i-1}-b^{i-1})>0\qquad(i\ge2).
\tag{7.3}
$$

Only extension gives the required $T_{i+1}$. Hence there are $k$ consecutive distinct edges. If their $k+1$ vertices contained $q$, the final probability in (7.2) would instead be $\pi_s^k$, unequal for the two $s$. The path is therefore detached. Writing its vertices $[L,L+k]$, either $L\ge q+1$ or $L+k\le q-1$. The corresponding extreme queried left endpoint is at least $q+k$ or at most $q-k-1$, giving an actual read at least $j+2k+1$ or at most $j-2k-1$. Every zero-branch call is actually reached surely in the opposite phase. Integration over good seeds proves the universal lower, including $k=1$ when the extension induction is empty.

For completeness the inherited upper can be obtained by packing all potential tree nodes. A height-$k$ tree has at most $M=2^k-1$ read nodes. Fix a parity $\alpha$, collect its $m\le M$ distinct active spin edges, and adjoin $q'=q_{j,\alpha}$. Its graph is a disjoint union of integer intervals. Keep the target component $[q'-l,q'+r]$ fixed; it has $l+r$ edges. The detached components have positive edge lengths $\ell_i$ and vertex sizes $s_i=\ell_i+1$, with total detached edge count $D_*=m-l-r$. If there are $C_*$ such components, their total vertex count is $D_*+C_*$. Their sizes split into two groups with totals $x\le D_*$ and $y\le D_*+1$: for zero components use empty groups; for one place all $D_*+1$ vertices in the second. For $C_*\ge2$, every size is at most $D_*-C_*+2$ because the other components each have at least one edge. In increasing order of their original least vertices, take the shortest prefix of sizes whose sum is at least $C_*-1$. Its preceding sum is at most $C_*-2$, so its final sum $x$ is at most $D_*$, and the remainder $y=D_*+C_*-x$ is at most $D_*+1$.

Translate the first group's components into consecutive disjoint vertex blocks immediately left of $q'-l$, and the second group's into blocks immediately right of $q'+r$. Keep each component's orientation. This injective vertex map fixes the target and preserves every equality among target and oriented queried-edge endpoints, including all repeated occurrences. Nearest vertices in different blocks may be adjacent, but the intervening unqueried edge imposes no equality on distinct iid spins. All occupied vertices are between $q'-l-x\ge q'-m$ and $q'+r+y\le q'+m+1$. Every mapped queried left endpoint is therefore in $[q'-m,q'+m]$.

Do this separately for the two parity classes and give each node the one actual address $2e'+\alpha$ from its own class. In each actual phase only that matching parity is active; the other nodes are separators. The phase alternatives impose no cross-phase spin-slot condition. Thus these two packings define one actual tree assignment. In each phase, transport finite spin assignments along the injective vertex map. Their iid product masses, target, and full potential-reply array are unchanged, so execution preserves the entire $Z$ law. Every address lies in $[j-2M,j+2M+1]$ by (1.2), giving radius $2M+1$. The specified ordering and split define a map on countably many trees, and Lemma 2.2 supplies the same-seed lift. Shape and all depths are retained. This proves the upper in (7.1).

At cap zero there are no reads; keep the original seed-dependent terminal rule, with radius zero. At cap one an immediate terminal is kept. Otherwise a root of parity $\alpha$ is replaced by edge left endpoint $q_{j,\alpha}$ if touching the target and $q_{j,\alpha}+1$ otherwise, retaining both terminal labels. The touching/fresh-XOR argument in Theorem 3.2 preserves the target/reply law, including the inactive phase. Its address is $B_{j,\alpha}$ or $B_{j,\alpha}+2$, within $[j,j+3]$. Lemma 2.2 gives full same-seed preservation. The lower at $k=1$ is three, giving the remaining equality. $\square$

**Open question 7.2 (Original universal law-only radius growth).** For the complete original problem, does every total-budget-$k$ rule admit an exact full-joint-law representative in a polynomial-in-$k$ radius, or is there a superpolynomial obstruction for law alone? This is Address Open question 5.3 and Stopping Open question 8.1, with their original source, endpoint, clock, fixed public bias, all lawful acquired-record rules, arbitrary unchanged independent seed, actual-call charging, and total-cap quantifiers retained. The established information is now

$$
\rho_{\mathrm{law}}(0;p,j,\nu)=0,\qquad
\rho_{\mathrm{law}}(1;p,j,\nu)=3,\qquad
\rho_{\mathrm{law}}(2;p,j,\nu)=5,
\tag{7.4}
$$

and

$$
2k+1\le\rho_{\mathrm{law}}(k;p,j,\nu)\le2^{k+1}-1
\qquad(k\ge3).
\tag{7.5}
$$

The general question remains open. Theorem 6.1 excludes only continuation of the specified frozen prefix for the specified law. It does not exclude other prefixes or other law-equivalent trees, prove a new universal radius-seven lower bound, establish a superpolynomial obstruction, or settle all-$k$ growth. The original bridge rule itself remains an actual radius-seven representative of its law. The obstruction identifies a concrete compatibility obligation: early placements must leave edges capable of producing the future conditional correlations between previously queried components. Equality of a prefix law alone does not supply that extension.

The exponential whole-oriented-signature requirement in Address Theorem 5.2 is stronger than the objective here. Its witness always has $O=a_0,D=1,N=k$; reading the actual address $j$ exactly $k$ times, paying every occurrence and ignoring all replies before returning $a_0$, gives that same full law at radius zero. Thus the inherited exponential signature obstruction supplies no exponential law-only lower bound. The two-read construction likewise does not preserve the full oriented signature or the potential-reply joint law across incompatible siblings; its executed-law proof is the branch partition in (3.3).

## 8. Attribution and exact boundaries

**Attribution 8.1 (Owning sources and source-bounded increment).** The source comparison consists of the six supplied complete mathematical bodies. Their identities delimit this attribution; their checking dispositions do not replace any proof.

| Owning source | Content used and ownership |
| --- | --- |
| *FIB harmonic-edge load: fixed-state tail nonuniformity and an erasure-risk jump*, Proposition 2.1, (2.2), Definition 9.1, (9.4), Theorems 12.2–12.3 | Original stationary source, complete acquired-record semantics, actual endpoint table, semantic finite trees, finite source sections, signature sufficiency, and measurable same-given-seed representation. Lemmas 2.1–2.2 reproduce the needed interfaces. |
| *FIB paid reads: return mass and hidden-endpoint classification risk*, Definitions 1.2–1.3 and Section 6 | All-call charging and the distinction between total count and return-restricted risk quantities. Its risk bounds are not address arguments. |
| *FIB finite paid reads: explicit address compression and the exact whole-signature radius*, Lemmas 3.1–3.2, Theorems 4.1 and 5.2, Open question 5.3 | Target-fixing component packing, exponential universal upper, stronger signature comparison and original unresolved universal radius target. These remain inherited. |
| *FIB stopping-law rigidity and sharp linear address radius*, Theorems 3.2, 4.1, 5.1, Corollary 6.1 and Theorem 6.2 | Stopping witness full law, law-forced stopping/path detachment, exact witness radius $2k+1$, universal linear lower, and zero/one-budget values. Proposition 4.1 is the complete inherited $k=2$ instance; Proposition 7.1 retains the general arguments. |
| Supplied two-read proposal, N1, “Exact universal law-only radius at budget two”; independent two-read check, N1 proofs | The unordered two-edge placement and universal upper matching the inherited lower five. Lemma 3.1 and Theorems 3.2, 4.2 give the complete ordinary exposition. |
| Supplied two-read proposal, N2, “A full-law three-read obstruction to freezing the canonical two-read placement”; independent two-read check, N2 proofs | The precise bridge witness, equivalent canonical two-query prefix, and no-continuation result under the full-law objective. Propositions 5.1–5.2 and Theorem 6.1 carry the complete proofs. |

The increment relative to the four prior theory sources is the universal budget-two upper and the stated full-law frozen-prefix extension obstruction. This volume presents the supplied N1/N2 mathematics with its own complete exposition, retaining proposal ownership. The lower bound used to make the value exact is inherited. Finite iid products, XOR symmetry, elementary integer-line geometry, and product-measure integration are ordinary mechanisms, without a claim of new general methods. The results are `repo-derived` relative to these supplied sources; global novelty is unverified. The source-based overlap comparison does not establish external-literature absence or worldwide priority, and nested references are not independently certified here.

**Boundary 8.2 (Law, parameters, and effectivity).** Every strict obstruction is at each single fixed $0<p<1$, $p\ne1/2$, even against competitors using that public bias. At fairness (4.5), (7.3), and (6.5) lose the needed strictness and (6.3) becomes symmetric; at parameter endpoints the positive stopping masses disappear. Those parameters are outside the stated contract. No parameter-varying identity or joint measurability in $p$ is a premise.

The full-law upper includes nonreturn terminals at every possible paid depth. The stopping and bridge competitors also initially allow nonreturn; their required $D=1$ laws exclude it on positive-mass sections. Exceptional source and seed paths remain subject to the hard total cap. Every repetition and separator remains a paid node. Full-law equality is neither equality of records nor equality on each original realized source sample; finite numerical return times are not preserved statistics.

For a supplied finite tree with all finite-return and internal-nonreturn terminals specified, the two-edge table is an explicit finite relabelling. The semantic reduction of a general measurable rule and its same-seed lift are existence arguments. They do not decide divergence of arbitrary code, compute a selector for arbitrary presentations of seed spaces, or supply an effective arbitrary-code compiler.

**Boundary 8.3 (Remaining resources and goals).** Address radius is distinct from internal computation, address encoding, precision, persistent state, memory, physical storage, numerical return time, and expected paid-cost optimization; no bounds for these follow. No empirical-learning, neural, kernel, expected-cost-only, unbounded-history, or numerical larger-budget risk-frontier conclusion is asserted. Original Open Problem 6.4 on arbitrary-finite hidden attainment and separation is unchanged. The broader autonomous research objective is not completed by this bounded partial result.

All substantive proofs are ordinary arguments in this source. They rely on the stated finite products, source sections, and measurable integration, without mathematical execution, numerics, enumeration, experiments, or formal certification as evidence.

## 追加锚（本行以下为增补区）

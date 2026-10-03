# Greedy-brick rest histories and the successor birth band

## 1. States, histories and event laws

**定义 1.1（Finite rest state and first-zero transition）。** A rest state is a pair $s=(N,c)$ with $N\in\mathbb N$ and a finite list $c$ of natural numbers, every entry of which is at most $N$. Write $\ell(s)$ for the length of $c$ and $c_i(s)$ for its entry at list index $i-1$, defined only when $1\le i\le\ell(s)$. An assertion $c_i(s)=a$ includes existence of that entry; no value is assigned to an absent coordinate. Natural subtraction is truncated at zero.

A first-zero transition $R(s,t,k)$, where $s=(N,c)$, $t=(N',c')$ and $k\in\mathbb N$, has all the following conditions. Its label satisfies $0<k\le\ell(s)+1$, its endpoint is $N'=N+k$, and its height is $\ell(t)=\max(\ell(s),k)$. Every old coordinate $i<k$ is positive and satisfies $c_i(t)=c_i(s)-1$. If $k\le\ell(s)$, then $c_k(s)=0$. The selected coordinate satisfies $c_k(t)=N'$, and every old coordinate $i>k$ satisfies $c_i(t)=c_i(s)$. Thus $k$ is the least zero coordinate when one exists, and otherwise $k=\ell(s)+1$. These conditions describe a relation on finite lists, independently of a geometric brick construction.

**定义 1.2（Rest history and initialized unbounded trace）。** A rest history $T$ consists of states $s_t$ and labels $k_t$, indexed by all $t\in\mathbb N$, with $R(s_t,s_{t+1},k_{t+1})$ for every $t$. A bare history imposes no condition on $s_0$ or $k_0$. An initialized unbounded rest trace is a rest history with $s_0=(1,[1])$, $k_0=1$, and

$$
\forall h\in\mathbb N\quad\exists t\in\mathbb N\quad h\le\ell(s_t).
$$

Unbounded height and initialization are hypotheses on the supplied trace. They do not assert the existence of such a trace from any particular brick-placement rule. The motivating rule is the highest-eligible-row process in [OEIS A395531](https://oeis.org/A395531), with row conventions related to [A233380](https://oeis.org/A233380); no identification of its sequence with the endpoints below is assumed or concluded here.

**定义 1.3（Finite higher-event budget）。** For a rest history and $i,e,d\in\mathbb N$, put

$$
Q_T(i,e,d)=\{q\in\mathbb N:q<d,\ i<k_{e+q+1}\}.
$$

This set counts higher-label transitions among the next $d$ transitions after event $e$.

**定义 1.4（Abstract event sequence）。** An event sequence $E$ consists of five functions $n,k,H,\beta,p:\mathbb N\to\mathbb N$, called endpoint, bin label, height, birth index and predecessor. Define a renewal at $t$ by $t\ne\beta(k_t)$, and put

$$
\mathcal R_E(i,t)=\{g\in\mathbb N:g<t,\ i<k_g,\ g\ne\beta(k_g)\},
\qquad \rho_i(t)=|\mathcal R_E(i,t)|.
$$

The endpoint $n_t$ is distinct from the chronological event index $t$. A birth endpoint is $b_h=n_{\beta(h)}$.

**假设 1.5（Event laws）。** The predicate $\mathcal L(E)$ requires all the following laws. For every $t\in\mathbb N$, $0<k_t\le H_t$, the function $H$ is nondecreasing, and $n_{t+1}=n_t+k_{t+1}$. For every positive $h\in\mathbb N$, $H_{\beta(h)}=h$, $k_{\beta(h)}=h$, and for every $t\in\mathbb N$,

$$
H_t<h\quad\Longleftrightarrow\quad t<\beta(h).
$$

For every renewal $f$, $p_f<f$ and $k_{p_f}=k_f$, and every $g$ with $p_f<g<f$ satisfies $k_g\ne k_f$. Finally, for every renewal $f$, the exact reset balance is

$$
n_{p_f}+H_{p_f}+\rho_{k_f}(p_f)
=H_f+\rho_{k_f}(f).
$$

There is no successor-existence law, band inequality or counting reciprocity among these assumptions. Values of $\beta(0)$ and predecessors at nonrenewals have no prescribed properties.

**定义 1.6（Event sequence of a supplied trace）。** For an initialized unbounded trace $T$, let $E_T$ have $n_t$ equal to the endpoint of $s_t$, $k_t$ equal to its supplied label, and $H_t=\ell(s_t)$. Define

$$
\beta(h)=\min\{t:h\le H_t\},
\qquad
p_f=\max\{e:e\le f-1,\ k_e=k_f\},
$$

where the maximum is zero if the displayed finite set is empty. The minimum exists by unboundedness, including at $h=0$. When a later same-bin event exists, define $\sigma_T(e)=\min\{f:e<f,\ k_f=k_e\}$. Theorem 2.2 supplies its existence for every event of every initialized unbounded trace. These minima and maxima are the actual chronological selections from the supplied history.

## 2. Coordinate budgets, event realization and the birth band

**定理 2.1（No-reset coordinate budget）。** For every rest history $T$ and every $i,e,d,c\in\mathbb N$, if $0<i$, $c_i(s_e)=c$, and every $g$ with $e<g\le e+d$ has $k_g\ne i$, then there exists $r\in\mathbb N$ such that

$$
\begin{aligned}
c_i(s_{e+d})&=r,\\
r+|Q_T(i,e,d)|&=c,\\
\ell(s_{e+d})&\le\ell(s_e)+|Q_T(i,e,d)|.
\end{aligned}
$$

证明。Induct on $d$. At $d=0$, take $r=c$. For the next transition write $k=k_{e+d+1}$ and assume the induction hypothesis with remaining capacity $r$. The coordinate still exists by that hypothesis. The no-reset premise excludes $k=i$.

If $i<k$, prefix positivity gives $r>0$, and prefix decrement leaves $r-1$. The new higher-event set has one additional member, so $(r-1)+(|Q_T(i,e,d)|+1)=c$. The new height is at most the old height plus one, because $k\le\ell(s_{e+d})+1$. This proves the height bound in this case. If $k<i$, the suffix is unchanged. Since $i\le\ell(s_{e+d})$, the selected label is within the old height, so the height is unchanged as well. The higher-event count is unchanged. These two cases give all three conclusions and maintain existence of the coordinate. $\square$

**定理 2.2（Future occurrence of every actual bin）。** For every initialized unbounded rest trace $T$ and every $e\in\mathbb N$, there exists $f\in\mathbb N$ with $e<f$ and $k_f=k_e$.

证明。Initialization and the transition laws give $0<k_t\le\ell(s_t)$ for every $t$. Heights are nondecreasing because each transition replaces the old height by its maximum with the new label. Fix $e$, put $i=k_e$, and let $c=c_i(s_e)$, which exists. Suppose that no later event has label $i$.

Choose $n$ with $\ell(s_n)\ge\ell(s_e)+c+1$, using unboundedness. Height monotonicity forces $n\ge e$. Apply Theorem 2.1 with $d=n-e$. Its budget equality implies $|Q_T(i,e,d)|\le c$, whereas its height bound gives $\ell(s_n)\le\ell(s_e)+c$. This contradicts the choice of $n$. The argument applies to event zero and to births as well as renewals. $\square$

**定理 2.3（Realization of all event laws）。** For every initialized unbounded rest trace $T$, the event sequence $E_T$ of Definition 1.6 satisfies the complete predicate $\mathcal L(E_T)$ of Assumption 1.5.

证明。Positive labels, labels bounded by current height, nondecreasing heights and the endpoint increment law follow from initialization and the transition relation. Leastness of $\beta(h)$ and height monotonicity give the strict birth cut. At a positive birth $\beta(h)$, the height is exactly $h$ and the label is $h$: if the birth index is zero, initialization forces $h=1$; otherwise the preceding height is below $h$, and the next height can rise by at most one, only by selecting the new label. For a renewal $f$, the birth of its label occurs no later than $f$, and differs from $f$, so it is strictly earlier. The greatest earlier same-bin index therefore exists, is less than $f$, has label $k_f$, and has no intervening event of that label. This establishes every chronological law.

It remains to derive reset balance rather than assume it. Define

$$
A_i(t)=|\{g:g<t,\ i<k_g\}|.
$$

For every event $t$ of label $i$, higher events strictly before $t$ split into births and renewals. There is exactly one higher birth at each label $i+1,\ldots,H_t$. Indeed the strict cut puts its birth no later than $t$; equality is excluded because $k_t=i$. Conversely every higher birth before $t$ has label at most $H_t$. Distinct births have distinct labels. Consequently

$$
A_i(t)=H_t-i+\rho_i(t).
$$

Now fix a renewal $f$, and set $e=p_f$, $i=k_f$. Immediately after $e$, coordinate $i$ has capacity $n_e$: for $e=0$ this is initialization, and otherwise it is the reset clause of the transition ending at $e$. Immediately before $f$, that coordinate exists and is zero by monotonicity of height and the first-zero clause. There is no reset of it between these two times. Theorem 2.1 on the interval ending at $f-1$ therefore shows that precisely $n_e$ higher events occur strictly between $e$ and $f$. Since both endpoints have label $i$,

$$
A_i(f)=A_i(e)+n_e.
$$

Substitute the birth-renewal decomposition at $e$ and $f$. Since $i\le H_e\le H_f$, the truncated subtractions can be canceled to give

$$
n_e+H_e+\rho_i(e)=H_f+\rho_i(f).
$$

This is the final field of $\mathcal L(E_T)$. $\square$

**定理 2.4（Successor and predecessor inverse laws）。** For every initialized unbounded rest trace $T$, with $E=E_T$ and $\sigma=\sigma_T$, the following conjunction holds:

$$
\begin{aligned}
&\forall e\in\mathbb N,\quad
e<\sigma(e)\ \land\ k_{\sigma(e)}=k_e
\ \land\ \sigma(e)\ne\beta(k_{\sigma(e)})
\ \land\ p_{\sigma(e)}=e\\
&\hspace{30mm}\land\
\bigl(\forall g\in\mathbb N,\ e<g\Rightarrow g<\sigma(e)\Rightarrow k_g\ne k_e\bigr),\\
&\forall f\in\mathbb N,\quad f\ne\beta(k_f)\Rightarrow\sigma(p_f)=f.
\end{aligned}
$$

证明。Theorem 2.2 makes every $\sigma(e)$ defined. Its leastness gives $e<\sigma(e)$, equality of labels, and absence of an intervening event with that label. By Theorem 2.3 the birth of $k_e$ is no later than $e$, so $\sigma(e)$ is a renewal. The greatest earlier same-bin index at $\sigma(e)$ is at least $e$; if it were greater than $e$, it would be an intervening event, contradicting leastness. Thus $p_{\sigma(e)}=e$.

Conversely, for a renewal $f$, the event $f$ is a later same-bin candidate after $p_f$, so $\sigma(p_f)\le f$. A strict inequality would produce an event of label $k_f$ strictly between $p_f$ and $f$, contradicting the predecessor law from Theorem 2.3. Hence equality holds. No event is excluded from the first universal statement. $\square$

**定理 2.5（Successor birth band for abstract event laws）。** For every event sequence $E$, every instance of $\mathcal L(E)$, every $f\in\mathbb N$ with $f\ne\beta(k_f)$, and $e=p_f$, $h=H_e$, the conclusion is

$$
n_{\beta(h)}\le H_f<n_{\beta(h+1)}.
$$

证明。Endpoints are nondecreasing by their positive increments, every height is positive, and the strict birth cut gives $\beta(H_t)\le t$ for every $t$. Immediate predecessors of renewals are injective: if two distinct renewals had the same predecessor, their labels would agree, and the earlier renewal would lie strictly between that predecessor and the later renewal, contrary to immediacy.

Prove the lower bound by strong induction on the chronological renewal index $t$. Suppose it fails at a renewal $t$, and put $e=p_t$, $i=k_t$, $h=H_e$, $K=H_t$. Thus $K<n_{\beta(h)}$, $e<t$, and $0<i\le h\le K$. For every higher-bin renewal $g<t$, induction gives

$$
n_{\beta(H_{p_g})}\le H_g\le K<n_{\beta(h)}.
$$

The birth cut implies that positive birth indices are nondecreasing in their height parameter. Endpoint monotonicity then forces $H_{p_g}<h$, and hence $p_g<\beta(h)$. Its label is $k_g>i$. The injective predecessor map therefore sends $\mathcal R_E(i,t)$ into

$$
S=\{g:g<\beta(h),\ i<k_g\}.
$$

Births in $S$ inject by their labels into $\{i+1,\ldots,h-1\}$, giving at most $h-i$ of them. Renewals in $S$ are counted among $\mathcal R_E(i,e)$ because $\beta(h)\le e$. Thus

$$
\rho_i(t)\le |S|\le h-i+\rho_i(e).
$$

Reset balance now gives $n_e+h\le K+h-i$, hence $n_e+i\le K$. But endpoint monotonicity gives $n_{\beta(h)}\le n_e$, while $K<n_{\beta(h)}$ and $i>0$. This is impossible, proving the lower bound.

For the upper bound return to $f$ and $e=p_f$, $h=H_e$, $i=k_f$. Since $e<f$, higher-renewal counts are nondecreasing from $e$ to $f$. Reset balance gives $H_f\le n_e+h$. Put $q=\beta(h+1)$. The strict birth cut gives $e<q$, so $q>0$ and $e\le q-1$. The endpoint step and birth-label law yield

$$
n_q=n_{q-1}+h+1\ge n_e+h+1>H_f.
$$

This establishes the strict upper bound. The proof uses only $\mathcal L(E)$, and does not assume existence of later same-bin events or any reciprocity identity. Applied inside the trace setting, Theorems 2.3 and 2.4 supply these hypotheses for the renewal $\sigma_T(e)$ without adding a separate theorem. $\square$

## 追加锚（本行以下为增补区）

## 3. Literal placements and finite capacities

The placement convention in this section follows the brick rule and Python row generator of [OEIS A395531](https://oeis.org/A395531), with the row conventions of [OEIS A233380](https://oeis.org/A233380). The transfer, conjugacy, geometric correspondence and clock arguments below are deductions from that rule. Bricks have widths $1,2,3,\ldots$ and unit height. All natural-number subtractions are truncated at zero. None of these statements asserts the OEIS self-composition identity or weighted counting reciprocity.

**定义 3.1（Top-first capacities and the literal scan）。** Lists in this section are ordered from top to bottom. For a natural brick width $n$, define the transfer $F_n(c)=(d,b)$, where $b$ is a Boolean carry, by

$$
\begin{aligned}
F_n([])&=([],\mathrm{true}),\\
F_n(a::c)&=((a-n)::c,\mathrm{true}) &&(n\le a),\\
F_n(a::c)&=((a+n)::d,\mathrm{false}) &&(n>a,\ F_n(c)=(d,\mathrm{true})),\\
F_n(a::c)&=(a::d,\mathrm{false}) &&(n>a,\ F_n(c)=(d,\mathrm{false})).
\end{aligned}
$$

Put $S_n(c)=n::d$ if $F_n(c)=(d,\mathrm{true})$, and $S_n(c)=d$ otherwise. Define the literal trajectory by $C_0=[]$ and $C_{N+1}=S_{N+1}(C_N)$. Its weighted area and reconstructed widths are

$$
A([])=0,\qquad A(a::c)=(|c|+1)a+A(c),\qquad
W([])=[],\qquad W(a::c)=a::(a+W(c)),
$$

where addition to a list acts entrywise. The inverse gap map is $G([])=[]$ and $G(w::v)=w::G(v-w)$, with entrywise natural subtraction.

Define the existing-row scan $E_n([])=[n]$, $E_n([w])=[w+n]$, and

$$
E_n(w::v::u)=
\begin{cases}
(w+n)::v::u,&w+n\le v,\\
w::E_n(v::u),&w+n>v.
\end{cases}
$$

The complete row scan is $P_n([])=[n]$ and

$$
P_n(w::u)=\begin{cases}n::w::u,&n\le w,\\E_n(w::u),&n>w.\end{cases}
$$

It tests a supported new top row first, and otherwise extends the first supported existing row while scanning downwards; the floor is always available. Zero gaps are permitted. There is no floor capacity and no assigned birth time for an absent row.

**定理 3.2（One-step capacity invariants）。** For every $n\in\mathbb N$ with $n>0$ and every finite natural list $c$ whose entries are at most $2n-1$,

$$
|c|\le |S_n(c)|\le |c|+1,\qquad
\forall a\in S_n(c),\ a\le2n-1,\qquad
A(S_n(c))=A(c)+n.
$$

证明。Induction on the input list gives, for $F_n(c)=(d,b)$, the same length and capacity bound and the identity

$$
A(d)+\begin{cases}|c|n,&b=\mathrm{true},\\0,&b=\mathrm{false}\end{cases}
=A(c)+\begin{cases}0,&b=\mathrm{true},\\n,&b=\mathrm{false}.\end{cases}
$$

At a donor $a\ge n$, subtracting $n$ preserves the cap and the area loss is its row weight times $n$. If the recursive tail carries, the preceding ineligible capacity $a<n$ receives $n$, remains at most $2n-1$, and cancels all but one unit of that weighted loss. If it does not carry, that capacity is unchanged. The empty tail is the floor case. A final carry adds one top row of capacity $n$; without it the length is unchanged. Substitution in the displayed transfer identity proves the area increment. $\square$

**定理 3.3（Reachable capacity and area invariants）。** For every $N\in\mathbb N$,

$$
\forall a\in C_N,\ a\le2N-1,\qquad
A(C_N)=\sum_{i=0}^{N}i,\qquad
|C_N|\le|C_{N+1}|\le|C_N|+1.
$$

证明。At zero the list is empty and the sum vanishes. The cap $2N-1$ implies the cap $2(N+1)-1$ required to apply Theorem 3.2 at width $N+1$. Its area increment, together with the induction hypothesis and the last term of the sum, gives the next exact area. Applying that same step to $C_N$ gives both height inequalities. $\square$

**定理 3.4（Positive reconstructed rows and inverse gaps）。** For every positive $N\in\mathbb N$, the list $W(C_N)$ has length $|C_N|$, is pairwise nondecreasing from top to bottom, has sum $A(C_N)$, satisfies $G(W(C_N))=C_N$, and every one of its entries is positive.

证明。Induction on an arbitrary capacity list proves length preservation, pairwise order and the area identity: adding a top capacity $a$ adds $a$ to every lower reconstructed width, so its contribution is $(|c|+1)a$. Another list induction proves the inverse, since subtracting the initial $a$ from every lower width recovers exactly $W(c)$. The top capacity of $C_1$ is one. At a later step it either becomes the positive new label, remains a previous positive top capacity, or increases by the new label. Hence it stays positive. Every lower reconstructed width includes that positive top capacity, proving positivity of all widths. $\square$

**定理 3.5（Actual least births with an explicit bound）。** For every $m\in\mathbb N$ with $1\le m$, there exists $B\in\mathbb N$ such that

$$
B>0,\qquad |C_B|=m,\qquad
\forall K<B,\ |C_K|<m,\qquad
B\le\begin{cases}1,&m=1,\\2m(m-1)-1,&m\ne1.\end{cases}
$$

证明。For a list of height $h$ with all capacities at most $q$, list induction gives $A(c)\le qh(h+1)/2$. At a positive endpoint $N$, Theorem 3.3 and this inequality give

$$
N(N+1)=2A(C_N)\le (2N-1)h(h+1)<2Nh(h+1),
\qquad h=|C_N|.
$$

The strict inequality holds because the area is positive and thus $h(h+1)>0$. Cancel $N>0$ to obtain $N+1<2h(h+1)$. For $m\ge2$, put $D=2m(m-1)-1>0$. If $|C_D|\le m-1$, the obstruction gives $D+1<2m(m-1)=D+1$, a contradiction. For $m=1$, $C_1=[1]$ supplies the crossing. Choose the least endpoint $B$ with height at least $m$. It is positive because $C_0=[]$; the height at $B-1$ is less than $m$, and the one-step upper bound makes the height at $B$ exactly $m$. Leastness supplies both minimality and the explicit bound. $\square$

**定理 3.6（Exact conjugacy of the row and capacity scans）。** For every positive $n\in\mathbb N$ and every finite natural capacity list $c$,

$$
W(S_n(c))=P_n(W(c)).
$$

证明。Induct on the tail capacities with an arbitrary common offset $a$. If $F_n(d)=(v,\mathrm{true})$, then

$$
E_n(a::(a+W(d)))=(a+n)::(a+n+W(v));
$$

if its carry is false, the result is $a::(a+W(v))$. At a tail donor $b\ge n$, eligibility is $a+n\le a+b$, and $a+n+(b-n)=a+b$ restores all lower widths. For $b<n$, the row scan descends and the induction hypothesis applies with offset $a+b$. These cases prove the offset identity. For the full list, a top donor produces a new row of width $n$ and leaves the previous top width unchanged after reconstruction; an ineligible top invokes the offset identity. The empty list gives $[n]$ on both sides. No reachability or capacity bound is needed. $\square$

## 4. Integer cells and labelled real rectangles

**定义 4.1（Cells, supported frontiers and exact addition）。** For a top-first width list $w$, let $O_w(u,y)$ denote occupancy of the natural cell $(u,y)$, recursively defined by $O_{[]}(u,y)$ false and

$$
O_{a::v}(u,y)\ \Longleftrightarrow\ (y=|v|\ \land\ u<a)\ \lor\ O_v(u,y).
$$

An existing-row frontier at $(x,y)$ for width $n$ is specified recursively: there is none in $[]$; for $[a]$ it is $x=a,y=0$; for $a::b::v$ it is either $x=a,y=|v|+1,a+n\le b$, or an existing-row frontier in $b::v$. A placement frontier additionally permits $x=0,y=|w|$ when $w=[]$ or its first width is at least $n$.

A legal cell brick at $(x,y)\in\mathbb N^2$ satisfies, for every natural $u$ in $[x,x+n)$, nonoccupancy $\neg O_w(u,y)$ and, unless $y=0$, support $O_w(u,y-1)$. It also satisfies $x=0$ or $O_w(x-1,y)$. An exact brick addition from $w$ to $v$ requires these same three constraints and, for all natural $u,z$,

$$
O_v(u,z)\ \Longleftrightarrow\ O_w(u,z)\ \lor\ (z=y\ \land\ x\le u<x+n).
$$

**定理 4.2（The scan is the leftmost highest legal cell addition）。** For every positive natural $n$ and every pairwise nondecreasing natural width list $w$, there exist natural $x,y$ that form a placement frontier, such that every legal cell competitor $(x',y')$ satisfies $x\le x'$ and $y'\le y$, and the transition from $w$ to $P_n(w)$ is an exact brick addition at $(x,y)$.

证明。Induction on the row list shows that no occupied cell lies at or above its length, and that the top row at height $|v|$ of $a::v$ has exactly the cells $u<a$. Every legal position is an enumerated frontier: below the top row apply the tail induction; on that row, nonoverlap and left contact force $x=a$ and support forces $a+n$ below the supporting width; above it, support forces exactly one new top row at $x=0$. For the existing-row scan, the floor case extends $[a]$. If $a+n\le b$, extend the top row: all lower frontiers have horizontal endpoint at least $a$ by pairwise order and smaller height. Otherwise that frontier is impossible and the tail induction supplies the optimum. The exact occupied-cell equivalence follows by splitting the extended row interval at $a$; lower rows are unchanged, and support and contact follow from eligibility. Finally, when a new top row is eligible its position $(0,|w|)$ dominates all existing frontiers; otherwise the existing-row result applies. $\square$

**定义 4.3（Real wall and physical competitors）。** The row endpoint $r_w(y)$ is zero for an empty list and otherwise is $a$ when $w=a::v$ and $y=|v|$, and $r_v(y)$ in all other cases. For real $t,z$, define

$$
\mathcal W_w(t,z)\ \Longleftrightarrow\
\exists y\in\mathbb N,\ y\le z<y+1\ \land\ 0\le t<r_w(y).
$$

The width-$n$ rectangle at a real position $(x,y)$ is $\mathcal B_n(x,y)=[x,x+n)\times[y,y+1)$. A physical row placement is legal when $x,y\ge0$, its rectangle is disjoint from $\mathcal W_w$, and either $y=0$ or there is $k\in\mathbb N$ with $y=k+1$ and every $t\in[x,x+n)$ satisfies $t<r_w(k)$. No left-contact constraint is imposed. A physical row optimum is a legal position $(x,y)$ with $x\le x'$ and $y'\le y$ for every legal real competitor $(x',y')$.

**定理 4.4（Continuous row geometry）。** For every positive natural $n$ and every pairwise nondecreasing natural width list $w$, there exist natural $x,y$ forming a placement frontier that are a physical row optimum when regarded as real coordinates, and for all real $t,z$,

$$
\mathcal W_{P_n(w)}(t,z)\ \Longleftrightarrow\
\mathcal W_w(t,z)\ \lor\ (t,z)\in\mathcal B_n(x,y).
$$

证明。The cell and real slices satisfy

$$
\mathcal W_w(t,z)\ \Longleftrightarrow\
0\le t\ \land\ 0\le z\ \land\ O_w(\lfloor t\rfloor,\lfloor z\rfloor).
$$

At natural endpoints, the same floor identities characterize rectangle membership. A legal real competitor has integer height $q$, by its floor-or-upper-face support condition. Nonoverlap forces $r_w(q)\le x'$, since otherwise the point $(x',q)$ belongs to both the competitor and the old wall. Support implies $x'+n\le r_w(q-1)$ when $q>0$: a contrary inequality supplies a point in the proposed bottom interval beyond the supporting row. Thus $(r_w(q),q)$ is a legal cell frontier with endpoint no greater than $x'$. Theorem 4.2 gives the required ordering against it and hence against every real competitor. Its natural chosen position is physically legal by the floor-slice identities and integer support. Those identities also transport the exact cell update to the displayed real union. $\square$

**定义 4.5（Actual labelled unions and support）。** For a position function $p:\mathbb N\to\mathbb N^2$, let

$$
\mathcal U_{p,N}(t,z)\ \Longleftrightarrow\
\exists i\in\mathbb N,\ 0<i\le N\ \land\ (t,z)\in\mathcal B_i(p_i^x,p_i^y).
$$

A legal history placement of width $n$ at real $(x,y)$ after endpoint $N$ has $x,y\ge0$, its rectangle disjoint from $\mathcal U_{p,N}$, and either $y=0$ or every $t\in[x,x+n)$ lies on an earlier brick's half-open upper face: some $0<i\le N$ satisfies $p_i^y+1=y$ and $p_i^x\le t<p_i^x+i$. A history optimum is a legal history placement with $x\le x'$ and $y'\le y$ against every such real competitor. Closed bottom support requires either $y=0$ or, for every $t\in[x,x+n]$, an earlier $0<i\le N$ with $p_i^y+1=y$ and $p_i^x\le t\le p_i^x+i$. These conditions refer only to the labelled rectangles already present.

**定理 4.6（One actual labelled history for every finite prefix）。** There exists one function $p:\mathbb N\to\mathbb N^2$ such that, simultaneously,

$$
\begin{aligned}
&\forall N\in\mathbb N\ \forall t,z\in\mathbb R,\quad
\mathcal W_{W(C_N)}(t,z)\ \Longleftrightarrow\ \mathcal U_{p,N}(t,z),\\
&\forall n\in\mathbb N,\quad n>0\Rightarrow
(p_n^x,p_n^y)\text{ is a history optimum after }N=n-1\text{ for width }n,\\
&\forall n\in\mathbb N,\quad n>0\Rightarrow
(p_n^x,p_n^y)\text{ has closed bottom support after }N=n-1\text{ for width }n,\\
&\forall i,j\in\mathbb N,\quad 0<i<j\Rightarrow
\forall t,z\in\mathbb R,\quad
(t,z)\in\mathcal B_i(p_i^x,p_i^y)\Rightarrow
(t,z)\notin\mathcal B_j(p_j^x,p_j^y).
\end{aligned}
$$

证明。Theorem 3.4 gives ordered widths at every positive endpoint, and the empty endpoint is ordered as well. Choose the natural optimum of Theorem 4.4 for width $N+1$ above $W(C_N)$ and set it to be $p_{N+1}$; the value at zero is immaterial. Theorem 3.6 transports that theorem's union to $W(C_{N+1})$. Induction on $N$ therefore proves the exact labelled-union identity.

Using that same identity, history legality is equivalent to row legality. In one direction an old supporting brick identifies an integer upper-face height, and every supporting point is in the corresponding occupied row. Conversely a supporting row point lies in the labelled union, whose rectangle containing it has exactly the required row height. This proves both support directions, without substituting an optimum as a legality premise. Thus each chosen position is a history optimum. An earlier rectangle belongs to the preceding union for any later label, so that later placement's nonoverlap proves the final disjointness statement. For closed support, the half-open support already covers every point short of the new right endpoint. Cover the point half a unit before that endpoint by an old supporting brick. Its integer right endpoint must extend at least to the new integer endpoint, and its left endpoint is no larger, supplying the missing closed endpoint. $\square$

## 5. Literal rest blocks and a cofinal clock

**定义 5.1（Least zero and the literal block）。** For a bottom-first capacity list $c$, put $Z([])=1$ and $Z(a::c)=1$ if $a=0$, and $Z(c)+1$ otherwise. Thus $Z(c)$ is the one-based least zero bin, or $|c|+1$ when every old entry is positive. For an arbitrary top-first list $v$, define successive literal placements by

$$
L(N,v,0)=v,\qquad L(N,v,k+1)=L(N+1,S_{N+1}(v),k).
$$

Define the bottom-first candidate rest update by $D_N([])=[N+1]$ and

$$
D_N(a::c)=\begin{cases}(N+1)::c,&a=0,\\(a-1)::D_{N+1}(c),&a>0.\end{cases}
$$

Reversal of a list is denoted $\operatorname{rev}$. The rest-state and transition relation retain exactly Definition 1.1.

**定理 5.2（Literal realization of a first-zero rest block）。** For every rest state $s=(N,c)$, there exists a rest state $t$ such that

$$
R(s,t,Z(c))\qquad\text{and}\qquad
L(N,\operatorname{rev}(c),Z(c))=\operatorname{rev}(\operatorname{capacity}(t)).
$$

证明。An ineligible top prefix passes through a transfer whose tail has no carry. Induct on a bounded bottom-first list to prove the relay identity, for $a>0$ and every lower list $v$,

$$
L(N,\operatorname{rev}(c)\mathbin{+\!+}((N+a)::v),Z(c))
=\operatorname{rev}(D_N(c))\mathbin{+\!+}((a-1)::v),
$$

where $+\!+$ denotes list concatenation and every entry of $c$ is at most $N$. The next width $N+1$ skips all those bounded higher bins, subtracts from the donor $N+a$, and transfers to its immediate recipient. A zero recipient ends the relay; a positive one enables the induction at endpoint $N+1$. The floor version of this argument gives $L(N,\operatorname{rev}(c),Z(c))=\operatorname{rev}(D_N(c))$.

A separate induction on $c$ shows $0<Z(c)\le|c|+1$, that the target entries are at most $N+Z(c)$, and that its height is $\max(|c|,Z(c))$. Every earlier bin was positive and decreases by one, the selected old bin was zero if present and resets to $N+Z(c)$, and every higher bin is unchanged. Hence $t=(N+Z(c),D_N(c))$ is a rest state and satisfies every clause of $R$. The floor realization above supplies the second conclusion, including the empty-list and first-bin cases. $\square$

**定理 5.3（Initialized unbounded literal trace and exact clock coupling）。** There exists an initialized unbounded rest trace $T$, with states $s_e$ and labels $k_e$ as in Definition 1.2, satisfying all six assertions below:

$$
\begin{aligned}
&\forall e\in\mathbb N,\quad k_{e+1}=Z(\operatorname{capacity}(s_e)),\\
&\forall e\in\mathbb N,\quad
\operatorname{rev}(\operatorname{capacity}(s_e))=C_{\operatorname{endpoint}(s_e)},\\
& e\longmapsto\operatorname{endpoint}(s_e)\text{ is strictly increasing},\\
&\forall N\in\mathbb N,\quad\exists e\in\mathbb N,\ N\le\operatorname{endpoint}(s_e),\\
&\forall e,d\in\mathbb N,\quad
L(\operatorname{endpoint}(s_e),\operatorname{rev}(\operatorname{capacity}(s_e)),d)
=C_{\operatorname{endpoint}(s_e)+d},\\
&\forall N\in\mathbb N,\quad 1\le N\Rightarrow
\exists e,d\in\mathbb N,\quad d<k_{e+1}\ \land\
N=\operatorname{endpoint}(s_e)+d\ \land\
C_N=L(\operatorname{endpoint}(s_e),\operatorname{rev}(\operatorname{capacity}(s_e)),d).
\end{aligned}
$$

证明。Start with $s_0=(1,[1])$ and $k_0=1$. Choose the successor supplied by Theorem 5.2 at each state and iterate that choice over the natural event indices, setting $k_{e+1}=Z(\operatorname{capacity}(s_e))$. Brick induction gives $L(N,C_N,d)=C_{N+d}$. Event induction using Theorem 5.2 then gives the sampled reversed-capacity equality, starting from $C_1=[1]$. The endpoint increment is the positive label, so endpoints are strictly increasing and cofinal; in particular the endpoint at event $N$ is at least $N$.

Theorem 3.3 makes literal height nondecreasing. For each $h$, Theorem 3.5 supplies a literal endpoint of height $h+1$, and cofinality supplies a sampled endpoint at least that large. Coupling transfers its height to the same rest state. Thus the constructed trace is unbounded, rather than having unboundedness assumed. The brick induction and sampled equality give every intermediate-offset equality.

Finally, for a positive brick $N$, choose the least event $f$ whose endpoint is strictly above $N$. It exists by cofinality and is positive since the initial endpoint is one. Leastness gives $\operatorname{endpoint}(s_{f-1})\le N$. Put $e=f-1$ and $d=N-\operatorname{endpoint}(s_e)$. The endpoint increment gives $d<k_{e+1}$ and the asserted endpoint decomposition, and the intermediate-offset equality gives its literal trajectory value. This proves all six assertions in the same initialized unbounded trace. $\square$

## 追加锚（本行以下为增补区）

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

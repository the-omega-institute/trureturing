# KBonacci forced-prefix parity costs and returning frontiers

## 1. Fixed reader, actual sources, and INITIAL cost

**定义 1.1（Matched complete-block reader）。** Fix integers $k\ge2$ and $m\ge1$. Read binary words from left to right in increasing weight position. A legal word avoids $1^k$. The original weights and value are

$$
G_i=2^i\quad(0\le i<k),\qquad
G_i=\sum_{r=1}^kG_{i-r}\quad(i\ge k),\qquad
V_k(w)=\sum_{i<|w|}w_iG_i.
\tag{1.1}
$$

The legal output is $V_k(w)\bmod2$. Put $T=k+1$ and use the matched coefficient sequence supplied by [S2, Theorem 14.1]:

$$
c_i=G_i\bmod2=\mathbf1_{\{0,-1\}}(i\bmod T).
\tag{1.2}
$$

A legal record is $(v,\theta,s)$, where $v\in\mathbb F_2$, $\theta$ is length modulo $T$, and $0\le s<k$ is the terminal run of ones. Rejection is a separate absorbing record $\bot$, with output different from both values. The literal bit transitions are

$$
\begin{aligned}
\delta_0(v,\theta,s)&=(v,\theta+1,0),\\
\delta_1(v,\theta,s)&=
\begin{cases}
(v\oplus c_\theta,\theta+1,s+1),&s<k-1,\\
\bot,&s=k-1,
\end{cases}
\qquad \delta_b(\bot)=\bot.
\end{aligned}
\tag{1.3}
$$

A block is exactly $m$ bits, composed in their literal order. Only block endpoints are observed. The two control alphabets are all $m$-bit words and all internally legal $m$-bit words, respectively; both use (1.3) at every seam. In the families below $k=Qm$, $Q\ge2$, so $m<k$ and the alphabets contain exactly the same words. Internal legality does not remove the seam obligation.

**定义 1.2（Actual prior and immutable labels）。** The prior consists of all finite actual complete-block histories, including the empty history and rejected histories. A target is a function of the original record. Every terminal leaf returns that record's INITIAL label, even after zeros erase its tail or an input changes its value. It never substitutes the target of the updated record.

The controller reads the initial value or $\bot$ for free. Thereafter it chooses a block or stops using only its acquired endpoint archive. Each emitted complete block costs one, including zero waits. The cost of a controller is the largest emitted block count over all initial histories. Let $C_{\rm ad}$ be the minimum such cost among adaptive controllers, and $C_{\rm pre}$ the minimum when the literal block stream is fixed in advance but stopping and decoding may use the archive. An initially rejected source has its own known label and stops at cost zero. The two free-value fibres can be treated separately; the full cost is their maximum. Offline computation and memory do not count as emitted blocks. Reset, source copying, intermediate observations, a hidden initial clock, and combining readings from different branches are excluded. This is the contract of [S1, Sections 1–2], not a homing or terminal-state objective.

**定义 1.3（Joint actual-source interface）。** In the remainder fix $Q\ge2$, $k=Qm$, $T=Qm+1$, and write

$$
j=-\theta_{\rm INITIAL}\pmod T.
\tag{1.4}
$$

Since $\gcd(m,T)=1$, every triple $(v,-j,s)$ occurs in a single legal complete-block history. The joint realization in [S1, Convention 1.3; S15, equation (1.1)] is explicit: choose

$$
n\equiv0\pmod m,\qquad n\equiv-j\pmod T,\qquad n\ge s+2,
\qquad D=\bigoplus_{i=n-s}^{n-1}c_i,
$$

and take the actual word

$$
(v\oplus D)\,0^{n-s-1}1^s.
\tag{1.5}
$$

The first factor is one bit. At least one zero separates it from the last $s<k$ ones. Its value is $(v\oplus D)\oplus D=v$, its length phase is $-j$, and its tail is $s$. Its length is divisible by $m$, so it splits into actual legal blocks. This supplies every lower-bound source below jointly, rather than asserting independent marginal reachability. The lengths of witnesses for different phases may differ; those lengths are not revealed to the controller.

**定义 1.4（Literal path response）。** Block index $t$ starts at zero: before emitting block $t$, exactly $t$ blocks have been paid on a continuing branch. Put

$$
u_t=tm\pmod T,\qquad W_t=\{u_t,u_t+1,\ldots,u_t+m\}\pmod T,
\tag{1.6}
$$

in the displayed path order. For a successful block $x_0\cdots x_{m-1}$ its endpoint difference, as a function of INITIAL phase, is

$$
\begin{aligned}
q_t(u_t)&=x_0,\\
q_t(u_t+i)&=x_{i-1}\oplus x_i\quad(1\le i<m),\\
q_t(u_t+m)&=x_{m-1},
\end{aligned}
\qquad q_t(j)=0\quad(j\notin W_t).
\tag{1.7}
$$

These are the actual path equations of [S10, Interface 2.1; S15, equations (1.3)–(1.4)]. The total charge is even. Conversely an even full-window prescription determines exactly one literal block:

$$
x_i=\bigoplus_{r=0}^{i}q_t(u_t+r),\qquad0\le i<m.
\tag{1.8}
$$

The last equation in (1.7) holds because the total charge is zero. This inverse also applies to a wrapping path. The equations do not grant arbitrary subset queries: support, even charge, the inverse word, and its literal seam must hold together. All prescriptions used below are inverted by (1.8), and their seams are checked.

## 2. Forced prefixes and sharp first-tour screening

**定义 2.1（Threshold target with a blind band）。** Assume

$$
3\le a<m,\qquad I=\{1,\ldots,a-1\}.
\tag{2.1}
$$

Let $\lambda:I\to Y$ have $N=|\lambda[I]|\ge2$ distinct labels. Choose a low-tail outside label $A$; it may also occur in $\lambda[I]$. Choose $R$ different from $A$ and every label in $\lambda[I]$. On both free-value fibres prescribe

$$
f(v,-j,s)=
\begin{cases}
R,&s\ge k-a,\\
\lambda(j),&s<k-a,\ j\in I,\\
A,&s<k-a,\ j\notin I.
\end{cases}
\tag{2.2}
$$

A band source means a legal INITIAL record with $j\in I$ and $s<k-a$; an outside source means one with $j\notin I$ and $s<k-a$. Sources with higher INITIAL tails are called high-tail sources, including those whose phases lie in $I$. The INITIAL $\bot$ label is separately fixed and known. Put $L=\lceil\log_2N\rceil$. The guard used for the exact cost theorem is

$$
L\le m-a+1.
\tag{2.3}
$$

There is no assertion here for $a=m$.

**定理 2.2（Forced root and first-tour parity obstruction）。** For the target (2.2), every correct controller on either free-value fibre has root prefix $1^a0$. All band sources consequently have the same zero-difference archive through block indices $0,\ldots,Q-1$ and a common current tail. On that archive, complete removal of low-tail sources outside $I$ within these $Q$ blocks is possible if and only if

$$
m\text{ is odd}\quad\text{or}\quad a\text{ is even}.
\tag{2.4}
$$

When $m$ is even and $a$ is odd, every correct controller retains at least one actual outside source there. A common literal scan retains exactly one, at INITIAL phase $m$. In all other cases the same construction retains none. The surviving phase support is thus exactly $I\cup\{m\}$ in the exceptional case, and exactly $I$ otherwise; all its sources have low INITIAL tails.

Proof. The root cannot stop freely: the same free-value fibre has both high-tail label $R$ and low-tail labels. At a fixed phase and value choose actual tails $k-a-1$ and $k-a$, supplied by (1.5). Their labels differ. If the first zero follows $\alpha<a$ ones, both survive to it and become the identical current record, with identical accumulated value. The erased INITIAL distinction cannot be recovered. If $\alpha>a$, both reject before the first endpoint: even the smaller tail reaches $k$ after $a+1$ ones. A root with no zero has $m>a$ leading ones and has the same defect. Thus every correct root has $\alpha=a$. This is the first-zero irreversible-merge principle of [S1, Lemma 4.3 and Theorem 5.2] applied to this target. Exactly the high tails $s\ge k-a$ reject; every lower tail survives the prefix and clears at its zero. The remaining suffix has fewer than $k$ bits, so it cannot reject after that zero.

By (1.7) every such root has

$$
q_0(0)=q_0(a)=1,\qquad q_0(j)=0\quad(j\in I).
\tag{2.5}
$$

After the root the band sources have common current value and tail. For $1\le t<Q$, $W_t=[tm,(t+1)m]$ does not intersect $I$, so their successful differences are zero. Along their shared archive the controller chooses the same input for all of them. Legality depends only on input and current tail, not on phase. Uniform rejection would merge at least two different band labels and cannot be correct. Hence their common zero archive exists through the first tour and cannot stop early.

First prove the obstruction for all roots and all adaptive continuations. Suppose every outside source leaves this archive within $Q$ blocks. Root-only outside phases $0,a,a+1,\ldots,m-1$ must all have root response one; otherwise they remain observationally identical to the band throughout the tour. Even charge then forces

$$
q_0(m)=(m-a+1)\bmod2.
\tag{2.6}
$$

For every subsequent first-tour window write its left and right responses as $\ell_t=q_t(tm)$ and $r_t=q_t((t+1)m)$. Every strictly interior vertex is an outside phase with only this first-tour visit, so its response must be one. Even charge implies

$$
\ell_t\oplus r_t=(m-1)\bmod2.
\tag{2.7}
$$

If $m$ is even and $a$ is odd, (2.6) gives $q_0(m)=0$. To remove phase $m$, the next row must have $\ell_1=1$; (2.7) gives $r_1=0$. To remove phase $2m$, the following row must similarly have $\ell_2=1$, hence $r_2=0$. Continue to the last first-tour window. Its right endpoint $Qm=k$ has response zero, has no later first-tour opportunity, and remains an outside source. This contradicts complete removal. The argument follows one actually acquired zero archive; it does not combine rows from different adaptive branches. The source at any unremoved phase can be chosen with INITIAL tail zero and the same free value as the band sources.

For attainment define the root word $H_{m,a}$ by its bits

$$
(H_{m,a})_i=
\begin{cases}
1,&0\le i<a,\\
(i-a)\bmod2,&a\le i<m.
\end{cases}
\tag{2.8}
$$

It is exactly $1^a0$ followed by alternating bits. Its response is one at $0,a,\ldots,m-1$, zero on $I$, and (2.6) at $m$. For each $1\le t<Q$, emit the same word

$$
M_m=
\begin{cases}
(01)^{m/2},&m\text{ even},\\
(10)^{(m-1)/2}1,&m\text{ odd}.
\end{cases}
\tag{2.9}
$$

For odd $m$ its response is one on all of $W_t$. For even $m$ it is one on $W_t\setminus\{tm\}$. Thus an odd-width scan removes every remaining outside phase, including a root survivor at $m$. At even width all later interiors and right endpoints are removed, and only the root phase $m$ can remain: it remains exactly when $a$ is odd. Phase zero is always removed by the root. Every first positive successful difference has original label $A$, so it may stop immediately; root rejection returns $R$.

The words are complete $m$-bit blocks. The root rejects exactly the prescribed high tails and has a zero; each middle word has a zero. After the root, terminal and leading runs of each word are at most $m-1$, so every interblock run is at most $2m-2<k$. These statements include $Q=2$ and $a=m-1$: there is one middle block, and the root then ends at its first zero. All continuing low-tail sources therefore execute the same legal scan. The all-zero response archive has the exact support asserted, with the original labels still attached. This also proves sufficiency in (2.4). ∎

## 3. Guarded exact total costs and actual attaining streams

**定理 3.1（Guarded forced-prefix cost law）。** Under Definitions 1.1–2.1 and guard (2.3),

$$
C_{\rm ad}(f)=C_{\rm pre}(f)=QL+1+\Delta,
\qquad
\Delta=
\begin{cases}
1,&N=2,\ A\notin\lambda[I],\ m\text{ even},\ a\text{ odd},\\
0,&\text{otherwise}.
\end{cases}
\tag{3.1}
$$

This is a total INITIAL fee, including the root and all emitted waits.

Proof of the lower bounds. Write $t=hQ+b$, $0\le b<Q$. Since $Qm\equiv-1\pmod T$,

$$
W_{hQ+b}=[bm-h,(b+1)m-h]\pmod T.
\tag{3.2}
$$

For $1\le h\le L$, the band lies in $W_{hQ}=[-h,m-h]$: its largest phase is $a-1\le m-L$. For $b\ge1$ and $0\le h\le L-1$, the left endpoint is at least $m-(L-1)\ge a$, while the right endpoint is at most $k<T$. These windows do not wrap into $I$. Thus through index $LQ$ the only potentially informative band endpoints after the forced root are

$$
Q,2Q,\ldots,LQ.
\tag{3.3}
$$

At guard equality the last band phase is the right endpoint of $W_{LQ}$; it is included. Every strictly smaller total budget has at most $L-1$ such endpoints. On the band subprior, all sources in any node have common value and current tail, so a block is either uniformly successful or uniformly rejecting. Rejecting a node with different INITIAL labels cannot help; a successful endpoint gives at most two children. Removing the uninformative single-child nodes leaves a binary tree with at most $2^{L-1}<N$ label leaves. This elementary adaptive-tree count, with the common-tail hypothesis from [S10, Lemma 3.2], excludes every smaller adaptive budget and proves $C_{\rm ad}\ge QL+1$.

If $N=2$ and the exceptional conditions in (3.1) hold, a budget of $Q+1$ leaves just one endpoint after the first tour. Theorem 2.2 guarantees an outside source on the common band archive, and its label $A$ is different from both band labels. These three labels have common current value and tail. One more complete block is either uniform rejection or has at most two successful observations, so it cannot finish. Hence $C_{\rm ad}\ge Q+2$. This is an all-root argument, including arbitrary root suffixes, adaptive actions, and early stopping.

Proof of attainment. First emit the $Q$-block scan

$$
H_{m,a}\mid\underbrace{M_m\mid\cdots\mid M_m}_{Q-1\text{ complete blocks}}.
\tag{3.4}
$$

Use the stopping labels in Theorem 2.2. Let $E$ mean $m$ even and $a$ odd. The continuing archive has support $I$ when $E$ is false, and $I\cup\{m\}$ when $E$ is true. In particular phase zero is actually excluded from this very archive.

Assign each different band label an injective code $c(y)\in\mathbb F_2^L$, assigning the same code to all repeated occurrences. Make the following choices:

| Band membership and code space | Code choice |
| --- | --- |
| $A\in\lambda[I]$ | $c(A)=0$, other labels have different nonzero codes. |
| $A\notin\lambda[I]$, $N<2^L$ | All band labels have different nonzero codes; reserve zero for $A$. |
| $A\notin\lambda[I]$, $N=2^L$ | Use all $L$-bit codes for the band labels. |

The first choice is possible because $N-1\le2^L-1$, and the second because $N\le2^L-1$. The third is genuinely saturated. A residual source at phase $m$ would produce the zero code at all the band-query times.

For $1\le r\le L$, at index $t=rQ$ prescribe the $r$-th code coordinate on the band and compensate its parity at the already excluded phase zero:

$$
\begin{aligned}
q_{rQ}(j)&=c(\lambda(j))_r\quad(j\in I),\\
q_{rQ}(0)&=\bigoplus_{j\in I}c(\lambda(j))_r,
\end{aligned}
\qquad q_{rQ}(j)=0\quad\text{at every other phase}.
\tag{3.5}
$$

Here coordinates are in the order $r=1,\ldots,L$. The support lies in $W_{rQ}$, its charge is even, and (1.8) gives its actual complete word. The left endpoint is $-r\ne0$ and is outside the band, so its first bit is zero. At the last endpoint equality in (2.3), (3.5) may prescribe a nonzero right endpoint, which is permitted and yields the actual trailing one of the inverse. No additional clearing block is appended. At earlier query times $r<L$ the band and the donor are strictly before the right endpoint; the even charge then gives final bit zero.

A repair is used precisely when $E$ holds, $A$ is absent from the band, and $N=2^L$. At index $Q+1$ emit

$$
J_m=1\,0^{m-1}.
\tag{3.6}
$$

Its full response support is $\{m-1,m\}$, because $u_{Q+1}=m-1$. Since $a<m$, phase $m-1$ is outside $I$ and was actually excluded in (3.4). On the continuing support the repair therefore selects only phase $m$. Difference one returns its original label $A$; difference zero retains band sources and their original labels. The first band query at $Q$ has zero response at $m$, so this repair remains correct after that query. For $L\ge2$, $Q+1<2Q$ and the repair replaces one already needed interquery wait; it adds no total fee. For $L=1$, it is a final extra block and adds exactly one.

Every other index after (3.4) and before the last query is filled by a literal $0^m$. There are $Q-1$ complete intervening blocks between consecutive band queries, with the one replacement just described. Each is charged. The last index is $LQ$, except for the $L=1$ repair case, when it is $Q+1$. The total stream lengths are consequently $QL+1$ and $Q+2$, respectively.

To decode without repair, collect the differences at (3.3). A band source yields exactly $c(\lambda(j))$. If the exceptional scan left phase $m$, it yields zero: in the first code choice this returns $A$ because it is the code of the band label $A$; in the second it returns the reserved outside label $A$. If there is no residual source, saturated coding is harmless. With repair, its positive branch stops at $A$, and its zero branch contains only band sources; the collected code returns their INITIAL band label. All early scan positives and root rejections were already decoded in (3.4). Decoding can also stop whenever the acquired archive has one original label; it does not require an unobserved phase.

Finally check literal legality. Every word after the scan has a zero: code words start with zero, waits are all zero, and $J_m$ has a zero. Each such word has length $m$, and each leading or terminal run is at most $m-1$. Combined with the scan this gives the strict seam bound $2m-2<k$. In particular the repair is safe even for $Q=2$, when it immediately precedes the second query, and even if the final inverse has a nonzero terminal tail. The actual terminal tail is retained. The root's high-tail rejection is exactly (2.2); lower tails execute successfully throughout. The same literal stream works for both free values by storing the free initial output and taking successive endpoint differences. Initial $\bot$ executes no block. Thus the construction gives the asserted preset upper bounds; $C_{\rm ad}\le C_{\rm pre}$ and the lower bounds yield (3.1).

When $a=m-1$, the root is $1^{m-1}0$ and safely clears every low tail. If $L=m-a+1$, then $(a-1)+L=m$, so the last band phase is precisely the right endpoint of the last code window. Equation (1.8), including its endpoint condition, realizes its assigned bit; a final one is retained without cleanup. For $m=6,a=5,N=4$, the first-tour survivor is phase six. The repair at $Q+1$ precedes $2Q$ even for $Q=2$, and replaces one of the $Q-1$ actual gap blocks. The final band phase four is the right endpoint of $W_{2Q}=[-2,4]$. This is both a saturated-code instance and an endpoint-equality instance; a repair's necessity does not imply a surcharge when a charged waiting slot is available.

These boundary meanings are part of the same literal construction, not additional cost laws. ∎

## 4. When an outside-label query can be omitted

**定义 4.1（Post-tour band-silent outside query）。** Fix a controller and its continuing archive after the first $Q$ blocks. At a later node call a block a band-silent outside query if: its window satisfies $W_t\cap I=\varnothing$; the node contains a low-tail outside source and at least one band source; and its successful observations distinguish an outside source from a band source. This definition concerns actual candidates in the same acquired node. It excludes first-tour screening, queries on hypothetical absent sources, and blocks whose outputs do not separate the two kinds of source. At these indices within the horizons below, every band phase has response zero, independently of the chosen literal action.

**定理 4.2（Optimal-horizon necessity and omissibility）。** In the guarded class of Definition 2.1, put $H=QL+1+\Delta$ as in (3.1). A correct controller of worst cost at most $H$ can omit all post-tour band-silent outside queries if

$$
m\text{ odd},\quad\text{or }a\text{ even},\quad\text{or }A\in\lambda[I],\quad\text{or }N<2^L.
\tag{4.1}
$$

If none of (4.1) holds, every correct controller of worst cost at most $H$ must use at least one such query on an actual mixed archive. The necessity is for arbitrary adaptive controllers within this horizon, rather than a property of one particular scan. It is not a necessity assertion for controllers with an unrestricted larger budget.

Proof of omissibility. The first two conditions let the scan of Theorem 2.2 remove every outside source. Under either of the other conditions a possible phase-$m$ survivor can share the zero code with the label $A$, or receive the reserved zero code, as in Theorem 3.1. That theorem's common stream then omits $J_m$ entirely; the remaining interquery actions are zero waits. All labels, including an outside $A$ when present, are decoded correctly. This is an existence claim about a complete correct controller, not merely a code-count heuristic.

Proof of necessity. Suppose $m$ is even, $a$ is odd, $A\notin\lambda[I]$, and $N=2^L$. Consider the actual common band archive after the first tour in any correct controller. Theorem 2.2 forces at least one outside source there, regardless of its root suffix and subsequent scans. The node contains $N+1=2^L+1$ different original labels and has common current value and tail. Up to total cost $H$ there are at most $L$ band-query opportunities. For $L\ge2$, this is exactly the calendar in (3.3). For $L=1$, $H=Q+2$ allows indices $Q$ and $Q+1$ after the tour, but the latter window starts at $m-1>a-1$, so only $Q$ can query the band.

Assume no block after the tour is a band-silent outside query. At every non-band index, all band candidates in a node have the same zero difference. If the node also contains an outside source, that source must have the same observation under this assumption; otherwise that block would be a query of Definition 4.1. Uniform rejection cannot help a mixed-label node. A node with no band sources has only label $A$ and may stop. Consequently, after deleting single-child nodes and replacing already monochromatic subtrees by leaves, every branching node in the tree from the depth-$Q$ archive must lie at one of its at most $L$ band-query indices. A binary tree with at most $L$ such branch opportunities on each path has at most $2^L$ leaves. It cannot return the $2^L+1$ different INITIAL labels in this archive. This contradiction proves necessity.

The argument does not assume that all controllers retain phase $m$, or that they assign a particular band label the zero code. It uses the all-root survival obstruction and the saturated number of distinct band labels. Theorem 3.1 realizes the required query at $Q+1$ by the same-archive pair $\{m-1,m\}$; when $L\ge2$ it fits in a charged waiting slot. ∎

**定理 4.3（Larger-budget boundary of the necessity claim）。** In the saturated exceptional case of Theorem 4.2, additionally assume $L+1\le m-a+1$. There is a correct common-stream controller of cost $Q(L+1)+1$ with no post-tour band-silent outside query. Consequently unrestricted larger-budget controllers cannot be ruled out by Theorem 4.2.

Proof. Use (3.4), leaving $I\cup\{m\}$. Take $L+1$ coordinates and give the $N=2^L$ band labels different nonzero $(L+1)$-bit codes, with zero reserved for $A$. At every index $rQ$, $1\le r\le L+1$, prescribe these code bits on all band phases, which the additional guard places inside $W_{rQ}$, and supplement parity at phase zero in that same window. The additional width hypothesis ensures the support and literal safety of every row exactly as in (3.5), with no outside query. This gives a larger-budget counterexample to an unrestricted necessity claim under the stated stronger width condition.

For a concrete instance not depending on an extra unspecified guard, set $a=3,m=6$, any $Q\ge2$, and two distinct band labels $B,C$ different from $A,R$. The scan leaves $\{1,2,6\}$. At index $Q$ use the mask $\{0,1\}$ and at index $2Q$ the mask $\{0,2\}$, with $Q-1$ paid zero blocks between them. Phase six gives $00$, phase one gives $10$, and phase two gives $01$. All masks are inside their respective wrapping windows, each inverse starts with zero, and all seams satisfy $2m-2<k$. The total cost is $2Q+1$, rather than the optimal $Q+2$; for $Q\ge2$ it is a correct controller with no query of Definition 4.1. Thus optimal-horizon necessity cannot be promoted to arbitrary-budget necessity. ∎

## 5. Four-label intake and endpoint boundaries

**定理 5.1（Two adjacent low-tail labels）。** For every $Q\ge2$ and $m\ge4$, choose distinct $A,B,C,R$ and set

$$
f(v,-j,s)=
\begin{cases}
R,&s\ge k-3,\\
B,&s<k-3,\ j=1,\\
C,&s<k-3,\ j=2,\\
A,&s<k-3,\ j\notin\{1,2\}.
\end{cases}
\tag{5.1}
$$

Then

$$
C_{\rm ad}(f)=C_{\rm pre}(f)=
\begin{cases}
Q+1,&m\text{ odd},\\
Q+2,&m\text{ even}.
\end{cases}
\tag{5.2}
$$

For odd $m$ a literal attaining stream is

$$
111(01)^{(m-3)/2}\mid
\underbrace{(10)^{(m-1)/2}1\mid\cdots\mid(10)^{(m-1)/2}1}_{Q-1\text{ blocks}}\mid
01\,0^{m-2}.
\tag{5.3}
$$

For even $m$ an attaining stream is

$$
1110(10)^{(m-4)/2}\mid
\underbrace{(01)^{m/2}\mid\cdots\mid(01)^{m/2}}_{Q-1\text{ blocks}}\mid
01\,0^{m-2}\mid1\,0^{m-1}.
\tag{5.4}
$$

Proof. Set $a=3$, $N=2$, $L=1$ in Theorem 3.1. Its guard is $1\le m-2$ and $a<m$ holds. The root and middle words in (5.3)–(5.4) are (2.8)–(2.9). After their $Q$ zero differences the exact support is $\{1,2\}$ for odd $m$ and $\{1,2,m\}$ for even $m$. Every earlier positive difference returns $A$; root rejection returns $R$.

At $Q$, the isolated one at local position one in $01\,0^{m-2}$ gives full mask $\{0,1\}$. Phase zero was actually excluded, so difference one returns $B$. In the odd case difference zero returns $C$. In the even case the zero child contains exactly phase two with label $C$ and phase $m$ with label $A$; the final mask $\{m-1,m\}$ returns $A$ on one and $C$ on zero. The predecessor tail is zero, and the final block has a single leading one followed by zeros. No clearing block or unpaid displacement is needed. Both free values, all initial tails, and the free initial $\bot$ branch follow Definition 1.2.

The smallest even and odd parameter cases are literal:

$$
\begin{array}{c|c|c}
(Q,m)&\text{stream}&\text{worst cost}\\\hline
(2,4)&1110\mid0101\mid0100\mid1000&4\\
(2,5)&11101\mid10101\mid01000&3.
\end{array}
\tag{5.5}
$$

Their lower bounds are the all-root lower bounds already proved, rather than a comparison only with these particular streams. ∎

## 6. A five-label width-seven returning frontier

**定理 6.1（Five band labels at width seven）。** For every $Q\ge2$ set $m=7$, $k=7Q$, $a=6$. Give the five phases $1,\ldots,5$ pairwise different low-tail labels $B_1,\ldots,B_5$, all different from $A$; give every other low-tail phase label $A$ and every INITIAL tail $s\ge k-6$ label $R$, different from all low-tail labels. Then

$$
C_{\rm ad}(f)=C_{\rm pre}(f)=2Q+2.
\tag{6.1}
$$

A single literal attaining stream is

$$
1111110\mid
\underbrace{1010101\mid\cdots\mid1010101}_{Q-1\text{ blocks}}\mid
0000100\mid
\underbrace{0000000\mid\cdots\mid0000000}_{Q-1\text{ blocks}}\mid
0000110\mid1000000.
\tag{6.2}
$$

Proof of the lower bound. The forced-root argument in Theorem 2.2 applies with $a=6<m$. Band phases have zero root response and common current tail. Within a hypothetical budget of $2Q+1$, indices range only from zero through $2Q$. The windows are still (3.2). At nonzero residue $b$ and $h=0,1$, their left endpoints are at least $7-h\ge6$, so none contains any of the five band phases. Thus after the root the only potentially informative band endpoints are $Q$ and $2Q$. Uniform rejection cannot distinguish their labels, and two binary endpoints yield at most four label leaves, even with adaptive actions and early stopping. Five distinct band labels require at least one additional emitted block. Therefore $C_{\rm ad}\ge2Q+2$.

For attainment, the first $Q$ blocks of (6.2) are the scan (3.4) with odd width. They reject exactly the high tails and remove every outside phase; every positive successful scan difference returns $A$. The continuing archive has support exactly $\{1,2,3,4,5\}$, with immutable labels $B_j$. The three remaining nonzero query words occur at indices $Q$, $2Q$, and $2Q+1$. Their full-window masks, derived directly by (1.7), are respectively

$$
\{3,4\},\qquad\{2,4\},\qquad\{5,6\}.
\tag{6.3}
$$

Indeed $u_Q=-1$, the one at local position four in $0000100$ has boundary vertices three and four; $u_{2Q}=-2$, the pair of adjacent ones at positions four and five in $0000110$ has boundary vertices two and four; and $u_{2Q+1}=5$, the initial one of $1000000$ has boundary vertices five and six. Phase six is actually absent from the same scan archive. The endpoint differences at these three indices are

| INITIAL phase | Original label | Acquired difference code |
| --- | --- | --- |
| $1$ | $B_1$ | $000$ |
| $2$ | $B_2$ | $010$ |
| $3$ | $B_3$ | $100$ |
| $4$ | $B_4$ | $110$ |
| $5$ | $B_5$ | $001$ |

These five distinct codes return exactly the INITIAL label. Between the first two query words are $Q-1$ paid all-zero complete blocks. After the second query, phase five is a returning frontier: it is the left endpoint of the next window and can be selected using excluded phase six. It does not have to wait to the next common band visit at $3Q$.

The root has leading run six and a zero, so every low tail $s<k-6$ safely clears and every high tail rejects. Each scan word has leading and terminal runs one; all query words end zero. The final word has one leading one, following the zero-ending $0000110$. Every internal run and seam is strictly below $k$, and every displayed block has seven bits. The total is $Q+1+(Q-1)+2=2Q+2$ actual blocks, including all waits. Initial $\bot$ stops free, and both legal initial values use the same stream and difference decoder. This establishes the preset upper bound matching the adaptive lower bound. ∎

**定理 6.2（Guard removal changes the exact fee）。** Extending the formula $Q\lceil\log_2N\rceil+1$ without the calendar guard to the family of Theorem 6.1 gives the wrong value $3Q+1$, exceeding the exact optimum by $Q-1$.

Proof. Here $N=5$, so $L=3$, whereas $m-a+1=2$. The guard (2.3) is violated. At index $2Q+1$ the window starts at $m-2=5$, which is a band phase, so the non-band exclusion used in (3.2) fails at precisely the returning frontier. Theorem 6.1 gives the actual optimum $2Q+2$ and an explicit legal stream. For $Q=2$, that stream is

$$
1111110\mid1010101\mid0000100\mid0000000\mid0000110\mid1000000,
\tag{6.4}
$$

of cost six, rather than seven. This falsifies an unguarded exact-cost extrapolation; it does not claim that (2.3) is necessary for every target to have the numerical value $QL+1$. ∎

## 7. Reuse conditions and the unresolved general optimum

**定义 7.1（Remaining full INITIAL problem）。** The general problem asks, for every $k\ge2$, $m\ge1$, and every arbitrary attainable immutable INITIAL target on the full joint actual-history prior, for its exact minimum worst-branch emitted-complete-block cost and an actual attaining controller. This problem remains unresolved. Theorem 3.1 treats only $k=Qm$, a single forced tail threshold, a fully populated band $1..a-1$, one constant outside label, and its stated calendar guard. Theorem 6.1 treats one particular unguarded five-label family. Neither gives a formula for arbitrary phase layouts, multiple outside labels, arbitrary mixed-tail targets, other width regimes, or general adaptive/preset equality.

**数学引文 7.2（Immutable mathematical suppliers）。** The ordinary derivations here are `repo-derived`. The following fixed versions supply their stated intermediate interfaces; they are not new results of this volume.

| Supplier | Exact use and retained restrictions |
| --- | --- |
| [S1] | Sections 1–2 fix the actual reader, history prior, free initial output, absorbing rejection, immutable labels, and total fee; Proposition 2.3 gives alphabet equivalence. Convention 1.3 supplies the same-word joint witness. Lemma 4.3 and Theorem 5.2 supply irreversible first-zero merging and rejection. Their applications here keep the actual adjacent tail pair, rather than assuming a phase-only root-zero rule. |
| [S2] | Sections 13–14 and Theorem 14.1 supply the original $V_k\bmod2$ period with support $\{0,-1\}$ modulo $k+1$. No other recurrence or scalar readout is substituted. |
| [S10] | Interface 2.1 supplies the literal full-window response and inverse; Lemma 3.2 supplies the binary common-tail restriction. Neither permits an arbitrary mask independent of its literal representative or seam. |
| [S13] | Theorem 5.3 supplies the *phase-only* table $B$ at one, $C$ at two, $A$ elsewhere with cost $Q+1$ in its stated coprime narrow domain. Its coloured retirement/parity mechanism is background for the endpoint calculation. A root-zero phase target does not supply the forced-threshold parity surcharge in (5.2). |
| [S15] | Equations (1.1), (1.3)–(1.4) supply joint histories, path inversion, and actual seams. Theorem 7.1 supplies recurring visits from an already paid actual archive under $T=Qm+r$, $\gcd(m,r)=1$, and relative support $S\subseteq\{1,\ldots,m-1-(L-1)r\}$. It proves an *additional* cost $(L-1)Q+1$, not the unpaid INITIAL total. |
| [S16] | Definitions 1.1–1.4 retain the same source/control/fee interface. Theorem 7.1 supplies the three-label coarsening of (5.1) obtained by changing $C$ to $A$, with cost $Q+1$ for both parities. Its phase-capacity bounds concern maxima over tables, not the optimum of a fixed mixed-tail table. |

For precise comparison with [S15, Theorem 7.1], after the first tour the band-only archive has paid depth $Q$ and relative band phases $I-Qm=I+1=\{2,\ldots,a\}$. With $r=1$, that supplier's strict-interior hypothesis reads $a\le m-L$, namely $L\le m-a$. It applies directly to such a band-only archive in this stricter subdomain. The guard of Theorem 3.1 is one endpoint larger, $L\le m-a+1$: its equality case is justified here by (3.2), (3.5), and the full endpoint inverse. A surviving outside phase $m$ is not silently placed inside the supplier's guarded support. The unpaid forced parent, the sharp all-root outside survival obstruction, its same-archive removal, and the last-endpoint extension are handled by the proofs in Sections 2–4. The calendar and code-tree language are reused; no generic belief-game or Bellman solver is a new cost theorem here.

**数学引文 7.3（Identification and parity-query literature）。** Petra van den Bos and Frits Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*, arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2), Definition 11 and Figure 3, supply adaptive distinguishing graphs and examples where the first action destructively merges initial states. The correspondence here treats one literal block as an input and its endpoint as an output, while retaining the initial label. This generic framework does not supply the window calendar, forced threshold, parity charge, or emitted-block formula.

Anastasiya Chistopolskaya and Vladimir V. Podolskii, [*Parity Decision Tree Complexity is Greater Than Granularity*, arXiv:1810.08668v1](https://arxiv.org/html/1810.08668v1), introduction and Section 2.2, permit querying the parity of an arbitrary subset of a fixed unknown Boolean input and charge by query count. A one-hot representation of INITIAL phase explains binary responses but does not grant that unrestricted action alphabet. This volume uses only moving-window even-charge rows with a legal literal inverse. No optimal arbitrary-subset parity-tree cost is imported as a complete-block cost.

Uraz Cengiz Türker, Robert M. Hierons, Mohammad Reza Mousavi, and Khaled El-Fakih, [*Efficient State Identification for Finite State Machine-Based Testing*, author accepted manuscript](https://eprints.whiterose.ac.uk/id/eprint/230260/1/Ordered_Wset_Accepted.pdf), [DOI:10.1109/TSE.2025.3604472](https://doi.org/10.1109/TSE.2025.3604472), use different optimization contracts. The accepted version has SHA256 `a20067072d7349615f42c05ad7b431de04389c035b81f2388d779230dc906c7a`. Definition 13 fixes a transfer-free state-identification path starting at the specified state and covering every state/characterising-word pair. Definition 14 requires a shortest distinguishing prefix for each state pair. Definition 15 requires a nonredundant characterising set and combines minimality with a transfer-free path to define an ordered characterising set. Definition 18 bounds the total length of additional transfer sequences. These definitions give identification and scheduling context; they do not state the minimum worst complete-block cost of one unknown INITIAL target. Their transfer lengths, coverage requirement, and pairwise minimality are not substituted for the fee in Definition 1.2.

The scope of the results here is the source-specific mathematics proved in Sections 2–6. It entails no priority claim or exhaustive assertion that corresponding results are absent from all literature.

[S1]: https://raw.githubusercontent.com/the-omega-institute/trureturing/f64d9e5dc37301e04ffc33332c919dd56a81ed6f/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md
[S2]: https://raw.githubusercontent.com/the-omega-institute/trureturing/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md
[S10]: https://raw.githubusercontent.com/the-omega-institute/trureturing/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md
[S13]: https://raw.githubusercontent.com/the-omega-institute/trureturing/6850a89acdb12d4f17af57dacee2d67e0b514be4/docs/develop/theory/KBONACCI_MULTILABEL_PREFIX_AND_TERMINAL_COST.md
[S15]: https://raw.githubusercontent.com/the-omega-institute/trureturing/3541b57c0d31a89f11fb8b86c75b7b1555e49e6f/docs/develop/theory/KBONACCI_JOINT_RESPONSE_AND_SEAM_COST.md
[S16]: https://raw.githubusercontent.com/the-omega-institute/trureturing/5c531690b4ee33e642757c8485297e94aba5d9a1/docs/develop/theory/KBONACCI_INITIAL_CALENDAR_CAPACITY.md

## 追加锚（本行以下为增补区）

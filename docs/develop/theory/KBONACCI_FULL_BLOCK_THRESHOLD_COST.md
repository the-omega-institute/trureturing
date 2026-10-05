# KBonacci full-block thresholds, binary layouts, and peeling costs

## 1. Fixed source, immutable target, and actual blocks

This volume gives ordinary mathematical proofs and finite producer checks. It is reference theory, not Lean kernel evidence. All costs below count emitted complete blocks from the free INITIAL endpoint. The general objective remains the exact minimum worst-branch cost for every attainable immutable INITIAL target and every original order and block width; the restricted families here advance that objective without replacing it.

**定义 1.1（Original matched reader）。** Fix $k\ge2$ and $m\ge1$. Words are read in increasing weight position and are legal exactly when they avoid $1^k$. The original integer weights and value are

$$
G_i=2^i\quad(0\le i<k),\qquad G_i=\sum_{r=1}^kG_{i-r}\quad(i\ge k),\qquad V_k(w)=\sum_{i<|w|}w_iG_i.
$$

The legal endpoint reading is $V_k(w)\bmod2$. The matched coefficient interface of [S2, Sections 13–14] is

$$
T=k+1,\qquad c_i=G_i\bmod2=\mathbf1_{\{0,-1\}}(i\bmod T).
\tag{1.1}
$$

The actual legal record is $(v,\theta,s)$, with $v\in\mathbb F_2$, $\theta\in P=g\mathbb Z/T\mathbb Z$, $g=\gcd(m,T)$, and $0\le s<k$. Rejection is a separate absorbing record $\bot$. Its reading differs from both free values. Literal transitions, without any intermediate observation, are

$$
\delta_0(v,\theta,s)=(v,\theta+1,0),\qquad
\delta_1(v,\theta,s)=
\begin{cases}
(v\oplus c_\theta,\theta+1,s+1),&s+1<k,\\
\bot,&s+1=k,
\end{cases}
\qquad \delta_b(\bot)=\bot.
\tag{1.2}
$$

A block consists of exactly $m$ literal bits. Both original control alphabets are retained: all $m$-bit words, or all internally legal $m$-bit words. Cross-block rejection is checked in both. The prior is all finite actual histories of these complete blocks, including the empty and rejected histories. A leaf returns the target of the original record, even after destructive updates.

The initial value or known initial $\bot$ is free. Later outputs occur only at block endpoints. Every emitted block and every zero wait costs one; the cost is the maximum over actual initial histories. Write $C_{\rm ad}$ for the optimal adaptive cost and $C_{\rm pre}$ for the optimal cost of a single fixed literal stream, allowing endpoint-dependent stopping and decoding. The initial $\bot$ branch returns its specified label for free. Both legal free-value fibres are included. Offline search time and controller memory are separate from this fee. No reset, copy, hidden initial clock, intermediate observation, or combination of different branches is permitted. These are the contracts of [S1, Sections 1–2]; its Proposition 2.3 supplies general alphabet equivalence.

**约定 1.2（Full-block threshold family）。** Throughout Sections 2–6,

$$
Q\ge2,\qquad m\ge3,\qquad k=Qm,\qquad T=Qm+1,\qquad j=-\theta_{\rm INITIAL}\pmod T,
$$
$$
I=\{1,\ldots,m-1\},\qquad J=\{1,\ldots,m-2\},\qquad H=m-1.
\tag{1.3}
$$

Thus $g=1$ and $P=\mathbb Z/T\mathbb Z$. Because $m<k$, the two control alphabets contain the same literal words, while their common seam constraints still matter. Choose $\lambda:I\to Y$ with $N=|\lambda[I]|\ge2$, an outside label $A$ which may belong to $\lambda[I]$, and $R$ different from every low-tail label. The base target on both legal free-value fibres is

$$
f(v,-j,s)=
\begin{cases}
R,&s\ge k-m,\\
\lambda(j),&s<k-m,\ j\in I,\\
A,&s<k-m,\ j\notin I.
\end{cases}
\tag{1.4}
$$

An INITIAL high tail means $s\ge k-m$; all other tails are low. The target at initial $\bot$ is separately specified. This is the full-block boundary $a=m$, outside the strict $a<m$ scope of [S17, Definition 2.1 and Theorem 3.1]. In particular that theorem's root contains a zero, whereas the root forced below does not.

**约定 1.3（Joint original-history witnesses）。** The joint realization of [S1, Convention 1.3; S15, equation (1.1)] applies here. For every $v,j,s$, choose

$$
n\equiv0\pmod m,\quad n\equiv-j\pmod T,\quad n\ge s+2,
\qquad D=\bigoplus_{i=n-s}^{n-1}c_i,
\qquad w=(v\oplus D)0^{n-s-1}1^s.
\tag{1.5}
$$

The first factor is one actual bit. At least one zero separates it from $s<k$ terminal ones. Hence this single legal word realizes simultaneously the value $v$, phase $-j$, and tail $s$, and splits into actual legal complete blocks. Witness lengths may differ between phases and are not observed. Every lower-bound source and every upper-bound execution below belongs to this original joint prior. Rejected histories are also present, but their initially visible absorbing output already determines their label.

**约定 1.4（Literal response and inverse）。** Absolute block index $t$ starts at zero. Before block $t$, exactly $t$ complete blocks have been paid on a continuing branch. Put $u_t=tm\pmod T$ and use the ordered path $W_t=[u_t,u_t+m]\pmod T$. For a successful word $x_0\cdots x_{m-1}$ its endpoint difference is

$$
q_t(u_t)=x_0,\quad q_t(u_t+i)=x_{i-1}\oplus x_i\ (1\le i<m),\quad q_t(u_t+m)=x_{m-1},
\tag{1.6}
$$

and is zero outside the window. A full-window prescription has a literal inverse exactly when its total charge is even. For a set $E\subseteq W_t$ of even size, define the complete word

$$
\mathcal B_t(E)_i=\bigoplus_{r=0}^{i}\mathbf1_E(u_t+r),\qquad0\le i<m.
\tag{1.7}
$$

Its response support is exactly $E$, including the right endpoint, by (1.6). Empty $E$ gives the paid word $0^m$. This path inverse is reused from [S10, Interface 2.1; S15, Section 1], rather than counted as new content. All occurrences of $\mathcal B_t$ below specify one actual word, and their safety is proved separately. A parity donor must be absent from the same acquired archive, not merely from another branch or from a linear description.

The useful calendar identity, including both endpoints, is

$$
W_{rQ+b}=[bm-r,(b+1)m-r]\pmod T,\qquad0\le b<Q,
\tag{1.8}
$$

because $Qm\equiv-1\pmod T$. It is the supplier calendar of [S16, Section 2; S17, equation (3.2)].

## 2. The forced full-one root and first-tour screening

**定理 2.1（Full-block structural boundary）。** For every base target (1.4), every correct controller on either free-value fibre has root $1^m$. On its successful zero-difference archive, its next block begins with zero. All band sources have a common zero-difference archive through the first $Q$ paid blocks. Removing every low-tail outside source from that archive within those $Q$ blocks is possible exactly when

$$
m\text{ is even}\quad\text{or}\quad Q\ge3.
\tag{2.1}
$$

For $Q=2$ and odd $m$, every correct controller retains an actual outside source on that archive. This assertion concerns source removal even if $A$ is also a band label.

Proof. A root cannot stop, since both a low label and $R$ occur in the same free-value fibre. At any fixed phase, take the joint actual tails $k-m-1$ and $k-m$ with that free value. Their labels differ. If the root's first zero follows $\alpha<m$ ones, both survive to that zero and merge into the same current record. Their INITIAL distinction is then irrecoverable. This is precisely the first-zero loss principle of [S1, Lemma 4.3 and Theorem 5.2]. Thus the only possible root is $1^m$. It rejects exactly $s\ge k-m$; every lower tail survives, with current tail $s+m\le k-1$. Its response support is $\{0,m\}$, so its successful positive child has label $A$ and its zero child contains all band phases, all low tails, and excludes phases $0,m$.

Choose two differently labelled band phases with INITIAL tail $k-m-1$. In the root's zero child both have actual current tail $k-1$, the same current value, and the same archive. A next block beginning with one rejects both before its endpoint and makes them permanently indistinguishable. Hence that next block starts zero. It succeeds for every remaining low-tail source and makes their current terminal tail common. Afterward a literal action's safety depends only on that common tail, not on phase. Uniform rejection cannot finish a node retaining different band labels. The band has zero response at every first-tour index $1\le t<Q$, since $W_t=[tm,(t+1)m]$ misses $I$. It cannot stop before a returning band window. Therefore these zero archives are actual and shared, even for an adaptive controller.

If $Q=2$, only block 1 follows the root in the first tour. Its left response at $m$ is zero, since its first bit is zero. Every outside phase still in the root zero child is one of $m+1,\ldots,2m$, and must have response one to leave that archive. There are $m$ such phases. For odd $m$, this would give odd full-window charge, contradicting (1.6). At least one remains. Taking its INITIAL tail zero and the common free value gives its joint actual witness via (1.5). There is no phase-dependent rejection alternative after the compulsory leading zero.

Here is a common literal scan proving all positive cases and identifying the exceptional support. Emit $1^m$ at index 0. At index 1 emit

$$
Z_m=(0,1,0,1,\ldots)\quad\text{of length }m.
\tag{2.2}
$$

For even $m$, repeat $Z_m$ at indices $2,\ldots,Q-1$. Its response is one on every vertex of $W_t$ except the left endpoint. The previous row already removed that endpoint, starting with phase $m$ removed at the root. Thus every outside phase is removed by the tour's end.

For odd $m$, $Z_m$ has response one exactly on the strict interior of $W_1$ and zero at its endpoints; in particular it leaves phase $2m$. At indices $2,\ldots,Q-1$ instead emit

$$
O_m=(1,0,1,0,\ldots,1)\quad\text{of length }m.
\tag{2.3}
$$

Its response is one on its whole window. When $Q\ge3$, its first use removes the surviving frontier $2m$, and all later outside phases are also removed. When $Q=2$, the final zero archive has exactly $I\cup\{k\}$, with $k=2m$. In the other cases it has exactly $I$.

The root rejects exactly the high tails. The index-1 word starts zero, so it is safe even from current tail $k-1$. Each subsequent word contains zero and has leading and terminal runs at most one. Every subsequent seam is strictly shorter than $k$. Root rejection returns $R$; every successful positive response in this scan returns $A$; all band responses are zero. Both free values use these same words and take successive endpoint differences. This proves (2.1) with actual paid blocks. ∎

**约定 2.2（An alternative exceptional scan）。** For $Q=2$ and odd $m$, a second useful scan is

$$
1^m\mid Z'_m,\qquad Z'_m=00(10)^{(m-3)/2}1.
\tag{2.4}
$$

The second word has response support $\{m+2,\ldots,2m\}$, an even set of size $m-1$. It is safe from every surviving root tail because it starts zero. Its zero archive has exactly

$$
I\cup\{z\},\qquad z=m+1,
\tag{2.5}
$$

rather than $I\cup\{k\}$. Phases $0,m,k$ have actually been excluded from this archive. All scan-positive sources still have label $A$. This is a direct literal instance of the screening construction, not an assertion of a different optimum. The terminal tail of $Z'_m$ is one.

## 3. Every nonconstant binary band layout

**定理 3.1（Exact binary full-block fee）。** For the base target with $N=2$, for every arrangement of its two labels in $I$ and every coincidence of $A$ with those labels,

$$
C_{\rm ad}=C_{\rm pre}=Q+1+\mathbf1_{\{Q=2,\ m\text{ odd},\ A\notin\lambda[I]\}}.
\tag{3.1}
$$

Proof of all-adaptive lower bounds. Theorem 2.1 forces every root and keeps both band labels on one actual archive through $Q$ blocks. Hence $Q$ blocks cannot finish. If $Q=2$, $m$ is odd, and $A$ is fresh, the same theorem keeps at least one actual outside source there. Block 1 began zero, so the archive has a common current tail and value, and contains three different INITIAL labels. With only one further block there are at most two successful endpoint outputs; uniform rejection cannot separate them. Therefore $Q+1$ is impossible in this case, for every action and every adaptive continuation.

For ordinary attainment use the scan of Theorem 2.1. At index $Q$, $W_Q=[-1,H]$ includes all of $I$ and the absent donor 0. Assign its two band labels bits $b(y)\in\{0,1\}$, differently, and let

$$
E=\{j\in I:b(\lambda(j))=1\}\ \cup\
\begin{cases}
\{0\},&|\{j\in I:b(\lambda(j))=1\}|\text{ is odd},\\
\varnothing,&\text{otherwise}.
\end{cases}
\tag{3.2}
$$

Emit $\mathcal B_Q(E)$. Its first bit is zero, since $-1=k$ has not been selected; its final bit is the prescribed bit at $H$, which may be one. If the exceptional scan retained $k$ but $A$ is a band label, assign $b(A)=0$. That source has zero response, the same as the correct band label $A$. Otherwise there is no retained outside source. Consequently this one endpoint decodes both band labels and any remaining $A$ correctly. The total fee is $Q+1$, with no terminal cleanup.

For the remaining fresh-$A$ exception use (2.4), leaving $I\cup\{z\}$. Choose $b(\lambda(H))=1$, give the other band label bit zero, and use (3.2) at index $Q$. Then emit at index $Q+1$

$$
\mathcal B_{Q+1}(\{H,z\})=110^{m-2}.
\tag{3.3}
$$

The two acquired differences have the following meaning: $A$ at $z$ gives $01$; band label zero gives $00$; band label one gives $10$ or $11$, with the latter code at $H$. Repeated occurrences of a label may have different codes, which is harmless; no different labels share a code. The support $\{H,z\}$ is inside $W_{Q+1}=[m-1,2m-1]$, including its left endpoint. This query does not borrow a nonexistent donor at $H$: $H$ is an actual band source and its assigned response is included in the decoder.

After the first compulsory zero block all words have a zero. The main query starts zero; the last query has leading run two and terminal tail zero. Even if the main query ends with up to $m-1$ ones, the last seam has length at most $m+1<2m\le k$ for $m\ge3$. Other seams satisfy $2m-2<k$. All words have exactly $m$ bits. The scan's early leaves and the displayed codes return immutable labels on each original source. The stream is common to both free values. These preset upper bounds match the adaptive lower bounds. ∎

For the sharp smallest odd boundary $Q=2,m=3,k=6$, let $\lambda(1)=B$, $\lambda(2)=C$, with $A,B,C,R$ distinct. An attaining literal stream is

$$
111\mid001\mid011\mid110.
\tag{3.4}
$$

Its fee is four, not three. The fourth block separates the actual outside phase four from the two band labels. Coarsening $A$ to a band label removes the surcharge, exactly as (3.1) states.

## 4. The first returning-frontier classification

**定理 4.1（Complete $Q+2$ classification）。** For every base target,

$$
C_{\rm ad}\le Q+2\quad\Longleftrightarrow\quad C_{\rm pre}\le Q+2
\quad\Longleftrightarrow\quad
N=2\ \text{or}\ \bigl(N=3\text{ and }|\lambda[J]|=2\bigr).
\tag{4.1}
$$

In the three-label case the fee is exactly $Q+2$, for every choice of $A$. If $|\lambda[J]|\ge3$, then $C_{\rm ad}\ge Q+3$; this lower bound does not assert an exact later fee.

Proof of necessity. Up to total budget $Q+2$, the only post-root window which can inspect $J$ is $W_Q=[-1,H]$. The next window $W_{Q+1}=[H,2m-1]$ can inspect only the band frontier $H$. Earlier windows miss the band. After the compulsory leading zero, all candidates in any archive have common current tail, so a useful action supplies at most two successful outcomes and no extra rejection label. Restrict any adaptive controller to the actual sources $j\in J$, with the same free value and INITIAL tail zero. They have only one possible informative endpoint, at $Q$, and thus at most two label leaves. Therefore $|\lambda[J]|\le2$ is necessary. Adding the one frontier phase gives $N\le3$. If $N\ge2$, these conditions say precisely $N=2$ or $N=3$ with $|\lambda[J]|=2$. This is an all-action lower bound, rather than a restriction to the constructed streams.

For $N=2$, Theorem 3.1 proves the upper bound. For $N=3$, write the two interior labels as $B,C$ and the unique frontier label as $D=\lambda(H)$, distinct from them. At most $Q+1$ blocks give only one binary band endpoint, so three band labels require at least $Q+2$.

Here is an attaining common stream. If the scan of Theorem 2.1 removes all outside sources, assign $B,C$ first-query bits zero and one, assign $D$ bit one, use the donor 0 to make that row even, and emit its literal inverse at $Q$. At $Q+1$ use $\{H,m\}$, giving word $10^{m-1}$. Phase $m$ was excluded at the root. The interior codes are $00,10$, and the frontier code is $11$. All outside sources have already returned $A$ during the scan, including when $A$ equals any of these three labels.

For $Q=2$ and odd $m$, use (2.4), with actual surviving outside phase $z=m+1$. The following table specifies the first-query bit on each interior label, the first-query bit at $H$, and the second-query bit at $z$. The second-query bit at $H$ is always one, and all of $J$ has second-query bit zero.

| Outside-label case | Interior label assigned zero | First bit at $H$ | Second bit at $z$ |
| --- | --- | --- | --- |
| $A\in\{B,C\}$ | $A$ | $1$ | $0$ |
| $A=D$ | either $B$ or $C$ | $0$ | $1$ |
| $A\notin\{B,C,D\}$ | either $B$ or $C$ | $1$ | $1$ |

The other interior label is assigned one. At index $Q$ use these band bits and compensate even charge at the absent phase 0. The outsider $z$ lies outside that window and has first bit zero. At index $Q+1$ prescribe one at $H$, the table's bit at $z$, and their XOR at the absent donor $m$. All other responses are zero. The inverse is $10^{m-1}$ when the outsider bit is zero and $110^{m-2}$ when it is one. Thus the table gives respectively outsider code $00$, $01$, or $01$; these equal the correct existing label's code or a new reserved code. The three band labels have different codes in every row of the table. In particular a fresh outside label and the frontier use $01$ and $11$, and do not collide.

Both donors were excluded on this same scan archive. The main word starts zero. The second word has leading run at most two and ends zero, so the strict seam bound from Theorem 3.1 applies. Endpoint responses, including $H$ at the first window's right endpoint and the next window's left endpoint, are realized literally. The total stream length is $Q+2$; there is no unpaid displacement or final clearing action. This proves all equivalences and the asserted exact fee. ∎

The three-label clause includes every binary interior layout with a third frontier label. A three-label layout with all three labels already inside $J$ fails at this horizon, even if the frontier repeats one of them. No claim about its exact later optimum follows from that failure.

## 5. Injective bands: exact symbolic peeling law

**定理 5.1（Injective full-band cost）。** Suppose $\lambda(j)=B_j$ for $1\le j<m$, and $A,R,B_1,\ldots,B_{m-1}$ are mutually distinct. Let $h$ be the least positive integer satisfying

$$
m\le2^h+h+1,
\tag{5.1}
$$

and put

$$
\epsilon=\mathbf1_{\{m=2^h+h+1\ \text{or}\ (Q,m)=(2,3)\}}.
\tag{5.2}
$$

Then, for every $Q\ge2,m\ge3$,

$$
C_{\rm ad}=C_{\rm pre}=hQ+1+\epsilon.
\tag{5.3}
$$

The scope excludes $m=2$.

Proof of the all-adaptive lower bounds. First note $1\le h\le m-2$, since $r=m-2$ satisfies (5.1) for $m\ge3$. At any total budget at most $hQ$, restrict to band phases $1\le j\le m-h$ with INITIAL tail zero. Their only informative indices after the forced root are $Q,2Q,\ldots,(h-1)Q$. Indeed every window of residue one starts at least $m-(h-1)>m-h$, and residues at least two miss the band. They can have at most $2^{h-1}$ different output paths and hence at most that many different label leaves. There are only $h-1$ other band phases, each contributing at most its own one label. Thus a correct controller at this budget would require

$$
m-1\le2^{h-1}+h-1.
\tag{5.4}
$$

For $h=1$ this is false because $m\ge3$. For $h>1$, minimality of $h$ says $m>2^{h-1}+h$, which also contradicts (5.4).

This count applies to every adaptive controller: all restricted sources first share the forced root's zero archive; the compulsory second block clears their tails; a subsequent rejection at a nonconstant node cannot create a useful extra leaf. After pruning constant nodes, the only branching opportunities for the restricted phases are the stated main indices. The $h-1$ other phases are counted as individual sources, without combining their responses with those of a different branch. All counted sources have actual witnesses (1.5).

At total budget $hQ+1$, the same core $1..m-h$ has only $h$ informative main indices, and the remaining $h-1$ band phases still contribute at most one label each. Therefore at this budget

$$
m-1\le2^h+h-1
\tag{5.5}
$$

is necessary. If $m=2^h+h+1$, it fails, proving the additional block. If $(Q,m)=(2,3)$, the fresh-$A$ exception of Theorem 3.1 supplies the additional block. These prove the lower side of (5.3).

For attainment outside $(Q,m)=(2,3)$, use the ordinary scan of Theorem 2.1 when it removes all outsiders, and the alternative scan (2.4) when $Q=2$ and $m$ is odd. In the latter case $m\ge5$ and $h\ge2$. Thus the scan leaves exactly $I$, or exactly $I\cup\{z\}$ with $z=m+1$.

Write $e=\mathbf1_{\{m=2^h+h+1\}}$ and

$$
p=h-1+e,\qquad n=m-1-p=m-h-e.
\tag{5.6}
$$

The core is $K=1..n$ and the peeled phases are $H_r=m-r$, $1\le r\le p$. If $e=0$, $n\le2^h$; if $e=1$, $n=2^h$. Assign core phase $j$ the $h$-bit expansion of $j-1$, in increasing bit order:

$$
c_r(j)=\left\lfloor\frac{j-1}{2^{r-1}}\right\rfloor\bmod2,\qquad1\le r\le h.
\tag{5.7}
$$

At each main index $rQ$, prescribe these bits on $K$ and zero on all other phases, except for the special modification below. Their total charge is compensated at the absent phase 0. The whole core lies in $W_{rQ}=[-r,m-r]$: even its largest phase satisfies $n\le m-h\le m-r$. The donor 0 is in that window and was excluded by the root. Emit the unique word (1.7).

At each peeling index $rQ+1$, $1\le r\le p$, use

$$
E_r=\{m-r,m\},\qquad \mathcal B_{rQ+1}(E_r)=1^r0^{m-r}.
\tag{5.8}
$$

Phase $m$ is absent from the continuing root-zero archive. Thus this row selects exactly the actual band phase $H_r$, not a linear surrogate. Each core phase lies strictly below every peeling window's left endpoint, including the equality boundary $e=1$ where the last selected frontier is $m-h=n+1$. Every other peeled phase has response zero in this row. The main-query codes on the core are different; the peeling rows give separate unit coordinates to the other $p$ band phases. Consequently all $m-1$ band labels are identified.

For the exceptional scan $Q=2$, odd $m\ge5$, make two modifications: at the first main index $Q$ also prescribe one at $H_1=m-1$; at the first peeling index $Q+1$ replace (5.8) by

$$
E_1=\{H_1,z\},\qquad \mathcal B_{Q+1}(E_1)=110^{m-2}.
\tag{5.9}
$$

Compensate the modified main row at phase 0 as before. There is such a first peel because $h\ge2$. The outside phase $z$ is invisible at every main index and has only its first-peel coordinate one. Phase $H_1$ has that same peel coordinate but also its first-main coordinate one, so their codes differ. Every core phase has all peeling coordinates zero. Every other peeled phase has a different peeling unit coordinate. Thus $A$ and every $B_j$ have distinct actual codes. No outside-label clearance is added beyond a peeling slot already counted in the stream. In this scan phases $0,m,k$ have been excluded on the same archive; in particular the main row's left endpoint $-1=k$ is not an unaccounted source.

Place a literal $0^m$ at every remaining absolute index after the scan and before the last query. The final index is $hQ$ when $e=0$, and $hQ+1$ when $e=1$. These are genuine paid intervening blocks: a peel occupies the index immediately after its main query, and the other gap indices are zero waits. Hence the stream has exactly $hQ+1+e$ blocks. The case $(Q,m)=(2,3)$ is supplied by the actual binary stream (3.4), giving four blocks as required by (5.2).

To check literal safety, the index-1 scan word starts zero and clears even the maximal surviving current tail. Later scan words contain zero. Every main word starts zero, since its left endpoint $-r$ is unselected and $r\ge1$; it may end in one when a core or peeled phase is its right endpoint. Every peel word contains zero because $r\le p\le h\le m-2$, and (5.9) contains zero for $m\ge3$. Its leading run is at most $m-2$, or two in (5.9), and its terminal tail is zero. All post-scan words therefore have leading and terminal runs at most $m-1$, giving the strict general seam bound $2m-2<k$. The actual terminal tail of the final main word is retained. No cleanup is charged or silently omitted.

The decoder first returns $R$ on root rejection and $A$ on scan-positive archives. On the remaining archive it uses the main and peel difference coordinates just proved distinct. In the modified scan the additional code belongs to $A$ at $z$. Every returned label is an INITIAL label; no source is copied, and no two archives are combined. This is one fixed stream for both free values. The preset upper bound equals the all-adaptive lower bound, proving (5.3). ∎

The first saturated widths $m=2^h+h+1$ are $4,7,12,21$. At these widths the main-row core capacity is short by exactly one band source, and the final frontier query costs one extra block. At the unsurcharged boundary $m=2^h+h$, all $2^h$ core codes can be used; for $Q=2$ and odd $m$ the first peel simultaneously handles the fresh outside source by (5.9). Thus its presence does not require a new tour. These are consequences of the proved construction and count, not an assumption that adaptive and preset query models always agree.

## 6. Independent labels on the two root endpoints

**定理 6.1（Six-label endpoint refinement）。** Fix $Q\ge2,m\ge3,k=Qm$, six pairwise distinct labels $A,B,C,D,E,R$, and a surjective $\lambda:I\to\{B,C\}$. Give every high INITIAL tail label $R$. On low tails give phase 0 label $D$, phase $m$ label $E$, band phase $j$ label $\lambda(j)$, and every other phase label $A$. Then

$$
C_{\rm ad}=C_{\rm pre}=Q+1+\mathbf1_{\{Q=2,\ m\text{ odd}\}}.
\tag{6.1}
$$

The preset upper bound uses one common literal stream for both successful root children.

Proof of lower bounds. At each phase the tails $k-m-1$ and $k-m$ have different labels, so the same first-zero argument forces root $1^m$. Its positive child now contains both $D$ at 0 and $E$ at $m$; its zero child contains the two band labels and the other outside phases. On the latter child the forced leading-zero and first-tour lower bounds of Theorem 2.1 apply unchanged, because they involve only its actual band sources and low outside sources. Thus at least $Q+1$ blocks are needed, and $Q=2$, odd $m$ leaves a fresh outside label $A$ alongside $B,C$, requiring $Q+2$. This is an all-adaptive lower bound for the refined target.

For common-stream attainment use the ordinary scan when it removes all outside sources and the alternative scan (2.4) otherwise. The second block starts zero for both root children. On the positive child phase $m$ is the left endpoint of $W_1$ and has response zero; phase 0 is outside every remaining first-tour window. Hence both $D$ and $E$ have the same zero continuation differences through that tour, and remain available for the common final query. Their current tails after the second block are the same as on the other child.

Choose band bits $b(B),b(C)$ differently, with $b(\lambda(H))=1$. At index $Q$, let

$$
F=\{j\in I:b(\lambda(j))=1\},\qquad
E_Q=F\cup\{0\}\cup
\begin{cases}
\{k\},&|F|+1\text{ is odd},\\
\varnothing,&|F|+1\text{ is even}.
\end{cases}
\tag{6.2}
$$

This has even charge inside $W_Q=[k,0,1,\ldots,H]$ in path order. It assigns phase 0 response one and phase $m$ response zero, distinguishing $D,E$ on the positive root child. On the zero root child it assigns the required band bits. Phase $k$ is an actual absent donor in both continuing archives: on the positive child it was excluded by the root, and on the zero child it was excluded by the ordinary successful scan or by (2.4). Phase 0 here is deliberately an observed source on one child, not an absent donor there. Its response is fixed to one; parity is compensated at $k$ instead.

The inverse of (6.2) contains zero since its response at the interior vertex 0 is one, whereas a full-one word has only its two endpoint responses. Its leading run is zero or one: if the left endpoint $k$ is selected, the next response at 0 flips the next bit to zero. Its terminal tail may be nonzero and is retained. All seams after the scan are strictly legal.

When the scan removed all outsiders, stop after this endpoint: the positive-root branch decodes $D$ on difference one and $E$ on zero, and the zero-root branch decodes $B,C$. Each scan-positive branch of the zero-root child returned $A$ earlier. This gives $Q+1$ actual blocks.

When $Q=2$ and $m$ is odd, the alternative scan leaves outside phase $z=m+1$ on the zero-root child. Append the common block $110^{m-2}$ at index $Q+1$, with mask $\{H,z\}$. On that child its codes and labels are exactly those in (3.3): outsider $A$ gives $01$, bit-zero band label gives $00$, and bit-one band label gives $10$ or $11$. The positive-root child already stopped at the main endpoint, and requires no branch-specific action. Even if formally continued, the final word is safe from the common tail: leading two after a terminal run at most $m-1$ gives at most $m+1<k$. This one stream therefore realizes both root children within $Q+2$ blocks. Both free values use the same differences and stopping rules; the initial $\bot$ branch stops free. ∎

Identifying $D=E=A$ coarsens this refinement to the fresh-outside-label case of Theorem 3.1. Its binary fee is reused there, not counted as another standalone theorem. The refined proof supplies the extra common-stream condition that cannot be obtained merely by taking the maximum of two separately optimal preset continuations; [S15, Proposition 4.2] explicitly preserves this distinction.

## 7. Finite original-reader and controller checks

**数据 7.1（Exact finite scopes）。** Finite checks use chronological original transitions (1.2), preserve INITIAL labels across updates, and include both free values and every legal tail and phase in each stated parameter pair. Their role is falsification and regression evidence for the ordinary proofs, not independent mathematical review or a universal proof.

| Check family | Exact scope | Results |
| --- | --- | --- |
| Binary preset attainment | $Q\in\{2,3,4\}$, $3\le m\le8$; every nonconstant map $I\to\{0,1\}$; $A=0,1$, or fresh $2$ | 2,160 streams; every final output archive has one INITIAL label |
| Independent root-endpoint labels | Same $Q,m$ and binary layouts; fresh $A$ and separate $D,E,R$ | 720 common streams, with both root children checked |
| Three-label frontier attainment | $Q\in\{2,3,4\}$, $4\le m\le8$; every nonconstant binary layout on $J$, a third label at $H$; $A$ equal to each of the three labels or fresh | 1,368 streams; all four coincidence cases pass |
| Injective symbolic fee | $Q\in\{2,3,4,5\}$, every $3\le m\le24$ | 88 streams of length (5.3), including saturated widths $4,7,12,21$ and widths $3,6,11,20$ immediately below them, with the $(2,3)$ exception checked |
| Joint histories and literal rows | $Q\in\{2,3\}$, every $3\le m\le6$, all $v,j,s$, every $m$-bit action | 2,416 joint original-history witnesses; 95,552 source/action rows |

The four stream families total 4,336 streams, 5,075,216 record executions, and 348,824,892 chronological continuation-bit updates. Each stream's literal length equals its asserted fee. Final archives retain all earlier endpoint outputs, so continued execution of an already-decoded source cannot erase the decoding evidence. High-tail sources stop at the first rejecting endpoint; the finite full-stream comparison may extend their absorbing outputs without charging such formal extensions to the actual protocol.

Joint witness checks independently compute the integer weights by their original recurrence, construct (1.5), split its actual bits into complete blocks, and verify its value, phase, and tail together. These witnesses contain 109,346 bits in total. For every stated source/action row, direct bit execution checks rejection or the successful scalar increment against the matched original-weight coefficients. The continuation tests execute literal words, rather than treating an even response span as an action. Eight additional rejected-history witnesses, one per tested $(Q,m)$ pair, are the actual $Q$-block histories $(1^m)^Q$, with 90 bits in total. All 240 ensuing literal action checks preserve absorbing rejection. Their free initial output selects the prescribed bottom label immediately, with zero emitted continuation blocks.

**数据 7.2（First-tour exhaustive screening）。** Conditioned on the proved full-one root and compulsory leading-zero second block, all literal first-tour continuations were enumerated for $Q=2,3$ and $3\le m\le7$. Safety is checked from the actual surviving root tails and at every later seam. For $Q=2$, the numbers of safe second words at widths $3,4,5,6,7$ are $4,8,16,32,64$; the numbers completely removing all outside sources are $0,1,0,1,0$, and the minimum residual-source counts are $1,0,1,0,1$. For $Q=3$, the safe two-word continuation counts are $32,128,512,2048,8192$; each width has exactly one complete screen and minimum residual count zero. These 11,036 safe continuations corroborate (2.1). These are conditioned screening checks, not unrestricted searches over possible root choices.

**数据 7.3（Unrestricted versus conditioned adaptive feasibility）。** The finite feasibility check represents a candidate by its current original-reader record together with its immutable INITIAL label. Each literal action is evaluated by (1.2), its resulting candidates are grouped only by the endpoint reading, and monochromatic groups stop. If two different labels have become the same current record, that candidate action is rejected as irreversibly losing the target. Every $m$-bit action is considered at each remaining nonconstant node. Memoization only identifies identical labelled current-record sets and remaining horizons; it does not merge different observation branches or use a hidden source clock.

The following eight target rows were tested at the claimed fee and one block below it, separately on both free values. Their searches impose no root-action constraint. A row lists $\lambda(1),\ldots,\lambda(m-1)$; the endpoint refinement has additional independent $D,E$.

| $(Q,m)$ | Band layout | Outside label | Endpoint refinement | Exact checked fee |
| --- | --- | --- | --- | --- |
| $(2,3)$ | $(0,1)$ | fresh $2$ | no | $4$ |
| $(2,3)$ | $(0,1)$ | $0$ | no | $3$ |
| $(2,4)$ | $(0,1,2)$ | fresh $3$ | no | $4$ |
| $(2,4)$ | $(0,1,2)$ | $0$ | no | $4$ |
| $(2,4)$ | $(0,1,0)$ | fresh $2$ | no | $3$ |
| $(3,3)$ | $(0,1)$ | fresh $2$ | no | $4$ |
| $(2,3)$ | $(0,1)$ | fresh $2$ | yes | $4$ |
| $(2,4)$ | $(0,1,0)$ | fresh $2$ | yes | $3$ |

All 16 target/budget tests return infeasible below the fee and feasible at it on both free values. They evaluate 1,847 distinct labelled-belief/horizon states and 2,841 candidate actions in total. Rejection is an independent absorbing reading, including in these unrestricted root searches.

Three additional targets were searched conditioned on the proved root $1^m$: $(Q,m)=(2,5)$ with injective band $(0,1,2,3)$ and fresh outside $4$, at budgets four and five; $(2,6)$ with band $(0,1,2,0,3)$ and fresh outside $4$, at budgets four and five; and $(2,7)$ with injective band $(1,2,3,4,5,6)$ and fresh outside zero, at budgets five and six. Both values give infeasible then feasible, with 227,360 states and 12,117,779 candidate actions in total. These searches retain all literal continuation actions and actual tail updates; only the root is supplied by the theorem. A further conditioned check at $(2,5)$, band $(0,1,2,0)$ and fresh outside $3$, finds budget four infeasible on both values, evaluating 2,649 states and 16,561 candidate actions. It is a falsifier for extending the three-label frontier law to three labels already present inside $J$; no exact later fee is inferred.

All four finite batches—preset/original-history checks, screening, adaptive feasibility, and the interior obstruction—completed with exit code zero and no failed assertion. The sharp $(2,3)$ fresh-$A$ case explicitly rejects the incorrect fee three. These finite ranges do not cover every $Q,m$, every later horizon, arbitrary mixed-tail targets, or every multilabel layout. The ordinary proofs above carry the universal claims. No Lean compilation, ingestion, or formalization state is asserted.

## 8. Reuse, literature, and remaining scope

**数学引文 8.1（Precise supplier boundaries）。** The following immutable ordinary-theory sources supply interfaces or already-covered results. The new mathematical content consists of the full-block threshold screening boundary, its exact binary and returning-frontier refinements, the injective peeling law, and the simultaneous endpoint-label refinement proved above.

| Supplier | Exact reuse and boundary |
| --- | --- |
| [S1] | Sections 1–2 fix the actual source, free initial readings, absorbing rejection, immutable labels, and emitted-block fee; Convention 1.3 supplies joint histories; Lemmas 4.2–4.3 and Theorem 5.2 supply the first-zero irreversible-loss principle. A generic first-zero classification is not itself one of the new cost laws. |
| [S2] | Sections 13–14 supply the matched original integer-reader coefficient cycle $c_i$ and $T=k+1$. No other recurrence polynomial or chosen scalar is substituted. |
| [S10] | Interface 2.1 supplies literal consecutive-window responses and their inverse. Its common-tail binary observations apply after the compulsory zero, not immediately after this full-one root. |
| [S11] | Coprime phase-only binary and singleton costs retain their phase-only assumptions. They do not remove the threshold obligation in (1.4), and none is used as a mixed-INITIAL optimum. |
| [S13] | Actual-support one-block certificates and guarded arbitrary-label prefix costs are background. Their guard and seam data do not identify the late returning-frontier fees here. |
| [S15] | Joint response, actual row realizability, current-tail safety, and first-zero parent composition are reused. Proposition 4.2 warns that separately preset-optimal root children need not admit one common stream; Section 6 above constructs that stream. Generic Bellman or adaptive-tree machinery is used only for finite feasibility checking, not delivered as new mathematics. |
| [S16] | The calendar and full-INITIAL phase capacity are reused with their original hypotheses. Its arbitrary phase-label capacity does not give the forced mixed-tail target cost. |
| [S17] | Definition 2.1 and Theorems 2.2–3.1 assume strict $a<m$, and their guarded exact law requires $\lceil\log_2N\rceil\le m-a+1$. Here $a=m$, so neither root structure nor costs follow by specializing them. Its width-seven frontier example is supplied overlap; the present injective law proves all widths in its own scope. |

The local declaration search includes private declarations as well as public ones; the inspected KBonacci acquisition interfaces include `LiteralModel.literal_block_execution`, `LiteralModel.joint_history_realization`, the first-zero recursion, and actual endpoint operators. They are reused as source interfaces, without compilation claims, new wrappers, or code delivery. The saturated-band construction with length $10Q+1$ is an upper bound when its supplied hypotheses apply; it is not an old optimum and is not used as the lower bound in Theorem 5.1.

**数学引文 8.2（Authoritative external contracts）。** Bounded literature inspection covers the following versions and the related search topics of parity-query restrictions, adaptive versus preset state identification, and ordered characterising sets. It does not establish exhaustive absence, priority, or external novelty.

Petra van den Bos and Frits Vaandrager, [State Identification for Labeled Transition Systems with Inputs and Outputs, arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2), Definition 11 and Figure 3, supply adaptive distinguishing graphs and the obstruction caused by a first action merging different initial sources. Their general setting does not supply this matched reader's windows, strict seams, or exact INITIAL block fees.

Anastasiya Chistopolskaya and Vladimir V. Podolskii, [Parity Decision Tree Complexity is Greater Than Granularity, arXiv:1810.08668v1](https://arxiv.org/html/1810.08668v1), introduction and Section 2.2, permit a query of an arbitrary subset parity of an unknown Boolean input. That action freedom is not available here. A one-hot phase encoding cannot bypass the current window, even charge, actual inverse, or seam. The elementary binary leaf count is reused; no optimum from unrestricted parity queries is imported.

Uraz Cengiz Türker, Robert M. Hierons, Mohammad Reza Mousavi, and Khaled El-Fakih, [Efficient State Identification for Finite State Machine-Based Testing, accepted manuscript](https://eprints.whiterose.ac.uk/id/eprint/230260/1/Ordered_Wset_Accepted.pdf), [DOI 10.1109/TSE.2025.3604472](https://doi.org/10.1109/TSE.2025.3604472), Definitions 13–15 and 18, distinguish transfer-free identification paths, shortest distinguishing prefixes for every state pair, ordered characterising sets, and bounds on transfer length. The accepted manuscript has SHA256 `a20067072d7349615f42c05ad7b431de04389c035b81f2388d779230dc906c7a`. Its transfer-free paths do not require extra transfer steps, so they cannot be dismissed as necessarily reset-based. Their specified-start coverage of every state/word pair and pairwise-prefix minimality nevertheless differ from the single unknown INITIAL label's worst emitted-block fee. None of those generic optimum claims replaces the source-specific proofs here.

Theorems 2.1, 3.1, 4.1, 5.1, and 6.1 are `repo-derived` ordinary deductions. The verified source correspondence and literal constructions, rather than an originality assertion, support their use.

**开放问题 8.3（Unchanged general objective）。** The exact minimum worst-branch actual emitted-block cost for every arbitrary attainable immutable INITIAL target, for all original $k\ge2,m\ge1$, remains unresolved. This volume settles the displayed full-block threshold families at $k=Qm$, with unrestricted binary band layouts, a complete $Q+2$ multilabel boundary, injective bands of every width $m\ge3$, and independent labels at both root endpoints. It does not settle arbitrary later multilabel layouts, competing admissible INITIAL parents, general mixed-tail partitions, nonmultiple $k/m$, or the $m=2$ degeneration. The lower bound $Q+3$ in Theorem 4.1 is not an exact later fee. A general all-width law and actual optimal protocols still require source-specific composition beyond these conditions.

[S1]: https://raw.githubusercontent.com/the-omega-institute/trureturing/f64d9e5dc37301e04ffc33332c919dd56a81ed6f/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md
[S2]: https://raw.githubusercontent.com/the-omega-institute/trureturing/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md
[S10]: https://raw.githubusercontent.com/the-omega-institute/trureturing/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md
[S11]: https://raw.githubusercontent.com/the-omega-institute/trureturing/ef2fddd6bab3fe4b861b07e4c01577e942912ab8/docs/develop/theory/KBONACCI_COPRIME_PHASE_TARGET_COST.md
[S13]: https://raw.githubusercontent.com/the-omega-institute/trureturing/6850a89acdb12d4f17af57dacee2d67e0b514be4/docs/develop/theory/KBONACCI_MULTILABEL_PREFIX_AND_TERMINAL_COST.md
[S15]: https://raw.githubusercontent.com/the-omega-institute/trureturing/3541b57c0d31a89f11fb8b86c75b7b1555e49e6f/docs/develop/theory/KBONACCI_JOINT_RESPONSE_AND_SEAM_COST.md
[S16]: https://raw.githubusercontent.com/the-omega-institute/trureturing/5c531690b4ee33e642757c8485297e94aba5d9a1/docs/develop/theory/KBONACCI_INITIAL_CALENDAR_CAPACITY.md
[S17]: https://raw.githubusercontent.com/the-omega-institute/trureturing/799d8549ae4d270122eb9a2a42024fdbbbe69459/docs/develop/theory/KBONACCI_FORCED_PREFIX_PARITY_COST.md

## 追加锚（本行以下为增补区）

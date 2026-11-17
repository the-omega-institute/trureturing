# KBonacci: a guarded GLOBAL k-block ceiling

## 1. The full INITIAL experiment and its paid resource

**定义 1.1（Original reader and alphabets）。** Fix integers $m\ge3$ and $k\ge2m$ with $\gcd(m,k+1)=1$, and put $T=k+1$. The matched coefficient interface of [S1, Definition 1.1] is the periodic sequence

$$
c_i=\mathbf1_{\{0,T-1\}}(i\bmod T).
\tag{1.1}
$$

The immutable INITIAL record set is

$$
Q_{k,m}=\bigl(\mathbb F_2\times\mathbb Z/T\mathbb Z
\times\{0,\ldots,k-1\}\bigr)\sqcup\{\bot\}.
\tag{1.2}
$$

The current successful record evolves by the original literal operations

$$
\begin{aligned}
\delta_0(v,\theta,s)&=(v,\theta+1,0),\\
\delta_1(v,\theta,s)&=
\begin{cases}
(v\oplus c_\theta,\theta+1,s+1),&s+1<k,\\
\bot,&s+1=k,
\end{cases}\\
\delta_b(\bot)&=\bot\qquad(b\in\{0,1\}).
\end{aligned}
\tag{1.3}
$$

All phases are residues modulo $T$. An issued action is one complete $m$-bit word. The two original alphabets are $A_{\rm all}=\{0,1\}^m$ and its subset $A_{\rm loc}$ of words internally avoiding $1^k$. Here $m<k$, so their literal word sets coincide. In both alphabets the actual concatenation rejects as soon as a run reaches $k$, including across a block boundary. Only the initial scalar value or $\bot$, and the endpoints of issued complete blocks, are observed. Intermediate bit states are not readings.

**约定 1.2（Joint actual histories and hidden length）。** Every triple in (1.2) is one jointly realized INITIAL source. Write $j=-\theta_{\rm INITIAL}$. The source witness from [S1, Convention 1.2] chooses an integer $\ell$ with

$$
\ell\equiv0\pmod m,\qquad \ell\equiv-j\pmod T,
\qquad \ell\ge s+2,
\qquad d=\bigoplus_{i=\ell-s}^{\ell-1}c_i,
\tag{1.4}
$$

and uses the single legal history

$$
w(v,j,s)=(v\oplus d)\,0^{\ell-s-1}1^s.
\tag{1.5}
$$

Coprimality supplies the simultaneous length congruences. The first factor is one bit; the separating zero and $s<k$ make the entire history legal. Its scalar value is $v$, its phase is $-j$, and its tail is $s$. Its length is divisible by $m$, so it is a complete-block history under either alphabet. A sufficiently long all-one complete-block history realizes $\bot$. Original history lengths may differ between sources and remain hidden. No promise restricts the INITIAL phase, tail or support, and separately reachable marginals are not substituted for these joint sources.

**定义 1.3（GLOBAL-preset cost）。** Let $Y$ be any finite nonempty set and $f:Q_{k,m}\to Y$ any map. The output required from an INITIAL source $q$ is always $f(q)$, even after the current record changes. For $A\in\{A_{\rm all},A_{\rm loc}\}$, let $C_{\rm pre}^{A}(f)$ be the least uniform worst number of actually issued complete blocks among deterministic correct protocols for which every source, on both free INITIAL values, receives a prefix of one fixed literal stream. Stopping and decoding may depend on that source's own chronological issued-word/endpoint archive. If no uniformly bounded correct protocol exists, set the cost to $+\infty$.

Every issued whole block costs one, including zero waits, padding, duplicate words and a rejecting block. There is no free displacement, clearing step or extra observation. Initial $\bot$ returns its independently prescribed $f(\bot)$ at fee zero. There is no reset, copied source, borrowed branch, unobserved initial clock or observation between endpoints. This is the source and resource contract of [S1, Definitions 1.1–1.3], [S2, Section 1] and [S3, Definition 8.1].

## 2. Reused common-cut and literal-response interfaces

**定义 2.1（Eligible common cut in INITIAL coordinates）。** Use the ordered value join

$$
\Gamma(j,s)=\bigl(f(0,-j,s),f(1,-j,s)\bigr),
\qquad \Lambda(j)=\Gamma(j,0).
\tag{2.1}
$$

Equality of these pairs means equality component by component; the two components need not equal one another. For each all-one block index $t\ge0$ put

$$
\begin{aligned}
I_t(j)&=\mathbf1_{\{tm,(t+1)m\}\bmod T}(j),\\
S_t(\beta)&=\{j:(I_0(j),\ldots,I_{t-1}(j))=\beta\},
\qquad \beta\in\mathbb F_2^t,\\
h_t&=k-tm.
\end{aligned}
\tag{2.2}
$$

An integer $0\le a<k$, written $a=qm+r$ with $q\ge0$ and $0\le r<m$, is eligible when

$$
\begin{aligned}
&\operatorname{Const}\{\Gamma(j,s):j\in S_t(\beta),\ h_t-m\le s<h_t\}
&& (0\le t<q,\ \beta\in\mathbb F_2^t),\\
&\operatorname{Const}\{\Gamma(j,s):j\in S_q(\beta),\ h_q-r\le s<h_q\}
&& (\beta\in\mathbb F_2^q),\\
&\Gamma(j,s)=\Lambda(j)
&& (j\in\mathbb Z/T\mathbb Z,\ 0\le s<k-a).
\end{aligned}
\tag{2.3}
$$

Here $\operatorname{Const}$ means image size at most one, and empty bands impose no condition. The single $a$ precedes all value and archive quantifiers. These are exactly [S1, Definition 51.1, (51.2)–(51.4)]. Theorem 24.2 and Theorem 29.2 of [S1], including their proof bodies, supply an eligible cut whenever $C_{\rm pre}^{A}(f)<\infty$. The value join preserves that cost, including infinity, on one actual stream: complementing successful scalar readings computes the other value's archive by symmetry, without a second experiment. A decoded pair is projected using the remembered free INITIAL value.

**数学引文 2.2（Literal charges, tree geometry and the boundary case）。** At absolute issued-block index $t$, a successful word $x_0\cdots x_{m-1}$ has charge

$$
q_t(j)=\bigoplus_{i=0}^{m-1}x_i c_{-j+tm+i}.
\tag{2.4}
$$

On the ordered path $tm,tm+1,\ldots,tm+m$, its charges are $x_0$, then $x_{i-1}\oplus x_i$ for $1\le i<m$, then $x_{m-1}$; outside the path the charge is zero. This is [S1, Interface 1.4] and [S2, Section 1]. In particular, the all-one word and the single-pulse word have the actual charge edges

$$
H_t=\{tm,(t+1)m\},\qquad
E=01\,0^{m-2},\qquad F_t=\{tm+1,tm+2\},
\tag{2.5}
$$

with vertices reduced modulo $T$.

For $qm\le T-2$, the proof of [S1, Theorem 51.2, (51.7)–(51.9)] supplies the spanning tree

$$
\mathcal S=\{H_0,\ldots,H_{q-1},F_{q+1},\ldots,F_{T-1}\}.
\tag{2.6}
$$

Before its $H$ chords are attached, its cycle-edge path components, in ordinary representatives, are

$$
\begin{aligned}
C_t&=\{tm+2,\ldots,(t+1)m+1\} &&(0\le t<q),\\
C_q&=\{qm+2,\ldots,T-1\}\cup\{0,1\}.
\end{aligned}
\tag{2.7}
$$

The first interval of $C_q$ can be empty. The chords join these components in a chain: $H_0$ joins $C_q$ to $C_0$, and $H_t$ joins $C_{t-1}$ to $C_t$ for $1\le t<q$. At $q=0$ there is just the one spanning path.

At an eligible boundary cut $r=0$, [S1, Theorem 51.3 and its proof] already supplies a full-INITIAL common stream of fee at most $T-1$. Its literal schedule is $q$ words $1^m$, followed by $0^{m-1}1$ at indices $q,\ldots,T-2$. This boundary result is reused. The new shortened interior schedule below consumes the supplied tree and its explicit path components, rather than reproving either source result.

## 3. The guarded GLOBAL ceiling

**定理 3.1（Every finite GLOBAL-preset cost is at most k）。** For all integers $m\ge3$, $k\ge2m$ with $\gcd(m,k+1)=1$, every finite nonempty label set $Y$, every map $f:Q_{k,m}\to Y$, and each original alphabet $A\in\{A_{\rm all},A_{\rm loc}\}$, under the full INITIAL, endpoint, common-stream and fee contracts of Section 1,

$$
C_{\rm pre}^{A}(f)<\infty
\quad\Longrightarrow\quad
C_{\rm pre}^{A}(f)\le k.
\tag{3.1}
$$

**证明（common prefix and retained observations）。** Put $T=k+1$ and assume the left side. Use the supplied common-cut and value-join laws to choose one eligible $a=qm+r$, $0\le a\le T-2$. If $r=0$, the boundary part of [S1, Theorem 51.3] proves (3.1). Henceforth $r>0$. Write

$$
h=T-qm,\qquad 1\le r\le h-2,\qquad h\ge3.
\tag{3.2}
$$

Use $q$ all-one blocks, then at absolute block index $q$ use

$$
B=1^r0^{m-r}.
\tag{3.3}
$$

This is the eligible first-zero prefix of [S1, Theorem 24.2]. At an all-one rejection at index $t<q$, the INITIAL candidates are the band $S_t(\beta)\times[h_t-m,h_t)$ from the source's own previous successful archive. Its joined label is constant by (2.3). Rejection in $B$ has the analogous band $S_q(\beta)\times[h_q-r,h_q)$, also constant. These branches return the corresponding component using their remembered INITIAL value. Their rejecting block is paid.

Every surviving source has $s<k-a$, reaches the first zero, and ends $B$ at tail zero. Its INITIAL joined label is $\Lambda(j)$. Retain the earlier $q$ all-one differences. In the separation argument, omit $B$'s charge coordinate, while retaining its actually observed endpoint as the baseline for the next difference. This is omission of information from the decoder, with the block and its reading still present and paid.

First try $E$ at indices $q+1,\ldots,T-2$. The retained charge graph is

$$
\mathcal G=\mathcal S\setminus\{F_{T-1}\}.
\tag{3.4}
$$

Its columns are the retained differences for INITIAL phase $j$. The incidence collision criterion used in [S1, proof of Theorem 51.2] applies also to this disconnected graph: a simple graph has distinct vertex incidence columns exactly when it has at most one isolated vertex and no component on two vertices. Indeed, equal zero columns mean two isolated vertices. Equal nonzero columns at distinct vertices force every incident edge to contain both vertices, giving a two-vertex component; conversely such a component has equal columns. This criterion is credited reuse inside the proof.

**证明（all one-edge deletion cases）。** In ordinary representatives,

$$
F_{T-1}=\{T-m+1,T-m+2\}.
\tag{3.5}
$$

Cut this edge in the paths (2.7), retaining the same $H$ chords. The component sizes after the cut are as follows.

If $h\ge m+1$, the cut is in $C_q$. Its detached interval and complementary size are

$$
\{qm+2,\ldots,T-m+1\},\qquad
h-m\quad\hbox{and}\quad(q+1)m.
\tag{3.6}
$$

The detached interval has no chord endpoint. The other part of $C_q$, containing zero, stays joined through the supplied chord chain to the other paths. Thus these are exactly the two components, also when $q=0$.

If $3\le h\le m-2$, the cut lies in $C_{q-1}$ and detaches

$$
\{(q-1)m+2,\ldots,T-m+1\},\qquad
h\quad\hbox{and}\quad qm.
\tag{3.7}
$$

Here $q\ge1$. The detached left interval has no chord endpoint; the right part contains $qm$, and the remaining chord chain connects the complement. If $h=m-1$, the detached component is the singleton $\{qm+1\}$, with complementary size $T-1$. The value $h=m$ would make $T=(q+1)m$ and is excluded by coprimality. These cases exhaust $h\ge3$.

Every complement just described has at least three vertices. In (3.7) the detached component also has at least three; the singleton case has the only isolated vertex. In (3.6) the detached size is positive and is two only when

$$
h=m+2.
\tag{3.8}
$$

Apart from (3.8), the incidence criterion therefore gives distinct columns in $\mathcal G$. Connectedness is unnecessary: one isolated vertex has the unique zero column, and separate components of size at least three have no equal columns. The shortened stream already separates every INITIAL phase in all these cases.

**证明（exceptional simultaneous repair）。** Suppose now that $h=m+2$, so

$$
T=(q+1)m+2.
\tag{3.9}
$$

The guard $T\ge2m+1$ implies $q\ge1$, and $\gcd(m,T)=1$ forces $m$ odd. Keep $E$ at indices $q+1,\ldots,T-3$, and replace the final block at index $T-2$ by the single actual word

$$
R=01\,0^{m-3}1.
\tag{3.10}
$$

The literal charge interface (2.4)–(2.5) gives its row as the symmetric difference

$$
F_{T-2}\mathbin{\triangle}J,
\qquad J=\{T-m-1,T-m\}.
\tag{3.11}
$$

Its two literal ones occupy positions $1$ and $m-1$. Formula (3.11) includes their cancellation at a shared charge vertex when they are adjacent at $m=3$.

For $m\ge5$, the retained graph before $R$, ignoring $B$, is

$$
\mathcal S\setminus\{F_{T-1},F_{T-2}\}.
\tag{3.12}
$$

Its components are exactly

$$
A=\{T-m,T-m+1\},\qquad
D=\{T-2m,T-2m+1\},
\tag{3.13}
$$

and one connected complement of size $T-4\ge3$. To see the component description, use (3.9) in (2.7). The first removed edge cuts off the two-vertex left arm $A$ of $C_q$, and the second cuts off the two-vertex left arm $D$ of $C_{q-1}$. No $H$ chord endpoint lies in either arm; all chord endpoints remain in the complement and keep its remaining path pieces joined.

Consequently its only equal-column pairs are the two vertices of $A$ and the two vertices of $D$. Columns in different components cannot equal each other: each is nonzero and uses only that component's edge coordinates. The row (3.11) is one on exactly one vertex of $A$, namely $T-m$, and exactly one vertex of $D$, namely $T-2m+1$. It therefore separates both residual pairs simultaneously. Adding this coordinate cannot merge columns that were already distinct.

For $m=3$, the graph (3.12) instead has the components

$$
A=\{T-3,T-2\},\qquad \{T-4\},
\tag{3.14}
$$

and one connected complement of size $T-3\ge5$. In (2.7) the second cut now leaves a singleton component; again all chord endpoints stay in the connected complement. The only equal pair is $A$, and the singleton has the sole zero column. The actual word $R=011$ has charge $\{T-5,T-3\}$ by (3.11), so it separates $A$. The columns after $R$ are distinct in this case as well.

Thus deleting the paid coordinates leaves precisely the stated residual collisions, and one final literal row repairs all of them at the same shortened horizon. This deletion-and-repair relation is the additional structural step consumed by the phase decoder; the supplied tree, incidence criterion and charge identities are its reused inputs.

**证明（one stream, all tails, and the exact paid total）。** Choose the nonexceptional or exceptional schedule according to the fixed cut and parameters, independently of the source and both free INITIAL values. Every $E$ starts zero, has one isolated one and ends zero. The exceptional $R$ starts zero and has no one-run longer than two. Since $k\ge2m\ge6$, all suffix seams are safe on every survivor. The parent $B$ ends zero, and its only possible rejection is during the eligible initial run already handled above. The word sets of both alphabets contain every displayed word. Stopping at the final endpoint requires no clearing operation.

A survivor computes its own $q$ all-one differences and its own consecutive differences after $B$, using its own actual parent endpoint as the first suffix baseline. These are exactly its retained incidence-column entries, followed by the repaired row when applicable. Their injectivity determines $j$ over all of $\mathbb Z/T\mathbb Z$. The decoder returns the remembered INITIAL-value component of $\Lambda(j)$, which equals the required $f(v,-j,s)$ for every surviving original tail by (2.3). The current phase is $-j+(t+1)m$ after block $t$; the displacement uses the known issued count, without revealing the original history length.

Earlier rejection branches use only their own prior archives and homogeneous bands. Initial $\bot$ has already stopped at fee zero. No sibling output, promised support or second value-fibre execution is acquired. The same fixed schedule is available across every actual source; archive-dependent early stopping only shortens its prefixes. In particular, separately optimal child continuations are never combined, in accordance with [S2, Proposition 4.2 and Theorem 8.1]. The paid-displacement contract of [S3, Section 8] is preserved throughout.

In the nonexceptional case the complete scheduled fee is

$$
q+1+(T-q-2)=T-1.
\tag{3.15}
$$

In the exceptional case it is

$$
q+1+(T-q-3)+1=T-1.
\tag{3.16}
$$

The terms count, respectively, the all-one prefix, the parent, the remaining $E$ words and, in (3.16), $R$. Every reached block, including all its padding bits, is paid once. Every source therefore pays at most $T-1=k$, proving (3.1). ∎

**数学引文 3.2（Self-calibration and exact scope）。** The construction calibrates the unknown INITIAL phase from retained chronological responses of the same source, while preserving its INITIAL label and all original tail possibilities. The separating code remains injective after the stated coordinate deletion, although its graph need not stay connected; at the exceptional geometry the single actual word $R$ simultaneously resolves the residual equal-column pairs. The parent response is not needed as a phase-separating coordinate in this proof; its endpoint is acquired and used as a baseline, and its block remains paid.

Equation (3.1) is an upper bound conditional on finite GLOBAL-preset cost. It does not assert that adaptive attainability implies GLOBAL attainability. The adaptive structural minimum of [S1, Theorem 62.2 and Scope 64.2] retains its distinct quantifiers. The bound does not give an exact fee for every table or establish that $k$ is optimal. Widths $m=1,2$, the region $k<2m$ and noncoprime calendars lie outside its stated scope. The sharp supremum of finite costs under the present guard remains unresolved. These statements are ordinary paper mathematics.

## 4. Mathematical sources and reuse boundary

**数学引文 4.1（Pinned source interfaces）。** The source-relative status of Theorem 3.1 is `repo-derived`. Its load-bearing addition is the shortened schedule's deletion cases and exceptional simultaneous repair, used in the proof to obtain phase injectivity and then the full-INITIAL common-stream decoder at fee $T-1$. The common-cut law, ordered value join, original tree geometry, boundary-cut bound, incidence collision criterion and literal XOR identities are credited reuse within that proof. No external priority or literature-absence assertion is made.

| Source | Reused mathematical interface |
| --- | --- |
| [S1] [KBonacci INITIAL-target acquisition costs](https://github.com/the-omega-institute/trureturing/blob/049017e05f0c24d3d35a54dc29761cc0e9f17673/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md) | Definitions 1.1–1.3, Convention 1.2 and Interface 1.4: original histories, reader, fees and literal charges. Theorems 24.2 and 29.2 with proofs: one eligible cut across values and archives, and the exact value join. Definition 51.1 and the proof of Theorem 51.2, especially (51.7)–(51.9): actual $H/F$ edges, path components, chord tree and incidence criterion. Theorem 51.3 with proof: the eligible boundary-cut $k$ bound. Theorem 62.2 and Scope 64.2: the separate adaptive law and its GLOBAL boundary. |
| [S2] [KBonacci joint response and seam cost](https://github.com/the-omega-institute/trureturing/blob/3541b57c0d31a89f11fb8b86c75b7b1555e49e6f/docs/develop/theory/KBONACCI_JOINT_RESPONSE_AND_SEAM_COST.md) | Sections 1–4, including Theorems 2.5 and 3.3 and Proposition 4.2: literal response inversion, strict seams, common-tail scope, INITIAL parent data and one common-stream certificates. Theorem 8.1 with proof: separate feasible rows do not guarantee simultaneous safe preset execution. No independent child-optimum combination is used here. |
| [S3] [KBonacci multilabel prefix and terminal cost](https://github.com/the-omega-institute/trureturing/blob/6850a89acdb12d4f17af57dacee2d67e0b514be4/docs/develop/theory/KBONACCI_MULTILABEL_PREFIX_AND_TERMINAL_COST.md) | Section 8, especially Definitions 8.1 and 8.3 and Theorem 8.4 with proof: actual acquired support, paid displacement, strict literal seams and inclusion of the acquired prefix in total fee. No extra one-block cut theorem is claimed here. |

## 追加锚（本行以下为增补区）

## 5. A guarded GLOBAL k-minus-one ceiling

**定理 5.1（Every finite GLOBAL-preset cost is at most k−1）。** For every pair of integers $m\ge3$ and $k\ge2m$ with $\gcd(m,k+1)=1$, every finite nonempty label set $Y$, every full INITIAL target $f:Q_{k,m}\to Y$, and each $A\in\{A_{\rm all},A_{\rm loc}\}$, under the original source, literal-reader, endpoint, common-stream and paid-resource contracts of Section 1,

$$
C_{\rm pre}^{A}(f)<\infty
\quad\Longrightarrow\quad
C_{\rm pre}^{A}(f)\le k-1.
\tag{5.1}
$$

More precisely, every eligible common cut in Definition 2.1 admits one lawful literal stream with uniform worst fee at most $T-2=k-1$, where $T=k+1$. This improves the upper bound in Theorem 3.1 without asserting sharpness.

**证明（reused common cut, value join and actual rows）。** Assume finite cost. Reuse [S1, Theorems 24.2 and 29.2], including their proof bodies, exactly as recorded in Definition 2.1. They supply an eligible

$$
a=qm+r,\qquad 0\le r<m,\qquad a\le T-2.
\tag{5.2}
$$

Put $h=T-qm$. Then $h\ge r+2\ge2$. Retain the ordered labels $\Gamma(j,s)=(f(0,-j,s),f(1,-j,s))$ and $\Lambda(j)=\Gamma(j,0)$ from (2.1). Issue $q$ all-one blocks followed at index $q$ by a parent $B$ whose first zero is at position $r$, counting positions from zero. The eligible bands decode each rejection from that source's own preceding archive. Every survivor has original tail $s<k-a$, and its required ordered label is $\Lambda(j)$.

The parent's bits after its first zero may be chosen freely: every later internal run has length less than $m<k$, and its terminal tail is at most $m-r-1$. The suffix words below begin zero. Thus this is the original common-cut construction on the full INITIAL prior and target.

For $1\le p\le m-1$ define the pulse word and its actual charge edge by

$$
P_p=0^p1\,0^{m-p-1},\qquad
F_t^p=\{tm+p,tm+p+1\}\pmod T.
\tag{5.3}
$$

By the reused literal-charge interface (2.4), namely [S1, Interface 1.4], the earlier all-one rows are $H_t=\{tm,(t+1)m\}$ for $0\le t<q$. At every index $q+1,\ldots,T-3$ issue the same $P_p$; the choices of $p$ and the paid parent are specified below. The scheduled fee is

$$
q+1+(T-q-3)=T-2.
\tag{5.4}
$$

All indices are valid, including the shortest schedules: $T\ge2m+1\ge7$ and $q\le(T-2)/m\le T-4$. In particular, the two late edges at indices $T-2,T-1$ are distinct suffix edges of the comparison tree, and the actual suffix range starts no later than $T-3$.

**证明（shifted supplied tree and incidence collisions）。** Suppose $h\ge3$ and choose $1\le p\le m-1$ with $p<h$. Consider

$$
\mathcal S_p=\{H_0,\ldots,H_{q-1},F_{q+1}^p,\ldots,F_{T-1}^p\}.
\tag{5.5}
$$

This is the shifted form of the tree construction in [S1, proof of Theorem 51.2], reused in Section 2. Coprimality makes $F_0^p,\ldots,F_{T-1}^p$ exactly the adjacent edges of the physical $T$-cycle. The removed edges $F_0^p,\ldots,F_q^p$ have ordered left endpoints $p,m+p,\ldots,qm+p<T$. Their complementary paths, in ordinary representatives, are exactly

$$
\begin{aligned}
C_i&=\{im+p+1,\ldots,(i+1)m+p\} &&(0\le i<q),\\
C_q&=\{qm+p+1,\ldots,T-1\}\cup\{0,\ldots,p\}.
\end{aligned}
\tag{5.6}
$$

The first interval in $C_q$ may be empty; $p<h$ makes this a literal description without an extra wrap. The $H$ chords connect the paths in a chain. For $q>0$, $H_0$ joins $0\in C_q$ to $m\in C_0$, while $H_t$ joins $tm\in C_{t-1}$ to $(t+1)m\in C_t$ for $1\le t<q$. When $q=0$, there is just one spanning path. Thus $\mathcal S_p$ is connected with $T-1$ edges, hence is a tree on all $T$ INITIAL phases.

Temporarily ignore the parent row. The rows actually retained by the stream are the incidence rows of the forest

$$
\mathcal G_p=\mathcal S_p\setminus\{F_{T-2}^p,F_{T-1}^p\}.
\tag{5.7}
$$

It has three components. The two removed edges have left endpoints

$$
x_1=T-m+p,\qquad x_2=T-2m+p,
\tag{5.8}
$$

where an endpoint $T$ is interpreted as zero. In each $C_i$ with $i<q$, all $H$ attachments use its single vertex $(i+1)m$; $C_q$ attaches at zero. Hence all $H$ endpoints remain in one connected component, and each other component is an interval cut off from one of these paths.

Use the incidence-column criterion already supplied in Section 3 and [S1, proof of Theorem 51.2]. Equal zero columns occur precisely at two isolated vertices. If two distinct vertices have equal nonzero columns, every edge incident to either must contain both; they therefore form a component of size two. Conversely, the two vertices of such a component have equal columns. Components with at least three vertices have distinct nonzero columns, and different such components have disjoint nonzero row supports. The actually acquired parent coordinate can split collisions and cannot merge previously distinct columns.

The following seven cases choose $p$ and $B$ and account for every component. Unless explicitly replaced, use $B=1^r0^{m-r}$, whose actual parent charge is $\{qm,qm+r\}$ when $r>0$, and is zero when $r=0$.

**证明（case (a): $3\le h\le m-2$）。** Set $p=1$, so $1\le p\le m-1$ and $p<h$. The guard implies $q\ge2$. In (5.6), the cuts detach the left intervals

$$
\begin{aligned}
&\{(q-1)m+2,\ldots,(q-1)m+h+1\}\subset C_{q-1},\\
&\{(q-2)m+2,\ldots,(q-2)m+h+1\}\subset C_{q-2}.
\end{aligned}
\tag{5.9}
$$

Each has size $h\ge3$. The connected complement has size $T-2h=qm-h\ge m+2$. All three components have size at least three, so the retained incidence columns already separate every phase. The default parent has first zero exactly at $r$ and needs no additional separating property.

**证明（case (b): $h=m-1\ge3$）。** Here $q\ge2$. If $r>0$, set $p=r$ and retain $B=1^r0^{m-r}$. Eligibility gives $1\le r\le m-3$, hence $1\le p\le m-1$ and $p<h$. If $r=0$, set $p=1$ and $B=01\,0^{m-2}$; its first zero is at position zero and again $p<h$.

Since $x_1=qm+p-1$ and $x_2=(q-1)m+p-1$, each cut isolates the final vertex of the corresponding $C$ path. The detached components are

$$
\{u\}=\{qm+p\},\qquad \{w\}=\{(q-1)m+p\},
\tag{5.10}
$$

and the connected complement has size $T-2\ge3$. The only equal-column pair is $\{u,w\}$. For $r>0$, the actual parent support $\{qm,qm+r\}$ contains $u$ and not $w$. For $r=0$, its support is $\{qm+1,qm+2\}$, which also contains $u$ and not $w$. Thus the one paid parent row distinguishes the only collision while preserving the required first-zero position.

**证明（case (c): $h=m+1$）。** Set $p=m-1$, which satisfies $1\le p\le m-1$ and $p<h$; here $q\ge1$. The first deleted edge is $\{T-1,0\}$ and detaches $\{T-1\}$ from $C_q$. The second cuts at $qm$ and detaches

$$
\{qm+1,\ldots,qm+m-1\}\subset C_{q-1},
\tag{5.11}
$$

of size $m-1$. The connected complement has size $T-m\ge m+1$. For $m\ge4$ there is exactly one singleton and no size-two component, so no parent repair is needed; use the default parent.

For $m=3$, the sole equal pair is $\{qm+1,qm+2\}$. If $r>0$, its possible values are $1,2$, and the default parent support $\{qm,qm+r\}$ splits the pair. If $r=0$, take $B=001$; its actual support $\{qm+2,qm+3\}$ splits the pair. Each parent has first zero exactly at the stipulated $r$.

**证明（case (d): $h=m+2$）。** Coprimality gives $\gcd(m,2)=1$, so $m$ is odd, and $q\ge1$. Choose

$$
\begin{cases}
p=m-1,\quad B=1^r0^{m-r-1}1,&0\le r\le m-2,\\
p=m-2,\quad B=1^{m-1}0,&r=m-1.
\end{cases}
\tag{5.12}
$$

Both choices have $1\le p\le m-1$ and $p<h$. In the first branch the zero run is nonempty, so the parent has first zero at $r$; in the second branch that first zero is at $m-1=r$.

For either choice, the first detached interval is the two-vertex set

$$
A=\{qm+p+1,qm+p+2\}.
\tag{5.13}
$$

The second detached interval is

$$
\begin{cases}
\{qm+2,\ldots,qm+m-1\},&p=m-1,\\
\{qm+1,\ldots,qm+m-2\},&p=m-2.
\end{cases}
\tag{5.14}
$$

It has size $m-2$, and the connected complement has size $T-m\ge m+1$. Since $m$ is odd, $m-2$ is one when $m=3$ and is at least three otherwise; it is never two. Thus $A$ is the only equal-column pair.

For $p=m-1$, $A=\{qm+m,qm+m+1\}$. The actual parent ends in one, so its charge at $qm+m$ is one by (2.4); its charge at $qm+m+1$ is zero, since that vertex is outside the parent's path. These are ordinary representatives below $T$. For $p=m-2$, $A=\{qm+m-1,qm+m\}$, and the parent $1^{m-1}0$ has actual support $\{qm,qm+m-1\}$. This again splits $A$. No other collision remains.

**证明（case (e): $m+3\le h\le2m-1$）。** Set $p=1$ and $d=h-m$, so $p<h$, $p\le m-1$ and $3\le d\le m-1$. Here $q\ge1$. The detached $C_q$ interval is

$$
\{qm+2,\ldots,qm+d+1\},
\tag{5.15}
$$

of size $d$. If $3\le d\le m-2$, the other detached left interval is

$$
\{(q-1)m+2,\ldots,(q-1)m+d+1\}\subset C_{q-1},
\tag{5.16}
$$

also of size $d$. The complement has size $T-2d=(q+1)m-d\ge5$. If $d=m-1$, the cut in $C_{q-1}$ instead leaves its last vertex $\{qm+1\}$ as a singleton; the detached $C_q$ interval has size $m-1$, and the complement has size $T-m\ge m+1$. In both subcases there is no size-two component and at most one singleton. Use the default parent with first zero at $r$; no parent repair is needed.

**证明（case (f): $h\ge2m+1$, $h\ne2m+2$）。** Set $p=1$, so $1\le p\le m-1$ and $p<h$. Both cuts lie in the nonwrapped portion of $C_q$. Its detached left interval and the middle interval between the cuts are

$$
\{qm+2,\ldots,T-2m+1\},\qquad
\{T-2m+2,\ldots,T-m+1\},
\tag{5.17}
$$

of sizes $h-2m$ and $m$, respectively. The connected complement has size $(q+1)m$. The first size is either one or at least three, since $h=2m+2$ is excluded, and the other two are at least three. The incidence criterion therefore gives separation without a parent repair. The default parent has first zero at $r$. This also covers $q=0$, when $\mathcal S_p$ is a single spanning path and the connected complement is its remaining interval.

**证明（case (g): $h=2m+2$）。** Again coprimality forces $m$ odd. Choose $p$ and $B$ exactly as in (5.12), with the same constraints $1\le p\le m-1$, $p<h$, and first zero at $r$. Both cuts now lie in $C_q$. The detached left component is $A$ from (5.13), the middle component is

$$
\{qm+p+3,\ldots,qm+m+p+2\},
\tag{5.18}
$$

of size $m$, and the remaining connected component has size $(q+1)m$. Consequently $A$ is the only equal-column pair, also when $q=0$. For $p=m-1$, the parent's final one gives charge one at $qm+m$ and zero at $qm+m+1$, the two vertices of $A$. For $p=m-2$, its support $\{qm,qm+m-1\}$ splits $A=\{qm+m-1,qm+m\}$. These are the same actual parent endpoint calculations as in case (d).

These seven cases exhaust $h\ge3$. The omitted values $h=m$ and $h=2m$ would make $T=qm+h$ divisible by $m$, contradicting coprimality. Cases (a) and (b) require $q\ge2$ by $T\ge2m+1$; cases (c)–(e) require $q\ge1$; cases (f) and (g) include $q=0$. The cut positions (5.8) in the literal intervals (5.6) give the displayed component counts. In every case their complement is connected through the retained $H$ chain, or is the remaining path when $q=0$. Every residual collision is split by one actual paid parent row, without an additional block or an independent abstract response row.

**证明（the boundary remainder $h=2$）。** Eligibility forces $r=0$. Coprimality implies $m$ odd, and the guard gives $q\ge2$. Reuse the boundary stream of [S1, Theorem 51.3]: $q$ all-one blocks followed by $L=0^{m-1}1$, but stop one block earlier, at index $T-3$.

In the supplied construction the $q$ rows $H_0,\ldots,H_{q-1}$ and the $L$ rows at $q,\ldots,T-2$ form a spanning tree. Remove its last row, the actual edge $\{T-m-1,T-m\}$. The supplied cycle-path components are $\{im,\ldots,(i+1)m-1\}$ for $0\le i<q$, and $\{qm,\ldots,T-1\}$. The cut lies in the component with $i=q-1$ and detaches exactly

$$
\{(q-1)m+2,\ldots,qm-1\},
\tag{5.19}
$$

of size $m-2$. Its complement remains connected through the supplied chords and has size $T-m+2\ge3$. Since $m$ is odd and at least three, the detached size is one or at least three. There is no two-vertex component and at most one singleton, so the same incidence criterion gives distinct columns after this deletion.

The shortened boundary stream costs

$$
q+(T-2-q)=T-2.
\tag{5.20}
$$

Its first $L$ is still the paid parent with first zero at $r=0$. Thus this is a shortening of the supplied lawful boundary construction, with neither a free parent nor an omitted charge.

**证明（full INITIAL decoder and actual fees）。** Make the applicable choice once from the fixed parameters and eligible cut, independently of every actual source, phase, free INITIAL value and original tail. This specifies a single literal stream. Before the parent, rejection bands are exactly those in (2.3): an all-one rejection at $t<q$ uses $S_t(\beta)$ and $h_t-m\le s<h_t$. Parent rejection uses $S_q(\beta)$ and $h_q-r\le s<h_q$. Each such source decodes the constant ordered pair on its own band from its own earlier chronological archive and returns the component selected by its remembered free INITIAL value. It pays for its rejecting block. Initial $\bot$ returns its independent $f(\bot)$ at fee zero.

Every survivor has original tail $s<k-a$, so $s+qm+r<k$ and it reaches the parent's first zero. Subsequent internal parent runs are safe because $m<k$. Every $P_p$ and $L$ begins zero and has one isolated one; successive suffix blocks therefore safely clear any previous terminal tail, including when a parent ends in one. All displayed words have length $m<k$ and belong to both original alphabets. The actual cross-block rejection during the initial all-one prefix and the parent's leading run is retained.

A survivor computes its own $q$ earlier differences, its own parent difference and its own consecutive suffix differences, using its actual parent endpoint as the first suffix baseline. The preceding separation argument concerns exactly these acquired charge coordinates. For $h\ge3$, the earlier $H$ rows and suffix rows have the columns of $\mathcal G_p$, and the actual parent row splits every remaining pair. At $h=2$, the shortened boundary rows themselves already have distinct columns. Hence the survivor recovers its INITIAL phase parameter $j\in\mathbb Z/T\mathbb Z$ and returns the remembered INITIAL-value component of $\Lambda(j)$. Eligibility makes this precisely $f(v,-j,s)$ for every surviving original tail, not a target on the current state.

Only that source's own scalar endpoints and freely remembered initial value are used. The issued-block count determines displacement from the INITIAL phase without revealing original history length or observing interior bits. Convention 1.2 supplies every jointly realized original $(v,-j,s)$ in this argument; no promise on acquired support replaces the full INITIAL prior. No sibling archive is executed, borrowed or combined. Both values, all phases and all tails receive prefixes of the same literal stream, with archive-dependent early stopping allowed. There is no reset, copy, clearing action outside a paid word, free wait or free calendar displacement.

Every scheduled whole block is charged, including padding, duplicate or waiting words if any, and every rejecting branch pays its rejecting block. Equations (5.4) and (5.20) give maximum scheduled fee $T-2=k-1$; earlier stops only reduce it. Thus (5.1) holds for both $A_{\rm all}$ and $A_{\rm loc}$. ∎

## 6. Mathematical sources and scope of the improved ceiling

**数学引文 6.1（Reused interfaces and the compatibility relation）。** The source-relative status of Theorem 5.1 is `repo-derived`. The common-cut law and ordered value join are reused from [S1, Theorems 24.2 and 29.2] in exactly the form of Definition 2.1. The literal charges are [S1, Interface 1.4] and (2.4). The supplied chord-tree geometry and boundary tree are reused from [S1, proofs of Theorems 51.2–51.3]; the incidence-column criterion is reused from the proof of Theorem 51.2 and Section 3. The earlier deletion-and-repair construction is Theorem 3.1. These are mathematical sources for the proof, without a claim of literature priority.

The additional relation is the compatibility, for every eligible $(q,r)$, of a remainder-dependent pulse position and an actual first-zero parent with injectivity of the retained $H$ rows, the paid parent row and pulse rows only through $T-3$. At $h=2$ it is the injectivity of the shortened supplied boundary stream. Cases (a)–(g) and (5.19) establish this relation, and the full INITIAL decoder consumes it directly at total fee $T-2$. The tree translation, charge identities and incidence criterion are reused inputs to that relation.

**数学引文 6.2（Exact mathematical scope）。** Theorem 5.1 is a conditional upper bound for every finitely attainable full INITIAL GLOBAL-preset target under the guard $m\ge3$, $k\ge2m$, $\gcd(m,k+1)=1$. It establishes neither sharpness nor an exact fee for each target. Theorem 3.1 remains valid. No extension to excluded parameters or conversion from adaptive attainability to GLOBAL attainability follows. The original hidden-history, joint-source, endpoint, own-archive, both-value, all-tail and whole-block fee contracts remain those of Section 1. The conclusion is ordinary paper mathematics, with no external priority or global novelty claim.

## 追加锚（本行以下为增补区）

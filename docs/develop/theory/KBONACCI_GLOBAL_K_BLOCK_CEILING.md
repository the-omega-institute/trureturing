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

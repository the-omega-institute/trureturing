# KBonacci prefix-label spectrum cost

## 1. Original source and immutable labels

**定义 1.1（Reader and fee）。** Fix integers $Q\ge2$ and $m\ge3$, and put $k=Qm$ and $T=k+1$. The original integer reader has weights

$$
G_i=2^i\quad(0\le i<k),\qquad
G_i=\sum_{a=1}^kG_{i-a}\quad(i\ge k),\qquad
V_k(w)=\sum_{i<|w|}w_iG_i.
\tag{1.1}
$$

Bits are read in increasing weight position. A word is legal when it avoids $1^k$; its successful reading is $V_k(w)\bmod2$. The matched coefficient interface of [S2, Sections 13–14] is

$$
c_i=G_i\bmod2=\mathbf1_{\{0,-1\}}(i\bmod T).
\tag{1.2}
$$

The source prior consists of all actual finite complete-block histories, including the empty history and rejected histories. Since $\gcd(m,T)=1$, its successful joint records are all

$$
(v,\theta,s)\in\mathbb F_2\times\mathbb Z/T\mathbb Z\times\{0,\ldots,k-1\}.
\tag{1.3}
$$

There is also a separate absorbing record $\bot$, whose reading differs from both legal readings. Its literal transitions are

$$
\delta_0(v,\theta,s)=(v,\theta+1,0),\qquad
\delta_1(v,\theta,s)=
\begin{cases}
(v\oplus c_\theta,\theta+1,s+1),&s+1<k,\\
\bot,&s+1=k,
\end{cases}
\qquad \delta_b(\bot)=\bot.
\tag{1.4}
$$

A control action emits one literal word of exactly $m$ bits. The two control alphabets are all such words and all internally legal such words. Here $m<k$, so these literal alphabets agree; cross-block rejection is checked in either. The initial reading is free, and every subsequent reading is acquired only at a complete-block endpoint. Every emitted block, including every $0^m$ wait, costs one. The fee is the worst branch's number of emitted blocks. Offline computation and controller memory are separate resources. A returned label belongs to the INITIAL record, even if its current tail, phase, or value has changed. There is no reset, copy, intermediate observation, hidden initial clock, or observation obtained by combining different branches. These source and acquisition conventions are those of [S1, Sections 1–2].

Let $C_{\rm ad}(f)$ be the minimum fee of a correct deterministic adaptive protocol for an INITIAL target $f$. Let $C_{\rm pre}(f)$ require one fixed literal block stream for all sources, with stopping and decoding permitted to depend on the endpoint archive. Both legal initial-value fibres are included in either fee. The initially visible $\bot$ returns its independently specified label for free. In particular $C_{\rm ad}(f)\le C_{\rm pre}(f)$.

The full joint prior in (1.3) is essential. Its actual-history witnesses are supplied by [S1, Convention 1.3; S15, equation (1.1)]. Explicitly, for any $v,j,s$, choose an integer $n$ satisfying

$$
n\equiv0\pmod m,\quad n\equiv-j\pmod T,\quad n\ge s+2,
\qquad D=\bigoplus_{i=n-s}^{n-1}c_i,
$$
$$
w=(v\oplus D)0^{n-s-1}1^s.
\tag{1.5}
$$

The first factor is one bit. There is a zero between it and the terminal $s<k$ ones, so this single word is legal. Its first bit contributes $v\oplus D$ because $G_0=1$, and its terminal run contributes $D$. Thus its record is exactly $(v,-j,s)$. Its length is a multiple of $m$, so it is one actual complete-block history under either alphabet. Witness lengths are not observed and may differ between sources. The rejected history $(1^m)^Q$ supplies $\bot$. All sources used below are therefore jointly realized, rather than assembled from independently attainable coordinates.

**定义 1.2（Repeated band target）。** Set $I=\{1,\ldots,m-1\}$. Let $Y$ be a label set, let $\lambda:I\to Y$ be any nonconstant map, let $A\in Y$ be an outside label, and choose $R\in Y\setminus(\{A\}\cup\lambda[I])$. Repetitions and arbitrary ordering in $\lambda$ are allowed, and $A$ may be a band label. For $j=-\theta_{\rm INITIAL}\pmod T$ define, on both legal initial-value fibres,

$$
f(v,-j,s)=
\begin{cases}
R,&s\ge k-m,\\
\lambda(j),&s<k-m,\ j\in I,\\
A,&s<k-m,\ j\notin I.
\end{cases}
\tag{1.6}
$$

The label at initial $\bot$ is arbitrary and separately specified. Call $s\ge k-m$ high and $s<k-m$ low. This is the full-block threshold target of [S18, Convention 1.2], with a general repeated band table. The binary layouts, first returning-frontier classification, and injective tables in [S18, Theorems 3.1, 4.1, 5.1] are supplied special cases, not additional claims of this volume.

## 2. Prefix spectrum and literal query calendar

**定义 2.1（Spectrum and surcharge）。** For $1\le t\le m-1$, define the distinct-label count

$$
n_t=\left|\lambda[\{1,\ldots,m-t\}]\right|.
\tag{2.1}
$$

This counts labels, not occurrences. Define

$$
h=\min\{r\in\{1,\ldots,m-2\}:n_{r+1}\le2^r\},
\tag{2.2}
$$
$$
e=\mathbf1_{\{n_h>2^h\ \text{or}\ (Q=2,\ m\text{ odd},\ h=1,\ A\notin\lambda[I])\}}.
\tag{2.3}
$$

The minimum exists: $n_{m-1}=1\le2^{m-2}$. Thus $1\le h\le m-2$. Nonconstancy gives $n_1\ge2$. If $h>1$, minimality gives $n_h>2^{h-1}$; the same strict inequality holds for $h=1$ because $n_1>1$. Removing one phase removes at most one distinct label. Consequently, when $n_h>2^h$, necessarily $n_h=2^h+1$ and $n_{h+1}=2^h$: the label at $m-h$ is absent from the shorter prefix. These elementary observations will be used inside the cost proof.

**约定 2.2（Responses and actual inverse）。** Absolute block index $t$ starts at zero; the endpoint of block $t$ has total fee $t+1$ on a continuing branch. Write $u_t=tm\pmod T$ and use the ordered window $W_t=[u_t,u_t+m]\pmod T$. For a successful word $x_0\cdots x_{m-1}$, its endpoint difference as a function of INITIAL phase index $j$ is supported in this window and satisfies

$$
q_t(u_t)=x_0,\qquad
q_t(u_t+i)=x_{i-1}\oplus x_i\ (1\le i<m),\qquad
q_t(u_t+m)=x_{m-1}.
\tag{2.4}
$$

For every even-cardinality set $E\subseteq W_t$, the actual inverse is

$$
\mathcal B_t(E)_i=\bigoplus_{a=0}^{i}\mathbf1_E(u_t+a),
\qquad 0\le i<m.
\tag{2.5}
$$

It emits exactly $m$ literal bits and has response support exactly $E$, including the right endpoint. The charge condition and inverse are reused from [S10, Interface 2.1; S15, Section 1]. Safety must additionally be proved from the current tail. An algebraic span is not substituted for an action. A parity donor below is a phase absent from the actual archive where it is used.

The calendar [S16, Section 2; S18, equation (1.8)] is

$$
W_{rQ+b}=[bm-r,(b+1)m-r]\pmod T,\qquad 0\le b<Q,
\tag{2.6}
$$

since $Qm\equiv-1\pmod T$. For all tours used below, $r\le h\le m-2$. Main indices are $rQ$ with $1\le r\le h$; frontier indices are $rQ+1$. They refer to the number of blocks this protocol has emitted, not to the unobserved length of an INITIAL history.

## 3. Exact fee for every repeated band table

**定理 3.1（Prefix-label spectrum law）。** For every $Q\ge2$, $m\ge3$, every nonconstant $\lambda:I\to Y$, and every outside-label coincidence allowed in Definition 1.2, with $h,e$ defined by (2.2)–(2.3),

$$
C_{\rm ad}(f)=C_{\rm pre}(f)=hQ+1+e.
\tag{3.1}
$$

Proof. We first prove the lower bound for every adaptive action tree, and then exhibit a preset stream of the same fee.

At each fixed $v,j$, the actual tails $k-m-1$ and $k-m$ have different INITIAL labels. By the first-zero loss principle [S1, Lemma 4.3 and Theorem 5.2], a root with a zero after fewer than $m$ leading ones would merge these two sources before any acquired endpoint. Their lost distinction cannot be recovered. A root cannot stop either. Hence the root is necessarily $1^m$. It rejects exactly the high tails, has successful response support $\{0,m\}$, and puts every band phase in its successful zero-difference child. All high sources then return $R$.

The full-block structural boundary [S18, Theorem 2.1] applies to this nonconstant table without any injectivity assumption. On the root-zero child, two differently labelled band phases with INITIAL tail $k-m-1$ have current tail $k-1$ and the same current value and archive. A second block beginning with one rejects and permanently merges them. Thus this second block starts zero. It succeeds for all remaining low sources and makes their current tail common. The band has a common zero-difference archive through the first $Q$ paid blocks, since every first-tour window after the root misses $I$.

After this compulsory zero, within any acquired archive all its candidates have the same current value and tail. An action's rejection depends on that tail and its literal bits, not on phase. A rejecting action therefore supplies no extra distinguishing leaf at a nonconstant node: all its candidates become the same absorbing record. Such a node cannot occur in a correct tree. Constant nodes can stop before any further action. Every useful endpoint is consequently binary, and its successful difference is (2.4).

Restrict to the jointly realized sources with one fixed free value, INITIAL tail zero, and phases

$$
K_h=\{1,\ldots,m-h\}.
\tag{3.2}
$$

Up to total fee $hQ$, their only possible informative indices are $Q,2Q,\ldots,(h-1)Q$. To verify this for all literal actions, an index after the root and before $hQ$ has the form $rQ+b$. If $b\ge1$, then $r\le h-1$ and its window starts at $bm-r\ge m-h+1$, strictly above $K_h$; its right endpoint is at most $k-r<T$, so there is no wrap into that prefix. If $b=0$ and $r\ge1$, it is one of the stated main indices. The root itself has zero response throughout $I$. Thus even an adaptive tree has at most $h-1$ binary branching opportunities on these sources. Pruning constant restricted nodes gives at most $2^{h-1}$ label leaves. But $K_h$ contains $n_h>2^{h-1}$ different labels by Definition 2.1. Hence total fee $hQ$ is impossible.

At total fee $hQ+1$, exactly one more main endpoint, at index $hQ$, is available to the same prefix. Its label capacity is at most $2^h$. Therefore $n_h>2^h$ forces one more paid block. These counts use only actual sources on each tree branch. They do not combine observations from different branches, or presume that sources with the same label need the same code.

The other condition in (2.3) has $h=1$. If $n_1>2$, the preceding prefix count already excludes fee $Q+1$. Otherwise nonconstancy gives exactly two band labels. For $Q=2$ and odd $m$, [S18, Theorem 2.1] says every correct first tour retains at least one actual outside phase on the band's zero archive. Its label $A$ is fresh in the exceptional condition. Thus three different INITIAL labels share that archive after two blocks, with common current value and tail; one remaining endpoint can provide at most two successful readings, and uniform rejection cannot distinguish them. Fee $Q+1$ is impossible. Equivalently this is the fresh-outside case of [S18, Theorem 3.1]. All conditions in (2.3), including when both hold, therefore imply the lower bound $hQ+1+e$.

We now construct actual words attaining this bound. Put

$$
p=h-1+e,\qquad n=m-1-p=m-h-e,\qquad
K=\{1,\ldots,n\},\qquad H_r=m-r\ (1\le r\le p).
\tag{3.3}
$$

The core $K$ is nonempty. Its distinct-label count is at most $2^h$: when $e=0$ it is $n_h\le2^h$, and when $e=1$ it is $n_{h+1}\le2^h$. Choose an injective code assignment

$$
c:\lambda[K]\longrightarrow\{0,1\}^h,
\qquad c(y)=(c_1(y),\ldots,c_h(y)).
\tag{3.4}
$$

Codes are assigned to core labels, not to occurrences. The $p$ other band phases $H_1,\ldots,H_p$ are treated individually. A repeated label may occur in the core and at several of these phases; its several acquired codes are permitted to differ.

Use the supplied first-tour scans [S18, Theorem 2.1 and Convention 2.2]. Their literal choices, needed for the later donor and seam conditions, are as follows. Index zero is $1^m$. If $m$ is even, indices $1,\ldots,Q-1$ use the length-$m$ word $Z_m=(0,1,0,1,\ldots)$. If $m$ is odd and $Q\ge3$, index one uses $Z_m$ and indices $2,\ldots,Q-1$ use $O_m=(1,0,1,0,\ldots,1)$. On the root-zero child their continuing zero archive is exactly $I$; every scan-positive archive has label $A$ and stops. Phase $k$ is excluded there.

If $Q=2$ and $m$ is odd, instead use the second word

$$
Z'_m=00(10)^{(m-3)/2}1.
\tag{3.5}
$$

Its support is $\{m+2,\ldots,2m\}$, so the continuing root-zero archive is exactly $I\cup\{z\}$, where $z=m+1$. Its sole extra source has label $A$. Phases $0,m,k$ are excluded from this same archive. The scan-positive sources again stop with label $A$. The index-one word begins zero, hence is safe even from root tail $k-1$; subsequent scan seams are strict. These are the actual screening facts of [S18], reused here.

There is one code convention when the exceptional scan has no frontier row. Namely, if $Q=2$, $m$ is odd, and $p=0$, then $h=1$, $e=0$, $\lambda[I]$ has exactly two labels, and $A\in\lambda[I]$. Here $K=I$; choose $c(A)=0$ and the other label's bit one. The extra source $z$ will have zero main response and can correctly share the code of $A$.

For $1\le r\le h$, let

$$
F_r=\{j\in K:c_r(\lambda(j))=1\}.
\tag{3.6}
$$

At the first main index $Q$, put

$$
L_1=F_1\cup\{0\}\cup
\begin{cases}
\{H_1\},&Q=2,\ m\text{ odd},\ p\ge1,\\
\varnothing,&\text{otherwise},
\end{cases}
$$
$$
E_Q=L_1\cup
\begin{cases}
\{k\},&|L_1|\text{ odd},\\
\varnothing,&|L_1|\text{ even}.
\end{cases}
\tag{3.7}
$$

All these vertices lie in the ordered window $W_Q=[k,0,1,\ldots,m-1]$. Phase $k$ is absent from the continuing root-zero archive in either scan. Phase 0 is also absent there, so its deliberately fixed response one does not alter the band or the extra source. For every later main index $rQ$, $2\le r\le h$, use

$$
E_{rQ}=F_r\cup
\begin{cases}
\{0\},&|F_r|\text{ odd},\\
\varnothing,&|F_r|\text{ even}.
\end{cases}
\tag{3.8}
$$

The whole core belongs to $W_{rQ}=[-r,m-r]\pmod T$, since $n\le m-h\le m-r$. Phase 0 is in this window and absent from the acquired root-zero archive. The left endpoint $-r$ is unselected. Both (3.7) and (3.8) have even charge. Emit their actual inverses (2.5).

For $1\le r\le p$, at index $rQ+1$ use

$$
E_{rQ+1}=
\begin{cases}
\{H_1,z\},&Q=2,\ m\text{ odd},\ r=1,\\
\{H_r,m\},&\text{otherwise}.
\end{cases}
\tag{3.9}
$$

These are actual even supports in $W_{rQ+1}=[m-r,2m-r]$. In the ordinary rows, phase $m$ was excluded at the root. The row's literal word is $1^r0^{m-r}$; it selects only the band phase $H_r$ among continuing band sources. In the exceptional first row, both $H_1$ and $z$ are actual continuing sources, and the inverse is $110^{m-2}$. No absent-donor assertion is made for $z$.

Every core phase is strictly below every frontier window: its largest possible value is $m-h-e$, whereas the smallest frontier endpoint is $m-p=m-h+1-e$. Of the other band phases, exactly $H_r$ has response one at frontier row $r$; those numerically above it lie in the window but were prescribed zero. All unmentioned absolute indices between the scan and the last selected row use the literal paid wait $0^m$.

For decoding, retain successive endpoint differences together with the root and scan archive. Ignore the coordinates at paid zero waits, which are known to be zero. On the continuing root-zero archive, write a code as its $h$ main coordinates and $p$ frontier coordinates. Each core label $y$ has code $(c(y),0^p)$. Every ordinary frontier phase $H_r$ has main code $0^h$ and frontier unit vector with coordinate $r$ one. These codes cannot coincide with a core code or with each other. Different occurrences of the same band label may have these different codes; each code is decoded to its own INITIAL label $\lambda(H_r)$ or $y$. Thus repetitions across any of these geometric regions cause no false identification.

For the exceptional scan with $p\ge1$, $z$ and $H_1$ share the first frontier coordinate one, but (3.7) assigns their first main coordinates zero and one respectively. All later main coordinates of both are zero. Indeed $H_1$ is beyond the right endpoint of every later main window, and $z=m+1$ is outside every main window through $h\le m-2$: it exceeds each nonnegative right endpoint and lies below the negative segment's least residue $T-h\ge m+3$. At later frontier rows, $z$ is prescribed zero and $H_1$ is prescribed zero. Hence their two full codes differ. Neither has the all-zero frontier code of a core source, and neither shares another frontier phase's unit vector. Decode $z$ to $A$ and $H_1$ to $\lambda(H_1)$. This remains correct whether $A$ is fresh or coincides with any core or frontier label. For $p=0$, the special one-bit convention already decodes the same $z$ correctly. Thus every remaining archive has a unique INITIAL label.

All words are legal at their actual seams. After the compulsory index-one zero, a scan tail is at most one. The first main word has response one at the interior vertex 0: if its first bit is one, its second bit is zero; if its first bit is zero, it already has a zero. Its leading run is at most one and its terminal run at most $m-1$. Each later main word starts zero, because its left endpoint $-r$ is unselected. Each ordinary frontier word has leading run $r\le p\le h\le m-2$ and terminal run zero. The exceptional frontier word has leading run two and terminal run zero. Every post-scan word contains zero, so every leading or terminal run is at most $m-1$. The general seam bound is the strict inequality

$$
2m-2<k=Qm.
\tag{3.10}
$$

In particular a main word's terminal ones followed by the exceptional leading two have total length at most $m+1<2m\le k$. Paid zero waits are safe and clear the tail. No terminal cleanup is needed; the final word's actual terminal tail is simply retained.

The last index is $hQ$ when $e=0$ and $hQ+1$ when $e=1$, so exactly $hQ+1+e$ complete blocks are available on the stream's longest branch. The counts include all intervening waits. Initial $\bot$ stops free; root rejection stops at fee one with $R$; the successful root-positive child stops at fee one with $A$; scan-positive children return $A$ at their acquired endpoints; all other children use the displayed decoder and stop by the final endpoint. Every decoder uses only its own archived outputs and the stream's known emitted indices. Both free values use the same literal stream and endpoint differences. The adaptive lower bound and this preset attainment coincide, proving (3.1). ∎

The smallest width is included without a separate convention: for $m=3$, $h=1$ and the two band labels are different. When $Q=2$ and $A$ is fresh, $e=1$, the core is $\{1\}$, and the first frontier row handles $H_1=2$ and $z=4$. When $A$ is a band label, $e=0$ and the special zero-code convention applies. For $Q\ge3$ the ordinary scan removes all outsiders. At the limiting permitted $h=m-2$, the construction still has $n=m-h-e\ge1$ and $p\le m-2$; every donor, window, and strict seam used in the proof remains valid.

The law also exhibits arrangement dependence with equal multiplicities beyond the first returning window. Take $m=12$ and any $Q\ge2$. The two band tables

$$
(B,B,B,C,C,C,L,L,L,U,V),\qquad
(U,V,B,B,B,C,C,C,L,L,L)
\tag{3.11}
$$

have the same five distinct labels and multiplicities $(3,3,3,1,1)$. For the first table, $n_2=4$ and $n_3=3$, so $h=2,e=0$ and the fee is $2Q+1$. For the second, $n_2=n_3=5$ and $n_4=4$, so $h=3,e=0$ and the fee is $3Q+1$. These fees hold for any allowed $A$. In the second construction the label $L$ appears both in the core and at the two separately queried frontier phases, illustrating why codes need not be constant on a label outside the core. This example is an application inside (3.1), rather than a claim that total label count or multiplicities determine the fee.

## 4. Independent endpoint labels on one common stream

**定理 4.1（Simultaneous endpoint refinement）。** Under all hypotheses of Theorem 3.1, choose additional labels $D,E$ in a containing label set, distinct from each other and from $\{R,A\}\cup\lambda[I]$. Replace the low-tail labels at phases $j=0$ and $j=m$ by $D$ and $E$, respectively, retaining (1.6) elsewhere and the separately specified label at initial $\bot$. Denote the refined INITIAL target by $f_{D,E}$. Then, with the same $h,e$ from the band and outside label,

$$
C_{\rm ad}(f_{D,E})=C_{\rm pre}(f_{D,E})=hQ+1+e.
\tag{4.1}
$$

The preset optimum is attained by one common literal stream across both successful root children, with endpoint-dependent stopping.

Proof. Coarsening the two fresh labels $D,E$ to $A$ recovers exactly $f$. Applying this map only to returned labels converts any correct adaptive protocol for $f_{D,E}$ to a protocol for $f$ of the same or smaller fee, without altering any action or observation. Theorem 3.1 therefore supplies the adaptive lower bound. This step is only a lower bound; it does not infer a common preset stream from separately optimized children.

For attainment use exactly the literal stream (3.5)–(3.9) and its ordinary scan alternatives from the proof of Theorem 3.1. Root $1^m$ rejects the high tails with label $R$. On the root-zero child, phases 0 and $m$ are absent, and the target and decoder agree exactly with the proof of Theorem 3.1. On the root-positive child the support is precisely $\{0,m\}$, with labels $D,E$; every such source has a low INITIAL tail. The common index-one word starts zero, so both are safe even when their current tail is $k-1$.

Phase $m$ is the left endpoint of $W_1$ and its response is zero because this word starts zero. Phase 0 lies outside $W_1$. Every further first-tour window lies above $m$, so neither source has a nonzero scan response. Hence both remain on this child through the first $Q$ paid blocks. The common main word at index $Q$ has $q_Q(0)=1$ by (3.7), whereas phase $m$ lies outside $W_Q$ and has response zero. At this endpoint the positive-root child therefore returns $D$ on difference one and $E$ on difference zero, and stops at total fee $Q+1$.

The parity compensation in (3.7) is important here. Phase 0 is an observed source on this child, and is assigned response one rather than used as an absent donor. Compensation is at phase $k$, which the root excluded from this child and the scan excluded from the other continuing child. Its possible response one makes the first main bit one but forces the second bit zero, as proved above. Thus this shared word remains safe and actually distinguishes $D,E$. Later rows may compensate at 0 because this root-positive child has already stopped; no later observation on it is needed or borrowed. The root-zero child still has the same missing phase 0 and the same literal safety as before.

There is no exceptional surcharge beyond (2.3). In particular, if $Q=2$, $m$ is odd, $h=1$, and $A$ is a band label, then $p=0$ and the special convention $c(A)=0$ decodes $z$ on the root-zero child while the very same main word distinguishes $D,E$ on the positive child. If $A$ is fresh, $e=1$ and the frontier row separates $z$ as in Theorem 3.1; the positive-root child has already stopped. If $h\ge2$, the first frontier row already exists and handles $z$ with no extra tour, irrespective of whether its label also occurs in the band.

Every active branch uses an initial segment of this one stream, all its seams are strict, and its latest stopping endpoint costs $hQ+1+e$. Both free values use the same differences; the initially known $\bot$ stops free with its specified label. This actual common-stream upper bound matches the adaptive lower bound. ∎

## 5. Mathematical sources and boundaries

**数学引文 5.1（Reuse and migration conditions）。** The source, first-zero obstruction, literal path inverse, and calendar are reused with their original hypotheses. The new deductions are (3.1) for arbitrary repeated band tables and later returning horizons, and (4.1) with the simultaneous common-stream condition. They are `repo-derived` ordinary mathematics.

| Supplier | Exact use and boundary |
| --- | --- |
| [S1], Sections 1–2, Convention 1.3, Lemma 4.3, Theorem 5.2 | Original actual-history prior, immutable INITIAL labels, first-zero loss, absorbing rejection, free initial reading, and emitted-complete-block fee. Its generic first-zero criterion is reused rather than restated as a new cost theorem. |
| [S2], Sections 13–14 | Original integer reader's matched mod-two coefficient cycle. No chosen scalar or different recurrence replaces this interface. |
| [S10], Interface 2.1; [S15], Sections 1–3 | Consecutive-window response, even charge, actual inverse, and common-tail operation safety. The present construction supplies literal words and checks the INITIAL parent and every seam. A linear response span alone is insufficient. |
| [S13], Definition 1.3, Theorem 2.3, Theorem 8.4 | Guarded arbitrary phase-label costs and actual-support one-block certificates. Their phase-only parent and bounded retirement horizon do not supply the forced full-one mixed-tail parent or the later fixed-table spectrum fee here. |
| [S15], Proposition 4.2 | Separately preset-optimal children do not imply one common preset optimum. Theorem 4.1 explicitly realizes that additional condition. Generic adaptive-tree or Bellman descriptions supply no spectrum fee. |
| [S16], Section 2 | Calendar and binary leaf capacity under the fixed actual observations. Its phase-only capacity does not eliminate the full-INITIAL threshold obligation. |
| [S17], Definition 2.1 and Theorem 3.1 | The strict $a<m$ forced-prefix family and its width guard are supplied background. The present threshold has $a=m$, so that zero-containing parent and its fee are not specialized here. |
| [S18], Theorem 2.1, Convention 2.2 | Forced full-one root, compulsory next zero, and actual first-tour scans, including the odd-width residual source. These exact archive facts are used in every construction. |
| [S18], Theorems 3.1, 4.1, 5.1, 6.1 | Binary layouts, the $Q+2$ boundary, injective bands, and binary independent-endpoint refinement are supplied overlap. The proofs here extend to repeated labels, outside-label coincidences at later horizons, and one common stream for arbitrary band tables. The unused ancillary $10Q+1$ bound remains `ASSUMED-UNVERIFIED` and is excluded from the premises. |

The original source correspondence also appears in the repository declarations `LiteralModel.literal_block_execution`, `LiteralModel.joint_history_realization`, `EndpointCells.first_zero_block_exact`, and `whole_first_zero_acquisition`, under their original reader and actual-history hypotheses. They supply source interfaces and acquisition principles, rather than the repeated-table fee. Their formal statements are not an identification of this ordinary proof with a kernel-verified application.

**数学引文 5.2（External identification and query contracts）。** The following primary sources describe adjacent established theories. They support the stated general principles and terminology; none supplies the literal calendar optimum (3.1).

Petra van den Bos and Frits Vaandrager, [State Identification for Labeled Transition Systems with Inputs and Outputs, arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2), Definition 11 and Figure 3, describe adaptive distinguishing graphs and the loss caused by an action merging different initial states. This general obstruction is compatible with the first-zero argument. Their general input/output setting does not furnish the KBonacci phase windows, tail threshold, or paid endpoint opportunities used here.

Anastasiya Chistopolskaya and Vladimir V. Podolskii, [Parity Decision Tree Complexity is Greater Than Granularity, arXiv:1810.08668v1](https://arxiv.org/html/1810.08668v1), introduction and Section 2.2, allow arbitrary-subset parity queries on a Boolean input. The binary leaf count is an elementary shared principle. Such unrestricted queries do not imply that a prescribed phase subset is an available literal block: (2.4)–(2.5), current-tail legality, and the calendar must all be satisfied. In particular a one-hot phase encoding does not bypass an unavailable endpoint opportunity.

Uraz Cengiz Türker, Robert M. Hierons, Mohammad Reza Mousavi, and Khaled El-Fakih, [Efficient State Identification for Finite State Machine-Based Testing, accepted manuscript](https://eprints.whiterose.ac.uk/id/eprint/230260/1/Ordered_Wset_Accepted.pdf), [DOI 10.1109/TSE.2025.3604472](https://doi.org/10.1109/TSE.2025.3604472), Definitions 13–15 and 18, distinguish transfer-free identification paths, pairwise shortest distinguishing prefixes, ordered characterising sets, and bounded total transfer length. The accepted manuscript has SHA256 `a20067072d7349615f42c05ad7b431de04389c035b81f2388d779230dc906c7a`. Its transfer-free paths need no added transfer and cannot uniformly be described as reset-based. Their specified-start coverage of every state/word pair and pairwise-prefix minimality differ from one unknown immutable INITIAL label's worst emitted-block fee. No equivalence of those optimization objectives is presumed.

These external correspondences are `literature-attested` within the scopes just stated. The prefix-spectrum fee and common-stream realization are deductions from the fixed source and constructions above; no exhaustive literature absence or priority claim accompanies them.

**开放问题 5.3（Remaining exact-cost objective）。** The minimum worst-branch actual emitted-complete-block fee for every arbitrary attainable immutable INITIAL target and all original $k\ge2,m\ge1$ remains open. Theorems 3.1–4.1 settle the complete repeated-band layout in (1.6), including independent fresh labels at its two root endpoints, for $k=Qm$, $Q\ge2$, $m\ge3$. They do not settle general mixed INITIAL-tail partitions, several differently labelled outside regions, competing admissible parent actions, nonmultiple $k/m$, or the excluded smaller widths. The full-one root and the calendar prefix are material hypotheses of the proof, so a generic adaptive testing optimum cannot remove these remaining source-specific obligations.

[S1]: https://raw.githubusercontent.com/the-omega-institute/trureturing/f64d9e5dc37301e04ffc33332c919dd56a81ed6f/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md
[S2]: https://raw.githubusercontent.com/the-omega-institute/trureturing/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md
[S10]: https://raw.githubusercontent.com/the-omega-institute/trureturing/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md
[S13]: https://raw.githubusercontent.com/the-omega-institute/trureturing/6850a89acdb12d4f17af57dacee2d67e0b514be4/docs/develop/theory/KBONACCI_MULTILABEL_PREFIX_AND_TERMINAL_COST.md
[S15]: https://raw.githubusercontent.com/the-omega-institute/trureturing/3541b57c0d31a89f11fb8b86c75b7b1555e49e6f/docs/develop/theory/KBONACCI_JOINT_RESPONSE_AND_SEAM_COST.md
[S16]: https://raw.githubusercontent.com/the-omega-institute/trureturing/5c531690b4ee33e642757c8485297e94aba5d9a1/docs/develop/theory/KBONACCI_INITIAL_CALENDAR_CAPACITY.md
[S17]: https://raw.githubusercontent.com/the-omega-institute/trureturing/799d8549ae4d270122eb9a2a42024fdbbbe69459/docs/develop/theory/KBONACCI_FORCED_PREFIX_PARITY_COST.md
[S18]: https://raw.githubusercontent.com/the-omega-institute/trureturing/f65f9a766bc1380a37a465f99c9cab6090ed06ff/docs/develop/theory/KBONACCI_FULL_BLOCK_THRESHOLD_COST.md

## 追加锚（本行以下为增补区）

# KBonacci three-class root-zero compatibility prices

This companion prices a tail-independent three-label table on an actually paid root-zero archive, then consumes that price in a full INITIAL target whose two free-value tables are different. The [canonical INITIAL cost theory][IC] supplies the experiment and value-join law; the [mixed-tail cut-price companion][MC] supplies the binary prices and subsequent-window geometry. The conclusions below are restricted ordinary mathematical proofs. The exact adaptive and one-GLOBAL-stream fees for every arbitrary attainable immutable INITIAL target and every original $k\ge2,m\ge1$ remain the original unresolved objective.

## 1. The paid archive and its physical calendar

**约定 1.1（Original sources, observations and fees）。** Retain [IC, Definitions 1.1–1.3 and Interface 1.4]: the original integer KBonacci weights, matched $V_k\bmod2$ reading, full jointly attainable complete-history prior, immutable INITIAL labels, free initial scalar or independently labelled absorbing bottom, and observations only at complete endpoints. Every actually issued length-$m$ block costs one, including waits, padding, repairs and blocks rejecting before their observed endpoint. There is no reset, copy, hidden initial clock, intermediate observation or borrowed branch archive. Assume

$$
3\le m<k\le2m-2,\qquad T=k+1,\qquad
g=\gcd(m,T),\qquad P=g\mathbb Z/T\mathbb Z,
$$
$$
h=k-m\in[1,m-2],\qquad a=2m-T=m-h-1\ge1.
\tag{1.1}
$$

No coprimality is imposed. Both original alphabets are preserved: because $m<k$, every literal length-$m$ word is internally legal in either, but cross-block rejection remains part of its execution. Let $W_t=[tm,(t+1)m]\pmod T$ be the ordered physical path at absolute issued-block index $t$, with the root indexed zero.

**定义 1.2（Actual root-zero table）。** Fix a remembered free INITIAL value $v$, emit $1^m$, and retain its successful zero-difference archive. With $J=P\setminus\{0,m\}$, the INITIAL candidates and current records are exactly

$$
(v,-j,s),\quad j\in J,\ 0\le s<h;
\qquad (v,-j+m,m+s).
\tag{1.2}
$$

Require the INITIAL target on these rows to be $\lambda(j)$ independently of $s$. Impose no labels on other root archives. Write $D_{\rm ad}(\lambda)$ for the minimum additional worst emitted-block fee on this archive and $D_{\rm child\text{-}pre}(\lambda)$ for its price with one fixed literal suffix and archive-dependent stopping. The root is already paid and is not included in $D$. Define the two actual missed sets

$$
H=J\setminus W_1=P\cap\{a+1,\ldots,m-1\},
\qquad O=J\setminus W_2.
\tag{1.3}
$$

The priced class has exactly three labels, $|\lambda[J]|=3$, and $\lambda$ is constant on $H$. Empty-set constancy is allowed. When $H$ is nonempty, denote its label by $L_H$.

**接口 1.3（Supplied histories, inversion and later missed arc）。** Each candidate is a whole actual source, rather than a product of reachable marginals. For every $v,j,s$, the supplied witness [IC, (1.3); S1, Convention 1.3; S15, Section 1] chooses

$$
\ell\equiv0\pmod m,\quad \ell\equiv-j\pmod T,\quad \ell\ge s+2,
\qquad d=\bigoplus_{i=\ell-s}^{\ell-1}c_i,
\qquad w=(v\oplus d)0^{\ell-s-1}1^s,
\tag{1.4}
$$

where $c_i=\mathbf1_{\{0,T-1\}}(i\bmod T)$ is the matched cycle of [S2, Theorem 14.1]. Generalized CRT applies because $g\mid j$. The separating zero makes $w$ legal; its value, phase, tail and complete-block length are jointly the required ones. Its unobserved length is not an input. The same actual root succeeds precisely at $s<h$, has charge support $\{0,m\}$, and yields (1.2). An all-one history of complete-block length at least $k$ separately realizes initial bottom.

For an even full-path support $E\subseteq W_t$, use the supplied literal inverse

$$
\mathcal B_t(E)_i=\bigoplus_{r=0}^i\mathbf1_E(tm+r\bmod T),\qquad 0\le i<m.
\tag{1.5}
$$

Its successful charge is $\mathbf1_E$ on the full path and zero outside, with first bit $\mathbf1_E(tm)$ and last bit $\mathbf1_E((t+1)m)$. This is [IC, (1.4)–(1.5); S10, Interface 2.1; S15, Section 1], not a separate word-existence theorem. For a finite support $A$ and a donor $d\notin A$, put $\widehat A^{\,d}=A\cup\{d\}$ when $|A|$ is odd, and $\widehat A^{\,d}=A$ otherwise.

The path $W_1$ runs through $m,\ldots,T-1,0,\ldots,a$; $W_2$ starts at $a$ and contains $H$ and the excluded vertex $m$. Thus $O\cap H=\varnothing$, $O\subset W_1$, and $m$ occurs strictly after $a$ at path position $h+1\le m-1$. Write $c=3m\pmod T$. The ambient complement of $W_2$ is the $h$ vertices immediately after $c$, so

$$
O\subset W_3\setminus\{c\},\qquad
d_3=\begin{cases}0,&a+m<T,\\m,&a+m\ge T\end{cases}
\ \in\ \{0,m\}\cap(W_3\setminus\{c\}).
\tag{1.6}
$$

This is the later-window geometry used in [MC, Theorem 2.1]. Indeed, in the first case $c=a+m>m$ and $W_3$ wraps through zero; in the second $c=m-2h-2<m$ and $W_3$ reaches $m$ strictly after its start. The inequalities $h<m$ and $m>h+1$ give the stated inclusions. Donors $0,m$ are excluded INITIAL phases in this archive, even when they are actual phases of other archives.

## 2. The exact three-class price and simultaneous safe seams

**定理 2.1（Three labels, homogeneous first missed set, every actual gcd）。** Under Definitions 1.1–1.2, in either original alphabet,

$$
\boxed{D_{\rm ad}(\lambda)=D_{\rm child\text{-}pre}(\lambda)=
\begin{cases}
2,&|\lambda[O]|\le2,\\
3,&|\lambda[O]|=3.
\end{cases}}
\tag{2.1}
$$

The attainments use one literal suffix shared by all continuing children of this archive. Every finite correct continuation starts its first additional block with zero. The price is additional to the actually emitted root, and is independent of its surviving original tails.

**证明（all literal actions and sharp lower bounds）。** The archive contains all INITIAL tails $0\le s<h$ at every $j\in J$. At three differently labelled phases choose the actual tail $s=h-1$, whose current tail is $k-1$. Any next word starting one sends these sources immediately to the same absorbing bottom, with identical completed endpoint archives and identical future behaviour. It can never recover their labels. This excludes every such literal action at every future horizon, including all ones, a delayed first zero, paid waits with a leading one, and proposed subsequent repairs. Free stopping also fails. Therefore a correct first word starts zero. It clears every incoming tail and succeeds throughout, since every subsequent internal run is shorter than $k$.

This word has two possible successful endpoint differences; three labels cannot finish in one additional block. On each difference child the current value and actual terminal tail are common. The supplied common-tail fact [S10, Lemma 3.2] says a second literal word either succeeds on every candidate of that child or rejects them all. A live child cannot be completed by the latter action, and later absorbing observations cannot repair it.

Every successful second word has charge zero on $O$, regardless of the first response, its literal choice or whether that choice is adaptive. For completion in at most two additional blocks, each set $O\cap q_1^{-1}(e)$ must therefore have a single INITIAL label. This remains necessary if that child stopped after the first word, or is empty. There are only two first-response values. If $|\lambda[O]|=3$, at least one child has two such labels and cannot finish. Thus the all-action adaptive lower bound is three in this case; otherwise it is at least two. These arguments include rejection, endpoint stopping and all paid calendar advances, rather than only a proposed family of favourable words.

**证明（a one-label first child and the actual seam）。** Choose a label $S\in\lambda[J]$ absent from $H$. Such a label exists because $H$ has at most one of the three labels. If $|\lambda[O]|=2$, additionally choose $S\in\lambda[O]$; one of those two labels is absent from $H$. If $|\lambda[O]|\le1$ or equals three, any label absent from $H$ is allowed. Put

$$
A_1=\{j\in J:\lambda(j)=S\},\qquad
E_1=\widehat A_1^{\,0},\qquad B_1=\mathcal B_1(E_1).
\tag{2.2}
$$

The entire $S$ class lies in $W_1$ because it misses $H$. The excluded zero is a parity donor strictly after the leading vertex $m$. Thus $E_1$ is an even physical support and $B_1$ starts zero. It is safe on every record in (1.2), including current tail $k-1$. Its difference-one child consists precisely of label $S$ and stops. Its difference-zero child has support $U=J\setminus A_1$ and exactly the other two labels; call them $D,E$.

The last bit of this very word, not of an alternative representative, obeys

$$
(B_1)_{m-1}=\mathbf1_{A_1}(a).
\tag{2.3}
$$

If it is zero, every continuing source has actual current tail zero. If it is one, $a\in A_1$ has already stopped with $S$ and is absent from the continuing support $U$. Consequently a following charge prescription on $U$ can set the leading charge at $a$ to zero. This ties the physical terminal bit to the same actual stopped label class; it does not assume that the chosen $B_1$ ends zero.

**证明（two blocks when the second missed set has at most two labels）。** The choice of $S$ makes $\lambda[O\cap U]$ contain at most one label. When that set is nonempty, name its label $D$; otherwise choose either label of $U$ as $D$. Name the other $E$. Set

$$
A_2=\{j\in U\cap W_2:\lambda(j)=E\},\qquad
E_2=\widehat A_2^{\,m},\qquad B_2=\mathcal B_2(E_2).
\tag{2.4}
$$

The excluded donor $m$ is strictly after $a$, so this is an even full-path support with leading bit $\mathbf1_{A_2}(a)$. If $B_1$ ends zero, its incoming tail is zero and every length-$m$ word, even an all-one inverse, satisfies $0+m<k$. If $B_1$ ends one, (2.3) gives $a\notin U$, so $a\notin A_2$ and $B_2$ begins zero. It clears the actual incoming tail, after which all runs are shorter than $k$. Thus the same $B_1\mid B_2$ seam is safe on every continuing source in both cases.

On $U$, the second difference is one exactly on label $E$: every missed phase in $O\cap U$ has label $D$. Return $E$ on one and $D$ on zero. The earlier difference-one sources already returned $S$. Both labels in $U$ have actual joint sources and must emit $B_2$, so the additional worst fee is exactly two. These are prefixes of one fixed suffix, with no extra cleanup or uncharged wait.

**证明（three blocks when the second missed set has all three labels）。** Keep (2.2) and choose either ordering $D,E$ of the remaining labels. Use precisely (2.4). The seam proof is unchanged: zero terminal bit of $B_1$ gives a safe zero-tail arrival, and terminal bit one excludes $a$ from $U$ and forces the displayed $B_2$ to begin zero. Sources with second difference one all have label $E$ and stop. On the second-zero archive, every candidate inside $W_2$ has label $D$; the only remaining $E$ sources lie in $O$.

Using the physical donor of (1.6), set

$$
A_3=\{j\in O\cap U:\lambda(j)=E\},\qquad
E_3=\widehat A_3^{\,d_3},\qquad B_3=\mathcal B_3(E_3).
\tag{2.5}
$$

Neither $A_3$ nor $d_3$ contains the leading vertex $c$, and both lie in $W_3$. Hence the inverse is a complete word beginning zero. It clears every incoming tail of the actual $B_2$, including tail $m$ if $B_2$ was all ones. Every later internal run is shorter than $k$, so the actual $B_2\mid B_3$ seam is safe. On every continuing archive its third difference selects exactly label $E$; zero returns $D$. The donor is not a candidate, and no response from a stopped source is used.

Since $O$ originally contained $S,D,E$, its $D$ and $E$ sources both have first difference zero and second difference zero. They require and emit this third whole block. It can be a paid uninformative $B_2$ followed by an informative $B_3$; the displayed stream charges both. The construction and the all-action lower bound prove (2.1), including equality of adaptive and child-preset fees. ∎

## 3. Different free-value tables and one GLOBAL consumer

**定义 3.1（Full immutable INITIAL target）。** In the parameter range (1.1), take two tables $\lambda_0,\lambda_1:J\to Y$ with exactly two labels each. Require the ordered join

$$
\Lambda(j)=(\lambda_0(j),\lambda_1(j)),\qquad
|\Lambda[J]|=3,\qquad \Lambda\text{ constant on }H.
\tag{3.1}
$$

Choose distinct common root labels $R,C$ fresh from $\lambda_0[J]\cup\lambda_1[J]$, and any independent initial-bottom label $L_\bot$, with no freshness condition on $L_\bot$. Define the entire original target by

$$
f(v,-j,s)=\begin{cases}
R,&h\le s<k,\\
C,&0\le s<h,\ j\in\{0,m\},\\
\lambda_v(j),&0\le s<h,\ j\in J,
\end{cases}
\qquad f(\bot)=L_\bot.
\tag{3.2}
$$

Cross-value label coincidences are unrestricted subject to (3.1). In particular these are not identical free-value tables: identical tables with two labels would have only two joined labels.

**定理 3.2（Exact whole-source adaptive/GLOBAL separation）。** For (3.2), on the full original joint prior and under either original alphabet,

$$
\boxed{C_{\rm ad}(f)=2,\qquad
C_{\rm pre}(f)=\begin{cases}
3,&|\Lambda[O]|\le2,\\
4,&|\Lambda[O]|=3.
\end{cases}}
\tag{3.3}
$$

**证明（supplied forced root and individual binary price）。** At either free value and any $j\in J$, the actual INITIAL tails zero and $h$ have different labels $\lambda_v(j)$ and fresh $R$. A zero-containing root has at most $m-1$ leading ones. Both records survive to that first zero because $h+(m-1)=k-1$; they have the same scalar and phase there, and that zero merges their whole records. No later endpoint archive, rejection, wait or stopping rule can recover their different INITIAL labels. This is the supplied first-zero loss [S1, Lemma 4.3; IC, Proposition 4.2; MC, Corollary 3.1]. It excludes every such root at arbitrary later depth and also free stopping. Every correct root is therefore $1^m$, separately on both free values and for one GLOBAL stream.

The root rejects the high tails into the homogeneous label $R$ and its positive-success archive returns the homogeneous label $C$, both at fee one. Its two zero-success archives are (1.2), labelled respectively by $\lambda_0,\lambda_1$. Each table is nonconstant and constant on $H$. The already supplied binary law [MC, Theorem 2.1, cut zero and $\mathsf A_1$; IC, Chapter 5] gives additional adaptive fee one. Explicitly, orient the common $H$ label as zero, or choose either label when $H$ is empty, and apply (2.2) to its other binary label. That complete word begins zero and returns its binary label in one endpoint. These two words may differ because the free value selects the adaptive control. The forced root and each live binary child give the matching total lower bound two.

**证明（credited value join, one literal suffix and its lower bound）。** Use exactly [IC, Definitions 29.1 and Theorem 29.2]. Under any fixed literal stream, changing the INITIAL scalar complements every successful scalar endpoint and leaves the phase, tail and rejection time unchanged. With its remembered free value, one actual archive therefore determines the two value-translated archives by deterministic output complementation. Their issued words and bottom entries are the same. A decoder may retain the first component once determined and continue the same actual stream until both are determined; no source copy or second experiment is executed. The supremum of these two stopping times remains within the same stream's uniform fee bound. Conversely, an acquired ordered pair returns its remembered value component. Thus the supplied value-join equality applies, including different stopping rules on the two free-value fibres.

For (3.2), that full joined target has high label $(R,R)$, endpoint label $(C,C)$ and low zero-archive table $\Lambda$, with the same forced root. Its positive and rejection archives have already stopped; initial bottom returns its independent pair freely. Theorem 2.1 prices its only live root-zero archive, and supplies the actual common suffix from (2.2)–(2.5). The GLOBAL stream for $f$ is the same $1^m$ followed by that suffix, with each source decoding its own consecutive differences and returning its value component. Every root/suffix seam has been checked on the same current records. Some actual sources emit all three or four blocks by the local lower bound.

Conversely, any purported cheaper GLOBAL controller for $f$ gives, by the supplied value-join decoder, an equally bounded GLOBAL controller for the joined target. Its forced root leaves the exact archive of Theorem 2.1, contradicting that theorem's adaptive lower bound if the total is below the respective value in (3.3). The price is therefore a common-stream result on full INITIAL sources, not a maximum of independently selected child optima. ∎

**例 3.3（Two symbolic consumers, including noncoprime fees）。** Let $q\ge1$ and use binary legal labels $0,1$, fresh $R,C$ and arbitrary $L_\bot$ in (3.2).

First take $m=4q$, $k=7q-1$, so the actual gcd is $q$. On $J=\{q,2q,3q,5q,6q\}$ set $\lambda_0=\mathbf1_{\{q,6q\}}$ and $\lambda_1=\mathbf1_{\{5q\}}$. The join has three labels, is $(0,0)$ on $H=\{2q,3q\}$, and has one label on $O=\{6q\}$. An attaining GLOBAL stream is

$$
1^{4q}\ \mid\ 0^{2q}1^{2q}\ \mid\ 0^{3q}1^q.
\tag{3.4}
$$

The first suffix row has even support $\{q,6q\}$ and ends with tail $2q$. Its one child stops with join $(1,0)$, including phase $a=q$. The next row has support $\{4q,5q\}$ and begins zero, so its actual seam safely clears that tail and selects $(0,1)$; $4q=m$ is the excluded donor. Theorem 3.2 gives full adaptive fee two and GLOBAL fee three. The nonzero terminal tail is part of the attaining word, not removed by an extra block.

Next take $m=6q$, $k=11q-1$, again with actual gcd $q$. Set $\lambda_0=\mathbf1_{\{9q\}}$ and $\lambda_1=\mathbf1_{\{10q\}}$ on $J$. The join is $(0,0)$ on $H=\{2q,3q,4q,5q\}$, while $O=\{8q,9q,10q\}$ contains all three joined labels. An attaining GLOBAL stream is

$$
1^{6q}\ \mid\ 0^{3q}1^{2q}0^q\ \mid\ 0^{6q}\ \mid\ 0^{3q}1^q0^{2q}.
\tag{3.5}
$$

Its first suffix row has support $\{9q,0\}$ and stops join $(1,0)$. The complete zero wait is paid. The last row, at absolute issued index three, has support $\{10q,0\}$ and stops $(0,1)$ versus $(0,0)$. Both suffix seams are strict. Theorem 3.2 gives adaptive fee two and GLOBAL fee four for every $q$, including all noncoprime $q\ge2$. These are consumers of the structural law, not separate mathematical novelty claims.

## 4. Suppliers, checks and the remaining objective

**数学引文 4.1（Precise reuse and the added source-specific connection）。** The canonical [IC] is pinned at `78532fbc37b92a9d781eb2c9652a49ef6ce41986`, with 540,719 bytes and SHA256 `94b83e49697b7a16006adf9fe40685a223d33a7d1809f09afb497c74aef0bb85`. At that same revision [MC] has 28,785 bytes and SHA256 `2dd7b5e02b4bfb9430cfb47e27dac8d89f27e67d481cf73eb620c9a32dfe4eae`. These are immutable mathematical inputs; their ordinary assertions are used with their displayed hypotheses.

| Supplier | Reused mathematical contribution |
| --- | --- |
| [IC], Chapter 1, Propositions 4.2–4.4, Theorem 5.1, Chapter 69 | The original experiment, jointly realized histories, forced root/first zero, literal charge inverse, and previously priced binary slices. |
| [IC], Definition 29.1 and Theorem 29.2 | Exact value-join equality for one GLOBAL stream, including different stopping times and absorbing rejection. |
| [MC], Definitions 1.1–1.3, Theorem 2.1 and Corollary 3.1 | Actual-gcd mixed-tail arrival, binary cut prices, the later missed-arc geometry and fresh-label root-forcing consumer. Its lower-table hypothesis is at most two labels. |
| [S1], Convention 1.3, Lemmas 4.2–4.3, Theorem 5.2 and Note 5.3 | Joint sources, irreversible INITIAL first-zero losses and the distinction between semantic and effective acquisition. Source SHA256 `97791e0a4806b27403f6b1faefc43ed75190ead6a076a78a2674ee9b0d650685`. |
| [S2], Theorem 14.1 | The original matched coefficient cycle. Source SHA256 `34f3cd82265aab2b3a2e08cc0aa3526d469bd8c198d11a17027bcc18faa81a3e`. |
| [S10], Interface 2.1 and Lemma 3.2 | Same-word physical responses and common-tail all-success/all-rejection semantics. Source SHA256 `3f09e24654eeed8aaeaca9231a733c24a4a941b421a38706fd6f71da2f9af0b7`. |
| [S15], Section 1, Definition 1.1 and Proposition 4.2 | Ordered inversion, strict seams and the distinction between child prices and GLOBAL compatibility. Its coprime central pricing theorems are not used on noncoprime parameters. Source SHA256 `8708dee18daff629f49c5bf077afe3af244d8425d8856a72dac5965bc49e0c7f`. |
| [S13], Definitions 8.1/8.3 and Theorem 8.4 | The existing binary terminal safe-cut certificate after a recorded zero. In (2.4) its actual support is $U$, displacement is $2m$, and tail is that of the displayed $B_1$. Source SHA256 `b9d746f4439629f48185bb2e3a38d5c511a9f93b3faa6ba02b6349d54a66e2cf`. |

The binary one-block prices, value joining, generic terminal certificates, parity inversion and irreversible merger principles are credited reuse. The added ordinary deduction is the exact three-class second-missed-set criterion, together with deletion of a whole one-label child and the physical implication (2.3) that makes the same suffix simultaneously safe. Its all-action lower bound and the explicit third-window elimination supply an exact price, rather than a terminal-certificate restatement or a phase-recovery upper bound. The full distinct-value target consumes that law through the existing value join; it is not counted as another independent theorem of generic identification. General noncoprime applicability is structural coverage under the actual subgroup, with no literature-priority claim.

Petra van den Bos and Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3][L1], supplies the inspected primary comparison: completed test observations, compatible inputs, distinguishing observations, and destructive first actions that prevent a joint identification experiment. One literal complete block corresponds here to one input and its completed endpoint to one output; only unequal INITIAL target labels require separation. That paper supplies no KBonacci physical window, parity compensation, safe seam or fee formula. Its generic distinguishing-graph algorithms are not asserted as new content here. No exhaustive literature-absence or priority conclusion is drawn.

**核验 4.2（Finite corroboration, separate from the ordinary proofs）。** Direct checks use the original bit transitions, retaining INITIAL sources and grouping only complete endpoint archives. They enumerate all three-symbol phase tables with exactly three labels and homogeneous $H$ for every allowed width $3\le m\le6$. Cases with fewer than three actual root-zero phases have no such table. On each table they exhaust every first literal word and every second literal word, allowing either separate adaptive second words or one common second word. Their exact depth-zero/one/two tests agree with (2.1): among 1,038 symbol-labelled tables, 876 have additional price two and 162 have additional price three. All constructed words and endpoint decoders are executed for every surviving INITIAL tail and both free values.

| $(m,k)$ | Actual $g$ | Price-two tables | Price-three tables |
| --- | --- | --- | --- |
| $(3,4)$ | $1$ | $6$ | $0$ |
| $(4,6)$ | $1$ | $36$ | $0$ |
| $(5,6)$ | $1$ | $150$ | $0$ |
| $(5,7)$ | $1$ | $150$ | $0$ |
| $(5,8)$ | $1$ | $150$ | $0$ |
| $(6,9)$ | $2$ | $6$ | $0$ |
| $(6,10)$ | $1$ | $378$ | $162$ |

For every one of those tables, a full consumer (3.2) uses the three ordered pairs $(0,0),(1,0),(0,1)$ as its joined labels. Its adaptive words and common GLOBAL stream are checked on every INITIAL phase and tail of both free values, with fresh root labels and independently stopped initial bottom. These are 1,038 complete consumer checks, not an enumeration of every possible full target or every possible labelling of its two components.

A separate original-weight check generates $G_i$ by the integer recurrence, verifies 5,254 complete-history witnesses (1.4), and compares 7,292 actual successful root/suffix endpoint values with $V_k\bmod2$. Its parameter cases are $(m,k)=(3,4),(4,6),(6,9),(6,10),(8,9)$ and $(6q,11q-1)$ for $2\le q\le6$. The case $(8,9)$ includes an empty-$H$ three-class table. Absorbing-bottom complete-history witnesses are checked separately. For the five listed cases with $m\le8$, every literal full root on both free values is also tested on a specified complete consumer: all 816 root actions agree with root forcing, and each zero-containing root produces an irreversible unequal-INITIAL-label collision. The finite checks pass; they corroborate the ordinary proofs and do not establish their unbounded quantifiers by enumeration. No check program or separate runtime data is delivered.

**边界 4.3（Semantic acquisition, algorithm costs and original residuals）。** Theorem 2.1 assumes exactly the actual acquired rectangle (1.2), tail independence, exactly three labels, homogeneous $H$, and the parameter range (1.1). Theorem 3.2 additionally assumes exactly two labels in each free-value table, a three-label homogeneous-$H$ ordered join, the complete target (3.2), and fresh common root labels. The initial-bottom label is unrestricted. Prices apply to these stated classes; an arbitrary full extension of a local table can have other live siblings and a different GLOBAL price.

For arbitrary label sets, the constructions and minimum statements are semantic. A finite target-partition presentation or decidable equality on the finite label tables makes selection effective: form the actual missed sets, choose the isolated label and remaining orientation, compare labels on the finite supports, then invert the displayed physical rows. This takes $O(T)$ label comparisons and charge/word coordinates; arithmetic, label-equality and input-representation costs are separate, and this is not a bit-complexity bound for them. A controller uses its remembered INITIAL value and its own endpoint differences, with at most three suffix blocks; offline acquisition/search time and controller representation costs are separate from emitted-block fees. No general algorithm for factoring an arbitrary history expression through the INITIAL record is supplied.

The remaining original obligations include tail-dependent lower tables with more than two labels, three-label tables nonconstant on $H$, four or more lower labels, other acquired supports/calendars, arbitrary live positive siblings, competing roots, nonfresh full extensions and unrestricted compatibility across free values and siblings. The other parameter regions and the exact all-target/all-$k,m$ adaptive/GLOBAL objective of [IC, Definition 1.3 and Open Problem 9.1] remain unresolved by this companion. Earlier restricted results retain their own hypotheses. No Lean/code implementation, compilation, ingestion, coverage, deposit, freezing, axiom report or CI certification is asserted.

[IC]: https://github.com/the-omega-institute/trureturing/blob/78532fbc37b92a9d781eb2c9652a49ef6ce41986/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md
[MC]: https://github.com/the-omega-institute/trureturing/blob/78532fbc37b92a9d781eb2c9652a49ef6ce41986/docs/develop/theory/KBONACCI_MIXED_TAIL_ROOT_ZERO_CUT_PRICE.md
[S1]: https://raw.githubusercontent.com/the-omega-institute/trureturing/f64d9e5dc37301e04ffc33332c919dd56a81ed6f/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md
[S2]: https://raw.githubusercontent.com/the-omega-institute/trureturing/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md
[S10]: https://raw.githubusercontent.com/the-omega-institute/trureturing/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md
[S13]: https://raw.githubusercontent.com/the-omega-institute/trureturing/6850a89acdb12d4f17af57dacee2d67e0b514be4/docs/develop/theory/KBONACCI_MULTILABEL_PREFIX_AND_TERMINAL_COST.md
[S15]: https://raw.githubusercontent.com/the-omega-institute/trureturing/3541b57c0d31a89f11fb8b86c75b7b1555e49e6f/docs/develop/theory/KBONACCI_JOINT_RESPONSE_AND_SEAM_COST.md
[L1]: https://arxiv.org/html/1907.11034v2

## 追加锚（本行以下为增补区）

## 5. Complete stationary memory at the adaptive deadline

**定义 5.1（Counted control for exactly Definition 3.1）。** Keep the entire contract of Definition 3.1, including both original alphabets, all jointly realized INITIAL sources, every original tail, the arbitrary initial-bottom label, and all cross-table label equalities. The actual record set is

$$
Q=\{\bot\}\sqcup
\{(v,-j,s):v\in\mathbb F_2,\ j\in P,\ 0\le s<k\}.
$$

Every displayed tuple has the whole-history witness (1.4), equivalently [IC, (1.3)]; initial bottom has its rejected-history witness. Put

$$
U_Y=\lambda_0[J]\cup\lambda_1[J],\qquad r=|U_Y|,\qquad
N=|f(Q)|=r+2+
\mathbf1_{\{L_\bot\notin U_Y\cup\{R,C\}\}}.
\tag{5.1}
$$

Thus $r\in\{2,3,4\}$ and $4\le N\le7$. In particular $N$ counts actual output labels, not joined pairs or just the cross-table union.

Use the existing complete Moore control of [FC, Definitions 26.1–26.2]:

$$
c:\{0,1,\bot\}\to K,\qquad
u:K\to\{0,1\}^m\sqcup\operatorname{Halt}(f(Q)),\qquad
V:K\times\{0,1,\bot\}\to K.
\tag{5.2}
$$

At a word row $x$, perform that whole literal word on the current apparatus record, observe only its completed endpoint, and apply $V(x,o)$. Rejection is a defined absorbing response, and its issued block is charged. At a Halt row return its installed label. Every retained value, difference, endpoint baseline, program position, stopping decision and output belongs to $K$; the apparatus phase and tail are unavailable as inputs. The source witness, support indices and proof rank are also unavailable as inputs. No archive, clock, reset, copy, intermediate observation or separate output latch is supplied.

Let $K_{\min}^{\rm ad}(d;f)$ minimize $|K|$ over these complete controllers correct on all $Q$ within $d$ emitted blocks. Let $K_{\min}^{\rm GLOBAL}(d;f)$ additionally require every actual emitted sequence to be a prefix of one fixed installed stream. Responses can choose stopping, but cannot choose the next word of that stream. Distinct halt outputs require distinct states. Equal-labelled Halt rows can be merged, so an attainment with $e$ word rows and one Halt row per actual label has $N+e$ states. Descriptor bits, word-dictionary bits, expanded-stream bits, installation work and physical operations are separate coordinates; no formula below identifies them with $|K|$ or with emitted-block fee.

For the following controllers, write $H_y$ for the row installing $\operatorname{Halt}(y)$ and set $V(H_y,o)=H_y$ for every response. A specified word row's unused bottom update is $H_R$. This completes the tables without treating an unreachable response as a new runtime input.

**定理 5.2（Exact adaptive memory on the full complete-target class）。** For every Definition 3.1 target,

$$
\boxed{K_{\min}^{\rm ad}(2;f)=N+4.}
\tag{5.3}
$$

Proof of attainment. For each value $v$, choose its label $Z_v$ on $H$, or either of its two labels if $H$ is empty, and name the other $X_v$. Set

$$
A_v=\{j\in J:\lambda_v(j)=X_v\},\qquad
B_v=\mathcal B_1(\widehat A_v^{\,0}).
\tag{5.4}
$$

The class $A_v$ misses $H$, lies in $W_1$, and omits the leading vertex $m$. The donor zero also omits that vertex. Thus the supplied inverse makes $B_v$ begin zero and have charge $\mathbf1_{A_v}$ on the actual archive. It clears every incoming tail, including $k-1$, and succeeds throughout because $m<k$.

Take four word rows $a_0,a_1,b_0,b_1$, and all $N$ Halt rows. Initialize $c(v)=a_v$ and $c(\bot)=H_{L_\bot}$. The complete word-row table is

| Row | Installed word | Endpoint $v$ | Endpoint $1-v$ | Bottom |
| --- | --- | --- | --- | --- |
| $a_v$ | $1^m$ | $b_v$ | $H_C$ | $H_R$ |
| $b_v$ | $B_v$ | $H_{Z_v}$ | $H_{X_v}$ | $H_R$ |

Use the immutable-target/current-record supports

$$
\begin{aligned}
\Gamma_{a_v}&=\{(f(v,-j,s),(v,-j,s)):j\in P,\ 0\le s<k\},\\
\Gamma_{b_v}&=\{(\lambda_v(j),(v,-j+m,m+s)):j\in J,\ 0\le s<h\}.
\end{aligned}
\tag{5.5}
$$

For a Halt row, take precisely its initial-bottom pair, when applicable, together with all its incoming actual word images:

$$
\Gamma_{H_y}=
\bigl(\{(L_\bot,\bot)\}\text{ if }y=L_\bot,\ \varnothing\text{ otherwise}\bigr)
\ \cup\!
\bigcup_{\substack{x\text{ word row},\ e\in\{0,1,\bot\}\\V(x,e)=H_y}}
\{(z,\delta_{u(x)}q):(z,q)\in\Gamma_x,
\ o(\delta_{u(x)}q)=e\}.
\tag{5.6}
$$

Here $o(q)$ is the original endpoint readout. Give the root, query and Halt supports ranks $2,1,0$. The root sends exactly high tails to $R$, low endpoint phases to $C$, and the low $J$ rectangle to $b_v$. Formula (5.4) sends the latter to its correct binary labels. All actions are original total word updates, all source pairs are covered, all successors lie in the displayed supports, and every word step strictly lowers rank. Every Halt support has its installed immutable label. These are exactly the conditions of [FC, Theorem 27.2], applied as an ordinary paper certificate.

Proof of the arbitrary-controller lower bound at fee two. Each initial value fibre must emit, and Theorem 3.2's first-zero loss forces its first word to be $1^m$. If the two initial rows were one row, its scalar endpoint $y$ would contain fresh $C$ and both labels of $\lambda_y$. Choose the actual maximal surviving INITIAL tail $h-1$ at an endpoint phase and at differently labelled $J$ phases. Their current tail is $k-1$. A second word beginning one irreversibly merges unequal labels in bottom; a word beginning zero succeeds on all these sources and has only two scalar responses. Neither can finish three labels in the one remaining block. Hence $a_0\ne a_1$ in every fee-two controller, regardless of delayed homogeneous stopping.

Its two root-zero successors must emit and begin zero, by the same maximal-tail merger argument on the nonconstant binary tables. They are distinct from the all-one root rows. If both were one row $b$, its last word would have one charge function $q(j)$ and two installed final outputs $G(0),G(1)$. Correctness would require

$$
\lambda_0(j)=G(q(j)),\qquad
\lambda_1(j)=G(1\oplus q(j)).
\tag{5.7}
$$

The ordered join would have at most two classes, contrary to (3.1). Thus four distinct word rows are compulsory, as are the $N$ distinct output rows. This exhausts arbitrary words, rejection, early or delayed stops and all possible reuse within the two-block deadline. ∎

**引理 5.3（Four word rows are necessary even without a fixed finite deadline）。** Every correct finite stationary controller for this complete target has at least four word rows, hence at least $N+4$ states. In particular this lower bound applies to every GLOBAL controller at either deadline of Theorem 3.2.

Proof. Suppose there are at most three word rows. Root forcing still holds at arbitrary later horizons. Any actual high-tail source rejected from an initial root must eventually return $R$. Consequently a later successful $C$ or lower-label source cannot reject at that same root row: it would have the identical apparatus bottom and stationary successor as that actual $R$ source. This retains delayed rejection stopping rather than presuming an immediate $H_R$ update.

If the two initial root rows are distinct, their mandatory root-zero successors, which begin zero, can only be the one remaining word row $b$. A root scalar update cannot directly return a lower label: its mandatory first occurrence contains either nonconstant lower labels or fresh $C$. Its bottom continuation returns $R$. Since $b$ begins zero, no successful source rejects there. All lower labels must therefore be direct scalar Halt updates of $b$. At least two distinct lower labels occur, so both scalar updates must halt. Equation (5.7) then contradicts the three-class join. If there are three or four lower labels, the same two scalar exits already have insufficient capacity.

If the initial roots coincide, call the root $a$ and its scalar successors $b_0,b_1$. Each successor contains $C$ and two lower labels, so it must begin zero and cannot have both scalar updates halt. If $b_0\ne b_1$, these exhaust the three word rows. Each supplies at most one scalar Halt exit, the root supplies none, and no successful source rejects at a zero-leading row. The at least three non-$R$ labels $C$ and the binary lower labels cannot all be returned.

It remains that $b_0=b_1=b$. Each scalar response of this row contains an actual $C$ source: use original endpoint phase $j=m$, for which the first suffix charge is zero because its first bit is zero, and choose either initial value. Each scalar response also contains a lower source: at each $j\in J$ the two actual initial values produce complementary endpoints. Thus both scalar updates of $b$ emit. Only a third row $p$ can directly return $C$ or a lower label. At least three such labels must be returned, so all three response updates of $p$ would have to halt with distinct labels. Every successful $C$/lower arrival at $p$ comes from $b$; the root's scalar updates are both $b$, and a root-bottom continuation can return only $R$. Because the word of $b$ starts zero, all these arrivals have its same literal terminal tail, at every possible depth. The word at $p$ either rejects all of them or succeeds on all of them. It therefore offers at most two actual responses for these three labels. Contradiction.

This argument counts actual output exits and their common-tail constraints, rather than layers of a tree. Arbitrary later words, waits, delayed homogeneous stops, shared roots and reuse across depths remain admitted throughout. ∎

## 6. GLOBAL attainments and different lower-label sets

**定理 6.1（Complete GLOBAL upper certificates at both original deadlines）。** Let $D=C_{\rm pre}(f)$ be exactly the fee in (3.3). Then

$$
\boxed{
\begin{array}{ll}
N+4\le K_{\min}^{\rm GLOBAL}(3;f)\le N+5,
& |\Lambda[O]|\le2,\\
N+4\le K_{\min}^{\rm GLOBAL}(4;f)\le N+6,
& |\Lambda[O]|=3.
\end{array}}
\tag{6.1}
$$

Neither upper endpoint in (6.1) is asserted universally sharp. The lower endpoints are Lemma 5.3.

Proof of the three-block upper certificate. Three occupied pairs in two binary coordinates are three corners of a rectangle. Call the corner adjacent to both others central, and the other two leaves. Deleting a leaf makes one component constant on the two remaining classes. Choose a leaf $S$ such that $|\Lambda[O]\setminus\{S\}|\le1$. Such a leaf exists: if $O$ has two labels, at least one is a leaf; otherwise either leaf works. Write $U=\{j\in J:\Lambda(j)\ne S\}$. Let $i\in\{0,1\}$ be the component for which $S$ is its singleton class, and let $w=1-i$ be the component still nonconstant on $U$.

If $S$ is absent from $H$, take $A_1=J\setminus U$ and $\sigma=0$. If $H$ has label $S$, take $A_1=U$ and $\sigma=1$. Empty $H$ uses the former case. In either case $A_1\subset W_1$ misses $H$, so

$$
B_1=\mathcal B_1(\widehat A_1^{\,0})
\tag{6.2}
$$

begins zero, safely clears all root tails, and has difference $\sigma$ on $U$ and $1-\sigma$ on $S$. This reverse orientation is needed when the selected leaf is the $H$ class; it preserves the original fee and source set.

Choose $Z$ as the $w$-component label on $O\cap U$ when that set is nonempty, and either label of $\lambda_w[U]$ otherwise. Name its other label $E$. Set

$$
A_2=\{j\in U\cap W_2:\lambda_w(j)=E\},\qquad
F_2=\begin{cases}
A_2\cup\{a+1\},&\sigma=1\text{ and }a\in A_2,\\
A_2,&\text{otherwise},
\end{cases}
\qquad B_2=\mathcal B_2(\widehat F_2^{\,m}).
\tag{6.3}
$$

When $\sigma=0$, the seam is exactly the proof of (2.3)–(2.4): a final one of $B_1$ removes $a$ with the stopped $S$ class and forces $B_2$ to start zero; a final zero of $B_1$ gives incoming tail zero. When $\sigma=1$, the first interior vertex $a+1$ is not in $U$: it lies in the ambient interval $a+1,\ldots,m-1$, and if actual belongs to the stopped homogeneous $H$ class. Also $m$ is at path position $h+1\ge2$, distinct from $a$ and $a+1$. If $a\in A_2$, (6.3) sets the first two path charges to $1,1$, making the actual first two bits $1,0$. The actual terminal tail of the zero-leading $B_1$ is at most $m-1$; that single leading one reaches at most $m<k$ and the following zero clears it. If $a\notin A_2$, $B_2$ begins zero. In all cases the remaining internal runs are shorter than $k$. The added interior charge and parity donor are absent from the continuing sources. Thus this very $B_2$ is safe and selects $E$ exactly on $U$, including every missed phase with label $Z$. No cleaning or waiting block is added.

Install two roots $a_v$ as in Theorem 5.2 and two first-query rows $b_v$ with word $B_1$. Let $z_i$ denote the single label in $\lambda_i[U]$, put $s_v=S_v$ and $\beta=w\oplus\sigma$, and add just one last-query row $p_2$ with word $B_2$. The scalar updates are

$$
\begin{aligned}
V(b_i,i\oplus\sigma)&=H_{z_i},&
V(b_i,i\oplus(1-\sigma))&=H_{s_i},\\
V(b_w,w\oplus\sigma)&=p_2,&
V(b_w,w\oplus(1-\sigma))&=H_{s_w},\\
V(p_2,\beta)&=H_Z,&V(p_2,1-\beta)&=H_E.
\end{aligned}
\tag{6.4}
$$

Initialize and complete bottom/Halt entries as in §5. All executions emit prefixes of the single installed stream $1^m\mid B_1\mid B_2$. They use five word rows and exactly $N$ Halt rows. In addition to the root and root-zero supports (5.5), the only live later support is

$$
\Gamma_{p_2}=\{(\lambda_w(j),(\beta,-j+2m,\tau_1)):j\in U\},
\tag{6.5}
$$

where $\tau_1$ is the actual terminal tail of (6.2). All original $s<h$ have this same image because $B_1$ starts zero. Use (5.6) for exact Halt supports and ranks $3,2,1,0$ on roots, first queries, last query and Halts. The literal support identities and the proved seams give all-source closure and label correctness. Both labels on $U$ actually occur, so the $w$ component uses the last word; the deadline is the original three blocks.

Proof of the four-block upper certificate. Choose a leaf $S$ absent from homogeneous $H$, which is always possible because there are two leaves. Use exactly the words (2.2), (2.4), (2.5) for the joined table, naming the remaining joined classes $D_0,E_0$. Let $i$ be the singleton component of $S$ and $w=1-i$; the two remaining classes agree in component $i$ and differ in component $w$. At $b_i$ both scalar replies halt with their component labels. At $b_w$, reply $1-w$ returns $H_{S_w}$ and reply $w$ enters $p_2$. Install $B_2$ at $p_2$ and $B_3$ at $p_3$, with

$$
V(p_2,1-w)=H_{(E_0)_w},\quad V(p_2,w)=p_3,
\qquad
V(p_3,1-w)=H_{(E_0)_w},\quad V(p_3,w)=H_{(D_0)_w}.
\tag{6.6}
$$

The two roots and their updates are unchanged; the two $b_v$ rows both install $B_1$. Complete every other entry as in §5. This uses six word rows. The actual support at $p_2$ is (6.5) with $\beta=w$, and

$$
\Gamma_{p_3}=
\{(\lambda_w(j),(w,-j+3m,\tau_2)):
j\in U,\ q_2(j)=0\},
\tag{6.7}
$$

where $q_2$ and $\tau_2$ are the successful charge and actual terminal tail of the displayed $B_2$. Take ranks $4,3,2,1,0$ and exact Halt images (5.6). Theorem 2.1 proves the safety of these same words, including a nonzero $\tau_1$, possible all-one $B_2$, and its zero-leading $B_3$. The two remaining $O$ classes both continue through the second-zero reply, so some actual sources issue all four paid blocks. Every execution is a prefix of $1^m\mid B_1\mid B_2\mid B_3$. Both attainments satisfy [FC, Theorem 27.2] with the immutable target retained; neither a decoded component nor a calendar position is an external latch. ∎

**定理 6.2（Exact fee-three memory when the lower-label sets differ）。** Throughout Definition 3.1, if $|\Lambda[O]|\le2$ and $r\ge3$, then

$$
\boxed{K_{\min}^{\rm GLOBAL}(3;f)=N+5.}
\tag{6.8}
$$

Proof. The upper bound is Theorem 6.1. By Lemma 5.3 it remains to exclude exactly four word rows. The following argument admits arbitrary words, delayed homogeneous stops and reuse across depths.

All initial roots emit $1^m$, and all first root-zero words begin zero. GLOBAL makes this first suffix word the same literal $B$ on both values, with charge $q(j)$ and common successful terminal tail $\tau$. A mixed actual scalar archive after this word, with one block remaining, can finish only in a row whose two scalar successors halt with different labels. Its word must succeed on the common tail; uniform rejection would destroy the distinction. Call such a row a final separating row. A root cannot be such a row, because its mandatory root-zero update emits. Also, a first suffix row with an emitting scalar update cannot be such a row. These are facts about fixed raw-response updates, not an assumption that depths have separate states.

First suppose the initial root rows are distinct. If their first root-zero rows are also distinct, all four word rows have been used. There is a mixed lower archive after $B$ in at least one value fibre: otherwise the root and this common word, with archive-based decoding, would acquire the entire target in two blocks, contradicting Theorem 3.2. Its final separating row must be the other value's first suffix row, since its own first suffix row has a continuing update and the roots cannot separate. That other row has both scalar updates halt and, at its mandatory first occurrence, its two halt labels are exactly that value's binary table labels. The mixed archive has exactly the original value's two binary labels. These two label sets would therefore coincide, contrary to $r\ge3$.

If the first root-zero rows coincide in $b$, only one further word row $p$ is available. All lower Halt exits lie at $b$ or $p$; neither root can directly halt with a lower label, and a root rejection has its already fixed eventual label $R$. All lower arrivals at $p$ that could stop within three blocks are successful images of the zero-leading $B$ and have tail $\tau$, so $p$ supplies at most two lower output labels. Hence $b$ must have a scalar Halt exit. Such an exit must be homogeneous on its actual first occurrence. If $q$ is constant on $J$, either scalar child contains an entire nonconstant binary table and cannot be homogeneous. Otherwise each scalar child has sources from both values, so a homogeneous child's label must be common to the two lower-label sets. For $r=4$ there is no such label. For $r=3$, write those sets $\{L,A\}$ and $\{L,B\}$ with $L,A,B$ distinct. The homogeneous child must have label $L$. If an occupied joined class were $(A,B)$, neither of its complementary-value sources could enter that child with $L$. Thus the three occupied classes must be $(L,L),(A,L),(L,B)$. Their opposite scalar child contains respectively $L,A,B$, three labels with current scalar and tail common. It cannot finish in one remaining block, whatever row is chosen. This excludes the shared first suffix case.

Now suppose the initial root is shared. After its scalar response $y$, the actual archive contains $C$ and both labels of $\lambda_y$, with maximal tail $k-1$ actually present. Its first suffix row must begin zero and have an emitting scalar update. If these two rows coincide, each scalar child after $B$ contains $C$ from original phase $m$ and, at every $j\in J$, one of the two complementary-value lower sources. Completion in one remaining common-tail block allows at most one lower label $L_e$ in each raw scalar child $e$. It would imply $\lambda_0(j)=L_{q(j)}$ and $\lambda_1(j)=L_{1\oplus q(j)}$, again a join of at most two classes. Thus the two first suffix rows are distinct.

The fourth row $p$ is then the only possible final separating row. For each $y$, its three initial labels must split after $B$ into a homogeneous child and a two-label mixed child: three labels in one child are impossible, and two different mixed children could only use $p$'s same two halt labels and hence could not cover all three. The mixed pair for each value must equal the halt-label pair of $p$. It lies in both $\{C\}\cup\lambda_0[J]$ and $\{C\}\cup\lambda_1[J]$. If $r=4$, this intersection is only $\{C\}$, impossible. If $r=3$, it is $\{C,L\}$ with the same $L,A,B$ notation. Therefore the other lower label $A$ or $B$ must form the homogeneous child. Original phase $m$ supplies $C$ in the charge-zero child because $B$ begins zero. Consequently, on $J$ the charge-one class must be exactly $\lambda_0^{-1}(A)$ and also exactly $\lambda_1^{-1}(B)$. A charge-zero phase has pair $(L,L)$ and a charge-one phase has pair $(A,B)$, contradicting three joined classes. Possible delayed $C$ stops and the phase-zero $C$ source only add requirements; they do not remove the actual phase-$m$ sources used here.

The four-row cases are exhausted without excluding shared roots or identifying a last row with its depth. Thus five word rows and all $N$ actual output rows are necessary. ∎

## 7. Complete consumers of stationary reuse

**定理 7.1（A reused query row with exact memory and unequal block prices）。** Set $m=3$, $k=4$, so $T=5$, $g=1$, $h=1$, $J=\{1,2,4\}$, $H=\{2\}$ and $O=\varnothing$. Use distinct lower labels $0,1$, fresh distinct $R,C$, and arbitrary $L_\bot$. Let

$$
\lambda_0=\mathbf1_{\{1\}},\qquad
\lambda_1=\mathbf1_{\{4\}}\quad\text{on }J.
\tag{7.1}
$$

With the entire full target (3.2), including all high tails and endpoint phases,

$$
K_{\min}^{\rm ad}(2;f)=K_{\min}^{\rm GLOBAL}(3;f)=N+4,
\qquad C_{\rm ad}(f)=2<3=C_{\rm pre}(f).
\tag{7.2}
$$

In particular the complete count is eight if bottom uses an existing label, and nine if its label is fresh.

Proof. The adaptive count is Theorem 5.2. Install the following four GLOBAL word rows and the $N$ Halt rows, initialize $c(v)=a_v$, $c(\bot)=H_{L_\bot}$, and complete Halt rows as in §5:

| Row | Word | Endpoint $0$ | Endpoint $1$ | Bottom |
| --- | --- | --- | --- | --- |
| $a_0$ | $111$ | $d_0$ | $H_C$ | $H_R$ |
| $a_1$ | $111$ | $H_C$ | $d_1$ | $H_R$ |
| $d_0$ | $010$ | $d_1$ | $d_1$ | $H_R$ |
| $d_1$ | $010$ | $H_1$ | $H_0$ | $H_R$ |

Every emitted sequence is a prefix of $111\mid010\mid010$. On $J$, the same word $010$ has charge $q_1=\mathbf1_{\{4\}}$ at index one and charge $q_2=\mathbf1_{\{2\}}$ at index two. Its full ambient supports are respectively $\{4,0\}$ and $\{2,3\}$. It begins and ends zero, so it is safe both after the root's tail three and after a previous $010$.

Use the full root supports (5.5), and

$$
\begin{aligned}
\Gamma_{d_0}&=\{(\lambda_0(j),(0,-j+3,3)):j\in J\},\\
\Gamma_{d_1}&=\{(\lambda_1(j),(1,-j+3,3)):j\in J\}\\
&\qquad\cup\{(\lambda_0(j),(q_1(j),-j+6,0)):j\in J\}.
\end{aligned}
\tag{7.3}
$$

Phases are modulo five. The first part of $\Gamma_{d_1}$ arrives after one block on initial value one; its next scalar is $1\oplus q_1(j)$, zero exactly when $\lambda_1(j)=1$. The second part arrives after two blocks on initial value zero; its next scalar is $q_1(j)\oplus q_2(j)$, zero exactly when $\lambda_0(j)=1$. Thus the very same word and raw endpoint updates work on the entire union support. No free stage bit chooses between the two occurrences.

Ranks $3$ at roots, $2$ at $d_0$, $1$ at $d_1$, and $0$ at exact Halt images (5.6) strictly descend; some paths skip a rank. All $41$ actual INITIAL records, namely $40$ successful value/phase/tail tuples and bottom, are covered by the source supplier. Lemma 5.3 matches this four-word-row attainment, giving the exact GLOBAL count. The prices are Theorem 3.2. A block premium therefore need not produce a complete-memory premium. The installed dictionary here has two distinct three-bit words; its six expanded dictionary bits and nine-bit stream prefix are separate from the four word states, actual output states and physical execution fee. ∎

**例 7.2（A lawful shared-root competitor with delayed endpoint labels）。** Retain $m=3,k=4,J,H,O$ but take $\lambda_0=\mathbf1_{\{2\}}$ and $\lambda_1=\mathbf1_{\{4\}}$. Keep fresh $R,C$ and arbitrary $L_\bot$ in the full target (3.2). This is another admissible three-class target with GLOBAL fee three. The following complete controller shares its initial root; it is an attainment, not a minimum claim:

| Row | Word | Endpoint $0$ | Endpoint $1$ | Bottom |
| --- | --- | --- | --- | --- |
| $a$ | $111$ | $d_0$ | $d_1$ | $H_R$ |
| $d_0$ | $011$ | $p_{00}$ | $H_0$ | $H_R$ |
| $d_1$ | $011$ | $p_{10}$ | $p_{11}$ | $H_R$ |
| $p_{00}$ | $011$ | $H_C$ | $H_1$ | $H_R$ |
| $p_{10}$ | $011$ | $H_0$ | $H_1$ | $H_R$ |
| $p_{11}$ | $011$ | $H_0$ | $H_C$ | $H_R$ |

Initialize $c(0)=c(1)=a$ and $c(\bot)=H_{L_\bot}$; install all actual Halt labels and their self-updates. The common stream is $111\mid011\mid011$. Its suffix full supports are $\{1,4\}$ and $\{2,4\}$. Each $011$ starts zero and ends with tail two, so both seams are safe. To specify full supports without retaining an external archive, put $L=1^3$, $B=011$, and

$$
\begin{aligned}
\Gamma_a&=\{(f(q),q):q\in Q\setminus\{\bot\}\},\\
\Gamma_{d_y}&=\{(f(q),\delta_Lq):q\ne\bot,\ \delta_Lq\ne\bot,
\ o(\delta_Lq)=y\},\\
\Gamma_{p_{00}}&=\{(z,\delta_Bq):(z,q)\in\Gamma_{d_0},\ o(\delta_Bq)=0\},\\
\Gamma_{p_{10}}&=\{(z,\delta_Bq):(z,q)\in\Gamma_{d_1},\ o(\delta_Bq)=0\},\\
\Gamma_{p_{11}}&=\{(z,\delta_Bq):(z,q)\in\Gamma_{d_1},\ o(\delta_Bq)=1\}.
\end{aligned}
\tag{7.4}
$$

The immutable targets in the three last supports are respectively $\{C,1\}$, $\{0,1\}$ and $\{C,0\}$. Their current scalars are respectively $0,0,1$ and all current tails are two. The displayed final support $\{2,4\}$ gives exactly their installed outputs. Exact Halt images (5.6), and ranks $3,2,1,0$, give the complete all-source closure and termination certificate. There are six word rows and $N$ Halt rows. This lawful competitor shows why adaptive root separation and immediate $C$ stopping are not GLOBAL normal forms. Its larger count is not used to assert that a minimum shares its root.

**例 7.3（An actual consumer of the different-label-set minimum）。** Keep $m=3,k=4,J,H,O$ as above, but use $\lambda_0(1)=1$, $\lambda_0(2)=\lambda_0(4)=0$, and $\lambda_1(4)=2$, $\lambda_1(1)=\lambda_1(2)=0$. The labels $0,1,2$ are distinct, $R,C$ are fresh and distinct, and $L_\bot$ is arbitrary. Here $r=3$ and the ordered classes are $(1,0),(0,0),(0,2)$. The exact adaptive and GLOBAL counts are respectively $N+4$ and $N+5$ by Theorems 5.2 and 6.2.

The following five-word-row certificate attains the latter count on the full target, with $c(v)=a_v$, $c(\bot)=H_{L_\bot}$ and all $N$ actual Halt rows:

| Row | Word | Endpoint $0$ | Endpoint $1$ | Bottom |
| --- | --- | --- | --- | --- |
| $a_0$ | $111$ | $b_0$ | $H_C$ | $H_R$ |
| $a_1$ | $111$ | $H_C$ | $b_1$ | $H_R$ |
| $b_0$ | $001$ | $H_0$ | $H_1$ | $H_R$ |
| $b_1$ | $001$ | $H_0$ | $p$ | $H_R$ |
| $p$ | $001$ | $H_2$ | $H_0$ | $H_R$ |

Use the root and root-zero supports (5.5) and

$$
\Gamma_p=\{(\lambda_1(j),(1,-j+6,1)):j\in\{2,4\}\},
\tag{7.5}
$$

with exact Halt images (5.6) and ranks $3,2,1,0$. The two $001$ words have full supports $\{0,1\}$ and $\{3,4\}$ at indices one and two. Both begin zero and end with tail one, so the actual seams are safe. The updates select precisely the displayed component labels on all $41$ INITIAL records. This is one application of the general certificates and lower theorem, not a new independent minimum proof. Its complete GLOBAL count is ten for an existing bottom label and eleven for a fresh bottom label; its adaptive count is nine or ten respectively. Equal installed words at the two positions do not by themselves identify their stationary response updates.

## 8. Scope, credited machinery and the remaining compatibility proof

**来源 8.1（Ordinary deductions and precise reuse）。** Sections 5–7 concern only the existing complete target of Definition 3.1. The original integer reader, two alphabets, endpoint readout, actual-history supplier, first-zero loss, physical inverse and common-tail rule are reused from [IC, Chapter 1], [S1, Definitions 1.2 and Convention 1.3], and [S10, Interface 2.1 and Lemma 3.2]. Theorem 3.2 supplies the deadlines, and [IC, Definition 29.1 and Theorem 29.2] supplies only block-fee joining. The latter retains decoded components in its history decoder and is not a memory-preserving isomorphism of finite $c,u,V$; it supplies no equality of complete state minima.

[FC, Definitions 26.1–27.1 and Theorems 27.2–27.3] supply complete control and immutable-target/current-record certificates. By their necessity direction, every competing correct finite controller has its actual reachable union supports and a closed-loop descending rank. Such a rank may depend on the proof's target, apparatus and control coordinates; it does not rule out reuse of one control row at different depths. The new deductions are the target-specific compulsory control distinctions, the reverse-oriented safe seam consumed in (6.3), the five/six-row complete attainments, the fee-three $r\ge3$ exclusion, and the complete reuse consumer. No generic identification, bounded-trace or no-finite-observer theorem is repeated.

Edward F. Moore, *Gedanken-Experiments on Sequential Machines*, in *Automata Studies* (1956), pp.129–131 [MO], distinguishes one-machine fixed/adaptive simple experiments from experiments with several copies, and describes absorbing destruction. The one-machine correspondence applies here; the multiple-copy operation does not. For [L1]'s HTML rendering, Definitions 7–11 specify acyclic tests, completed observations, tests valid for a system and distinguishing graphs; Figure 3 gives irreversible first-action mergers. One literal complete block and its completed endpoint correspond to one input experiment and response here, but only unequal INITIAL target labels require separation. Those acyclic test nodes neither count this stationary $K$ nor justify forbidding cross-depth reuse. These are primary conceptual comparisons, not suppliers of a KBonacci state formula. The deductions in this appendix are repository-derived ordinary paper mathematics; no literature-priority or exhaustive absence claim is made.

**开放问题 8.2（Exact residual on the unchanged complete target）。** The exact adaptive count is (5.3). At the original GLOBAL deadline three, (6.8) closes all branches with $r=3$ or $r=4$. For $r=2$, the remaining exact choice is

$$
K_{\min}^{\rm GLOBAL}(3;f)\in\{N+4,N+5\};
\tag{8.1}
$$

Theorem 7.1 closes its stated actual table, not every $r=2$ table. At the original deadline four, for every $r\in\{2,3,4\}$ the remaining exact choice is

$$
K_{\min}^{\rm GLOBAL}(4;f)\in\{N+4,N+5,N+6\}.
\tag{8.2}
$$

No endpoint of these residual sets is a numerical conjecture. The missing proof is an all-controller existence/exclusion classification at four word rows for (8.1), and at four and five word rows for (8.2). Its domain remains every $3\le m<k\le2m-2$, actual $g,P,H,O$, all placements and sizes of the three joined phase classes, tail independence on the full original low rectangle, homogeneous possibly empty $H$, fresh $R,C$, and arbitrary bottom label. It must retain both two-label tables literally. Up to renaming their four component labels, the equality patterns, in order $(A,A',B,B')$, are $0101,0110,0102,0120,0112,0121,0123$; these cover all cross-table coincidences, but are not a classification of physical phase compatibility.

For each proposed smaller count, either give full $c,u,V$ and all-source supports/ranks at that count, or exclude every such controller. In particular the remaining proof must cover shared and distinct initial roots; arbitrary words via their actual full-path charges; early and delayed stopping of $R,C$ and homogeneous component branches; zero waits and safe all-one words; rejection of homogeneous supports; and identifications across paid depths when the installed stream repeats a word. A state identification must use the same word and the same successor for each raw endpoint on the union of all its actual immutable-target/current-record supports, with the original leading-run/current-tail seam and remaining fee budget at each occurrence. Retaining phase-zero or phase-$m$ sources because $C$ was delayed changes the available parity donors. The isolated-class decoder of Theorem 2.1 and the five/six-row attainments are not asserted to be normal forms for these competitors. Selected word menus, finite samples, joined block prices and layered quotients do not prove their exclusion.

This leaves a finite next proof assignment at this same owner: the four-row compatibility criterion for equal lower-label sets at fee three, and the four-/five-row criterion for each original fee-four target. The exact full-scope GLOBAL goal remains unresolved until those obligations are proved. The broader arbitrary-target/all-$k,m$ objective of [IC, Open Problem 9.1] also retains its original scope.

**核验 8.3（Evidence boundary and resource judgments）。** The statements and support/rank certificates above are ordinary paper proofs. Finite direct-bit executions of the displayed constructions check completed responses, immutable labels, raw-update compatibility, strict ranks and common-stream prefixes; they corroborate attainments, not universal lower bounds. The full-state arguments use every permitted literal word and actual source witnesses rather than extrapolating finite enumeration. No Lean, build, kernel, ingestion, atom coverage, freezing or CI verification is asserted. Independent mathematical review remains a separate acceptance obligation.

The finite construction checks cover every exactly-three-class phase assignment with homogeneous $H$ for all allowed widths $3\le m\le6$, and additionally $(m,k)=(8,9)$, under all seven cross-table equality patterns. Cases with $|J|<3$ have no admissible table. There are 7,308 labelled-table cases, with 14,616 adaptive/GLOBAL constructions and 2,452,632 complete INITIAL-record executions; 1,820 GLOBAL constructions use the reverse orientation in (6.3). Each existing output label and one fresh initial-bottom label give 42,804 target variants and 85,608 separate initial-bottom control/Halt checks. Those changes leave successful-source instructions unchanged. The three displayed consumers are separately checked on all 41 INITIAL records each. These checks use the original bit transitions; whole-history realizability is supplied by (1.4), rather than claimed as a new integer-weight or kernel verification. All these construction checks pass. No finite competitor enumeration is used to establish a minimum.

The local form keeps the source-specific memory result with its target and fee owner, reuses the existing certificate machinery, and exposes the remaining competitor budgets. Its useful depth is the compulsory distinctions and compatible actual source images; counting more protocol layers would not close the union-support gap. The exact consumer and the lawful shared-root competitor distinguish block fee from complete memory and permissible reuse from free runtime coordinates. A generic new framework or a transfer of a different five-label target's state count would add no missing proof for this target. Representation bits, installation/search cost and physical cost remain separate and unpriced here.

[FC]: https://github.com/the-omega-institute/trureturing/blob/06aa305f75d2e8f0f38ccc4c763391e8caa15e6b/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md
[MO]: https://www.cs.cmu.edu/~cdm/resources/Moore1956-gedanken-experiments.pdf

## 追加锚（本行以下为增补区）

## 9. The complete deadline-three criterion for equal lower-label sets

**约定 9.1（Physical data and the unchanged full target）。** Keep exactly Definitions 3.1 and 5.1, with all original joint sources, both free values, every original tail, both alphabets, fresh distinct $R,C$, and arbitrary $L_\bot$. In this section assume $r=2$ and $|\Lambda[O]|\le2$. Fix a notation-only bijection $\kappa:U_Y\to\mathbb F_2$ and write $b_v=\kappa\circ\lambda_v$. Labels are still returned literally. All phase arithmetic is modulo $T$.

For $i\in\mathbb F_2$, let $M_i$ be the unique whole $\lambda_i$ label class on which $\lambda_{1-i}$ is nonconstant. Exactly three occupied corners of a two-by-two rectangle give this unique class; on $J\setminus M_i$ the other component is constant. For an ambient support $E$, write $e_E=\mathbf1_E$, extended by zero outside $E$. If $E\subseteq W_1$ is even and $m\notin E$, the actual inverse $B=\mathcal B_1(E)$ begins zero. Its charge on the next window, when the **same literal word** is repeated, is

$$
q_2^B(j)=e_E(j-m).
\tag{9.1}
$$

This is the physical translation of (1.5), not a separately selectable second charge. Write $\tau(B)$ for the literal terminal one-run and $\alpha(D)$ for the leading one-run of a word $D$, with $\alpha(1^m)=m$. Full ambient even supports are used throughout; their restrictions to $P$ need not be even.

Define the following two explicit compatibility conditions.

* **A, a repeated query with one fixed raw decoder:** there are $i,\eta\in\mathbb F_2$ and an even $E\subseteq W_1$ with $m\notin E$ such that

$$
\begin{aligned}
e_E(j)&=b_i(j)\oplus\eta &&(j\in J),\\
e_E(j-m)&=1\oplus b_0(j)\oplus b_1(j) &&(j\in M_i).
\end{aligned}
\tag{9.2}
$$

* **B, a shared query with one homogeneous scalar child:** there are distinct literal lower labels $L,L'$, a raw endpoint $e\in\mathbb F_2$, $\delta\in\mathbb F_2$, and even full supports $E\subseteq W_1$, $F\subseteq W_2$, with $m\notin E$, such that

$$
\Lambda[J]=\{(L,L),(L',L),(L,L')\},\qquad
\mu(j)=\mathbf1_{\{\Lambda(j)\ne(L,L)\}},
\tag{9.3}
$$
$$
\begin{aligned}
\lambda_{e\oplus e_E(j)}(j)&=L &&(j\in J),\\
e_F(j)&=\mu(j)\oplus\delta &&(j\in J),\\
\tau(\mathcal B_1(E))+\alpha(\mathcal B_2(F))&<k.
\end{aligned}
\tag{9.4}
$$

These conditions involve phase classes, full physical charges and the actual seam of the same inverses. They quantify no controller, archive or extra runtime coordinate. In A one can equivalently test whole label classes: there are $i$ and a $\lambda_i$ class $A$ missing $H$ such that

$$
M_i\cap(A+m)=\{j\in M_i:\lambda_i(j)=\lambda_{1-i}(j)\}.
\tag{9.5}
$$

Indeed (9.2) prescribes $A=\{j:b_i(j)\oplus\eta=1\}$ on $J$. A shifted actual argument $j-m$, with $j\in J$, belongs to $J$, is the excluded vertex $m$, or lies outside $W_1$; it cannot be zero because $j\ne m$. Thus the only unrestricted actual parity donor zero does not affect (9.2)'s second equation. The even completion $\widehat A^{\,0}$ realizes every consistent (9.5). Nonactual vertices introduce no additional constraint on this equivalence. For B, (9.4) retains the central first charge as a free physical coordinate and includes safe all-one final words.

**定理 9.2（Exact complete-state classification at deadline three, $r=2$）。** Under Convention 9.1,

$$
\boxed{K_{\min}^{\rm GLOBAL}(3;f)=
\begin{cases}
N+4,&\text{A or B holds},\\
N+5,&\text{neither holds}.
\end{cases}}
\tag{9.6}
$$

Proof of all-controller necessity. Lemma 5.3 excludes fewer than four word rows. Suppose a correct deadline-three GLOBAL controller has four. Every initial root installs $1^m$ by Theorem 3.2, and every mandatory root-zero successor emits a word beginning zero: differently labelled phases at the actual maximal surviving tail $h-1$ would otherwise merge in bottom. GLOBAL makes this first suffix one literal $B$ for both values. All its successful images have the literal terminal tail $\tau(B)$.

A two-label scalar child after $B$, with one whole block left, requires a final separating row: its word succeeds and its two scalar updates directly halt with the two different labels. Uniform rejection cannot separate this common-scalar, common-tail child. A root is not a final separating row, since its mandatory root-zero scalar update emits. A first-query row with an emitting scalar update is not one either. These are constraints on fixed raw-response updates at actual occurrences; rows have not been separated by depth.

First allow a shared initial root $a$. Its scalar successor $d_y$ contains $C$ and both lower labels of $\lambda_y$: the lower sources have initial value $y$, and the $C$ sources have initial value $1-y$. Original phase $m$ supplies an actual $C$ source whose charge under the zero-leading $B$ is zero.

If $d_0=d_1=d$, each raw child after $B$ contains this phase-$m$ $C$ source and, for every $j\in J$, one of the complementary-value lower sources. There can be **two** other word rows; allow both as distinct final rows. Even so, a common-tail child can finish in its one remaining block only if it has at most two labels, hence at most one lower label besides $C$. Write these lower labels as $L_0,L_1$ for the raw children. Correctness would give $\lambda_0(j)=L_{q_1^B(j)}$ and $\lambda_1(j)=L_{1\oplus q_1^B(j)}$, so the join has at most two classes. This contradicts (3.1), independently of which last row each child uses.

If $d_0\ne d_1$, each has an emitting scalar update because its actual first support contains three labels. The fourth word row $p$ is the only possible final separator. Each three-label support must therefore split into one homogeneous child and a two-label child whose label pair is exactly the two scalar Halt labels of $p$. Two mixed children could not cover three labels with that same pair. Thus the excluded homogeneous label is the same in both supports; it need not stop immediately for this argument. If it is a lower label $L$, the final pair is $\{C,L'\}$. Phase $m$ puts $C$ in the charge-zero child, forcing $q_1^B(j)=1$ exactly when $\lambda_y(j)=L$ for both $y$. The two literal tables would coincide. If the excluded label is $C$, every $J$ source must have charge one and enter $p$. Their current scalars are complementary, and its fixed successful last word and raw decoder allow at most two joined pairs. Both cases contradict (3.1). Shared roots are therefore impossible at this particular four-row deadline; no root-separation rule for larger controllers is inferred.

Now take distinct roots $a_0,a_1$. Their mandatory first-query rows are not roots, since they begin zero. If these rows are distinct, all four word rows have been used. At least one value $w$ has a mixed child after $B$; otherwise the root and the common $B$ would acquire the full join within two blocks, contrary to Theorem 3.2. Its final separator must be the other value's first-query row $d_i$, $i=1-w$. At the mandatory early occurrence of $d_i$, both scalar updates already halt and return its two lower labels. There is therefore an $\eta$ with $q_1^B=b_i\oplus\eta$ on all $J$, and the installed decoder is

$$
G_i(x)=\kappa^{-1}(x\oplus i\oplus\eta).
\tag{9.7}
$$

The later mixed child is exactly $M_i$. GLOBAL requires the last word of this row to be the same $B$ as at its early occurrence. Its late raw scalar is $w\oplus q_1^B(j)\oplus q_2^B(j)$. Equation (9.7) returns $\lambda_w(j)$ on this whole actual support precisely when the second equation of (9.2) holds. The first equation and even zero-leading full support have already been extracted from the arbitrary actual $B$. This is condition A.

If the two roots share their first-query row $d$, only one other word row $p$ remains. Two mixed scalar children after $B$ would both require $p$. Applying its same word and raw decoder to both complementary-value sources would again allow at most two joined pairs. Hence one raw child, say $e$, is homogeneous, with a common lower label $L$, and the other is mixed. The homogeneous child must halt immediately. If it too entered $p$, the same two-pair contradiction would hold. A root cannot return this lower label in the last block: its mandatory scalar exit emits, any direct other scalar Halt must return fresh $C$, and its bottom continuation has the mandatory eventual label $R$. Sending this child back to $d$ would leave both scalar updates emitting ($d$ and $p$), with no final scalar Halt; bottom cannot return a lower label either. This exhausts possible delays within the four-row budget.

At every $j$, the actual value $e\oplus q_1^B(j)$ enters that homogeneous child with label $L$. Thus $(L',L')$ is absent; since three corners are occupied, (9.3) follows. The other child has current scalar $1-e$, every actual phase in $J$, and immutable label $L$ on the central class and $L'$ on the two leaves. Its final $p$ word must succeed on the common actual tail. Its full even support $F$ and the orientation of its two scalar Halt labels give exactly (9.4), including the strict seam and the no-zero case. This is condition B.

These four sharing cases exhaust four word rows. The argument extracted mandatory unequal-label sources from each possible controller; it neither transforms controllers to a chosen menu nor assumes early $C,R$ stopping. Delayed homogeneous paths, waits, homogeneous rejection and cross-depth identifications were retained whenever they could affect these sources. Lemma 5.3 covers smaller budgets. Necessity is therefore over the full competitor domain.

Proof of complete attainments. Put

$$
\begin{aligned}
\mathcal R_v&=\{(f(v,-j,s),(v,-j,s)):j\in P,\ 0\le s<k\},\\
\mathcal S_v&=\{(\lambda_v(j),(v,-j+m,m+s)):j\in J,\ 0\le s<h\}.
\end{aligned}
\tag{9.8}
$$

For both attainments use two root rows $a_v$, $c(v)=a_v$, $c(\bot)=H_{L_\bot}$, $u(a_v)=1^m$, and

$$
V(a_v,v)=d_v,\qquad V(a_v,1-v)=H_C,\qquad V(a_v,\bot)=H_R.
\tag{9.9}
$$

In A take $w=1-i$, $B=\mathcal B_1(E)$, $\beta=w\oplus e_E(M_i)$, and let $L_S$ be the constant label of $\lambda_w$ on $J\setminus M_i$. There are just two further word rows $d_i,d_w$, both installing $B$, with

$$
V(d_i,x)=H_{G_i(x)}\quad(x\in\mathbb F_2),\qquad
V(d_w,\beta)=d_i,\qquad V(d_w,1-\beta)=H_{L_S}.
\tag{9.10}
$$

Here $e_E(M_i)$ denotes its constant value, supplied by (9.2). The actual word-row union supports are

$$
\begin{aligned}
\Gamma_{a_v}&=\mathcal R_v,&\Gamma_{d_w}&=\mathcal S_w,\\
\Gamma_{d_i}&=\mathcal S_i\ \cup\
\{(\lambda_w(j),(\beta,-j+2m,\tau(B))):j\in M_i\}.
\end{aligned}
\tag{9.11}
$$

The same decoder (9.7) works on both parts of $\Gamma_{d_i}$ by (9.2). Both occurrences of $B$ begin zero, clearing every incoming tail, including root tail $k-1$; internal runs are shorter than $k$. Ranks $3,2,1,0$ on $a_v,d_w,d_i,H_y$ strictly decrease. The stream is $1^m\mid B\mid B$; both labels on $M_i$ actually continue, so its worst fee is three.

In B take $B=\mathcal B_1(E)$, $D=\mathcal B_2(F)$ and identify $d_0=d_1=d$ in (9.9). Install $B$ at $d$ and $D$ at $p$. Define $\ell(0)=L$, $\ell(1)=L'$, $\beta=1-e$, and

$$
V(d,e)=H_L,\qquad V(d,\beta)=p,\qquad
V(p,x)=H_{\ell(x\oplus\beta\oplus\delta)}
\quad(x\in\mathbb F_2).
\tag{9.12}
$$

The exact actual supports are

$$
\Gamma_{a_v}=\mathcal R_v,\qquad
\Gamma_d=\mathcal S_0\cup\mathcal S_1,\qquad
\Gamma_p=\{(\ell(\mu(j)),(\beta,-j+2m,\tau(B))):j\in J\}.
\tag{9.13}
$$

There is one genuine continuing initial value at every $j$ in $\Gamma_p$. Equation (9.4) gives the same raw decoder on this entire support. The zero-leading $B$ clears all original surviving tails. The actual inequality $\tau(B)+\alpha(D)<k$ makes this very $D$ safe, including $D=1^m$; later internal runs are shorter than $k$. Ranks $3,2,1,0$ on roots, $d,p,H_y$ descend. The stream is $1^m\mid B\mid D$, and the nonconstant $\mu$ support actually emits its third block.

For both tables set the unused bottom update of every nonroot word row to $H_R$, install exactly one $H_y$ for every actual $y\in f(Q)$, and make all its updates self-updates. Its actual support is exactly (5.6): the initial-bottom pair if applicable and all routed incoming word images from the displayed unions. Thus all $c,u,V$ entries, every actual source and all stopping outputs are accounted for. Each construction has $N+4$ states and satisfies the existing [FC, Theorem 27.2] conditions. No support or rank is an input. If neither condition holds, the necessity proof excludes four rows and the unchanged full five-row certificate (6.2)–(6.5), including its reverse orientation and safe seam, attains $N+5$. Together with Lemma 5.3 this proves (9.6). ∎

**推论 9.3（An unbounded equal-label consumer with a strict memory premium）。** For every integer $q\ge1$, set

$$
m=3q,\quad k=5q-1,\quad T=5q,\quad g=q,\quad
J=\{q,2q,4q\},\quad H=\{2q\},\quad O=\varnothing,
\tag{9.14}
$$
$$
\lambda_0(q,2q,4q)=(0,1,0),\qquad
\lambda_1(q,2q,4q)=(0,1,1).
\tag{9.15}
$$

Use these literal lower labels, fresh $R,C$ and arbitrary $L_\bot$ on the entire target (3.2). Then

$$
K_{\min}^{\rm ad}(2;f)=N+4<N+5=K_{\min}^{\rm GLOBAL}(3;f),
\qquad C_{\rm ad}(f)=2<3=C_{\rm pre}(f).
\tag{9.16}
$$

Proof. Both diagonal joined pairs occur, so B fails. For A with $i=0$, $M_0=\{q,4q\}$ and the required repeated charge at $j=q=a$ is one, because the two labels agree there. But $q-m=m$ modulo $T$, and the compulsory leading-zero charge at $m$ is zero. For $i=1$, $M_1=\{2q,4q\}$. The missed phase $2q$ forces $\eta=1$, hence $e_E(4q)=0$; at $j=2q$ the required repeated charge is one while $e_E(2q-m)=e_E(4q)=0$. These are actual-vertex conflicts for every literal word, irrespective of nonactual parity freedom. Theorem 9.2 proves the universal $N+5$ lower bound.

For a complete attainment put $L=1^{3q}$ and $B=0^{2q}1^q$. Use the following five word rows and all actual Halt rows, with $c(v)=a_v$, $c(\bot)=H_{L_\bot}$:

| Row | Word | Endpoint $0$ | Endpoint $1$ | Bottom |
| --- | --- | --- | --- | --- |
| $a_0$ | $L$ | $b_0$ | $H_C$ | $H_R$ |
| $a_1$ | $L$ | $H_C$ | $b_1$ | $H_R$ |
| $b_0$ | $B$ | $p$ | $H_0$ | $H_R$ |
| $b_1$ | $B$ | $H_0$ | $H_1$ | $H_R$ |
| $p$ | $B$ | $H_1$ | $H_0$ | $H_R$ |

The full supports of $B$ at indices one and two are $\{0,q\}$ and $\{3q,4q\}$. Both words begin zero and their terminal tail is $q$. The root and $b_v$ supports are (9.8), and

$$
\Gamma_p=\{(\lambda_0(j),(0,-j+2m,q)):j\in\{2q,4q\}\}.
\tag{9.17}
$$

Ranks $3,2,1,0$ on roots, first queries, $p$ and exact Halt images (5.6) give all-source closure, correct literal outputs and termination. All executions are prefixes of $L\mid B\mid B$, and both labels in (9.17) issue the last word. There are $2|P|k+1=50q-9$ jointly attainable INITIAL records, including bottom; every one is retained. The adaptive count and the two block prices are Theorems 5.2 and 3.2. The complete GLOBAL count is nine for an existing bottom label and ten for a fresh one. This family consumes the new universal exclusion; it is not merely a local archive example. ∎

## 10. Deadline four: compulsory distinct first queries and the disjoint-label minimum

**引理 10.1（The third missed-set class forces safe later words and separates first queries）。** Under the full Definitions 3.1 and 5.1, assume $|\Lambda[O]|=3$. In every correct deadline-four GLOBAL controller, the first suffix charge $q_1$ is nonconstant on $O$. There are $w,d\in\mathbb F_2$ such that

$$
M=\{j\in O:q_1(j)=d\}
\quad\text{contains both labels of }\lambda_w.
\tag{10.1}
$$

The words at absolute indices two and three succeed on every still-active successful $C$/lower-label source. If $r\ge3$, the mandatory root-zero first-query rows $b_0,b_1$ are distinct, regardless of the controller's other row count or root sharing.

Proof. The root is $1^m$ and the first common suffix $B$ begins zero, by the same mandatory maximal-tail argument as in Theorem 9.2. Hence every active successful $C$/lower source has tail $\tau(B)$. Every literal word at index two has charge zero on $O$, by the full physical window (1.5).

If $q_1$ were constant on $O$, both component tables, which are nonconstant on $O$, would retain a mixed common-tail support after $B$. Its index-two word cannot reject or distinguish it. The index-three word must also succeed on a mixed support. The only further successful distinction on $O$ would be its single binary charge at index three, allowing at most two joined classes. A phase could not evade this argument by stopping earlier: the common earlier responses give the same stopping decision to every phase in that value fibre. Thus $q_1$ is nonconstant. If every $q_1$ fibre on $O$ were homogeneous in both components, the join would again have at most two classes. This proves (10.1).

Its actual sources share one raw scalar $e=w\oplus d$, one control successor after $B$, and the tail $\tau(B)$. Their next word cannot reject them, and its charge zero on $O$ leaves them mixed. They therefore issue index three, whose word cannot reject them either. Safety depends only on the common literal word and incoming tail, not on phase or value. Since GLOBAL uses these same words for every active source, all active successful $C$/lower sources succeed at both indices. After a safe all-one word the tail is the common incoming tail plus $m$; after a safe word containing zero it is the literal terminal tail. This establishes common tails and safety without excluding either kind of word. Homogeneous rejection is allowed in the competitor model; it cannot occur on these active sources at these two indices.

Suppose $b_0=b_1=b$. At an $O$ phase $j$, the raw response after $B$ is $v\oplus q_1(j)$, and the next response is that same scalar. Subsequent control is therefore a function of this raw bit. For each $e,t\in\mathbb F_2$ write $D_e(t)$ for its output when the index-three difference is $t$; if it stopped earlier, extend its actual output constantly. This merely names the fixed control updates and includes delayed stops. Writing $q_3$ for the common last charge, correctness gives

$$
\Lambda(j)=
\bigl(D_{q_1(j)}(q_3(j)),D_{1\oplus q_1(j)}(q_3(j))\bigr)
\quad(j\in O).
\tag{10.2}
$$

For a fixed $t$, this pair is one of the two orientations of $(D_0(t),D_1(t))$. Put $U_v=\lambda_v[J]$. If both orientations belong to $U_0\times U_1$, both entries belong to $U_0\cap U_1$. For $r\ge3$ this intersection has at most one label, so the two orientations are identical. Each $t$ can consequently contribute at most one admissible ordered pair, giving $|\Lambda[O]|\le2$, a contradiction. This excludes shared first queries for $r=3,4$. For $r=2$ the orientation argument does not give that conclusion: two orientation families can contain three pairs. ∎

**定理 10.2（Exact complete deadline-four count for disjoint lower-label sets）。** Throughout the full target domain, if $|\Lambda[O]|=3$ and $r=4$, then

$$
\boxed{K_{\min}^{\rm GLOBAL}(4;f)=N+6.}
\tag{10.3}
$$

Proof of the arbitrary-controller lower bound. Here $U_0$ and $U_1$ are disjoint. Take $w,d,M$ from Lemma 10.1 and put $e=w\oplus d$. Let $X=V(b_w,e)$ be the word row issued by these mixed sources at index two. Its $O$ charge is zero, so they still have raw scalar $e$ afterwards and must enter a word row $F=V(X,e)$ at index three. Since that is their last block, both scalar updates of $F$ halt with the two distinct labels in $U_w$. This row is a genuine final separator.

The row $F$ cannot be an initial root, since each root's mandatory root-zero scalar update emits. It cannot be $b_w$, whose mixed-child update emits $X$. Nor can it be $b_i$, $i=1-w$: $q_1$ is nonconstant on $O$, so at the mandatory first occurrence of $b_i$ both raw scalar children contain actual labels of $U_i$, whereas both fixed scalar Halts of $F$ are in the disjoint set $U_w$. Lemma 10.1 makes $b_0,b_1$ distinct, and their zero-leading words distinguish both from the all-one root rows.

The intermediate $X$ is also distinct from all these rows. It is not $F$, since its scalar $e$ successor must emit $F$. If $X=b_w$, the edge $V(b_w,e)=b_w$ would repeat at index two and force $F=b_w$. If $X=b_i$, its mandatory first occurrence has an actual $O$ source with raw response $e$. The fixed edge $V(b_i,e)=F$ sends that source to $F$ at index two. Lemma 10.1 makes its word safe there, and either scalar Halt returns a $U_w$ label instead of the source's $U_i$ label. This is a conflict on an actual cross-depth union, not a ban on cross-depth reuse.

If $X$ is a distinct initial root $a_i$, its raw $e$ edge is either its mandatory root-zero edge to $b_i$, or its positive-root edge containing fresh $C$. The former would identify $F=b_i$, already excluded. The latter sends an actual $C$ source to $F$ at index one. GLOBAL then makes its installed word the common zero-leading first suffix, which succeeds on that source; neither of its $U_w$ scalar Halts can return $C$. If the initial root is shared, both its scalar edges are the already excluded $b_0,b_1$. Thus $X$ is distinct from every root, both first queries and $F$.

With distinct initial roots, the six rows $a_0,a_1,b_0,b_1,X,F$ are therefore compulsory. It remains to allow a shared root $a$. If there were at most five word rows, they would have to be exactly $a,b_0,b_1,X,F$. Both scalar edges of $a$ emit. Each $b_y$ has actual $O$ lower sources in both raw children, so neither edge can directly halt with $C$ or a label of $U_{1-y}$. Its first support also has $C$ and both labels of $U_y$, so it has at most one scalar Halt exit. The row $F$ returns only $U_w$. By Lemma 10.1 no active successful $C$/lower source uses a bottom exit after the root. Hence some scalar Halt exit of $X$ must return the actual label $C$. Its other scalar edge $e$ already emits $F$, leaving no lower Halt exit at $X$. Both labels of $U_i$, $i=1-w$, could then be returned only by $b_i$, which has at most one scalar Halt exit. Contradiction.

Delayed $R$ paths may use other responses but cannot return a $C$/lower source in this argument. Delayed $C$ was explicitly retained in the shared-root case and in the positive-root conflict. Arbitrary waits, repeated literal words, safe all-one actions and attempted row reuse have not been discarded. Six word rows and the $N$ different actual Halt outputs are necessary.

For complete attainment reuse precisely the four-block certificate of Theorem 6.1, with its words (2.2), (2.4), (2.5), the two roots and root updates of §5, first-query updates (6.6) as specified there, and $c(v)=a_v$, $c(\bot)=H_{L_\bot}$. More explicitly, choosing a leaf $S$ absent from $H$, let $i$ be its singleton component, $w=1-i$, and name the remaining joined classes $D_0,E_0$. The six word rows are $a_0,a_1,b_0,b_1,p_2,p_3$; their words are $1^m,1^m,B_1,B_1,B_2,B_3$. Their entire scalar table is

$$
\begin{aligned}
V(a_v,v)&=b_v,&V(a_v,1-v)&=H_C,\\
V(b_i,i)&=H_{(D_0)_i},&V(b_i,1-i)&=H_{S_i},\\
V(b_w,w)&=p_2,&V(b_w,1-w)&=H_{S_w},\\
V(p_2,w)&=p_3,&V(p_2,1-w)&=H_{(E_0)_w},\\
V(p_3,w)&=H_{(D_0)_w},&V(p_3,1-w)&=H_{(E_0)_w}.
\end{aligned}
\tag{10.4}
$$

Every word-row bottom update is $H_R$ and every actual Halt row self-updates. The exact supports are $\Gamma_{a_v}=\mathcal R_v$, $\Gamma_{b_v}=\mathcal S_v$, (6.5) with $\beta=w$, (6.7), and the exact Halt images (5.6). The ranks are $4,3,2,1,0$ on roots, first queries, $p_2,p_3,H_y$. The already proved same-word seams of Theorem 2.1 give all-source closure and safety, including a possible all-one $B_2$, for the single stream $1^m\mid B_1\mid B_2\mid B_3$. This is the existing complete upper certificate consumed at its original hypotheses, with six word rows; it is not imposed on competitors. It matches the new lower bound. ∎

**例 10.3（A full disjoint-label consumer at every scale）。** For $q\ge1$, use $m=6q$, $k=11q-1$, $g=q$, and

$$
\lambda_0(j)=\mathbf1_{\{9q\}}(j),\qquad
\lambda_1(j)=2+\mathbf1_{\{10q\}}(j)\quad(j\in J).
\tag{10.5}
$$

The label sets are $\{0,1\}$ and $\{2,3\}$. Here $H=\{2q,3q,4q,5q\}$ is homogeneous and $O=\{8q,9q,10q\}$ has all three pairs. Fresh $R,C$ and arbitrary bottom complete the full target. The unchanged certificate (10.4), with isolated leaf $(1,2)$ and $w=1$, uses

$$
1^{6q}\ \mid\ 0^{3q}1^{2q}0^q\ \mid\ 0^{6q}\ \mid\ 0^{3q}1^q0^{2q}.
\tag{10.6}
$$

Its actual supports, ranks and raw decoder are those just specified; no source is omitted. Theorem 10.2 gives twelve complete states when bottom uses an existing output and thirteen when it is fresh. The universal branch proof supplies this minimum; the family illustrates its consumption.

## 11. Deadline four: an exact sufficient region with root and query reuse

**定理 11.1（A sufficient two-block translation condition, without a converse）。** Keep the entire Definitions 3.1 and 5.1 contract, assume $r=2$ and $|\Lambda[O]|=3$, and choose $v\in\mathbb F_2$, $w=1-v$. Let $B$ be a literal length-$m$ word beginning zero, let $q_1=q_1^B$ be its physical charge, put

$$
I=\{j\in J:q_1(j)=1\},\qquad U=J\setminus I,
\tag{11.1}
$$

and let $G:\mathbb F_2\to U_Y$ be a bijection. Suppose there is a literal label $z$ such that

$$
\begin{aligned}
\lambda_w(j)&=G(w\oplus q_1(j)) &&(j\in J),\\
\lambda_v(j)&=z &&(j\in U),\\
j'=j-2m&\in J,\qquad \lambda_v(j)=\lambda_w(j') &&(j\in I).
\end{aligned}
\tag{11.2}
$$

Then

$$
\boxed{K_{\min}^{\rm GLOBAL}(4;f)=N+4.}
\tag{11.3}
$$

Failure of (11.2) does not exclude any four-row controller. This theorem gives an exact sufficient region inside the original deadline-four classification, not a classification of its complement.

Proof. The actual vertex $a=2m\pmod T$ belongs to $J$. It cannot lie in $I$, because its translated $j'$ would be zero, excluded from $J$. Hence $q_1(a)=0$, which by (1.5) is the actual last bit of $B$. Thus $B$ ends zero as well as begins zero.

Use four word rows $a_v,a_w,b_v,b_w$, all $N$ actual Halt rows, $c(x)=a_x$ for $x\in\mathbb F_2$, and $c(\bot)=H_{L_\bot}$. Install $L=1^m$ at both roots and $B$ at both queries. The complete scalar table is

$$
\begin{aligned}
V(a_x,x)&=b_x,&V(a_x,1-x)&=H_C &&(x\in\mathbb F_2),\\
V(b_v,v)&=H_z,&V(b_v,w)&=a_w,\\
V(b_w,e)&=H_{G(e)} &&&&(e\in\mathbb F_2).
\end{aligned}
\tag{11.4}
$$

Set every word-row bottom update to $H_R$ and all Halt updates to self-updates. The stream is the single installed $L\mid B\mid L\mid B$. Its actual unions are

$$
\begin{aligned}
\Gamma_{a_v}&=\mathcal R_v,&\Gamma_{b_v}&=\mathcal S_v,\\
\Gamma_{a_w}&=\mathcal R_w\ \cup\
\{(\lambda_v(j),(w,-j+2m,0)):j\in I\},\\
\Gamma_{b_w}&=\mathcal S_w\ \cup\
\{(\lambda_v(j),(w,-j+3m,m)):j\in I\}.
\end{aligned}
\tag{11.5}
$$

Both added sets are already subsets of the corresponding first supports: use $j'=j-2m\in J$, the immutable-label equality in (11.2), and original tail $s=0$. These are actual reachable unions; coincidence with an existing support is a consequence of the target relation, not a free archive or phase input.

At initial value $w$, the root-zero support is decoded by the first equation of (11.2). At value $v$, $q_1=0$ stops with $z$; $q_1=1$ produces scalar $w$, phase $-j+2m$ and tail zero. This is the actual pair already in $\mathcal R_w$ at $j'$. The reused all-one root is safe because its incoming tail is zero and $m<k$. Since $j'\in J$, it has charge zero and reaches the corresponding pair of $\mathcal S_w$ at original tail zero. The same $B$ and the same raw decoder then return $\lambda_v(j)$. The first $B$ clears all root tails, including $k-1$, and its derived final zero makes the reused all-one seam safe; the last $B$ clears tail $m$. No cleaning block is added.

Use ranks $4,3,2,1,0$ on $a_v,b_v,a_w,b_w,H_y$, respectively, with exact Halt images (5.6). Every actual step is closed and strictly descending, even though $a_w$ occurs at indices zero and two and $b_w$ at indices one and three. The two binary tables and the first two equations of (11.2) show that $I$ has both labels of $\lambda_v$: on $U$ one joined class occurs, so its other two classes must occur on $I$. These actual sources emit all four blocks. The full certificate therefore attains $N+4$ states at the original fee four. Lemma 5.3 is the matching universal lower bound, including all other root/word/reuse competitors. No new all-controller restriction is needed for this sufficient region. ∎

**推论 11.2（An unbounded full-source consumer of exact root reuse）。** For every $q\ge1$, set $m=6q$, $k=11q-1$, $T=11q$, $g=q$. On

$$
J=\{q,2q,3q,4q,5q,7q,8q,9q,10q\},\quad
H=\{2q,3q,4q,5q\},\quad O=\{8q,9q,10q\},
\tag{11.6}
$$

take distinct literal lower labels $A,B$ and

$$
\lambda_0(j)=\begin{cases}B,&j=8q,\\ A,&j\ne8q,\end{cases}
\qquad
\lambda_1(j)=\begin{cases}A,&j\in\{8q,9q\},\\ B,&j\notin\{8q,9q\}.
\end{cases}
\tag{11.7}
$$

Use fresh $R,C$ and arbitrary bottom in the entire target (3.2). The join is $(B,A)$ at $8q$, $(A,A)$ at $9q$, and $(A,B)$ elsewhere; all three occur on $O$ and $H$ is homogeneous. With

$$
L=1^{6q},\qquad D=0^{2q}1^q0^{3q},
\tag{11.8}
$$

the original fees are $C_{\rm ad}=2$, $C_{\rm pre}=4$, while both complete minima at their respective deadlines are $N+4$.

Proof. The actual full physical supports of $L,D,L,D$ at indices zero through three are respectively

$$
\{0,6q\},\quad\{8q,9q\},\quad\{q,7q\},\quad\{9q,10q\}.
\tag{11.9}
$$

Use $v=0$, $w=1$, $G(0)=A$, $G(1)=B$, $z=A$, and $I=\{8q,9q\}$. Translation by $-2m$ sends these two phases to $7q,8q$, with matching labels $B,A$. Thus all of (11.2) holds for the displayed word $D$, not for a substitute representative. The complete raw table is

| Row | Word | Endpoint $0$ | Endpoint $1$ | Bottom |
| --- | --- | --- | --- | --- |
| $a_0$ | $L$ | $b_0$ | $H_C$ | $H_R$ |
| $a_1$ | $L$ | $H_C$ | $b_1$ | $H_R$ |
| $b_0$ | $D$ | $H_A$ | $a_1$ | $H_R$ |
| $b_1$ | $D$ | $H_A$ | $H_B$ | $H_R$ |

Initialize and install all actual Halt rows as in Theorem 11.1. The added root pairs are $(B,(1,4q,0))$ and $(A,(1,3q,0))$; the added query pairs are $(B,(1,10q,m))$ and $(A,(1,9q,m))$. They already occur in the full original supports at $j'=7q,8q$, original tail zero. Equations (11.5) and (5.6) are therefore the exact complete union supports. Ranks $4,3,2,1,0$ give the complete stationary certificate. All $22(11q-1)+1$ actual INITIAL records are retained, including all original tails and bottom. Theorem 11.1 gives eight complete states for an existing bottom label and nine for a fresh one; Theorems 5.2 and 3.2 give the credited adaptive minimum and the two fees. The two distinct dictionary words have $12q$ expanded bits and the four-block prefix has $24q$ bits; those representation lengths remain separate from complete states and emitted-block cost. ∎

## 12. Exact coverage, evidence and unchanged residual obligations

**来源 12.1（Reuse and the added compatibility content）。** The definitions and operative suppliers remain those of §§1, 4 and 8. The immutable bytes of [IC], [MC], [FC] and [S1], [S2], [S10], [S13], [S15] agree with their specified source hashes. [IC, Chapter 1] supplies the original integer reader, full-history witnesses and physical charge inverse. [S10, Interface 2.1 and Lemma 3.2] supplies same-word seams and the common-tail all-success/all-rejection constraint. [S13, Theorem 8.4] supplies the already known binary safe-cut interpretation of (9.4); no new generic terminal certificate is claimed. [FC, §§26–27] supplies complete stationary control and actual union-support/rank certificates. Theorem 5.2, Lemma 5.3 and the full upper certificates of Theorem 6.1 are reused. Block-fee value joining is not used to transfer a memory count.

The added ordinary deductions are the exhaustive four-row deadline-three compatibility criterion and strict-price consumer, the deadline-four shared-first-query obstruction for $r\ge3$, the disjoint-label six-row lower bound, and the sufficient translation condition with full root/query reuse. The r=4 proof uses disjoint labels at its actual raw-exit conflicts; it does not transfer those conflicts to overlapping or equal label sets. The sufficient condition (11.2) has a real unbounded full-source consumer and does not assert necessity.

The primary comparisons remain Moore [MO, pp.129–131] and van den Bos–Vaandrager [L1, Definitions 7–11 and Figure 3]: one-machine experiments, completed compatible observations and irreversible mergers are applicable. Multiple-copy experiments are unavailable here; acyclic test nodes do not count stationary control states or justify forbidding row reuse. The inspected primary theory and source-local stationary/certificate results provide no replacement for the target-specific translated-charge and disjoint-label arguments above. This is a bounded overlap assessment, with no exhaustive literature-absence, priority or formal-verification claim.

**开放问题 12.2（Residual map on the original target and parameters）。** At the original deadline three, $|\Lambda[O]|\le2$, Theorems 6.2 and 9.2 now determine every $r=2,3,4$ branch, all seven cross-table equality patterns and every original actual-gcd phase placement satisfying Definition 3.1. This does not price deadline four for a target whose original optimum fee is three.

At the original deadline four, $|\Lambda[O]|=3$, Theorem 10.2 determines all $r=4$ targets as $N+6$, and Theorem 11.1 determines its stated sufficient $r=2$ region as $N+4$. Every $r=2$ target outside that sufficient region, and every $r=3$ target, retains the original exact-choice obligation

$$
K_{\min}^{\rm GLOBAL}(4;f)\in\{N+4,N+5,N+6\}.
\tag{12.1}
$$

No failure of (11.2) is an exclusion theorem. Lemma 10.1 removes shared mandatory first queries for $r=3$ but does not classify its four-/five-row possibilities, shared initial roots, delayed $C,R$, repeated words or other raw-update reuse. The unresolved proofs still require universal four-/five-row existence or exclusion with complete matched attainments, actual immutable-target/current-record unions and the same installed raw updates at every occurrence. They retain arbitrary literal words, actual source seams, homogeneous rejection, safe all-one words, waits, early and delayed stops, both initial values, every original tail and phase, and arbitrary bottom-label equalities. Selected word menus, finite samples and joined block prices do not supply these exclusions.

Tail-dependent low tables, nonhomogeneous $H$, other class counts or target extensions, other parameter regions and the arbitrary-target/all-$k,m$ adaptive/GLOBAL objective of [IC, Open Problem 9.1] keep their full original obligations. The earlier restricted theorems retain their own hypotheses. Exact classification of the whole original goal is not claimed.

**核验 12.3（Ordinary proofs and bounded direct-bit corroboration）。** The proof arguments above are ordinary mathematics. Direct-bit checks execute the original total transitions on every successful INITIAL record of each tested target, preserving its immutable label, using only completed endpoint updates, and checking common-stream prefixes, actual reused union supports and strict row ranks. No finite competitor non-hit is used as an all-controller proof.

The checks include every admissible $r=2$ deadline-three table for all allowed widths $3\le m\le6$, additionally $(m,k)=(8,9)$, with all three-corner placements and homogeneous possibly empty $H$: 3,528 labelled-table cases. Condition A yields 412 checked certificates and condition B yields 1,156; 2,148 tables satisfy neither. The counts for A and B are overlapping. The selected B certificates include 568 final words beginning one and 72 safe all-one final words. For the same parameter set, all 648 deadline-four three-corner placements with disjoint component-label sets use the unchanged complete six-row upper certificate. Each of the three full parameter families in §§9–11 is additionally checked at every scale $1\le q\le8$, including their actual noncoprime phases and all original tails. Across these checks, 2,240 complete attaining controllers execute 365,712 successful INITIAL records; 12,512 separate initial-bottom variants cover every existing output label and one fresh label. The checks pass and corroborate attainments and physical prescriptions; the unbounded necessary statements are supported by their displayed proofs.

Complete states, dictionary/stream bits, descriptor size, offline search, installation and physical work remain different resources. There is no Lean, build, kernel, ingestion, coverage, freezing or CI claim. Independent mathematical review and publication checks are separate obligations. The results stay with the target owner, reuse the existing lower/upper and certificate machinery, and expose exactly which original compatibility obligations remain.

## 追加锚（本行以下为增补区）

## 13. Deadline-four phase conditions for the remaining equal-label case

**约定 13.1（Unchanged sources and literal translations）。** Keep exactly Definitions 3.1 and 5.1, and assume $|\Lambda[O]|=3$. All original INITIAL records, both values and alphabets, every original tail, the actual subgroup $P$, fresh $R,C$ and arbitrary bottom-label equalities remain in force. For $r=2$ write $U_Y=\{A,B\}$, with $A\ne B$ literal labels. A diagonal pair means $(A,A)$ or $(B,B)$, using literal label equality. Three occupied corners contain either one or both diagonal pairs; because $\Lambda[O]=\Lambda[J]$, the same alternatives hold on $O$.

For an even full physical support $E\subseteq W_1$ with $m\notin E$, let $B_E=\mathcal B_1(E)$ and put

$$
q_1(j)=\mathbf1_E(j),\qquad
q_2^B(j)=\mathbf1_E(j-m),\qquad
q_3^B(j)=\mathbf1_E(j-2m).
\tag{13.1}
$$

These are the charges of the **same literal word** at indices one, two and three. Values outside the full support are zero. In particular $B_E$ begins zero. For another even full support $F\subseteq W_2$, write $D_F=\mathcal B_2(F)$ and $q_2^D=\mathbf1_F$. Retain the actual leading run $\alpha$, terminal run $\tau$, and safe tail update $\Phi$ of [S15, Definition 1.1]. Full even supports include every nonactual vertex; no parity condition is imposed just on their restrictions to $P$.

Define $\mathsf R$ to mean that (11.2) holds for some $v,w,B,G,z$ exactly as in Theorem 11.1. The following two further conditions concern only physical charges and literal phase labels.

For either component $i$, let $M_i$ be its unique whole label class on which the other component $w=1-i$ is nonconstant. This is a property of the three occupied corners, independent of a selected word. The other component has a constant literal label $z$ on $J\setminus M_i$.

**定义 13.2（Condition $\mathsf P$: an early final query reused after a middle word）。** There are $i\in\mathbb F_2$, a bijection $G:\mathbb F_2\to U_Y$, and full supports $E,F$ as above, such that

$$
\lambda_i(j)=G(i\oplus q_1(j))\quad(j\in J),\qquad
\tau(B_E)+\alpha(D_F)<k.
\tag{13.2}
$$

Set $w=1-i$, let $d$ be the constant value of $q_1$ on $M_i$, and put $e=w\oplus d$, $h_e=1-e$. Require

$$
\lambda_w(j)=G(e\oplus q_3^B(j))
\quad(j\in M_i,\ q_2^D(j)=0).
\tag{13.3}
$$

On $M_i\cap\{q_2^D=1\}$ require either constancy of $\lambda_w$, with any literal value in $U_Y$, or

$$
\lambda_w(j)=G(h_e\oplus q_3^B(j)).
\tag{13.4}
$$

Empty-set constancy is allowed. The charge at the last query is translated from $E$, not selected independently. The middle word remains arbitrary, including zero waits and safe all-one words.

**定义 13.3（Condition $\mathsf Q$: three repeated queries, including a possible control cycle）。** Choose $E$ as in Convention 13.1, $w,e\in\mathbb F_2$, $i=1-w$, $h_e=1-e$, and a bijection $G:\mathbb F_2\to U_Y$. Choose two markers $\theta_w,\theta_i$, each in the disjoint set

$$
\operatorname{Stop}(U_Y)\sqcup\{\mathrm{Final},\mathrm{Cross}\},
\tag{13.5}
$$

with at most one $\mathrm{Cross}$. Thus there are eight marker patterns before choosing any literal Stop labels. For each actual phase $j$, abbreviate $b=q_2^B(j)$ and $c=q_3^B(j)$. Define

$$
T_j(\operatorname{Stop}(L))=L,\qquad
T_j(\mathrm{Final})=G(h_e\oplus c).
\tag{13.6}
$$

A first raw response is $x=v\oplus q_1(j)$. Its required literal return is the following table. An undefined entry must have no actual phase satisfying its row conditions.

| Component, first raw response and further condition | Required return |
| --- | --- |
| $v=i$, $x=e$ | $G(e\oplus b)$ |
| $v=w$, $x=e$, $b=0$ | $G(e\oplus c)$ |
| $v=w$, $x=e$, $b=1$, $\theta_i=\operatorname{Stop}(L)$ | $L$ |
| $v=w$, $x=e$, $b=1$, $\theta_i=\mathrm{Final}$ | $G(h_e\oplus c)$ |
| $v=w$, $x=e$, $b=1$, $\theta_i=\mathrm{Cross}$ | $L$ if $\theta_w=\operatorname{Stop}(L)$ and $c=0$; otherwise undefined |
| Either $v$, $x=h_e$, $\theta_v=\operatorname{Stop}(L)$ | $L$ |
| Either $v$, $x=h_e$, $\theta_v=\mathrm{Final}$ | $G(h_e\oplus b)$ |
| $v=w$, $x=h_e$, $\theta_w=\mathrm{Cross}$, $b=0$ | $T_j(\theta_i)$ |
| $v=w$, $x=h_e$, $\theta_w=\mathrm{Cross}$, $b=1$ | $G(e\oplus c)$ |
| $v=i$, $x=h_e$, $\theta_i=\mathrm{Cross}$, $b=0$ | $T_j(\theta_w)$ |
| $v=i$, $x=h_e$, $\theta_i=\mathrm{Cross}$, $b=1$ | Undefined |

Condition $\mathsf Q$ says that every entry selected by each $v\in\mathbb F_2,j\in J$ is defined and equals $\lambda_v(j)$. At most one Cross makes each occurrence of (13.6) defined. This is an explicit comparison of the original tables with three translations of one physical charge, including the phases outside the intermediate window. The markers specify the eight complementary-exit patterns forced in the proof below; they do not range over a controller graph, a word menu or hidden runtime data.

**引理 13.4（A blank middle translation cannot repair the missed set）。** For any $B_E$ of Convention 13.1, if $q_2^B=0$ on all $J$, then $q_3^B=0$ on $O$.

Proof. Translation by $-m$ sends $J$ to $P\setminus\{0,-m\}$. Consequently $E\cap P\subseteq\{0,-m\}$. Its translation by $2m$ can be nonzero on actual phases only at $2m=a$ or $m$. Both are in $W_2$, and $m\notin J$, so neither belongs to $O$. Nonactual charges stay nonactual under translation by $m\in P$. This uses the actual subgroup, not a coprime replacement. ∎

## 14. Exhaustion of all four- and five-row competitors

**引理 14.1（A shared root with distinct first queries requires at least six word rows）。** Under Convention 13.1, in every correct deadline-four GLOBAL controller whose initial root is shared and whose two mandatory first-query rows are distinct, at least six word rows are necessary.

Proof. Reuse Lemma 10.1. The first suffix is one zero-leading word $B$, with charge nonconstant on $O$. Choose $w,d$ and a mixed $O$ fibre as in (10.1), put $e=w\oplus d$, and let its index-two row be $X$ and its index-three row be $F$. Then $V(b_w,e)=X$, $V(X,e)=F$, and both scalar updates of $F$ halt with the two distinct labels of $\lambda_w$. Every active successful $C$/lower source is safe at both later indices. A shared root $a$ has scalar successors $b_0,b_1$, each with $C$ and its two lower labels. Thus neither a root nor a first query can be $F$; every first-query scalar child contains an actual $O$ lower source, so neither query can have a direct scalar Halt exit $C$.

Four word rows leave only $a,b_0,b_1,F$, none with a possible successful $C$ exit. At five rows there is just one other row $Y$. The mixed intermediate $X$ cannot be $a$ (its scalar successor would be a first query), $F$, or $b_w$ (the fixed edge would repeat on the zero-charge $O$ fibre). It is therefore $b_i$, $i=1-w$, or $Y$.

If $X=b_i$, then $V(b_i,e)=F$. The actual phase-$m$ $C$ source in the mandatory first support of $b_i$ has raw response $i$, so $e\ne i$: otherwise it enters $F$ and returns a lower label. Hence $e=w$. Write $p=q_1^B(0)$. The actual phase-zero $C$ source in that same support forces $p=0$, since $p=1$ would give raw response $w=e$ and again enter $F$. GLOBAL now repeats $B$ at index two. The phase-$m$ $C$ source in $b_w$ enters $b_i$ with scalar $w$, and its next charge is $q_2^B(m)=q_1^B(0)=0$. It consequently enters $F$ at index three and incorrectly returns a lower label. This excludes $X=b_i$ without deleting the other delayed $C$ paths.

Suppose $X=Y$. All successful $C$ exits must be at $Y$, so its other scalar edge is $V(Y,1-e)=H_C$, while $V(Y,e)=F$. If $p=1$, both scalar children of each first query contain actual $C$ sources, at phases zero and $m$. Every query scalar edge then emits and cannot enter $F$ at index two. An actual $O$ lower source with raw response $1-e$ cannot enter $Y$ at index two, because its next charge is zero and $Y$ would return $C$. It cannot finish via a root, which leaves a query as the last row with both scalar edges emitting. Nor can it finish via a query: its unchanged index-two response would have to enter $F$, a fixed edge already forbidden by a mandatory first-occurrence $C$ source. No remaining row exists. Thus $p=0$.

For $p=0$, the phase-zero and phase-$m$ $C$ sources both have raw response $y$ at $b_y$. Its fixed $C$ edge can be neither a Halt, $F$, nor a root: the last option leaves a query with no direct $C$ exit. It cannot be a self-edge, since GLOBAL would repeat $B$ and $q_2^B(m)=p=0$ would repeat that edge through the last query. Therefore each $C$ edge goes to $Y$ or to the other query.

If $d=0$, then $e=w$ and $b_w$'s $C$ edge already goes to $Y$. Sending $b_i$'s $C$ edge directly to $Y$ would put the complementary scalars $w,i$ at the same word, only one of which can use its sole $C$ exit. Its edge must instead go to $b_w$. This forces $Y$'s index-two word to be $B$. But $q_2^B(m)=0$ sends the phase-$m$ $C$ source from $b_w$ along $Y$'s emitting edge to $F$, a contradiction.

If $d=1$, then $e=i$. The two $C$ edges cannot both go directly to $Y$, for the same complementary-scalar reason. A cross-query edge therefore forces the index-two word at $Y$ to be $B$, with $q_2^B(m)=0$. A direct $C$ entry to $Y$ can now be correct only with scalar $w=1-e$, so $b_i$'s $C$ edge must go to $b_w$. If $b_w$'s $C$ edge goes to $b_i$, correct last-block $C$ stopping forces $b_i$'s other scalar edge to $Y$. The two phase-$m$ $C$ sources then enter $Y$ at index three with complementary scalars; its one $C$ exit cannot return both. Otherwise $b_w$'s $C$ edge goes directly to $Y$. Returning the phase-$m$ $C$ source from $b_i$, which enters $Y$ at index three with scalar $i$, requires

$$
q_3^B(m)=q_1^B(-m)=1.
\tag{14.1}
$$

The phase-zero $C$ source from $b_w$ enters $Y$ at index two with scalar $w$, but $q_2^B(0)=q_1^B(-m)=1$ now sends it to $F$, again returning a lower label. These are actual endpoint-phase sources on the same literal repeated word. They exhaust both values of $d$ and all five-row placements of $X$. Delayed $R$ and homogeneous rejection cannot add an exit for these successful sources. ∎

**引理 14.2（Both diagonal pairs exclude shared first queries at five rows）。** Assume $r=2$ and both diagonal pairs occur. No correct deadline-four controller with at most five word rows can share its mandatory first-query row, whether its initial roots are shared or distinct.

Proof. In the shared query $b$, each raw scalar child contains both lower labels on $O$: each diagonal phase supplies both initial values, hence one source to each raw child. The two children therefore both emit an index-two intermediate and an index-three final separator. The row $b$ has both scalar edges emitting and cannot be final. An intermediate cannot be $b$, because its fixed edge would repeat at the unchanged $O$ scalar and the last $b$ has no scalar Halt. A root's zero edge also leaves a last query with no scalar Halt. A distinct root's positive edge, if used to reach a final separator at the last index, sends a mandatory original phase-$m$ $C$ source to that same separator at index one; its zero-leading first suffix succeeds and returns a lower label. A shared root has only the two mandatory query edges. Thus roots cannot supply the required intermediates either.

With distinct roots the rows are exactly the two roots, $b$, one intermediate $X$ and one final separator $F$. Both $O$ raw children use $X$; its two scalar edges must enter $F$. With a shared root there are three other rows. If both children use one intermediate, its two emitting scalar edges leave only lower-label final separators, so no successful $C$ output is available anywhere. If they use distinct intermediates, only one final separator remains. In both remaining cases every initial value at every $O$ phase reaches the same final raw decoder $G$, with complementary scalar inputs:

$$
\Lambda(j)=
\bigl(G(q_1(j)\oplus q_3(j)),G(1\oplus q_1(j)\oplus q_3(j))\bigr)
\quad(j\in O).
\tag{14.2}
$$

The index-two charge on $O$ is zero. Since $G$ has two different scalar Halt labels, (14.2) has only two possible pairs and no diagonal pair. This contradicts the three original classes on $O$. The argument retains all shared-row occurrences and delayed endpoint outputs. ∎

**定理 14.3（The root-reentry condition is the complete four-row criterion）。** For every $r=2$ target of Convention 13.1,

$$
K_{\min}^{\rm GLOBAL}(4;f)=N+4
\quad\Longleftrightarrow\quad\mathsf R.
\tag{14.3}
$$

Proof of necessity. Lemma 5.3 supplies four as the lower word-row bound. Choose the mixed $O$ path $b_w\to X\to F$ with raw bit $e$ from Lemma 10.1. The final $F$ has both scalar updates Halt with the two lower labels. It cannot be a root or $b_w$. If the initial root is shared and the first queries are distinct, Lemma 14.1 excludes four rows. If the initial roots are distinct but their first query is shared, the only final row is the fourth row, leaving no intermediate: a shared-query self-edge repeats, a root-zero edge returns the shared query, and a root-positive edge sends a mandatory $C$ source to the lower-label final row at index one.

If both root and first query are shared, the four rows would be $a,b,X,F$. Each scalar child of $b$ contains an actual phase-$m$ $C$ source and an actual $O$ lower source. Both scalar edges emit. Since all active successful sources are safe, the only available $C$ exit is the other scalar edge of $X$, namely $V(X,1-e)=H_C$. The other child of $b$, with raw scalar $1-e$, cannot use $X$ (an $O$ source would return $C$), $F$ (an actual $C$ source would return a lower label), a self-edge (it repeats through the last nonhalting query), or $a$ (the last row is again $b$, with both scalar edges emitting). Shared roots are thus impossible at four rows, including shared first queries.

The roots and first queries must consequently all be distinct. The final row is the other value's first query $b_i$, $i=1-w$. Its two installed Halts give a bijection $G$ with $\lambda_i(j)=G(i\oplus q_1(j))$ on all $J$. The mixed intermediate can only be a root. Its positive edge cannot enter $b_i$, because the mandatory original $C$ sources would then execute this final query at index one and return lower labels. Its zero edge identifies it as $a_i$, with $e=i$, hence $d=1$. The stream is necessarily $1^m\mid B\mid1^m\mid B$.

The whole $I=\{q_1=1\}$ class enters $a_i$, and the other class has a constant $\lambda_w$ label $z$, because the join has exactly three corners. Safety of the actual index-two all-one word gives $\tau(B)+m<k$, hence $\tau(B)<h$. At $a_i$ its current pair is an actual original INITIAL pair with phase $j'=j-2m$ and original tail $\tau(B)$:

$$
(\lambda_w(j),(i,-j+2m,\tau(B)))\quad(j\in I).
\tag{14.4}
$$

The mandatory initial support of this same root contains that current record. Determinism forces its immutable label to equal the original target there. Fresh $C$ excludes $j'\in\{0,m\}$, and correctness gives $j'\in J$ and $\lambda_w(j)=\lambda_i(j')$. These are exactly (11.2), with its component names interchanged. In particular $a\notin I$ and the actual terminal bit of $B$ is zero. No source is copied in this comparison; it is a conflict or coincidence between two actual arrivals to the same stationary row. Theorem 11.1 supplies the complete matching four-row attainment. ∎

**定理 14.4（Every overlapping but unequal lower-label pair has exact six-row memory）。** Under Convention 13.1, if $r=3$, then

$$
\boxed{K_{\min}^{\rm GLOBAL}(4;f)=N+6.}
\tag{14.5}
$$

Proof. Lemma 10.1 makes the first queries distinct. Lemma 14.1 excludes a shared root with at most five rows. With distinct roots, write the two lower-label sets as $U_w=\{L,A_w\}$ and $U_i=\{L,A_i\}$, where the three labels are distinct. On the mixed $O$ path the final $F$ cannot be $b_i$: both its scalar Halts are in $U_w$, whereas the mandatory first support of $b_i$ has the actual exclusive label $A_i$. Nor can it be a root or $b_w$. At four rows there is no $F$. At five it is the additional row.

The intermediate $X$ cannot be $F$, a self-edge of $b_w$, or a root. A root-zero edge would identify $F$ with a first query; a root-positive edge would send an original $C$ source to $F$ at index one. Thus $X=b_i$, with $V(b_i,e)=F$. GLOBAL repeats the same zero-leading $B$ at index two. Since $q_1$ is nonconstant on $O$, a mandatory early $b_i$ source also enters $F$ at index two, forcing its word to be $B$ at both later positions.

The exclusive label $A_i$ can be returned only by the other scalar edge of $b_i$. Roots have their mandatory emitting zero edge and fresh-$C$ positive edge; $b_w$'s other scalar child contains an actual $U_w$ source on $O$; $F$ returns only $U_w$; and no active successful source rejects. Hence $V(b_i,1-e)=H_{A_i}$. Its early $e$ child is exactly the whole $L$ class. An actual $L$ source on $O$ enters $F$ early with unchanged raw bit $e$, so $F$'s raw-$e$ Halt is $L$.

Every early $L$ source then forces $q_2^B=0$ on that whole class. Every later $U_w$ source from the complementary whole $A_i$ class also forces $q_2^B=0$, since charge one at $b_i$ would return the exclusive wrong label $A_i$. Thus $q_2^B=0$ on all $J$. Lemma 13.4 gives $q_3^B=0$ on $O$, contradicting final separation of the two labels on the original mixed $O$ fibre. All four-/five-row competitors are excluded. The unchanged six-row certificate of Theorem 6.1 supplies the matching attainment for every one of these targets: its six installed words and complete scalar updates are (10.4), its initialization and all bottom updates are those of §5, its exact supports are (5.5), (6.5), (6.7) and the Halt images (5.6), and its ranks are $4,3,2,1,0$. Equal literal Halt labels alone are merged, giving exactly $N+6$ complete states. ∎

**定理 14.5（Complete remaining deadline-four classification）。** For every $r=2$ target of Convention 13.1,

$$
\boxed{K_{\min}^{\rm GLOBAL}(4;f)=
\begin{cases}
N+4,&\mathsf R,\\
N+5,&\neg\mathsf R\text{ and either one diagonal pair occurs or }
\mathsf P\text{ or }\mathsf Q,\\
N+6,&\neg\mathsf R,\text{ both diagonal pairs occur, and }
\neg\mathsf P\land\neg\mathsf Q.
\end{cases}}
\tag{14.6}
$$

Proof of the five-row necessity when both diagonal pairs occur. Lemmas 14.1–14.2 force distinct roots and distinct first queries. Choose the original mixed $O$ path $b_w\to X\to F$. The final row cannot be a root or $b_w$.

If $F=b_i$, its mandatory first occurrence directly returns its binary table, giving $G$ and (13.2). The charge-one or charge-zero whole class $M_i$ is the mixed child of $b_w$. If $X$ is a root, the same actual-support comparison as in Theorem 14.3 gives $\mathsf R$, even if a fifth row is present elsewhere. Otherwise $X$ is the fifth row, with its arbitrary actual index-two word $D$ and $V(X,e)=b_i$. The full actual seam is (13.2). Its charge-zero child necessarily returns (13.3) at the repeated last $B$. The other child either enters $b_i$, giving (13.4), or is homogeneous. To see the latter conclusion without presuming early stopping, its last row can only return a lower label at $b_w$'s one possible scalar Halt, or at a direct Halt of $X$: roots install $1^m$, whereas the actual last GLOBAL word is the zero-leading $B$; a self-edge of $X$ has no scalar Halt at its last occurrence. The other first-query row has an emitting mixed edge and at most its one other Halt, with one fixed literal output. A delayed homogeneous last step can therefore be replaced by that already correct literal Halt on this child. No mixed child is removed. This is exactly the constancy alternative in $\mathsf P$.

If $F$ is the fifth row, the intermediate can only be $b_i$. A root-zero edge would make $F$ a first query, and a root-positive edge would send a mandatory $C$ source to the lower-label final row at index one. Hence $V(b_w,e)=b_i$ and $V(b_i,e)=F$. An actual early $b_i$ source enters $F$ at index two. The words at indices one, two and three are therefore the same zero-leading $B$.

Only the raw-$1-e$ updates remain. A root cannot be used at either later index, because its all-one word differs from $B$. A self-edge of either query repeats on an actual $O$ source with unchanged scalar and leaves a last query with both exits emitting. A direct Halt there must be a literal lower label, because each raw child contains an actual $O$ lower source. The remaining options are the final row or the other query. Both complementary edges cannot cross: an actual early $O$ source would cross again at index two and reach a last query whose two scalar successors still emit. Thus there are exactly the eight marker patterns (13.5). Reading their actual raw updates gives every row of Definition 13.3's return table, including its undefined last-block cases. Correctness on the full $J$ support is exactly $\mathsf Q$.

This exhaustion used the original sources, unbounded literal-word alphabets and fixed actual raw updates. It includes root/query sharing before excluding it by actual conflicts, repeated words and control cycles, delayed $C,R$ and lower stops, homogeneous rejection and every paid wait. It does not infer all-controller exclusion from a finite search or from a selected family of words. Theorem 14.3 gives the four-row equivalence. Section 15 supplies complete five-row attainments for $\mathsf P$, $\mathsf Q$ and the one-diagonal-pair case. When neither five-row condition holds in the two-diagonal case, the just-proved exhaustion excludes five rows, and the existing six-row certificate of Theorem 6.1 attains six. Lemma 5.3 excludes fewer than four throughout, proving (14.6). ∎

**例 14.6（A full equal-label target requiring six word rows）。** Set $m=6,k=10$, with distinct literal lower labels $A,B$, fresh $R,C$ and arbitrary bottom. On the full target (3.2) take $\lambda_0=B$ only at phase $9$, and $\lambda_1=B$ only at phases $9,10$; all other $J$ entries are $A$. The joined pairs on $O=\{8,9,10\}$ are $(A,A),(B,B),(A,B)$, and $H=\{2,3,4,5\}$ has pair $(A,A)$. Then $K_{\min}^{\rm GLOBAL}(4;f)=N+6$.

Proof of the physical failures. In $\mathsf R$, decoding component zero first leaves the other component nonconstant outside its charge-one singleton $9$. Decoding component one first forces charge one at $9,10$, but the required translation $9-2m=8$ has label $A$ instead of the late component's label $B$. Thus R fails. In P, the homogeneous $H$ fixes the first charge orientation. For $i=0$ it is one only at $9$ on $J$; (13.3) fails at $j=8$. For $i=1$ it is one at $9,10$; (13.3) fails at $j=9$. These failures are on $O$, where no middle word can change the charge.

For Q, the early final entry on $O$ must be homogeneous, while the late entry must contain both labels. The actual translation $q_3^B(j)=q_1(j-2m)$ forces $e=0$ and just the following four possible first-charge triples, ordered at phases $8,9,10$. All other triples already fail one of those two requirements.

| Early component $i$ | First-charge triple | Remaining conflict |
| --- | --- | --- |
| $0$ | $110$ | Its early final entry at actual phase $3$ returns $B$ instead of $A$, since $q_2^B(3)=q_1(8)=1$. |
| $0$ | $101$ | Its early final entry at actual phase $4$ returns $B$ instead of $A$, since $q_2^B(4)=q_1(9)=0$. |
| $1$ | $100$ | Its complementary marker cannot Stop on the two actual labels; Final fails at phase $4$, and Cross is undefined at phase $3$. |
| $1$ | $001$ | Stop and Final fail on phases $8,9$; Cross with an opposite Stop cannot return their two labels, and Cross with an opposite Final fails at phase $8$, where $q_3^B(8)=q_1(7)=1$ is forced. |

This is a literal phase contradiction for all physical first supports and all eight complementary-exit patterns, not a numerical controller non-hit. Theorem 14.5 gives the six-row lower bound. The matching six-row complete certificate is (10.4) with isolated leaf $(B,B)$, $i=0,w=1$, remaining classes $(A,A),(A,B)$, and stream

$$
111111\mid000110\mid000000\mid000100.
\tag{14.7}
$$

Its full supports, raw updates and ranks are those of Theorem 6.1. All $221$ original INITIAL records, including bottom, are retained. Thus the complete count is ten when bottom uses an existing output and eleven when its label is fresh. ∎

## 15. Complete matched attainments with the original physical seams

**定理 15.1（One diagonal pair always admits five word rows）。** Under Convention 13.1 with $r=2$ and exactly one diagonal pair, there is a complete five-word-row GLOBAL controller of deadline four.

Proof. Write the three literal pairs as $(L,L),(L',L),(L,L')$, with $L\ne L'$. Choose $e\in\mathbb F_2$ and first charge $q$ on $J$ by

$$
q(j)=\begin{cases}
e\oplus1,&\Lambda(j)=(L',L),\\
e,&\Lambda(j)=(L,L'),\\
0,&\Lambda(j)=(L,L).
\end{cases}
\tag{15.1}
$$

If $H$ is a leaf class, choose $e$ so its charge is zero. If $H$ is central or empty, choose $e$ so $q(a)=0$. Such a choice exists in both cases. Then $q=0$ on $H$, and a raw first response $e$ always has label $L$ on both values. Set

$$
E_1=\widehat{\{j\in J:q(j)=1\}}^{\,0},\qquad
B=\mathcal B_1(E_1),\qquad
\mu(j)=\mathbf1_{\{\Lambda(j)\ne(L,L)\}},\qquad \beta=1-e.
\tag{15.2}
$$

The continuing raw-$\beta$ child has one actual initial value at every $j$, and target $L$ or $L'$ according as $\mu(j)=0$ or $1$. The full inverse begins zero and safely clears every original root tail. Put

$$
A_2=\{j\in J\cap W_2:\mu(j)=1\}.
\tag{15.3}
$$

If $B$ ends zero, take $F_2=A_2$. Otherwise, if $a\in A_2$ and $a+1$ is nonactual, take $F_2=A_2\cup\{a+1\}$; in all other cases take $F_2=A_2$. Let $D=\mathcal B_2(\widehat F_2^{\,m})$.

These are charges of this very middle word. If $B$ ends zero, incoming tail zero makes every length-$m$ word safe, including all ones. If it ends one, the choice of $e$ shows that $H$ is a leaf class, $q(a)=1$ and $\mu(a)=1$. The first interior vertex $a+1$ lies in the ambient missed interval of $W_1$: when actual it is in that homogeneous leaf class, so its charge in $A_2$ is one; when nonactual the displayed addition makes its charge one. The leading two charges of $D$ are consequently $1,1$, making its actual first bits $1,0$. The parity donor $m$ lies strictly later, at path position $h+1\ge2$. Since $\tau(B)\le m-1$, this seam satisfies $\tau(B)+1\le m<k$, and the following zero clears it. Thus the same literal $D$ is safe, with no cleanup block.

Use the actual third-window donor $d_3$ of (1.6), and put

$$
F=\mathcal B_3\left(\widehat{\{j\in O:\mu(j)=1\}}^{\,d_3}\right).
\tag{15.4}
$$

This word starts zero, safely clears the actual tail of $D$, and distinguishes the only missed $L'$ phases from every remaining $L$ phase.

Install two roots $a_v$ with $c(v)=a_v$, $u(a_v)=1^m$, $V(a_v,v)=b$, $V(a_v,1-v)=H_C$ and $V(a_v,\bot)=H_R$. Install three more word rows $b,X,F_0$, with words $B,D,F$ and

$$
V(b,e)=H_L,\quad V(b,\beta)=X,\qquad
V(X,e)=H_{L'},\quad V(X,\beta)=F_0,\qquad
V(F_0,e)=H_{L'},\quad V(F_0,\beta)=H_L.
\tag{15.5}
$$

All other word-row bottom updates are $H_R$. Install exactly the $N$ actual Halt rows and their self-updates; initialize $c(\bot)=H_{L_\bot}$. In the notation (9.8), the exact word supports are

$$
\begin{aligned}
\Gamma_{a_v}&=\mathcal R_v,\qquad
\Gamma_b=\mathcal S_0\cup\mathcal S_1,\\
\Gamma_X&=\{(L_{\mu(j)},(\beta,-j+2m,\tau(B))):j\in J\},\\
\Gamma_{F_0}&=\{(L_{\mu(j)},(\beta,-j+3m,\Phi_D(\tau(B)))):
j\in J,\ q_2^D(j)=0\},
\end{aligned}
\tag{15.6}
$$

where $L_0=L$, $L_1=L'$. Exact Halt supports are (5.6), including the independent initial-bottom pair. Ranks $4,3,2,1,0$ on roots, $b,X,F_0$, Halts strictly descend. Every source follows a prefix of $1^m\mid B\mid D\mid F$. Both labels occur on $O$ and have middle charge zero, so actual sources issue all four blocks. This gives the complete $N+5$ attainment used in (14.6); it places no restriction on competitors. ∎

**命题 15.2（Complete five-row realization of $\mathsf P$）。** Every instance of Condition $\mathsf P$ has a complete $N+5$-state GLOBAL controller correct within four blocks.

Proof. Use the two distinct roots and their complete updates (9.9). At both first-query rows install $B=B_E$. Let $w=1-i$, $z$ be the constant label on $J\setminus M_i$, and install one additional row $X$ with word $D=D_F$. Use

$$
V(b_i,x)=H_{G(x)}\ (x\in\mathbb F_2),\qquad
V(b_w,e)=X,\quad V(b_w,1-e)=H_z,\quad V(X,e)=b_i.
\tag{15.7}
$$

For the other scalar update of $X$, use the homogeneous literal Halt when choosing the constancy alternative of Definition 13.2, and otherwise use $V(X,1-e)=b_i$. Every bottom update is $H_R$, every actual Halt self-updates, and $c(\bot)=H_{L_\bot}$. The stream is $1^m\mid B\mid D\mid B$.

Let $A=M_i\cap\{q_2^D=0\}$, enlarged to all $M_i$ when both children enter $b_i$. The exact word supports are

$$
\begin{aligned}
\Gamma_{a_v}&=\mathcal R_v,\qquad \Gamma_{b_w}=\mathcal S_w,\\
\Gamma_X&=\{(\lambda_w(j),(e,-j+2m,\tau(B))):j\in M_i\},\\
\Gamma_{b_i}&=\mathcal S_i\ \cup\
\{(\lambda_w(j),(e\oplus q_2^D(j),-j+3m,\Phi_D(\tau(B)))):j\in A\}.
\end{aligned}
\tag{15.8}
$$

The same word and raw decoder at $b_i$ work on both occurrences by (13.2)–(13.4). The middle seam is the strict actual inequality in (13.2), including the no-zero case; the last zero-leading $B$ clears its actual incoming tail. Exact Halt images are (5.6). Ranks $4,3,2,1,0$ on roots, $b_w,X,b_i$, Halts give the complete support certificate, with early $b_i$ occurrences legitimately skipping ranks. Mixed $O$ sources emit all four blocks. ∎

**命题 15.3（Complete five-row realization of $\mathsf Q$, with pair-dependent rank）。** Every instance of Condition $\mathsf Q$ has a complete $N+5$-state GLOBAL controller correct within four blocks, without requiring its control graph to be acyclic.

Proof. Use the two distinct roots (9.9), two first queries $b_w,b_i$, and one final row $p$, all three installing the very same $B=B_E$. Set

$$
V(b_w,e)=b_i,\qquad V(b_i,e)=p,\qquad V(p,x)=H_{G(x)}.
\tag{15.9}
$$

At raw response $h_e$, marker $\operatorname{Stop}(L)$ installs $H_L$, marker Final installs $p$, and marker Cross installs the other query. All word-row bottom updates are $H_R$; every actual Halt self-updates and initial bottom initializes to its own Halt. This fully specifies $c,u,V$ on $N+5$ rows. The single stream is $1^m\mid B\mid B\mid B$.

After the first suffix, all successful incoming tails are $\tau(B)$; every further $B$ begins zero and is safe on that tail. Trace the fixed raw updates (15.9), keeping the actual scalars. The early $i,e$ case reaches $p$ at index two, giving $G(e\oplus q_2^B)$. The $w,e$ case reaches $b_i$ at index two: charge zero reaches $p$ last, while charge one takes its marker. A late Cross here enters $b_w$ last, so it can stop only through a Stop marker at raw $h_e$, exactly the guard $\theta_w=\operatorname{Stop}(L),q_3^B=0$. An early Cross from $b_w,h_e$ enters $b_i$ at index two; an early Cross from $b_i,h_e$ enters $b_w$ there. Their two charges give precisely the last four rows of Definition 13.3, including the undefined case in which a last $b_i$ has no Halt exit. The other marker cases give that table's direct or final returns. Its identities therefore prove literal INITIAL-label correctness and termination for every actual phase and both values, not just $O$.

Here is the exact union-support and rank certificate for these possibly repeated rows. Roots have $\Gamma_{a_v}=\mathcal R_v$. Before the first query at index one use $\mathcal S_v$. For each $v,j$, take the finite itinerary just specified by (15.9) and its markers. If word row $x$ occurs before index $t\in\{2,3\}$, include exactly the pair

$$
\left(\lambda_v(j),
\left(v\oplus\bigoplus_{\ell=1}^{t-1}q_\ell^B(j),
-j+tm,\tau(B)\right)\right)
\quad\text{in }\Gamma_x.
\tag{15.10}
$$

Together with the first-query supports, these are all actual word-row pairs, with union taken across every occurrence. All original $s<h$ have those same later images because the first $B$ clears them. Halt supports are the exact initial-bottom and incoming images (5.6).

Give each query pair the number of word steps remaining in its displayed itinerary, each root rank four, and each Halt rank zero. This is a well-defined function of the immutable label, current record and control row: if the same triple is reached twice, its remaining installed deterministic execution is identical. The table proves that execution ends; thus both occurrences have the same remaining count. Every actual word update decreases that count by one, and each root-to-query step decreases from four to at most three. A Cross can produce a cycle in the nominal control graph; it produces no cycle in this proved terminating closed-loop graph. This is precisely the existing [FC, Theorems 27.2–27.3] certificate, with no runtime rank, archive or stage input. Some actual mixed $O$ sources issue all four blocks by Theorem 3.2. ∎

## 16. Coverage, source contracts and the unchanged outer objective

**来源 16.1（Credited interfaces and source-specific deductions）。** The operative mathematical sources are the original owner §§1–12 and its immutable suppliers: [IC, Definitions 1.1–1.3, Interface 1.4, Propositions 4.2–4.4, Theorem 5.1, Definition 29.1, Theorem 29.2, Chapter 69 and Open Problem 9.1]; [MC, §§1–3]; [S1, Definitions 1.2/2.1, Convention 1.3, Lemmas 4.2–4.3, Theorem 5.2 and Note 5.3]; [S2, Theorem 14.1]; [S10, Interface 2.1 and Lemma 3.2]; [S13, Definitions 8.1/8.3 and Theorem 8.4]; [S15, Section 1, Definition 1.1 and Proposition 4.2]; and [FC, Definitions 26.1–27.1 and Theorems 27.2–27.3]. Their displayed hypotheses and the immutable versions of §§4, 8 and 12 are retained. In particular block-fee value joining is not a memory-preserving transformation, and the coprime central pricing theorems of S15 are not imported into actual-gcd cases.

The four-row lower bound, full six-row upper construction, forced root, physical inverse, common-tail semantics and complete-controller certificate are reused. The added ordinary content is the actual endpoint-phase obstruction for shared-root five-row reuse, the complete necessity of the two-block root-reentry condition, the overlapping-label six-row exclusion, the one-diagonal-pair five-row construction, and the exhaustive source-local five-row phase identities with their matched stationary attainments. No mathematical priority or exhaustive literature-absence claim is made.

The inspected primary comparisons remain Moore [MO, pp.129–131], which distinguishes one-machine fixed/adaptive simple experiments from several-copy experiments and explicitly models absorbing destruction, and van den Bos–Vaandrager [L1, Definitions 7–11 and Figure 3], which uses completed observations, compatible tests and irreversible first-action mergers. Their source contracts support these comparisons. Multiple copies are unavailable here; their acyclic test graphs do not imply an acyclic stationary control graph or prohibit the Cross case. Neither primary paper supplies this target's translated physical charges, actual-gcd parity donors, strict seams or state formula.

**核验 16.2（Finite direct-bit corroboration, separate from the proofs）。** Finite attainment checks execute the original bit transitions (1.2) of IC on every original successful INITIAL phase, tail and value in each checked target. They retain its immutable label, update only at whole endpoints, check the installed common stream and all union-support occurrences, and assign decreasing remaining-execution ranks to the actual closed-loop triples. The checks do not use the physical-charge formulas as the transition implementation. Initial bottom is initialized directly to its installed literal Halt; coincidence with any existing output, or a fresh bottom label, changes only the number and identity of actual Halt rows.

At $(m,k)=(6,10)$, all 648 $r=2$ three-corner assignments with homogeneous $H$ are checked. The conditions select 16 four-row R certificates, 316 five-row one-diagonal certificates, 160 five-row P certificates, and 156 six-row fallback certificates. All 142,560 successful INITIAL-record executions pass. At the same parameters all 2,592 cases under the four overlapping-label equality patterns $0102,0120,0112,0121$ use the matching six-row certificate, with 570,240 successful INITIAL-record executions passing. Eight separately selected Q certificates at $(8,12)$ and $(9,12)$ pass on all 2,496 of their successful INITIAL records. Four further certificates explicitly use a Cross marker and pass on all 1,248 successful INITIAL records. These presentation counts include overlap between available five-row conditions; selection of one certificate is not a count of all controllers.

Further direct executions check selected R, P and one-diagonal constructions, and each of the four overlapping-label patterns, at scaled actual parameters $m=6q,k=11q-1$ for $1\le q\le8$: 56 complete certificates and 59,752 successful INITIAL records, preserving their actual subgroup phases and all original tails. A separate exhaustive raw-response check verifies all 1,920 cases of the Q return table, including its 80 undefined cases, against the installed stationary updates. Together these checks execute 776,296 successful INITIAL records. All 19,164 initial-bottom variants, one for every existing literal output and one fresh output in each checked certificate presentation, separately return the installed bottom label at fee zero and retain total Halt self-updates. These corroborate literal attainments and the finite return table. The universal exclusions and exact classifications are the ordinary proofs in §14, not a finite numerical non-hit. No Lean, build, kernel, ingestion, atom coverage, freezing, CI or independent-review result is asserted.

**边界 16.3（Exact finite-unit result and original unresolved objective）。** Under exactly Definition 3.1, every original deadline-four $r=2$ target is classified by (14.6), every $r=3$ target has $N+6$ states by (14.5), and every $r=4$ target retains the already proved $N+6$ value of Theorem 10.2. Deadline-three targets retain the complete classification of Theorems 6.2 and 9.2. These are semantic existence and minimum statements for arbitrary literal labels; effective selection requires a finite target partition or decidable equality, as in S1 Note 5.3. The source-local phase identities range over full even physical supports and check the actual same-word seams; no free controller clock, remembered archive, copied source or uncounted decoder is introduced.

The residual (12.1) is thereby resolved for its stated finite unit. The original arbitrary-target/all-$k,m$ objective remains unresolved with all its original quantifiers. Tail-dependent lower tables, nonhomogeneous $H$, other class counts, other target extensions or parameter regions, competing roots and nonfresh root labels retain the obligations of [IC, Open Problem 9.1]. A deadline-four price for a target whose original optimum block fee is three is also outside these new statements. Complete memory, dictionary and stream bits, installation/search costs and physical execution remain separate resources. Ordinary proofs and bounded attainment checks supply no fresh kernel result or completion of the persistent outer goal.

## 追加锚（本行以下为增补区）

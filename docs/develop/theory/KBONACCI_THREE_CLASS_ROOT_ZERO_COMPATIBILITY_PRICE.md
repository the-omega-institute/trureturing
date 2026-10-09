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

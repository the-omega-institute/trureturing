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

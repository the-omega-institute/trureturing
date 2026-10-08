# KBonacci four-label root-zero intersection prices

This same-topic continuation consumes the [canonical INITIAL cost theory][IC72], the [mixed-tail root-zero cut-price companion][M72], and the [three-class root-zero compatibility-price companion][T72]. References to Definitions 1.1–1.3, Interface 1.4, Chapters 1–71, and equations numbered below 72 refer to the canonical volume. Clauses 72.x belong to this continuation. The original all-target, all-parameter adaptive and one-GLOBAL-stream fee objective retains the unresolved scope stated in Boundary 72.6.

## 72. Four-label root-zero fees from the intersection of missed-set images

**定义 72.1（The actual paid archive and the four-label class）。** Retain Definitions 1.1–1.3 and Interface 1.4 in their original scopes: integer KBonacci weights, matched $V_k\bmod2$ reading, all jointly attainable complete-history sources, immutable INITIAL record labels, a free initial scalar or independently labelled absorbing bottom, complete-endpoint observations, and actual emitted-complete-block fees. Assume

$$
3\le m<k\le2m-2,\qquad T=k+1,\qquad g=\gcd(m,T),\qquad P=g\mathbb Z/T\mathbb Z,
\qquad h=k-m,\qquad a=2m-T=m-h-1\ge1.
\tag{72.1}
$$

The actual gcd is unrestricted. In this range $1\le h\le m-2$, and both original alphabets contain every literal $m$-bit word; cross-block rejection is still enforced. Index the actually emitted root by zero and keep the ordered physical paths $W_t=[tm,(t+1)m]\pmod T$. Fix one remembered free INITIAL value $v$, actually issue $1^m$, and condition on its successful zero-difference archive. Put

$$
\begin{aligned}
J&=P\setminus\{0,m\},\\
H&=J\setminus W_1=P\cap\{a+1,\ldots,m-1\},\\
O&=J\setminus W_2.
\end{aligned}
\tag{72.2}
$$

Its INITIAL candidates and their current records are exactly

$$
(v,-j,s),\quad j\in J,\ 0\le s<h;
\qquad (v,-j+m,m+s).
\tag{72.3}
$$

On these INITIAL rows require $f(v,-j,s)=\lambda(j)$ independently of $s$, with

$$
L=\lambda[J],\qquad |L|=4,\qquad X=\lambda[H],\quad |X|\le2,\qquad Z=\lambda[O].
\tag{72.4}
$$

No labels are imposed on other archives. Empty images have cardinality zero. Let $D_{\rm ad}(\lambda)$ be the minimum additional worst-branch emitted-block fee from this archive, and $D_{\rm child\text{-}pre}(\lambda)$ its price using one fixed literal suffix for all its children, with stopping and decoding from their own complete endpoints. The already paid root is separate. Every issued wait, padding, repair or rejecting block costs one. There are no resets, copies, hidden initial clocks, intermediate readings or borrowed sibling observations.

**定理 72.2（The exact four-label intersection law）。** For every table and actual subgroup in Definition 72.1, under either original alphabet, set

$$
\mathsf K(\lambda)\quad\Longleftrightarrow\quad
|Z|\le2\ \text{ and }\quad
\bigl(|X|=|Z|=2\ \Longrightarrow\ |X\cap Z|=1\bigr).
\tag{72.5}
$$

Then

$$
\boxed{D_{\rm ad}(\lambda)=D_{\rm child\text{-}pre}(\lambda)=
\begin{cases}
2,&\mathsf K(\lambda),\\
3,&\neg\mathsf K(\lambda).
\end{cases}}
\tag{72.6}
$$

The two-block attainment uses one shared second word even though both first-response children remain live. The three-block attainment also uses one suffix shared by every continuing child. In particular neither equality is obtained by combining independent child optima.

**证明（actual joint histories and the all-action lower bound）。** The histories are the supplied witnesses (1.3), also [S1, Convention 1.3; S15, Section 1]. For each $v,j,s$, choose $\ell\equiv0\pmod m$, $\ell\equiv-j\pmod T$, $\ell\ge s+2$, let $d=\bigoplus_{i=\ell-s}^{\ell-1}c_i$, and use the single legal history $(v\oplus d)0^{\ell-s-1}1^s$. Generalized CRT applies since $g\mid j$. The separating zero, first-bit compensation and terminal run simultaneously realize the required value, phase and tail at a complete endpoint. All blocks are in both alphabets. Their different, unobserved history lengths provide no additional archive information. The same actual root succeeds precisely at $s<h$, has charge support $\{0,m\}$, and gives (72.3). Thus every tail in that rectangle is actually present at every indicated phase; it is not a product of marginal reachability claims.

Four labels prohibit stopping at the acquired archive. At differently labelled phases choose the actual INITIAL tail $s=h-1$. Their current tails are $k-1$. Every next literal word beginning one sends them immediately to the same absorbing record, with the same complete endpoint and all later observations. No later adaptive action, wait, repair or stopping rule can recover their different INITIAL labels. Consequently every correct continuation starts its first additional word with zero. This clears all current tails; the entire word then succeeds because each remaining internal run is shorter than $k$. It produces two successful difference children, each with a common current value and the actual common terminal tail of this very word.

By [S10, Lemma 3.2], a further literal word on either child succeeds on every candidate there or rejects all of them. Common rejection cannot finish a child with unequal labels, at that endpoint or at any later endpoint. A successful further word has only two scalar outcomes. Thus one additional block cannot finish four labels, and any completion within two additional blocks requires each first-response child to have at most two labels. Their union has four labels, so they must have exactly two each and their label images must be disjoint. In particular every occurrence of a label has the same first response: no label can be split between those two children. Neither child can stop after the first block.

Call their label pairs $G_0,G_1$, indexed by first difference. Every physical charge outside $W_1$ is zero, so $X\subseteq G_0$. Whatever second word is chosen, including an adaptive word chosen separately on each child, every phase of $O$ has second difference zero if that word succeeds. Therefore $Z\cap G_e$ has at most one label for each $e$. It follows that $|Z|\le2$; if $|X|=|Z|=2$, then $X=G_0$ and $Z$ has exactly one label in each pair, giving $|X\cap Z|=1$. Failure of (72.5) therefore forces additional fee at least three even for adaptive control. This reasoning exhausts all literal first and second words, absorbed rejection and all endpoint stopping decisions. An issued wait occupies one of these physical calendar slots and is charged; it cannot insert an uncounted later window.

**证明（the code and the same-word two-block seam）。** Suppose $\mathsf K(\lambda)$. Choose a pair $G_0\subset L$ containing $X$, with complement $G_1$, so that each $G_e$ contains at most one label of $Z$. Such a choice exists: when $|X|=|Z|=2$ it is exactly the intersection condition; when $|X|\le1$ one can complete $X$ to a pair splitting any two labels of $Z$; when $|Z|\le1$ no split is required. In each pair give its $Z$ label, if present, second bit zero, and give the other label second bit one. If it contains no $Z$ label, either orientation is allowed. This gives a bijection

$$
\gamma:L\longrightarrow\{0,1\}^2,\qquad
\gamma_1=0\text{ on }X,\qquad \gamma_2=0\text{ on }Z.
\tag{72.7}
$$

The vertex $a$ is an actual member of $J$: $g\mid(2m-T)$ and $0<a<m$. Choose the code in (72.7) with the additional property

$$
\gamma(\lambda(a))=(1,1)\quad\Longrightarrow\quad
(0,1)\in\gamma[X]\ \text{ and }\ (1,0)\in\gamma[Z].
\tag{72.8}
$$

To obtain it, start with any (72.7). If the code at $a$ is $(1,1)$ and $(0,1)$ is absent from $\gamma[X]$, exchange the labels coded $(1,1)$ and $(0,1)$. This preserves (72.7) and makes the first bit at $a$ zero. If instead $(1,0)$ is absent from $\gamma[Z]$, exchange $(1,1)$ and $(1,0)$; this preserves (72.7) and makes the second bit at $a$ zero. If neither exchange applies, (72.8) already holds. The exchanged labels are absent from the constrained images in exactly the coordinates being changed.

For a support $A$ not containing a donor $d$, write $\widehat A^{\,d}=A$ when $|A|$ is even and $\widehat A^{\,d}=A\cup\{d\}$ otherwise. Use the supplied full-path inverse (1.5), with no unstated padding or choice of a different representative:

$$
\begin{aligned}
A_1&=\{j\in J:\gamma_1(\lambda(j))=1\},&
E_1&=\widehat A_1^{\,0},& B_1&=\mathcal B_1(E_1),\\
A_2&=\{j\in J\cap W_2:\gamma_2(\lambda(j))=1\},&
E_2&=\widehat A_2^{\,m},& B_2&=\mathcal B_2(E_2).
\end{aligned}
\tag{72.9}
$$

Since $A_1$ misses $H$, it lies in $W_1$. The excluded donor zero lies strictly after its leading vertex $m$. Thus $E_1$ is even, $B_1$ begins zero, and every record in (72.3), including current tail $k-1$, safely executes it. Its first difference is precisely $\gamma_1\circ\lambda$. The path $W_2$ starts at $a$, contains $H$, and contains excluded donor $m$ strictly after $a$, at position $h+1\le m-1$. Hence $E_2$ is an even physical support. Formula (1.4) for these same two words gives

$$
(B_1)_{m-1}=\gamma_1(\lambda(a)),\qquad
(B_2)_0=\gamma_2(\lambda(a)).
\tag{72.10}
$$

If $B_1$ ends zero, its actual terminal tail is zero, and every next $m$-bit word is safe since $m<k$. If $B_2$ begins zero, it safely clears the actual incoming tail. These cases include any all-one $B_2$ following a terminal zero of $B_1$.

In the remaining case both bits in (72.10) are one. By (72.8) an actual phase of $O$ has code $(1,0)$ and hence is charged by $E_1$. The ambient complement of $W_2$ consists of the $h$ vertices immediately preceding $a$ in the cyclic order: $W_2$ goes from $a$ through $a+m$, leaving $a+m+1,\ldots,a+T-1$. Thus this charged phase occurs within $h$ steps before the endpoint $a$ along $W_1$. The last charged vertex before that endpoint is at least as late, so the actual terminal one-run $\rho(B_1)$ is at most $h$. Also an actual phase of $H$ has code $(0,1)$ and is charged by $E_2$. Every vertex of $H$ is at distance between one and $h$ after $a$ on $W_2$, so the actual leading one-run $\alpha(B_2)$ is at most $h$. Consequently the very same words satisfy the strict physical seam bound

$$
\rho(B_1)+\alpha(B_2)\le2h<m+h=k.
\tag{72.11}
$$

After the first zero of $B_2$, all remaining runs are internal and shorter than $k$. This proves simultaneous safety on both live children, including the case in which neither word offers a zero at their common boundary. No tail-minimizing replacement, extra clearing word or uncharged wait has been used.

Since $\gamma_2=0$ on $Z$, the second difference of $B_2$ is exactly $\gamma_2\circ\lambda$ on all of $J$, including outside $W_2$. Each source returns the unique label with its observed two-bit code. Both first children contain two actual labels and emit the same $B_2$. Thus (72.9) is one literal suffix with exact additional worst fee two, proving this clause of (72.6).

**证明（one three-block suffix for every failing intersection test）。** Suppose $\mathsf K(\lambda)$ fails. Choose any bijection $\gamma:L\to\{0,1\}^2$ whose first bit is zero on $X$. Such a code exists because $|X|\le2$. If its first bit at $\lambda(a)$ is one, orient that first-bit pair so its second bit at $\lambda(a)$ is zero. No condition on the second bit over $Z$ is imposed. Define $A_1,E_1,B_1,A_2,E_2,B_2$ by precisely (72.9) for this code. The first word again starts zero and is safe. If it ends zero, $B_2$ is safe from actual tail zero; if it ends one, the chosen orientation makes $B_2$ begin zero. Thus the same $B_2$ is safe on both live first children.

Each source remembers its own first difference $e$. On second difference one it returns the unique label coded $(e,1)$ and stops. On second difference zero, every remaining phase inside $W_2$ has code $(e,0)$; only phases in $O$ can still have code $(e,1)$. The second-zero children retain their own current values and the actual terminal tail of $B_2$, not a hypothetical cleared tail.

Put $c=3m\pmod T$, and use the later-window geometry supplied by [M72, proof of Theorem 2.1; T72, Interface 1.3]:

$$
O\subseteq W_3\setminus\{c\},\qquad
d_3=\begin{cases}0,&a+m<T,\\m,&a+m\ge T\end{cases}
\ \in\ \{0,m\}\cap(W_3\setminus\{c\}).
\tag{72.12}
$$

Indeed, the complement of $W_2$ is the $h$ vertices immediately after $c$, and $h<m$, giving the first inclusion. If $a+m<T$, then $c=a+m>m$ and $W_3$ wraps through zero. Otherwise $c=a+m-T=m-2h-2<m$ and $W_3$ reaches $m$ strictly after its start. These are full physical paths; restriction to $P$ is made only for candidate phases.

Set

$$
A_3=\{j\in O:\gamma_2(\lambda(j))=1\},\qquad
E_3=\widehat A_3^{\,d_3},\qquad B_3=\mathcal B_3(E_3).
\tag{72.13}
$$

Both the selected support and its excluded donor miss $c$. The inverse is therefore a complete word beginning zero. It clears every actual incoming tail of $B_2$, including tail $m$ when that word was all ones, and its later internal runs are shorter than $k$. This checks every actual $B_2\mid B_3$ seam. On a continuing second-zero child, third difference one returns the label coded $(e,1)$ and zero returns $(e,0)$. Earlier second-one children have already returned their own label. Donors $0,m$ were never candidates in this acquired archive; no stopped child's observation is used.

The stream $B_1\mid B_2\mid B_3$ is fixed for all these children. A zero or uninformative row, when issued, is still one paid complete block at its displayed index. Failure of (72.5), by the all-action lower bound, ensures that at least one actual source requires and emits the third block under any correct controller, including this one. The upper bound is three and the matching adaptive lower bound is three. This proves (72.6). ∎

**定理 72.3（Two binary free-value tables, four joined labels and a full INITIAL consumer）。** Under (72.1)–(72.2), take tables $\lambda_0,\lambda_1:J\to Y$ with exactly two labels each and ordered join

$$
\Lambda(j)=(\lambda_0(j),\lambda_1(j)),\qquad
|\Lambda[J]|=4,\qquad |\Lambda[H]|\le2.
\tag{72.14}
$$

Cross-value label coincidences are unrestricted; the ordered pairs are the labels relevant to the common stream. Choose distinct common root labels $R,C$ fresh from $\lambda_0[J]\cup\lambda_1[J]$, enlarge the label set if necessary, and give initial bottom any independent label $L_\bot$. Define the entire immutable INITIAL target by

$$
f(v,-j,s)=\begin{cases}
R,&h\le s<k,\\
C,&0\le s<h,\ j\in\{0,m\},\\
\lambda_v(j),&0\le s<h,\ j\in J,
\end{cases}
\qquad f(\bot)=L_\bot.
\tag{72.15}
$$

With $\mathsf K(\Lambda)$ defined by (72.5) using the joined images, the exact total original-source fees under either alphabet are

$$
\boxed{C_{\rm ad}(f)=
\begin{cases}
2,&|\Lambda[H]|\le1,\\
3,&|\Lambda[H]|=2,
\end{cases}
\qquad
C_{\rm pre}(f)=
\begin{cases}
3,&\mathsf K(\Lambda),\\
4,&\neg\mathsf K(\Lambda).
\end{cases}}
\tag{72.16}
$$

These total fees include the actual root; the local joined additional fees are two and three. The formula transports the local law to exactly the defined full consumer, not to arbitrary full extensions of $\Lambda$ or its components.

**证明（all roots, the credited binary scopes and every adaptive child）。** Fix either free value and any actual $j\in J$. The jointly realized INITIAL tails zero and $h$ have different labels $\lambda_v(j)$ and fresh $R$. Free stopping is impossible. Every root containing a zero has at most $m-1$ leading ones. Both sources survive to its first zero since $h+(m-1)=k-1<k$, have the same scalar and phase there, and merge their entire records at that zero. The remaining bits are safe, and their complete root endpoints agree. No later literal action, absorption, paid wait or endpoint stop can recover their unequal INITIAL labels. This is the credited first-zero obstruction of [S1, Lemma 4.3], Proposition 4.2 and [M72, Corollary 3.1]. Thus every correct root is $1^m$, separately on both free-value fibres and for a GLOBAL stream.

That forced root rejects exactly the high tails, which all return $R$ at fee one. Its successful positive-difference archive has exactly phases $0,m$, all labelled $C$, and stops at fee one. Its two successful zero-difference archives have exactly (72.3), with tables $\lambda_v$. Initial bottom returns $L_\bot$ freely; an all-one complete-block history of length at least $k$ realizes that separate source. The high, positive and zero archives are full joint-history fibres, and all phases and tails used here have the witness from the proof of Theorem 72.2.

The binary continuation law is supplied by [M72, Theorem 2.1, cut zero], agreeing with the appropriate clauses of Chapter 69: for a nonconstant binary table, its additional price is one when its $H$ image is homogeneous and two otherwise. Its second visibility test is automatic at cut zero. To spell out a legal attainment on the present actual subgroup, orient the homogeneous $H$ label as zero when there is one, and otherwise choose either binary orientation $b_v$. The first row charges exactly $\{j\in J\setminus H:b_v(\lambda_v(j))=1\}$, compensating parity at zero, and is inverted on $W_1$. It starts zero. If $H$ is homogeneous, both responses finish in that one block. Otherwise its one child returns the one-labelled INITIAL value and stops; the zero child follows the row charging exactly $\{j\in H:b_v(\lambda_v(j))=1\}$, with donor $m$ on $W_2$. This second word begins zero, safely clears the actual first-word tail, and finishes its two labels. Its full padding and any uninformative first row are paid. These are the supplied binary constructions, not a new binary theorem.

The remembered free value may select these different adaptive words. Write $d_v=1$ for homogeneous $\lambda_v[H]$ and $d_v=2$ otherwise. Each binary table has two labels on $J$, so its live zero archive cannot stop at the root, and the quoted binary all-action bounds give exact total adaptive fee $1+\max_v d_v$. The two component images are both homogeneous precisely when the join is homogeneous; when $|\Lambda[H]|=2$, at least one component is nonconstant there. This proves the adaptive formula, with all rejection and positive children already stopped.

**证明（the credited value join and one GLOBAL attainment/lower bound）。** Apply exactly Definition 29.1 and Theorem 29.2, including their original all-parameter, all-alphabet and different-stopping-time scopes. Under a fixed literal stream, the phase/tail trajectory and rejection time do not depend on the INITIAL scalar. The actual free value and actual endpoint archive determine the two value-translated successful archives by complementation, with identical issued words and bottom entries. A decoder retains a component when determined and continues the same actual stream until both component decoders stop. Their maximum stopping time remains within a uniform bound valid on both jointly realized free-value fibres. This computes the ordered join without another experiment or borrowed observation. Conversely, the joined label returns the component selected by the remembered free value.

For (72.15) the full joined target has high label $(R,R)$, positive-root label $(C,C)$, zero-root table $\Lambda$, and a separately readable bottom pair. The same root-forcing argument applies. Its only live root archive is exactly Theorem 72.2. For the upper bound, issue the one GLOBAL stream $1^m$ followed by (72.9) when $\mathsf K(\Lambda)$ holds, or by (72.9), (72.13) with the fallback code when it fails. Every original source uses its own consecutive differences, decodes the joined label as proved, and returns its value component. All root, suffix and terminal seams have been checked on these same sources. Stopping may occur earlier for a component; no later observation is then requested on that stopped source.

Conversely, any cheaper GLOBAL controller for $f$ yields, through the supplied value-join decoder on its very same stream, an equally bounded controller for this full joined target. Its forced paid root leaves the exact four-label archive (72.3), contradicting the all-action adaptive lower bound of Theorem 72.2 if its total fee is less than the corresponding value in (72.16). Actual sources attain the required maximal stopping depth. This proves the GLOBAL formula without inferring one stream from the separate binary optima. ∎

**命题 72.4（An infinite count obstruction and lawful attainments）。** For every integer $q\ge1$, take

$$
m=6q,\qquad k=11q-1,\qquad T=11q,\qquad g=q,\qquad
J=q\{1,2,3,4,5,7,8,9,10\},\quad
H=q\{2,3,4,5\},\quad O=q\{8,9,10\}.
\tag{72.17}
$$

For four distinct labels $A,B,C,D$ define two tail-independent tables by the entire following actual phase table:

| $j/q$ | $1$ | $2$ | $3$ | $4$ | $5$ | $7$ | $8$ | $9$ | $10$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $\lambda^+(j)$ | $D$ | $A$ | $A$ | $B$ | $B$ | $D$ | $B$ | $C$ | $C$ |
| $\lambda^-(j)$ | $D$ | $A$ | $A$ | $B$ | $B$ | $D$ | $C$ | $C$ | $D$ |

Both have the same phase sets, exactly four labels on $J$, and image counts $|X|=|Z|=2$. Nevertheless their exact additional adaptive and child-preset fees are respectively two and three. Thus the three counts $(|\lambda[J]|,|\lambda[H]|,|\lambda[O]|)$, even together with these entire physical phase sets and parameters, cannot determine the fee. Their missed-set label intersection is indispensable for this proposed count-only test.

An attaining paid root and shared suffix for $\lambda^+$ is

$$
1^{6q}\ \mid\ 0^q1^{2q}0^q1^{2q}\ \mid\ 1^q0^q1^{4q}.
\tag{72.18}
$$

For $\lambda^-$ it is

$$
1^{6q}\ \mid\ 0^q1^q0^q1^q0^q1^q\ \mid\ 0^{3q}1^q0^{2q}\ \mid\ 0^q1^q0^{4q}.
\tag{72.19}
$$

Encoding $A,B,C,D$ by $00,01,10,11$ and taking the two coordinate tables as $\lambda_0,\lambda_1$ in (72.15) gives full consumers with adaptive fee three in both cases and GLOBAL fees three and four respectively, with fresh common root labels $R_{\rm root},C_{\rm root}$ in the roles $R,C$ of (72.15), and arbitrary independent $L_\bot$.

**证明。** Here $h=5q-1$, $a=q$, and the actual gcd is indeed $q$. The displayed sets follow from the ordered paths $W_1=[6q,12q]\pmod{11q}$ and $W_2=[q,7q]$. The first table has $X=\{A,B\}$ and $Z=\{B,C\}$, whose intersection has size one. The second has the same $X$ and $Z=\{C,D\}$, whose intersection is empty. Theorem 72.2 gives the distinct sharp lower bounds.

In (72.18), the actual first suffix support is $\{q,7q,9q,10q\}$ and the second is $\{q,2q,3q,7q\}$. Both are even full-path supports. Their successive differences give codes $B\mapsto00$, $A\mapsto01$, $C\mapsto10$, $D\mapsto11$. The first suffix begins zero, clears all root survivors, and has terminal run $2q$. The second has leading run $q$, so their actual seam is $3q<11q-1=k$; it has terminal run $4q<k$ and stops at its complete endpoint. Both first children are live and use this same second word. No final clearing block is required.

In (72.19), the three actual suffix supports are $\{q,7q,8q,9q,10q,0\}$, $\{4q,5q\}$ and $\{8q,9q\}$. The excluded zero in the first row is parity compensation. Their physical inverses are exactly the displayed words. The first suffix begins zero and ends with run $q$; the second and third begin zero and end zero, so both actual later seams are safe. First difference zero contains $A,B$, and first difference one contains $C,D$. Second difference one returns $B$ on the child whose first difference was zero; its other live first child has second difference zero because $C,D$ lie in $O$ or have second charge zero. On the continuing second-zero archives, the third difference selects $C$ versus $D$, while the archive whose first difference was zero returns $A$. Every occurrence of $C,D$ in $O$ actually pays the third suffix block. These rules use their remembered first difference and their own later endpoints, and never another child's output. The root-positive and rejecting archives of the full consumers already stop with their fresh common labels. Formula (72.16) gives the stated full fees because the joined $H$ image has two labels. Generalized-CRT histories supply every successful phase/tail and both free values in the family, including every $q\ge2$ with nontrivial gcd. ∎

**数学引文 72.5（Exact overlap and the substantive increment）。** The canonical source, the [mixed-tail companion][M72] and the [three-class companion][T72] are mathematical inputs at [revision 55a96a032f24c8dd1670674e6537bd5f5698e552](https://github.com/the-omega-institute/trureturing/tree/55a96a032f24c8dd1670674e6537bd5f5698e552/docs/develop/theory). The precise reused contributions are Chapter 1's experiment, joint histories and literal inverse; Propositions 4.2–4.4 and Chapter 5's forced-root/one-block clauses; Theorem 29.2's exact preset value join; Chapter 69's stated binary slices; [M72, Definitions 1.1–1.3, Theorem 2.1 at cut zero and Corollary 3.1]'s actual-gcd binary fees, later-window geometry and fresh-label forcing; and [T72, Interface 1.3 and Theorem 2.1]'s three-class prices and stopped-label seam mechanism. Their original hypotheses remain attached. For Chapters 4–5, take their threshold parameter $r=h+1$, their leading-cut parameter zero, and equal endpoint labels $C$; their sets $H,Z,F$ then correspond respectively to the present $\{0,m\},J,H$. The present $a=2m-T$ is a physical path endpoint, not that leading-cut parameter. For M72 use $F(j,s)=\lambda(j)$ and cut zero. In particular T72's theorem assumes exactly three labels and a homogeneous $H$, whereas M72's priced lower table has at most two labels. Neither can be instantiated as a four-label two-live-child price theorem. The four-label code count alone supplies no physical seam.

The underlying suppliers retain their linked immutable pins: [S1, Convention 1.3, Lemmas 4.2–4.3 and Theorem 5.2] supplies actual histories and irreversible INITIAL losses; [S2, Theorem 14.1] supplies the matched coefficient cycle; [S10, Interface 2.1 and Lemma 3.2] supplies same-word charges and common-tail binary restrictions; [S15, Section 1, Definition 1.1 and Proposition 4.2] supplies path inversion, strict seam semantics and the distinction between independent children and GLOBAL compatibility. Its coprime central pricing theorems are not transported to noncoprime parameters. [S13, Definitions 8.1/8.3 and Theorem 8.4] supplies the existing safe terminal-cut criterion after a recorded zero. At the second word here its actual supports are the two first-response children, displacement $2m$ and incoming tail $\rho(B_1)$; applying that certificate separately does not establish one shared word or the intersection law.

The added reader-specific ordinary deduction is (72.6): the all-action four-label intersection obstruction, the shared two-block construction with the charged-vertex run bound (72.11), and the sharp common three-block fallback. The consumer and symbolic supplier instantiations expose this law on full original sources and are not separate new-content claims. This is a repo-derived deduction; no exhaustive literature-absence or priority claim is made. Van den Bos and Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3](https://arxiv.org/html/1907.11034v2), supplies the mature comparison of completed observations, compatible experiments and destructive first actions. A whole literal block is one input here and its complete endpoint is one output; unequal immutable INITIAL labels require separation. That paper supplies no matched KBonacci window, parity donor, strict run bound or fee formula for this class.

**边界 72.6（Effectivity, resource limits and the original objective）。** For arbitrary $Y$, (72.6) and (72.16) are semantic minimum statements. A finite target-partition presentation or decidable equality on the finite label tables makes the constructions effective: form the actual subgroup and missed sets, identify at most four labels, test (72.5), choose a code among the 24 bijections with the displayed orientation/exchange rule, then invert at most three physical rows. With unit-cost label comparison, scanning the supplied tables and physical rows takes $O(T)$ comparisons and coordinates. Integer arithmetic, label-equality implementation, input encoding, offline acquisition and controller representation costs are separate; this is not a bit-complexity assertion for those resources. The controller remembers its own free value and at most three additional endpoint differences. An arbitrary history expression still requires its factorization through the INITIAL record; no general effective factorization procedure is asserted.

All constants in the finite emitted-block bounds are uniform over the stated class, including noncoprime gcds and empty missed sets when the class is nonempty. They concern paid complete blocks, not physical bits: the families (72.18)–(72.19) emit three and four total blocks respectively at their worst source, hence $18q$ and $24q$ physical bits. Letting $q$ grow does not give one fixed-width controller for an infinite source union, exchange a finite observation bound with an infinite limit, or resolve unrestricted infinite-horizon acquisition. The symbolic witnesses and proofs, rather than a finite sample, establish the family for every integer $q\ge1$.

The local theorem keeps exactly the already paid root-zero archive (72.3), tail-independent exactly four labels, $|\lambda[H]|\le2$, the actual gcd group, and (72.1). The full formula additionally keeps exactly two labels per free-value table, four joined labels, the stated joined-$H$ condition, fresh common root labels and the entire extension (72.15). An arbitrary full extension can have differently labelled rejection or positive siblings, competing roots or incompatible live archives, and its total fee is not inferred from this local result. Tail-dependent richer tables, four-label tables with more than two labels on $H$, other supports/calendars, other full extensions and other parameter regimes are outside this increment. No heterogeneous three-label classification is needed for its proofs. Definition 1.3 and Open Problem 9.1 retain the original exact objective for every arbitrary attainable immutable INITIAL target, all original $k\ge2,m\ge1$, and both original alphabets, separately for adaptive control and one GLOBAL preset stream. All earlier restricted results retain their own scopes; this ordinary theory increment is not a Lean/kernel certification or a resolution of that full objective.

[M72]: KBONACCI_MIXED_TAIL_ROOT_ZERO_CUT_PRICE.md
[T72]: KBONACCI_THREE_CLASS_ROOT_ZERO_COMPATIBILITY_PRICE.md

[IC72]: KBONACCI_INITIAL_TARGET_COST_THEORY.md
[S1]: https://raw.githubusercontent.com/the-omega-institute/trureturing/f64d9e5dc37301e04ffc33332c919dd56a81ed6f/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md
[S2]: https://raw.githubusercontent.com/the-omega-institute/trureturing/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md
[S10]: https://raw.githubusercontent.com/the-omega-institute/trureturing/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md
[S13]: https://raw.githubusercontent.com/the-omega-institute/trureturing/6850a89acdb12d4f17af57dacee2d67e0b514be4/docs/develop/theory/KBONACCI_MULTILABEL_PREFIX_AND_TERMINAL_COST.md
[S15]: https://raw.githubusercontent.com/the-omega-institute/trureturing/3541b57c0d31a89f11fb8b86c75b7b1555e49e6f/docs/develop/theory/KBONACCI_JOINT_RESPONSE_AND_SEAM_COST.md

## 追加锚（本行以下为增补区）

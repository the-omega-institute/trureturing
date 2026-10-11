# KBonacci mixed-tail root-zero cut prices

This companion supplies one restricted continuation law and its whole INITIAL consumer. The canonical [INITIAL cost volume][IC], Chapters 1, 4–5, 68–69, supplies the experiment and the previously priced slices. Its original objective remains the exact minimum worst-branch number of actually emitted complete blocks for every attainable immutable INITIAL target and every original $k\ge2,m\ge1$, separately for adaptive control and one GLOBAL preset stream.

The text is ordinary mathematical reference input, without Lean/kernel verification. It uses the `generic-v1` claim convention. Published content is append-only; additions belong after the final addition anchor. Authorship and ordinary finite checks are by one delegated codex-cli author using `formal-thinking-and-answer` and `theory-volume-template` within pure-theory authorization. No independent review or independent-prior claim accompanies this companion.

## 1. Actual root-zero sources and eligible INITIAL cuts

**约定 1.1（Inherited original experiment）。** Use exactly [IC, Definitions 1.1–1.3]: the original KBonacci integer weights and matched $V_k\bmod2$ reader, $T=k+1$, actual endpoint phases $P=g\mathbb Z/T\mathbb Z$ with $g=\gcd(m,T)$, all jointly attainable complete-history sources, immutable INITIAL record labels, free initial value or independent absorbing bottom, and observations only at complete endpoints. Every issued complete block is charged, including waits, padding and blocks whose rejection occurs before the observed endpoint. Controls have no reset, copy, hidden initial clock, intermediate read or another branch's observations. Both original control alphabets are retained. Assume throughout

$$
3\le m<k\le2m-2,\qquad h=k-m\in[1,m-2],\qquad a=2m-T=m-h-1\ge1.
\tag{1.1}
$$

There is no coprimality hypothesis. Since $m<k$, the two alphabets both contain every $m$-bit word, with actual cross-block rejection still enforced. Let $W_t=[tm,(t+1)m]\pmod T$ retain its physical path order, and use the even full-path charge inverse $\mathcal B_t$ from [IC, Interface 1.4]. Compensation at an excluded or nonactual vertex is a literal bit prescription, not an extra source or observation.

**定义 1.2（One actually acquired mixed-tail archive）。** Fix a remembered free INITIAL value $v$, actually emit $1^m$ at issued index zero, and condition on successful difference zero. Put $J=P\setminus\{0,m\}$. The INITIAL candidates are exactly $(v,-j,s)$ for $j\in J$, $0\le s<h$, and their current records are $(v,-j+m,m+s)$. They share this very root archive. Write their original labels as $F(j,s)$, imposing no labels elsewhere. The support $J$ is nonempty: $T=m+h+1<2m$ implies $g<m$ and $T/g\ge3$.

Let $D_{\rm ad}(F)$ be the minimum additional worst emitted-block fee on this archive. Let $D_{\rm child\text{-}pre}(F)$ additionally require one literal suffix for this archive, with stopping and decoding from each source's own endpoints. The already emitted root costs one separately. Uniform finite nonexistence means $+\infty$.

For $0\le r<h$, call $r$ eligible when $F$ is constant on the common band $J\times[h-r,h)$ and is separately constant on each surviving fibre $\{j\}\times[0,h-r)$. Write the latter label as $\lambda(j)$. When $r>0$, denote the common upper label by $M$; it may coincide with either lower label. At $r=0$ the upper band is empty and has no label obligation. The priced class consists of constant $F$, every $F$ without an eligible cut, and every nonconstant $F$ whose eligible cut has $|\lambda[J]|\le2$. In particular every binary $F$ belongs to this class, as does every eligible binary lower table with any common upper label in any label set.

**定义 1.3（Two physical visibility tests）。** For an eligible $r$ put

$$
\begin{aligned}
H&=J\setminus W_1=P\cap\{a+1,\ldots,m-1\},\\
I_r&=P\cap\{m+1,\ldots,m+r-1\},\\
K_r&=\begin{cases}P\cap\{m+r\},&r>0,\\\varnothing,&r=0,\end{cases}\\
O&=J\setminus W_2.
\end{aligned}
\tag{1.2}
$$

Empty intervals and empty-set constancy have their usual meanings. The sets $I_r,K_r$ are subsets of $J\cap W_1$. A binary orientation is a bijection $\eta:\lambda[J]\to\{0,1\}$ when the lower table has exactly two labels; write $e=\eta\circ\lambda$.

The test $\mathsf A_1$ holds if $\lambda$ is constant on $J$, or if such an orientation satisfies

$$
e=0\text{ on }H\cup I_r,\qquad e=1\text{ on }K_r.
\tag{1.3}
$$

The test $\mathsf A_2$ holds if $\lambda$ is constant on $O$, or if an orientation satisfies

$$
e=0\text{ on }O\cap I_r,\qquad e=1\text{ on }O\cap K_r.
\tag{1.4}
$$

When $O$ is empty, $\mathsf A_2$ holds. The orientations in the two tests are separate existential choices. These tests concern the actual subgroup only; a full physical row is nevertheless inverted on the entire path.

## 2. The exact restricted cut-price law

**定理 2.1（Mixed-tail root-zero prices, every actual gcd）。** On Definition 1.2's actually acquired archive, under (1.1) and both original alphabets, a constant $F$ has $D_{\rm ad}=D_{\rm child\text{-}pre}=0$. A nonconstant $F$ has at most one eligible cut. If there is none, both prices are infinite by the credited first-zero obstruction. If that unique cut has $|\lambda[J]|\le2$, then

$$
\boxed{D_{\rm ad}(F)=D_{\rm child\text{-}pre}(F)=
\begin{cases}
1,&\mathsf A_1,\\
2,&\neg\mathsf A_1\text{ and }\mathsf A_2,\\
3,&\neg\mathsf A_1\text{ and }\neg\mathsf A_2.
\end{cases}}
\tag{2.1}
$$

Every finite correct continuation of nonconstant $F$ has its first zero exactly after that eligible number $r$ of leading ones in its first additional word. The attainments below are single literal suffixes simultaneously safe on both successful difference children of that word. The common upper label $M$ is arbitrary, including all coincidences with lower labels. No price for an eligible lower table with more than two labels is asserted.

**证明（actual arrival and credited irreversible cut）。** The matched coefficient cycle is [S2, Theorem 14.1]. The joint witness is [S1, Convention 1.3; S15, Section 1], equivalently [IC, (1.3)]: for every $(v,-j,s)$ choose a complete-history length $\ell\equiv0\pmod m$, $\ell\equiv-j\pmod T$, $\ell\ge s+2$, and the separated first bit compensating the terminal $1^s$ contribution. Generalized CRT applies because $g\mid j$. This one legal history simultaneously realizes value, phase and tail; its unobserved length is no extra input. Appending the same actual root $1^m$ succeeds exactly for $s<h$, leaves tail $m+s$, and has successful charge support $\{0,m\}$. It therefore gives exactly Definition 1.2's candidates, including all tails at every actual $j$.

A nonconstant acquired archive cannot stop. The only zero-free next word is $1^m$; because $k<2m$, it rejects every candidate into the same absorbing archive. A first zero after $r\ge h$ leading ones likewise rejects them all. For $0\le r<h$, [S1, Lemma 4.3 and Theorem 5.2; S15, Definition 4.1] gives exactly the rejected INITIAL band $J\times[h-r,h)$, whose labels must all agree, and merges all surviving INITIAL tails separately at each phase. Their labels must agree on each lower fibre. Remaining bits cannot reject a survivor, since a zero has separated every run and $m<k$. These are precisely the eligible-cut conditions. This exhausts every next action, not only optimal first words; later adaptive choices cannot restore a merged distinction. Absence of a cut thus means infinite fee at every horizon, not failure of a bounded search.

For uniqueness, suppose $r<t<h$ are eligible. The nonempty tail interval $[h-t,h-r)$ is in every lower fibre for $r$ and in the common upper band for $t$. Consequently all lower labels for $r$ equal the latter upper label. If $r>0$, its upper band is contained in the upper band for $t$, so its label is the same too. If $r=0$, its lower band is the entire domain. Either case makes $F$ constant, a contradiction. This uniqueness and nonexistence argument is the same credited first-zero mechanism as [IC, Theorem 68.2], now instantiated on $J$.

**证明（the physically forced row and one-block necessity）。** Write $q$ for the successful charge of the first additional word at index one. Its first zero is at $r$. The path starts at $m$. For $r>0$ its ambient charges are $q(m)=1$, $q(m+i)=0$ for $1\le i<r$, and $q(m+r)=1$; for $r=0$ it has $q(m)=0$. All charges outside $W_1$ are zero. Thus on $J$ it forces zero on $H\cup I_r$ and one on $K_r$. These are the prefix charges of [IC, Proposition 4.4], with its threshold parameter $h+1$ and leading cut $r$.

If $\lambda$ has one label, every successful endpoint can return it, while bottom returns $M$ when the upper band is nonempty. One additional word therefore suffices. Otherwise a one-block completion must give different successful endpoint differences to the two lower labels. This is exactly an orientation satisfying (1.3). The rejected band is a separate endpoint archive even when $M$ equals a successful label. This proves the necessity of $\mathsf A_1$ without any label-freshness assumption.

**证明（one-block literal sufficiency）。** A constant lower table uses $1^r0^{m-r}$. For a two-label table satisfying (1.3), keep the preceding ambient prefix charges, prescribe $q(j)=e(j)$ on $J\cap W_1$, and set every other free charge to zero except at phase zero. Choose that last charge to make the whole path even and use the supplied inverse $\mathcal B_1(q)$. Phase zero is the path vertex at position $h+1>r$, so compensation changes neither the prefix nor its first zero. All prescriptions agree by (1.3). Outside $W_1$ the zero-response label is the required common label on $H$.

Every lower source has $s\le h-r-1$, so its incoming tail obeys $m+s+r\le k-1$. It reaches that first zero safely. Exactly the upper band rejects before the zero; its complete endpoint returns $M$. No later run rejects a survivor, and no cleanup after the final endpoint is necessary. A successful difference $e$ returns its oriented INITIAL label. At least one further complete block is necessary for nonconstant $F$, so this attainment proves the fee-one clause. This clause is overlap with [IC, Chapters 4–5], not new one-block mathematics.

**证明（all-action two-block lower bound）。** The next ordered path $W_2$ starts at $a$. It contains $H$, because every vertex from $a+1$ through $m-1$ is within its first $m$ steps. Hence $O\cap H=\varnothing$, and every vertex of $O$ lies in $W_1$. Any first word with the necessary prefix therefore has on $O$ only the fixed constraints zero on $O\cap I_r$ and one on $O\cap K_r$.

After that first word, surviving lower sources have the common current tail $\rho(B_1)$, and its difference $q(j)$ specifies their child archive. Within each such archive, a second word either succeeds on all candidates or rejects them all, by [S10, Lemma 3.2; S15, Definition 1.1]. All-rejection cannot finish a live child. Every successful second word has charge zero outside $W_2$, so the subset $O\cap q^{-1}(e)$ must be homogeneous for each $e$. If $\lambda$ is nonconstant on $O$, these two subsets must be its two label classes: $q|_O$ is a binary orientation of $\lambda|_O$. Its fixed prefix constraints then give (1.4). If $\lambda$ is constant on $O$, there is no obstruction there. Thus every adaptive completion in at most two additional blocks requires $\mathsf A_2$. This includes early stops, arbitrary second words, attempted rejection and branch-dependent actions. Failure of $\mathsf A_2$ rules out fee two for adaptive and preset controllers alike.

**证明（one two-block suffix, with a paid zero-tail arrival）。** Suppose $\mathsf A_2$ holds and $\mathsf A_1$ fails. If $O$ is nonconstant, select the admitted orientation and prescribe $q(j)=e(j)$ there. If $O$ is homogeneous, assign zero to its free coordinates, retaining its forced prefix coordinates. Keep the ambient prefix charges, assign zero to all other free coordinates, including the final path vertex $a$, and compensate even parity at phase zero. The inverse supplies $B_1$ with the necessary first zero $r$ and final bit zero. The prescribed sets are disjoint from $a$, so this terminal zero is achieved by the very same word. The preceding seam proof applies, and every survivor now has actual current tail zero.

For each response $e\in\{0,1\}$ let $L_e$ be the label of $O\cap q^{-1}(e)$ when nonempty; homogeneity follows from the choice of $q$. When that set is empty, choose either of the two lower labels. On $J\cap W_2$ prescribe

$$
q_2(j)=\mathbf1_{\{\lambda(j)\ne L_{q(j)}\}}.
\tag{2.2}
$$

Set other free charges zero and compensate full-path parity at the excluded phase $m$. This phase lies at path position $m-a=h+1\le m-1$, so it is available in $W_2$. The inverse gives one actual $B_2$, shared by both response children. From the already attained tail zero every $m$-bit word is strictly safe since $m<k$, including a possible all-one inverse. No favourable incoming tail is presumed.

A source with first response $e$ and second response zero returns $L_e$; second response one returns the other lower label. Outside $W_2$, the zero response has the prescribed homogeneous label in each child. The upper band stopped with $M$ after $B_1$. Homogeneous successful children may also stop there, without emitting $B_2$. These are prefixes of the same fixed suffix $B_1\mid B_2$; no separately optimized words have been combined. Failure of $\mathsf A_1$ forces some actual source to emit both blocks. The two-block clause of (2.1) follows.

**证明（a safe three-block suffix for every remaining binary lower table）。** Suppose both tests fail. Use the ambient prefix row, set all other free first-row charges to zero, including $a$, and compensate at phase zero. Its inverse $B_1$ again ends zero and safely rejects exactly the common upper band. Choose either binary orientation $e=\eta\circ\lambda$. On $J\cap W_2$ prescribe $q_2=e$, set other free charges zero, and compensate at $m$. Its inverse $B_2$ is safe from the actual tail zero. Every source with second difference one has the same lower label $\eta^{-1}(1)$ and stops, regardless of its first difference. Among sources with second difference zero, those inside $W_2$ have label $\eta^{-1}(0)$; only $O$ can still contain the other label.

Let $c=3m\pmod T$, the endpoint of $W_2$ and the start of $W_3$. The ambient complement of $W_2$ has $h$ consecutive vertices immediately after $c$, and $h<m$, so $O\subset W_3\setminus\{c\}$. There is an excluded donor $d\in\{0,m\}\cap(W_3\setminus\{c\})$: if $a+m<T$, then $c=a+m>m$, and $W_3$ wraps through zero; choose $d=0$. If $a+m\ge T$, then $c=a+m-T=m-2h-2<m$, and $W_3$ reaches $m$ strictly after its start; choose $d=m$.

Give charge one to exactly $\{j\in O:e(j)=1\}$, compensate its parity at $d$, and set all other charges zero. Its inverse $B_3$ begins zero because neither the selected support nor its donor contains $c$. This clears every surviving tail of $B_2$, including a tail $m$ after a safe all-one $B_2$; the remaining runs are shorter than $k$. On continuing second-zero archives, third difference one returns $\eta^{-1}(1)$, and zero returns $\eta^{-1}(0)$. Any additionally charged excluded phase was never a candidate in this archive. Thus $B_1\mid B_2\mid B_3$ is one safe literal suffix on all continuing children. Every wait and padding bit is part of its emitted complete-block fee. The two-block lower bound forces an actual source to emit all three blocks. This proves the last clause and equality of adaptive and child-preset prices. ∎

## 3. A full immutable INITIAL consumer and an infinite fee-four family

**推论 3.1（Identical tables on both free-value fibres, one GLOBAL stream）。** Let $F:J\times[0,h)\to Y$ be in Theorem 2.1's priced class. Enlarge its labels by two distinct fresh labels $R,C\notin F[J\times[0,h)]$, and give initial bottom any independent label $L_\bot$. On the entire original INITIAL record space put

$$
f^F(v,-j,s)=\begin{cases}
R,&h\le s<k,\\
C,&0\le s<h,\ j\in\{0,m\},\\
F(j,s),&0\le s<h,\ j\in J,
\end{cases}
\qquad f^F(\bot)=L_\bot,
\tag{3.1}
$$

using exactly the same $F$ for both $v\in\mathbb F_2$. If $D(F)$ denotes Theorem 2.1's additional price, including infinity, then under both original alphabets

$$
\boxed{C_{\rm ad}(f^F)=C_{\rm pre}(f^F)=1+D(F).}
\tag{3.2}
$$

**证明。** Choose any actual $j\in J$. At either free value the INITIAL tails zero and $h$ have unequal labels $F(j,0)$ and fresh $R$. Free stopping is impossible. Every zero-containing root has a leading run $b\le m-1$; both tails survive to its first zero since $h+b\le k-1$, and the credited first-zero principle merges their whole records and archives. No later action can return their unequal INITIAL labels. Hence every correct root on each value fibre is $1^m$, including for a GLOBAL stream.

That root rejects precisely the high tails and returns $R$ at fee one. Its positive-success archive has only the label $C$ and stops there. Its zero-success archive is exactly Definition 1.2 with $F$. Initial bottom stops freely. Theorem 2.1 supplies the all-action lower bound on this actual live archive, including infinite nonexistence. For a constant $F$, every root archive is homogeneous, so the fee is one. Otherwise follow the root by the single literal suffix constructed there. Both free values use the same words and their own remembered baseline and consecutive endpoint differences; the root and positive siblings impose no suffix constraint after they stop. At least one actual zero-success source pays the necessary additional $D$ blocks. Thus this is genuinely one GLOBAL stream with worst actual emitted fee $1+D$, not a maximum of incompatible child optima. ∎

**例 3.2（A symbolic infinite family with full fee four）。** For every $m\ge6$ put $k=2m-2$, $h=m-2$, $T=2m-1$, and $r=m-3$. The actual gcd is one. Choose distinct $A,B$ and any common upper label $M$, which may equal $A$, $B$ or neither. On the root-zero rows put

$$
F(j,s)=\begin{cases}
M,&1\le s<h,\\
B,&s=0,\ j=2m-2,\\
A,&s=0,\ j\in J\setminus\{2m-2\}.
\end{cases}
\tag{3.3}
$$

The cut $r$ is eligible and unique. Here $a=1$, $H=\{2,\ldots,m-1\}$, $O=\{m+2,\ldots,2m-2\}$, $O\cap I_r=\{m+2,\ldots,2m-4\}$, and $K_r=\{2m-3\}$. All of $H$ and $K_r$ have label $A$, so $\mathsf A_1$ fails. The set $O$ contains both labels; the nonempty fixed-zero set $O\cap I_r$ and the fixed-one turn $K_r$ both have label $A$, so $\mathsf A_2$ fails too. Therefore $D=3$, and the full consumer (3.1) has both fees four.

One explicit attaining GLOBAL stream is

$$
1^m\ \mid\ 1^{m-3}0^3\ \mid\ 0^m\ \mid\ 0^{m-3}1\,0^2.
\tag{3.4}
$$

Its second word rejects exactly the original tails $1\le s<h$ into $M$ and leaves the lower tail-zero sources at actual tail zero. Its third word is a paid, uninformative calendar wait. At issued index three the final isolated one has physical support $\{2m-2,0\}$; excluded phase zero supplies compensation on this root-zero archive. It distinguishes exactly the label-$B$ lower source. Root-reject and root-positive sources already stopped with $R,C$. Theorem 2.1's adaptive lower bound excludes all cheaper roots and suffixes through the root-forcing consumer proof. Thus the fee-four claim survives upper-label coincidences. This family is a consumption of the cut law, not a separate novelty claim.

## 4. Exact reuse, finite corroboration and unresolved obligations

**数学引文 4.1（Source identities and the reused/new boundary）。** The canonical [IC] is acquired at commit `3d078b09f0fc917963a7332cff26b15c6bf514cd`, with 540,198 bytes and SHA256 `49d8798fe62eae94f66efe5d5d05e263611faec2b88b59cd5fe58b67befcd84b`. The necessary named suppliers are pinned as follows; SHA256 refers to the acquired source bytes.

| Supplier | Precise contribution and source SHA256 |
| --- | --- |
| [S1], Convention 1.3, Lemmas 4.2–4.3, Theorem 5.2 | Whole joint histories, actual all-one archives, irreversible INITIAL first-zero constancy and no-cut nonexistence; `97791e0a4806b27403f6b1faefc43ed75190ead6a076a78a2674ee9b0d650685`. |
| [S2], Theorem 14.1 | Original matched coefficient cycle, without changing the reader; `34f3cd82265aab2b3a2e08cc0aa3526d469bd8c198d11a17027bcc18faa81a3e`. |
| [S10], Interface 2.1 and Lemma 3.2 | Same-word physical charge realization and common-tail all-success/all-rejection semantics; `3f09e24654eeed8aaeaca9231a733c24a4a941b421a38706fd6f71da2f9af0b7`. |
| [S15], Section 1, Definitions 1.1, 2.1, 4.1 and Proposition 4.2 | Ordered path inverse, strict seam, actual zero arrival and separation of adaptive children from GLOBAL compatibility; `8708dee18daff629f49c5bf077afe3af244d8425d8856a72dac5965bc49e0c7f`. Its coprime central fee theorems are not invoked for noncoprime parameters. |
| [S13], Definitions 8.1, 8.3 and Theorem 8.4 | Existing general one-block safe-cut certificate after a recorded zero; `b9d746f4439629f48185bb2e3a38d5c511a9f93b3faa6ba02b6349d54a66e2cf`. It is credited overlap, not a pricing theorem for the unzeroed mixed-tail arrival. |

The constant and impossible clauses, eligible-cut mechanism, joint history construction, original response inverse and one-block criterion are reused content. With an eligible nonconstant lower table, (1.3) is the root-zero specialization of [IC, Propositions 4.3–4.4 and Theorem 5.1], including every gcd. With $r=0,g=1$, the fee-one/two law is [IC, Theorem 69.2]. Its two-window construction and full fee-three consumer are credited overlap. With a constant lower table, distinguishing its common label from a nonempty common upper band is the same one-block tail-threshold use, even when the upper label coincides in other cases.

The added connection is the exhaustive two-block condition (1.4) under a necessarily fixed mixed-tail cut, its simultaneous zero-tail-ending first-word realization, and the sharp three-block fallback on the actual second-window complement for every gcd. The failure of (1.4) is an all-action adaptive lower bound, and the construction proves equality with one child-preset suffix. The whole consumer and fee-four family expose this law on full original INITIAL sources. These are `repo-derived` ordinary deductions; renamed instances, supplier bindings and the consumer are not counted as separate new mathematics. No priority or exhaustive literature-absence claim is made.

Van den Bos and Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2, Definitions 8–11 and Figure 3](https://arxiv.org/html/1907.11034v2), is the inspected primary comparison. Completed observations, compatible test inputs and irreversible first-action identification loss are `literature-attested`. The comparison identifies a whole literal block with one input and its completed endpoint with one output, and separates unequal INITIAL labels rather than requiring full state identification. That paper supplies no physical window, parity donor, seam or KBonacci fee formula. Its generic distinguishing-graph machinery is not delivered as new content here.

**核验 4.2（Finite checks and their scope）。** Independent finite checks execute the original bit transitions and group only complete endpoint archives. They enumerate every binary $F$ on the entire root-zero candidate rectangle for $(m,k)=(3,4),(4,5),(4,6)$, including constants and no-cut tables. For eligible examples the checks exhaust every first and second literal word in both adaptive and shared-suffix arrangements, compare the exact depth-zero/one/two minima with (2.1), and execute the constructed shortest suffix and the complete consumer on both free values. No-cut examples are checked for an irreversible unequal-label collision after every first word. The source-history check separately constructs the original integer weights and verifies whole CRT histories, values, phases, tails and complete-block lengths. These finite checks corroborate ordinary proofs; they neither establish an infinite universal assertion by enumeration nor certify a Lean theorem.

The binary-rectangle check covers 1,034 tables: six constant, 38 of price one, 60 of price two, and 930 with no eligible cut and an unequal-label merger under every first action. Additional eligible presentations enumerate every binary lower phase table at every cut, with an empty upper band at cut zero and each of the two lower symbols or a third symbol as upper label otherwise: 56 presentations at $(m,k)=(6,9)$ and 5,120 at $(6,10)$. Their respective price counts $(0,1,2,3)$ are $(6,44,6,0)$ and $(8,242,4486,384)$. These are presentation counts, not distinct-target counts. Every presentation has its attaining stream and full consumer checked; every cut-zero or distinct-upper presentation additionally has its first/second-word minimum exhausted. The separate original-weight/CRT check verifies 926 jointly realized successful records over $(3,4),(4,5),(4,6),(6,9),(6,10),(12,21)$, with absorbing-bottom witnesses as well. The check result is `ALL_CUT_PRICE_CHECKS_PASSED`; no check program or runtime data is delivered.

The smallest fee-two boundary is $m=4,k=6,r=0$, with lower label $B$ only at phase two and $A$ elsewhere: the full stream is $1111\mid0000\mid0110$. At $m=3$ only $k=4,h=1,r=0$ is allowed, and its missed arc has one phase, so $\mathsf A_1$ always holds for a binary table. The smallest fee-three boundary is $m=6,k=10,r=3$, with lower label $B$ only at phase ten: the full stream is $111111\mid111000\mid000000\mid000100$. For $m\le5$, every allowed $r$ has $O\cap I_r=\varnothing$; at most one actual turn can prescribe one on $O$, so some orientation always satisfies $\mathsf A_2$. For $m=6,k=7,8,9$, $O$ is empty. These observations justify the stated smallest boundaries, rather than extrapolating their occurrence from a sampled table. A noncoprime three-block check uses $m=12,k=21,g=2,r=8$, lower label $B$ only at phase 18 and $A$ elsewhere; $O=\{16,18,20\}$ has both labels at its forced-zero vertices 16 and 18. Its full attaining stream is $1^{12}\mid1^80^4\mid0^{12}\mid0^41^40^4$. The common upper label is independently checked coincident with either lower label and distinct from both.

**边界 4.3（Completed and remaining obligations）。** Theorem 2.1 supplies complete ordinary proofs, actual original-reader arrival, every-action lower bounds, actual gcd geometry and simultaneously safe literal attainment for exactly its priced class. Corollary 3.1 proves the full consumer's adaptive and one-GLOBAL-stream fee, including infinity, and Example 3.2 gives a symbolic infinite full fee-four family. For arbitrary label sets these are semantic existence and minimum statements. Effective acquisition requires a finite target-partition presentation or decidable label equality to test cuts, orientations and homogeneity; controller words and decoding can then be selected by the displayed finite constructions. The fee does not charge offline comparison or search time. An unspecified history target still requires its INITIAL-record factorization.

Eligible lower tables with more than two labels, arbitrary other acquired supports, different live tables on the two free-value fibres, and arbitrary live root-positive siblings are not priced by this companion. The full fee formula applies to exactly (3.1); the price of an arbitrary full extension of the same local $F$ need not equal it. The excluded parameter regions and the original all-target, all-$k,m$ adaptive/GLOBAL objective remain unresolved here. No Lean compilation, ingestion, coverage, deposit, freeze, axiom report or CI certification is claimed.

[IC]: https://github.com/the-omega-institute/trureturing/blob/3d078b09f0fc917963a7332cff26b15c6bf514cd/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md
[S1]: https://raw.githubusercontent.com/the-omega-institute/trureturing/f64d9e5dc37301e04ffc33332c919dd56a81ed6f/docs/develop/theory/KBONACCI_IRREVERSIBLE_TARGET_ACQUISITION.md
[S2]: https://raw.githubusercontent.com/the-omega-institute/trureturing/73168b5b84a8ba1328b6fa51eb9d722f3d4a7daa/docs/develop/theory/KBONACCI_MINIMAL_MODULAR_OBSERVER.md
[S10]: https://raw.githubusercontent.com/the-omega-institute/trureturing/84c05a76262b9b8c1a491c02afdee34e60535e9b/docs/develop/theory/KBONACCI_NARROW_QUERY_WINDOW_COST.md
[S13]: https://raw.githubusercontent.com/the-omega-institute/trureturing/6850a89acdb12d4f17af57dacee2d67e0b514be4/docs/develop/theory/KBONACCI_MULTILABEL_PREFIX_AND_TERMINAL_COST.md
[S15]: https://raw.githubusercontent.com/the-omega-institute/trureturing/3541b57c0d31a89f11fb8b86c75b7b1555e49e6f/docs/develop/theory/KBONACCI_JOINT_RESPONSE_AND_SEAM_COST.md

## 追加锚（本行以下为增补区）

## 5. The exact stationary control memory of the five-label fee-four family

The consumer is exactly Example 3.2 extended by Corollary 3.1, with five pairwise distinct labels and initial bottom labelled $R$. The paid four-block fee is reused. The additional resource here is the complete stationary controller of [Continuation II, Definitions 26.1–26.2 and Theorem 27.2][CM]: its program positions, remembered endpoint values and stopping outputs are counted together. A proof's issued index or hidden apparatus coordinate is not an input to that controller.

**定义 5.1（The counted INITIAL contract）。** Fix $m\ge6$, $k=2m-2$, $T=2m-1$, $h=m-2$, and $r=m-3$. All residues below are modulo $T$. Since $\gcd(m,T)=1$, the source set is

$$
Q=\{\bot\}\sqcup\{(v,-j,s):v\in\mathbb F_2,\ j\in\mathbb Z/T\mathbb Z,\ 0\le s<k\}.
$$

Each successful record is a jointly realizable INITIAL source by [the canonical joint-history construction, (1.3)][IF]. Choose pairwise distinct $A,B,M,R,C$, put $j_B=2m-2$ and $J=(\mathbb Z/T\mathbb Z)\setminus\{0,m\}$, and fix the immutable target

$$
f(v,-j,s)=
\begin{cases}
R,&s\ge h,\\
C,&s<h,\ j\in\{0,m\},\\
M,&1\le s<h,\ j\in J,\\
B,&s=0,\ j=j_B,\\
A,&s=0,\ j\in J\setminus\{j_B\},
\end{cases}
\qquad f(\bot)=R.
\tag{5.1}
$$

The free observation is $v$ or $\bot$. A controller consists of a finite nonempty set $K$ and stationary tables

$$
c:\{0,1,\bot\}\to K,\qquad
u:K\to\{0,1\}^m\sqcup\operatorname{Halt}(\{A,B,M,R,C\}),\qquad
V:K\times\{0,1,\bot\}\to K.
\tag{5.2}
$$

An emitting state performs its literal word with the original bit updates [IF, (1.2)], pays one complete block even on rejection, and applies $V$ to the actual endpoint observation. A stopping state returns its installed label. There is no separately readable issued index, endpoint archive, hidden phase/tail, reset, copy or output latch. Every usable runtime distinction belongs to $K$. Let $K_{\min}(4;m)$ be the minimum cardinality of a controller correct on every source in $Q$ and stopping after at most four emitted blocks. Its tables and word descriptions may be compiled separately for known $m$.

**引理 5.2（Two forced roots and the complete cut entries）。** For every correct controller in Definition 5.1, the two scalar initial states $a_v=c(v)$ are distinct emitting states with $u(a_v)=1^m$. Their zero-difference successors

$$
d_v=V(a_v,v)
\tag{5.3}
$$

are emitting states distinct from both roots. For some $b_v,c_v\in\{0,1\}$ their words are exactly

$$
u(d_v)=1^r0b_vc_v.
\tag{5.4}
$$

If $d_0=d_1$, the two words, hence their two final bits, coincide. On the mandatory root occurrence, each of a root's scalar response entries is realized by a source with target different from $B$. On the mandatory cut occurrence, each scalar response entry is realized by an $A$ source. Consequently none of these scalar entries can lead directly to a state with instruction $\operatorname{Halt}(B)$.

Proof. At either free value, choose $j\in J$ and initial tails $0,h$. Their labels differ. A root containing a zero after $\ell<m$ leading ones lets both reach that zero, because $h+\ell\le2m-3=k-1$. Their values and phases agree and the zero clears both tails. They then have the same physical record and the same observed archive, so no later deterministic continuation recovers the unequal INITIAL labels. Stopping initially is also impossible. Thus the root word is $1^m$, as in Corollary 3.1.

Suppose its two initial control states coincide. After this common root, condition on either scalar endpoint $y$. That one control state must contain the zero-difference sources with initial value $y$, and the positive-difference sources with initial value $1-y$. It cannot stop. If its next word begins zero, at any fixed $j\in J\setminus\{j_B\}$ the former sources with initial tails $0,1$ merge, losing labels $A,M$. If it begins one, take initial tail $h-1$ from both a zero-difference phase in $J$ and a positive-difference phase in $\{0,m\}$. Both current tails are $k-1$ and both current values are $y$; the first bit rejects them into the same bottom record and endpoint, losing labels $M,C$. These two first-bit cases exhaust every literal next word. Hence $a_0\ne a_1$.

The root-zero archive at either value contains $A,B,M$ and cannot stop. Another $1^m$ rejects every member and loses unequal labels, so its next state is neither root. Theorem 2.1 and Example 3.2 force the unique eligible first zero at $r=m-3$. Directly, a first zero after $\ell<r$ leading ones lets the initial tails $0,1$ at a fixed $A$ phase survive and merge, losing $A,M$; after $\ell>r$, one has $\ell\ge h$ and even the initial tail-zero $A,B$ sources reject together. Only $\ell=r$ remains. There are then exactly two unconstrained final bits, giving all four words (5.4) without selecting a preferred final tail. The low-tail phase set $H=\{2,\ldots,m-1\}$ has cut charge zero and label $A$. The cut turn $2m-3$ has charge one and also label $A$, regardless of $b_v,c_v$. Thus both successful scalar entries at each cut are occupied by $A$ sources. At root $a_v$, response $v$ includes $A$ sources and response $1-v$ includes $C$ sources. Correctness prohibits a direct $B$ stop at all these entries. ∎

**引理 5.3（A required fourth-block state and the universal ten-state lower evidence）。** Define $\beta_v=v\oplus b_v$. On the $B$ source with free value $v$, let $e_v$ and $p_v$ be its control states after two and three emitted blocks. Then

$$
e_v=V(d_v,\beta_v),\qquad p_v=V(e_v,\beta_v).
\tag{5.5}
$$

Both are emitting states. The state $p_v$ is distinct from every root and every cut entry. Its two scalar successors are stopping states with labels $A$ and $B$, in some order. If $\beta_0\ne\beta_1$, then $p_0\ne p_1$. Every correct depth-four controller therefore has at least ten complete control states.

Proof. For each $v$, pair its $B$ source at $j_B$ and tail zero with the tail-zero $A$ source at

$$
j_A(v)=
\begin{cases}
2m-4,&b_v=0,\\
2m-3,&b_v=1.
\end{cases}
\tag{5.6}
$$

They are actual sources, including at $m=6$. Both have zero root difference. The cut charges at $j_B,j_A(v)$ are both $b_v$, by [IF, (1.4)]. Thus after the cut their observed values are both $\beta_v$, their current tails are the same trailing run $\tau_v\le2$, and they occupy the same state $e_v$.

For the third block the full physical charge window is $W_2=[1,m+1]$. All of $j_B,2m-4,2m-3$ lie outside it: $2m-4>m+1$ for $m\ge6$. Every legal third word therefore has charge zero on the pair. Every such word is also safe from their common tail, since $\tau_v+m\le m+2<2m-2=k$. Its actual endpoint is again $\beta_v$ on both sources, and its final tail is again common. The pair cannot have stopped after the root, cut or third word. This proves (5.5) and that $e_v,p_v$ emit.

At the fourth block, rejection is common to the pair: rejection depends on their equal incoming tails and the literal word, not on phase. Common rejection cannot recover their unequal labels. Thus the final word must succeed on both and give different scalar endpoints. With the four-block deadline, those two scalar successors must already be $\operatorname{Halt}(A)$ and $\operatorname{Halt}(B)$. Lemma 5.2 excludes $p_v$ from all root and cut states.

If the two $p_v$ were one state and $\beta_0\ne\beta_1$, its one fourth-block literal word would give the same charge $q_3(j_B)$ to both $B$ sources. Their endpoints $\beta_v\oplus q_3(j_B)$ would be opposite, forcing both scalar successors to output $B$. This contradicts the paired $A$ source. Hence unequal $\beta_v$ require distinct fourth-block states.

All five labels occur, so at least five distinct stopping states are required. If the cut entries differ, two roots, two cuts and at least one fourth-block state require five additional emitting states. If the cuts coincide, their $b_v$ coincide, so $\beta_0\ne\beta_1$; two roots, one cut and two fourth-block states again require five emitting states. This proves $K_{\min}(4;m)\ge10$ for all controllers. It uses no normal form for delayed homogeneous stops or third/fourth words. ∎

**定理 5.4（The exact all-controller minimum is eleven）。** Under Definition 5.1, for every $m\ge6$,

$$
\boxed{K_{\min}(4;m)=11.}
\tag{5.7}
$$

In particular the complete five-emitting-state competitor class has no correct depth-four controller. An attaining stationary controller has six emitting states and five stopping states. Its literal description and offline compilation resources are separate from this cardinality and from its four paid blocks.

Proof, constructive upper bound. Use the already priced four words

$$
L=1^m,\qquad D=1^r0^3,\qquad Z=0^m,\qquad P=0^r1\,0^2.
\tag{5.8}
$$

Take states $a_0,a_1,d,w,p_0,p_1$ and $H_A,H_B,H_M,H_R,H_C$. Initialize $c(0)=a_0$, $c(1)=a_1$, $c(\bot)=H_R$. The entire emitting table is

| State | Installed word | Endpoint $0$ | Endpoint $1$ | Endpoint $\bot$ |
| --- | --- | --- | --- | --- |
| $a_0$ | $L$ | $d$ | $H_C$ | $H_R$ |
| $a_1$ | $L$ | $H_C$ | $d$ | $H_R$ |
| $d$ | $D$ | $w$ | $w$ | $H_M$ |
| $w$ | $Z$ | $p_0$ | $p_1$ | $H_R$ |
| $p_0$ | $P$ | $H_A$ | $H_B$ | $H_R$ |
| $p_1$ | $P$ | $H_B$ | $H_A$ | $H_R$ |

For each label $X$, set $u(H_X)=\operatorname{Halt}(X)$ and $V(H_X,y)=H_X$ for every $y$. The bottom entries at $w,p_0,p_1$ complete the table and are unreachable from the allowed sources. There is no free clock: each row has one word and one endpoint update at every possible occurrence.

Here is a full support–rank certificate. Put $\lambda(j)=B$ when $j=j_B$ and $A$ otherwise, and put $\epsilon(j)=\mathbf1_{\{j=2m-3\}}$ for $j\in J$. Let $F(j,s)$ be the restriction of (5.1) to $j\in J,\ 0\le s<h$. Supports contain immutable target/current-record pairs; $v,j,s$ below are proof coordinates, not runtime inputs:

$$
\begin{aligned}
\Gamma_{a_b}
 &=\{(f(b,-j,s),(b,-j,s)):j\in\mathbb Z/T\mathbb Z,\ 0\le s<k\},\\
\Gamma_d
 &=\{(F(j,s),(v,-j+m,m+s)):v\in\mathbb F_2,\ j\in J,\ 0\le s<h\},\\
\Gamma_w
 &=\{(\lambda(j),(v\oplus\epsilon(j),-j+2m,0)):v\in\mathbb F_2,\ j\in J\},\\
\Gamma_{p_b}
 &=\{(\lambda(j),(b,-j+3m,0)):j\in J\},\\
\Gamma_{H_X}&=\{X\}\times Q.
\end{aligned}
\tag{5.9}
$$

Assign ranks $4,3,2,1,0$ to $a_b,d,w,p_b,H_X$, respectively. Initial coverage follows directly from $c$. The root rejects exactly $s\ge h$ with label $R$. On success its charge is $\mathbf1_{\{0,m\}}(j)$, so the positive branch has label $C$, and the zero branch is exactly $\Gamma_d$. On that support, $D$ rejects exactly $s\ge1$ into label $M$. At $s=0$, its first zero is safe because $m+r=k-1$, its endpoint tail is zero, and its charge restricted to $J$ is $\epsilon(j)$. This gives $\Gamma_w$. The paid $Z$ preserves the value, clears the tail, advances phase and enters exactly $\Gamma_{p_b}$ according to its actual scalar endpoint. Finally $P$ is safe from tail zero and at issued index three has charge support $\{j_B,0\}$. Phase zero was excluded from these supports, so its difference is exactly $\mathbf1_{\{j=j_B\}}$. The final comparison in the table therefore returns $\lambda(j)$.

These statements give legal literal actions, successor closure and strict rank descent on every emitting support. Each stopping support contains only its installed target. The terminal supports are permitted overapproximations; no action is executed after stopping. By the reused support–rank criterion [CM, Theorem 27.2], every allowed source stops correctly within four paid blocks. The proof of the certificate is ordinary and makes no current kernel claim. Actual $A,B$ sources use four blocks, $M$ sources two, successful $C$ and rejected $R$ sources one, and initial bottom zero.

Proof, exclusion of every ten-state competitor. Suppose a correct controller has at most ten states. Lemma 5.3 already excludes fewer than ten. All five stopping labels and the forced emitting roles must therefore fit into precisely five emitting states. Every fourth-block state $p_v$ has both scalar successors stopping with labels in $\{A,B\}$. In particular neither $e_v$ can be any fourth-block state: the actual third endpoint is scalar $\beta_v$, whereas $p_v=V(e_v,\beta_v)$ must still emit. No early stopping convention removes this requirement, because the paired unequal labels have not been separated.

Case one: $d_0=d_1=d$. The cut has a single word and $\beta_0\ne\beta_1$. By Lemma 5.3, the five emitting states are exactly

$$
\{a_0,a_1,d,p_0,p_1\}.
\tag{5.10}
$$

The third-block state $e_v$ is neither fourth-block state. It is not $d$ either: if $e_v=d$, then (5.5) gives $p_v=V(d,\beta_v)=e_v=d$, a contradiction. Thus $e_v=a_i$ for some $i$. If $i=\beta_v$, its mandatory zero-response entry is $V(a_i,i)=d$, again contradicting $p_v$ being a fourth-block state. Necessarily

$$
e_v=a_{1-\beta_v},\qquad V(a_{1-\beta_v},\beta_v)=p_v.
\tag{5.11}
$$

Case two: $d_0\ne d_1$. The five emitting states can contain only one fourth-block state, so $p_0=p_1=p$. Lemma 5.3 requires $\beta_0=\beta_1=\beta$. The emitting set is exactly $\{a_0,a_1,d_0,d_1,p\}$. Again neither $e_v$ is $p$. If $e_v=d_i$, stationarity and (5.5) imply

$$
p=V(e_v,\beta)=V(d_i,\beta)=e_i.
\tag{5.12}
$$

But $e_i$ cannot be a fourth-block state, a contradiction. Hence $e_v$ is a root. The zero-response root entry excludes $a_\beta$, leaving

$$
e_0=e_1=a_{1-\beta},\qquad V(a_{1-\beta},\beta)=p.
\tag{5.13}
$$

The same all-word contradiction closes both cases. Fix a value $v$ and write $p=p_v$, $\beta=\beta_v$, and $a=a_{1-\beta}$. Equations (5.11) or (5.13) say that a positive-difference root source with initial value $1-\beta$ enters $p$ after its first block. In particular take an actual $C$ source at $j=0$, initial tail zero. Its current value is $\beta$ and its current tail is $m$. If $u(p)$ succeeded on this source, its scalar endpoint would immediately enter one of the installed $A,B$ stops, mislabelling $C$. Therefore this literal word must reject the $C$ source.

For any length-$m$ literal word, rejection from tail $m$ requires at least $h=k-m=m-2$ leading ones. Indeed, if its first zero is after $\ell<h$ ones, it reaches that zero safely, and every later internal run has length at most $m<k$, so no later rejection is possible. The all-one word also has at least $h$ leading ones. This covers every possible $u(p)$, without a selected action summary.

On the actual $B$ execution, however, the third-block state is $a$, whose word is $1^m$. It is safe from the cut tail $\tau_v\le2$ and leaves current tail $m+\tau_v\ge m$. The same $h$ leading ones of $u(p)$ therefore reject this $B$ source as well. They also reject its paired $A$ source, whose tail is identical. Their shared bottom endpoint cannot yield both labels, contrary to Lemma 5.3. Both five-emitting-state cases are impossible. Thus every correct controller has at least eleven states, matching (5.8)–(5.9). ∎

**计量与范围 5.5（What is counted and what the conclusion closes）。** The eleven states include the six runtime program/value roles and all five stopping outputs. A separate immutable dictionary contains four expanded words of total length $4m$ bits; the routing and initialization tables have constant size. Descriptions of the five fixed labels, the target predicates and the binary parameter $m$ are separately metered. Generating expanded words has an output cost proportional to $m$; offline computation and compiler workspace are not charged by either $|K|$ or the emitted-block fee. The result is a uniform cardinal bound for controllers compiled for known $m$, not a constant-total-storage, physical-memory or optimal-compilation claim.

The lower proof retains every literal third/fourth word, both arbitrary final cut bits, delayed homogeneous stops and cross-depth state reuse. Its exhaustive split is equality or inequality of the two actually mandatory cut entries. The incompatibility of a shared fourth-block state with an early $C$ occurrence is proved from the actual union support, rather than imposed as a policy normalization. The specific $K=10$ completeness obligation is therefore closed by the ordinary proof. Different targets, label coincidences, horizons, hidden observation permissions, parameter ranges and the original guarded-tree or all-target objectives are outside (5.7).

**来源与证据边界 5.6（Mature premises and new ordinary content）。** The original bit reader, joint realization, charge inverse and first-zero loss come from [IF, Definitions 1.1–1.3 and Interface 1.4]. Root forcing, the complete cut entry and the four paid words reuse this companion's Theorem 2.1, Corollary 3.1 and Example 3.2. Complete Moore-style accounting and support–rank verification reuse [CM, Sections 26–27]. Reissig, Weber and Rungger, *Feedback Refinement Relations for the Synthesis of Symbolic Controllers*, [arXiv:1503.03715v3, Sections III-A–III-B](https://arxiv.org/html/1503.03715v3#S3), supplies the mature stateful-controller and closed-loop framework; van den Bos and Vaandrager's completed-observation identification framework is cited in Mathematical citation 4.1. Neither source supplies the numeric minimum (5.7).

The new family-specific content is the mandatory fourth-block support argument and the exhaustive five-emitting-state incompatibility proof. These are `repo-derived` ordinary deductions. Any `suspected-novel` priority assessment remains unverified; the cited comparison is not an exhaustive literature search. No Lean/kernel verification, ingestion, frozen-state acceptance, CI outcome or whole-project completion follows from this ordinary theorem.

[IF]: https://github.com/the-omega-institute/trureturing/blob/f41910858bd5ad5592fae12340cfb62c79a8c673/docs/develop/theory/KBONACCI_INITIAL_TARGET_COST_THEORY.md
[CM]: https://github.com/the-omega-institute/trureturing/blob/f41910858bd5ad5592fae12340cfb62c79a8c673/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md

## 追加锚（本行以下为增补区）

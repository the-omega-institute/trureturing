# Finite public offset alphabets and exact initial-cut identifiability

Fix a public positive rational unit and a finite public alphabet of nonnegative rational offsets, while one offset remains hidden and fixed. Exact recovery at every actual handoff has a sharp condition: no alphabet value is another alphabet value plus the unit. Under the public promise of a proper handoff, exact recovery always succeeds, even when that condition fails. Each statement holds separately for the original owned boundary and for each nonempty finite prefix of the original unread raw tail. The empty prefix requires no new source operation or measurement.

The arguments are ordinary conditional symbolic proofs for the explicitly specified sequential producer and finite-response interface. The supplied partition, finite-core and owned-image facts are stated below. No executed mathematical validation, Lean/kernel certificate, physical sensor, external priority or universal resource optimum is asserted.

## 1. Actual source, paid execution and owned boundaries

Put

$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,\qquad
\alpha=(\sqrt5-1)/2,\qquad \phi=\alpha^{-1}.
$$

Thus $\alpha^2+\alpha=1$, $0<\alpha<1$ and $\phi^2=\phi+1$. Positions run from low to high. Let

$$
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ for all }j\ge0\},\qquad
\mathcal B=\{0,10\}^{<\omega}.
$$

Every infinite word in $K$ has a unique complete-block parsing: zero supplies $0$, and one supplies $10$ using its promised next zero. Every nonempty $p\in\mathcal B$ ends in zero and permits every $t\in K$ after it. Write $C_p=\{pt:t\in K\}$, $q_m(x)=(x_0,\ldots,x_{m-1})$, $f(x)=x_0$, and $Z(A)$ for the zero-padded finite Zeckendorf word of $A\ge0$. Set $\operatorname{Low}(A)=f(Z(A))$.

The endpoint-inclusive arithmetic successor $T$ clears all positions below the first adjacent $00$, writes one at that pair's first position and retains higher digits. If no $00$ exists, it returns $Z(0)$. Both pure alternating words are included. This is the arithmetic successor, distinct from positional deletion.

The mathematical suppliers used from [PAID, Sections 1–3, 7 and 12][PAID] are the following precise structural facts. On the finite core, $T^hZ(A)=Z(A+h)$. For $p\in\mathcal B$, put

$$
d=|p|,\qquad N_p=\sum_{j<d}G_jp_j,\qquad
M_p=G_{d+1}-N_p,\qquad k_p=M_p-2,
$$

$$
b_\varnothing=0,\qquad b_{p0}=b_{p10}=M_p-1.
$$

The temporal partition atom of $C_p$ survives at precisely the inclusive lengths $b_p\le n\le k_p$; its next split is $C_{p0},C_{p10}$. All its itineraries agree below $k_p$, and the two child itinerary constants at $k_p$ are different, for arbitrary legal remaining tails. At every finite $L\ge1$, equality of $q_L$ is equivalent to equality of the future lowest-digit word of length $G_L-1$. These are supplied partition results. The owned-image formula stated below is a further supplied geometric result, including its full point fibres and endpoint conventions. No assertion here substitutes phase equality for equality of whole points or claims a new verification of the linked upstream sources.

The actual raw endpoint holds one fixed $x\in K$. Its only producer input operation is Read, which physically delivers the next original bit and advances its raw cursor by one. Every reached Read finishes. Passing a forced zero still pays its Read. Source-independent installation pays for finite programs, configuration, reference conventions, bindings, persistent rights and source provision. Initialization starts with $p=\varnothing$, raw cursor and absolute source count zero, fixed caches and empty scratch/pending output. Its fixed acknowledgement is return zero and performs no Read or Advance.

A returned state has actual acquired word $p$, absolute completed-Advance count $n$, cursor $d=|p|$ and caches $N_p,G_d,G_{d+1},k_p$. Next below death, $n<k_p$, reads nothing. At death, $n=k_p$, it Reads the next block: one bit for $0$, two for $10$, including the physical forced zero. With the resulting word $p'$ it computes $\operatorname{Low}(N_{p'}+n)$, then actually Emits that value, Advances once to $n+1$, clears scratch and Returns. Only Advance changes source time; queries, pauses and computation do not. The denotation is $T^n x$, with the same original endpoint at $\operatorname{tail}_{|p|}x$. This productive representation never executes an infinite raw first-$00$ search.

**Lemma 1.1 (Actual execution and inclusive attainment).** Every finite initialized run finishes and has precisely the stated actual fields, correct Emit values and exact unread-tail continuation. Every $x\in C_p$ actually reaches every return $b_p\le n\le k_p$ with precisely $p$ acquired. For nonempty $p$,

$$
b_p+N_p=G_d-1,\qquad k_p+N_p=G_{d+1}-2,
$$

and

$$
k_{p0}=k_p+G_d,\qquad k_{p10}=k_p+G_{d+1}.
\tag{1}
$$

**Proof.** At zero the state is genuinely empty. Below death, the supplied temporal atom has a common next bit; its member $Z(N_p)$ identifies it as $\operatorname{Low}(N_p+n)$. At death the actual unread endpoint supplies its unique next block. The chosen child is born at $k_p+1$; its common split-coordinate bit is identified by its finite representative $Z(N_{p'})$. Thus the actual Emit is correct in both branches. There are at most two reached Reads and otherwise finite arithmetic, so each call finishes. Advance gives $T^{n+1}x$, and Return has empty pending fields. Induction proves all finite runs, including alternating inputs.

Appending zero leaves $N$ fixed; appending $10$ at original cursor $d$ adds $G_d$. Substitution in $k$ and the Fibonacci recurrence gives (1). If a word is $u0$, its birth formula gives $b_p+N_p=G_d-1$ directly. If it is $u10$, its value adds $G_{d-2}$ and its birth is $G_{d-1}-N_u-1$, giving the same identity by the recurrence. The upper identity is the definition of $k_p$.

For actual attainment, induct on the complete blocks of $p$. Every source in a child cylinder first reaches its parent death with the parent's acquired word, then really reads the specified child block and Returns at its birth. Between that birth and the child's inclusive death it takes read-free calls. The positive increments (1) preserve the reached domain. This realizes every integer in the displayed interval on every $x\in C_p$. The empty word survives only at zero. Restarting at any such actual return uses the same caches and asks for exactly the original cursor's next bit when a Read is reached. Induction gives the suffix of the uninterrupted run, with no reread, substituted history or changed binding. $\square$

For $d\ge1$ define

$$
J_d=\{G_d-1,\ldots,G_{d+1}-2\},\qquad
s=N_p+n\in J_d,\qquad \delta=G_{d+1}-2-s=k_p-n.
$$

To specify the full owned boundary, let $e_j=[-j\phi]\in\mathbb R/\mathbb Z$ for integer $j$, and set

$$
(A_d,B_d)=
\begin{cases}(G_{d-1},G_d),&d\text{ even},\\(G_d,G_{d-1}),&d\text{ odd}.
\end{cases}
$$

The actual compatible set is

$$
T^nC_p=U(\partial(d,s)).
\tag{2}
$$

Its positive oriented phase arc has length $\alpha^d$, initial wall $e_{A_d-s}$ and terminal wall $e_{B_d-s}$. It contains every lift over an interior phase and exactly the following lifts at its respective walls:

$$
\chi_+(A_d-s),\qquad\chi_-(B_d-s),\qquad
\chi_\pm(j)=
\begin{cases}x_1^\pm,&j=1,\\Z(-j),&j\le0.
\end{cases}
\tag{3}
$$

Here $x_1^+,x_1^-$ are the two distinct split-side lifts with the stated initial/terminal roles in PAID's owned-image theorem. All attained labels are at most one. Label zero owns $Z(0)$ and has no artificial split side. Formulae (2)–(3), their unique $(d,s)$ coordinates and length are supplied by PAID Theorem 12.2. They are data of this conditional model; recovering only an unowned arc is a different task. Empty initialization is independently the whole circle with no walls, depth/slack zero and record $(0,0)$. There is no $J_0$ or $G_{-1}$.

The owned coordinates transport as follows. Positive slack gives a real read-free Next, Emit $\operatorname{Low}(s)$ and $(d,s+1)$. At zero slack the actual next $0$ or $10$ chooses respectively

$$
(d+1,G_{d+1}-1),\qquad(d+2,G_{d+2}-1).
\tag{4}
$$

Indeed, at death $N_p+n=G_{d+1}-2$; adding the new value, then one Advance, gives these sums by (1). The two possible actual Emits are the distinct supplied child constants

$$
c_0=\operatorname{Low}(G_{d+1}-2),\qquad
c_1=\operatorname{Low}(G_{d+2}-2).
\tag{5}
$$

Their inequality follows from the child partition split, with finite representatives in the two child cylinders. It is a real event distinction, not a private branch flag.

## 2. Public alphabet, fixed targets and complete observation

Fix, before considering a receiver, an explicitly encoded rational $q_0>0$ and a finite nonempty rational VALUE set $B\subseteq\mathbb Q_{\ge0}$. A presented list is validated and deduplicated by exact rational equality. Numerators and positive denominators of every value are public. Cardinality, code names or hidden parameter names alone do not supply this input. A single hidden finite index selects one $b\in B$ at source-independent installation. That value remains fixed throughout the initialized old history and all continuation.

At an actual returned cut of acquired depth $d$, Extent$(n)$, $n\ge1$, returns the entire nonnegative integer $a$, its canonical finite self-delimiting frame, request fields and separate service completion, with

$$
\varepsilon=2^{-n},\qquad u=a\varepsilon,\qquad
|u-(b+q_0\alpha^d)|\le\varepsilon.
\tag{6}
$$

Every reached service finishes, reads no raw bit, performs no Advance and preserves the actual producer, cursor, source and rights. It is unavailable inside an unfinished Step. Full integer parts are included; there is no modular reduction, clipping or saturation. Errors may be adaptive, correlated, biased, nonnested and at either closed endpoint. The positive statements quantify over every allowed reply trace with the same fixed $b$.

The region measured is the same actual paid-frontier compatible region in (2), with length one at the empty cut. It is neither a chord, complement arc, shorter circular wall distance nor the material length of an infinite tape. Known $\alpha$, known resolution and same-region correspondence are reference assumptions. No wall phase or phase origin is measured.

For necessity use the one public finite source-blind program $P(q_0,B;j)$ with fixed hidden selected value $b=B_j$:

$$
F_b(d,n)=\left\lfloor2^n(b+q_0\alpha^d)\right\rfloor.
\tag{7}
$$

It reads only its actual acquired-depth cache and fixed offset, returns the full integer with the prescribed frames, and has no advice field. Section 3 gives its finite arithmetic realization. Its error is strictly less than $2^{-n}$, so it is an instance of (6). The program, alphabet, unit, source conventions and protocol are fixed before any negative decoder-dependent choice.

A real finite driver prefix from the original initialization ends at any Return $(p_0,r_0)$ and transfers an already installed persistent exclusive Step/Extent turn. The producer, original raw endpoint, cursor, counters, caches and binding persist. The driver stops concurrent action. The receiver gets common source-independent state, fixed acknowledgement and descriptor literals, public $q_0,B,P$, its finite request, and actual continuing rights; local completed-Step count is zero. Step is the original Next, with each actual intermediate Emit VALUE, Advance and Return delivered in order. A pause has no source effect. Release makes its declared control transition and ends the turn, with no new informative handoff or invisible driver continuation.

The complete observation retains every request, precision, entire reply integer/frame/completion, fixed acknowledgement, actual Emit value and event order, local request and Step counts, declared modes, possession/control outcomes, local computed records and streamed outputs. Equal descriptor literals describe separate lawful installations, without copying authority. Private $p,n,N,d$, raw responses and Read counts, old history and absolute counter, hidden configuration length/digest, installation size, source identity, private work/storage and timing are excluded. There is no initial reread, rewind, raw getter, Wall, authenticated old counter, private exporter or informative response to an uninstalled command. Wrappers expand to the same real installed operations.

Write

$$
x=p_0t_0,\qquad d_0=|p_0|,\qquad s_0=N_{p_0}+r_0.
$$

The boundary target is always the ORIGINAL $\partial_0$ at this handoff. Separately, for each fixed $m\ge1$, the raw target is the ORIGINAL $q_m(t_0)$. Neither resets after a Step. A reached $\partial_i$ or a current spatial prefix $q_L(T^{r_0+i}x)$ is a different target. A proper promise means $r_0\ge1$, equivalently $d_0\ge1$, and includes both births and deaths.

**Proposition 2.1 (Zero target).** For $m=0$, output the empty word immediately. New Extent, Step, Read, source Emit, Advance and producer Return counts are all zero.

**Proof.** Every initial tail has the same empty prefix, so no source distinction or calibration is needed. The handoff remains the current source cut. Existing installation/handoff and literal local output/framing remain paid; local output completion is not a producer Return. All nonexistence assertions and nonempty-target clocks below use $m\ge1$. $\square$

## 3. Irrational differences and globally complete stationary isolation

**Lemma 3.1 (Differences, including depth zero).** For distinct nonnegative integers $d,e$, $\alpha^d-\alpha^e$ is irrational.

**Proof.** Suppose $d>e\ge0$ and put $v=\alpha^e-\alpha^d$, so $0<v<1$. Quadratic conjugation sends $\alpha$ to $-\phi$ and fixes every rational. If $v$ were rational it would equal $v'=(-\phi)^e-(-\phi)^d$. Opposite parities give $|v'|=\phi^e+\phi^d>1$. Equal parities give $d-e\ge2$ and

$$
|v'|=\phi^e(\phi^{d-e}-1)\ge\phi^e(\phi^2-1)=\phi^{e+1}>1.
$$

Either contradicts $|v|<1$. Reversing the exponents only changes sign. This covers $e=0$. In particular $\alpha^d$ is irrational for $d\ge1$, since otherwise $1-\alpha^d$ would be rational. Irrationality of the individual powers alone would not prove irrationality of their differences. $\square$

**Corollary 3.2 (Exact injectivity and the accumulation values).** The equality

$$
b+q_0\alpha^d=c+q_0\alpha^e\qquad(b,c\in B)
$$

forces $d=e$ and $b=c$. Every proper true scalar lies outside $B$. At depth zero it belongs to $B$ exactly when $b+q_0\in B$.

**Proof.** If $d\ne e$, rearrangement makes $\alpha^d-\alpha^e=(c-b)/q_0$ rational, contradicting Lemma 3.1. Equal depths then force equal offsets. Proper scalars are irrational whereas $B$ is rational. At zero the scalar is exactly $b+q_0$. Each chain $c+q_0\alpha^e$ tends to $c$; any sequence of distinct values from the finite union has unbounded exponents and a fixed-offset subsequence. Thus its possible accumulation values are precisely all members of $B$. $\square$

**Lemma 3.3 (Finite exact arithmetic).** The tests and floor service in this volume have finite exact arithmetic specifications.

**Proof.** Finite powers lie in $\mathbb Q(\sqrt5)$ by $\alpha^2=1-\alpha$. Clearing positive denominators reduces comparisons to the sign of $U+V\sqrt5$ for finite integers $U,V$. Zero terms and same-sign terms decide directly. For opposite signs compare $U^2$ with $5V^2$ and use the original signs to choose the direction; equality is included. This handles closed compatibility endpoints and rational or zero values. For a nonnegative quadratic target, coefficient bounds using $2<\sqrt5<3$ supply a finite rational upper bound and hence an integer bracket. Integer bisection with these exact comparisons yields its entire floor, including depth-zero integer endpoints. The target in (7) is positive, so its floor is nonnegative. Neither an infinite expansion nor a numerical equality oracle is required. These specifications are unexecuted symbolic mathematics. $\square$

For the all-return domain put $E=\mathbb N_0$; for the proper promise put $E=\mathbb N_{\ge1}$. The following stationary decoder is only claimed total when the actual $z=b+q_0\alpha^d$ lies outside $B$.

At the same actual returned cut request $n=1,2,\ldots$. From its current reply compute

$$
r_n=\min_{c\in B}|u-c|-\varepsilon.
$$

Skip stages with $r_n\le0$. Otherwise find the least $D_n\ge0$ such that $q_0\alpha^{D_n}<r_n$. Inspect EVERY $(e,c)$ with $c\in B$, $e\in E$ and $0\le e<D_n$. Retain exactly those satisfying

$$
|u-(c+q_0\alpha^e)|\le\varepsilon.
\tag{8}
$$

Finish the full scan, retaining one candidate and a count saturated at two. Accept exactly a singleton; otherwise clear stage scratch and refine. No past-reply intersection is used.

**Theorem 3.4 (Infinite-tail exclusion and every-error stopping).** Acceptance is globally sound on the selected actual depth domain. If $z\notin B$, every closed-error trace stops finitely and returns its exact $(d,b)$.

**Proof.** First $\alpha>1/2$, because $\alpha\le1/2$ would give $\alpha^2+\alpha\le3/4$. Consequently $\alpha^2=1-\alpha<1/2$ and $\alpha^{2j}<2^{-j}$, so the cutoff exists whenever $r_n>0$.

Any compatible $(e,c)$ satisfies, by the triangle inequality,

$$
q_0\alpha^e\ge |u-c|-\varepsilon\ge r_n.
$$

For $e\ge D_n$ this contradicts $q_0\alpha^e\le q_0\alpha^{D_n}<r_n$. Thus the scan excludes the ENTIRE infinite tail of depths, and the true pair lies in the finite scanned list and passes (8). An accepted singleton is globally unique, rather than unique inside an arbitrary sample.

For termination fix the actual $z\notin B$ only in the proof. The positive number $\Delta=\min_{c\in B}|z-c|$ exists since $B$ is finite. Every allowed reply has $r_n\ge\Delta-2\varepsilon$. Choose a finite $\overline D$ with $q_0\alpha^{\overline D}<\Delta/2$. Eventually $\varepsilon<\Delta/4$, so $r_n>\Delta/2$ and $D_n\le\overline D$. The fixed finite set

$$
F=\{c+q_0\alpha^e:c\in B,\ e\in E,\ 0\le e<\overline D\}
$$

contains $z$: indeed $q_0\alpha^d=|z-b|\ge\Delta$, so $d\ge\overline D$ would contradict the chosen cutoff. Corollary 3.2 makes all its values distinct. Let $\eta>0$ be the least distance from $z$ to another value in $F$, or any positive number if there is none. Eventually $2\varepsilon<\eta$ too. Every false passing value belongs to $F$ and would satisfy

$$
|z'-z|\le |z'-u|+|u-z|\le2\varepsilon<\eta,
$$

a contradiction. Therefore EVERY reply at every sufficiently large precision leaves exactly the true singleton, regardless of earlier errors. Sequential refinement stops on every permitted trace. The witnesses $z,\Delta,\overline D,\eta$ are not receiver inputs or free certificates. $\square$

Depth and offset VALUE are decoded, not slack, provenance, raw history, old absolute count, a whole infinite point or an invocation right. A canonical distinct-value list also fixes its value index. Duplicate syntactic encodings of one rational do not identify an original private encoding or index.

## 4. One real block update and the original owned boundary

On the proper domain, or on an all-return domain satisfying $B\cap(B+q_0)=\varnothing$, Corollary 3.2 gives $z\notin B$ at the original cut. Decode its true $d_0,b$ by Theorem 3.4. A boundary-only request with decoded $d_0=0$ immediately returns the whole-circle/no-wall record and takes no Step. The $m=0$ rule precedes even this search.

For a proper boundary request and for every $m\ge1$ raw request, choose a finite $n_c\ge1$ with

$$
4\varepsilon_c<q_0\alpha^{d_0+3},\qquad\varepsilon_c=2^{-n_c}.
\tag{9}
$$

Finite exact comparison and decay supply this choice. The known prospective scalars are $z_j=b+q_0\alpha^{d_0+j}$ for $j=0,1,2$. Start local $i=0$ and $W$ empty. Complete one actual Step, increment $i$ and query Extent$(n_c)$ at its Return. Test all three closed balls of radius $\varepsilon_c$. While the unique compatible category is $j=0$, continue. At the first $j=1$ or $2$, record $t_1=i$, $g_1=j$, append respectively $0$ or $10$ to $W$, and stop all Extent querying.

**Lemma 4.1 (No missed first acquisition).** The rule identifies each preceding read-free Step and the first actual new block exactly, on every error trace.

**Proof.** The adjacent gaps are $q_0\alpha^{d_0+2}$ and $q_0\alpha^{d_0+3}$, since $1-\alpha=\alpha^2$. Their smaller value exceeds $4\varepsilon_c$. Before the first acquisition the actual depth is $d_0$; at the first acquisition it becomes exactly $d_0+1$ or $d_0+2$. The true candidate therefore passes its closed ball at every tested cut through that acquisition. Two passing candidates would differ by at most $2\varepsilon_c$, contradicting the strict gap. Induction rules out both false updates and a missed real update. The recovered $b$ remains fixed. $\square$

**Theorem 4.2 (Original and attained boundary).** On the stated positive domains the boundary rule terminates. At a proper original cut it recovers

$$
t_1=\delta_0+1\le G_{d_0-1},\qquad
s_0=G_{d_0+1}-1-t_1,
\tag{10}
$$

and hence the full original $\partial(d_0,s_0)$, including (3). At its first-update Return it has actually attained

$$
D=d_0+g_1,\qquad s=G_D-1,
\tag{11}
$$

and physically read exactly $g_1\in\{1,2\}$ new bits. At an empty original cut, when this rule is needed for a raw target, $t_1=1$, $D=g_1$, and (11) still describes its actual child birth.

**Proof.** At a proper cut there are exactly $\delta_0=k_{p_0}-r_0$ read-free calls before death, followed by the block-reading call. The finite death clock and productive services make this finite. Formula (10) follows from the definition of slack; $s_0\ge G_{d_0}-1$ gives its upper bound. Lemma 4.1 measures this exact elapsed count using real Steps, so it recovers the actual sum coordinate. Formula (3) then gives every wall role and owned lift, including zero collapse and birth sides. The new child Returns at birth by Lemma 1.1, giving (11). Only that call reads, and it reads the complete physical block, including a forced zero. At the empty cut $k=r=0$, so the first call reads and the same child-birth argument applies, while its original whole-circle boundary is handled independently. No proper negative-index formula is used. $\square$

This is a boundary acquisition upper bound, not an earliest-boundary theorem. For a proper $(d_0,s_0)$ the supplied historical fibre remains

$$
\{(p_{d_0}(N),s_0-N):0\le N<G_{d_0-1}\},
$$

where $p_d(N)$ is the finite padded Zeckendorf word. At depth at least two it has multiple members. Choosing a possible member cannot authenticate the actual $p_0,r_0$; elapsed local Steps do not supply the old absolute counter.

## 5. Every nonempty original raw target at its physical target-block Return

After the earned birth, maintain the true current $(D,s)$. Let $\sigma=G_{D+1}-2-s$. At positive $\sigma$, complete one actual Step, append nothing and set $s\leftarrow s+1$. At zero $\sigma$, complete one Step and interpret its actual Emit using the unequal constants (5) at OLD $D$. Append $0$ or $10$ and update by (4), using old $D$ on each right-hand side. Increment the local count in both cases. Stop at the first completed Return with $|W|\ge m$ and output the first $m$ bits. No further Extent is used. If the first block already covers the target, stop at its first-update cut after stationary classification there.

**Theorem 5.1 (Actual original-tail invariant).** After $i$ completed and classified Steps, some complete actual newly acquired word $w_i$ satisfies

$$
\begin{aligned}
W&=w_i,&p_i&=p_0w_i,&d_i&=d_0+|w_i|,\\
N_{p_i}&=N_{p_0}+\sum_{j<|w_i|}G_{d_0+j}(w_i)_j,&n_i&=r_0+i,\\
\text{actual unread endpoint}&=\operatorname{tail}_{|w_i|}(t_0),&
\text{actual current point}&=T^{r_0+i}x.
\end{aligned}
\tag{12}
$$

The original caches match those fields, returned scratch/pending output are empty, and original binding/rights persist. From the first update onward the maintained $(D,s)$ is actual.

**Proof.** The actual handoff is the empty-word base. Before the first update, Lemma 4.1 appends nothing exactly when Next reads nothing and appends exactly the physically acquired first block. Theorem 4.2 gives its true birth. Thereafter positive slack preserves prefix/cursor/tail and advances the sum once. Zero slack physically reads the next block; (5) interprets its actual Emit and (4) gives its child birth. Appending uses the original absolute raw weights, giving the sum in (12). Each Next has exactly one real Advance and its full Return, giving time, denotation and empty pending fields by Lemma 1.1. Queries preserve every source field. These exhaustive cases prove the induction, including forced zeros and all owned side points. No origin, target, provenance member or endpoint is replaced. $\square$

**Theorem 5.2 (Finite exact original target).** For each fixed $m\ge1$, the procedure is finite and outputs exactly $q_m(t_0)$ at the source Return which physically acquires the block containing original-tail position $m-1$.

**Proof.** That finite position lies in a finitely numbered block of the unique parsing. At every reached parent, finitely many read-free Steps reach its finite death clock; the next productive Step reads its next block. Positive child increments preserve the lawful reached domain. Finitely many blocks through the target therefore require finitely many calls, and each initial query/search/comparison is finite by Sections 3–4. By (12), every preceding Return has $|W|<m$ and the target-block Return first has $|W|\ge m$. The output is its correct original prefix. Any needed post-Return classification and literal writing occur while stationary at that same cut. The proof covers all-zero, pure/eventual alternating and every other no11 tail, including the endpoint cases. It never tests an entire infinite tail for alternation or searches its nonexistent first $00$. $\square$

The earned current record $(D,s,i)$ and retained same-source turn support the supplied PAID LiveStep, guarded Peek, genuinely moving Seek and explicit finite Arm/Tick budgets only where that accepting interface is separately installed. These operations consume genuinely earned current data and continuing rights. The proof above itself needs only Step/Extent and local records. It grants no extra endpoint, rewind, whole-point getter, authenticated past or transferable authority.

## 6. Resonance: a legal empty reference and two deep actual death histories

Suppose $b_-,b_+\in B$ satisfy $b_+=b_-+q_0$. Fix this pair, public $q_0,B,P$, programs, frames and source/rights protocol before a proposed receiver. Consider either the original-boundary task or, separately, one fixed raw task $m\ge1$.

**Lemma 6.1 (Finite reference decision and upper floor-cell room).** If a deterministic causal receiver is finite on every legal all-return floor instance, its behavior on one legal empty reference supplies a finite precision set and a finite depth $d\ge1$ with the following property: two initial scalars $b_++q_0\alpha^d$ and $b_++q_0\alpha^{d+1}$ give exactly all the selected reference floor replies.

**Proof.** Use the actual source $x_{\rm ref}=0^\infty$ at original return zero, installed hidden offset $b_-$. This is genuine empty initialization: no old Read or Advance, zero cursor/count, fixed acknowledgement and lawful continuing turn. Its stationary scalar is $b_-+q_0=b_+$. It is an allowed world of the fixed public domain, without depth infinity, zero unit or a limiting environment.

Total finite completion implies a finite prefix ending either in a completed answer before any Step or in issuance of the first Step, whichever happens first. Otherwise it could only continue stationary queries, pauses or local computation and would not finish on this legal world. Keep this entire finite prefix, including all repeated requests, frames, completions, output prefixes, controls and local actions. Its precision set $F$ is finite, possibly empty.

For $n\in F$, let $a_n=\lfloor2^n b_+\rfloor$. The actual floor cell satisfies

$$
a_n2^{-n}\le b_+<(a_n+1)2^{-n}.
$$

Its UPPER room

$$
\rho_n=(a_n+1)2^{-n}-b_+>0
\tag{13}
$$

is strictly positive even when $b_+$ is dyadic and equals the LOWER boundary. No positive lower room or irrational reference is assumed. Let $\rho$ be the minimum of these finitely many positive rooms, or any positive rational if $F$ is empty. Geometric decay gives a finite $d\ge1$ with $q_0\alpha^d<\rho$. Both perturbed scalars are strictly above $b_+$ and strictly below every selected upper wall, hence lie in every selected half-open floor cell. Their entire integers are $a_n$, including integer parts. Fix this $d$ and the already fixed hidden value $b_+$ before both final original initializations. Neither $q_0$, $B$ nor the public program changes. $\square$

For EVERY symbolic integer $d\ge1$, define the following actual family, using the SAME hidden offset $b_+$ in both final worlds:

$$
x_A=0^d10\,0^\infty=Z(G_d),\quad r_A=G_{d+1}-2,\qquad
x_B=0^\infty=Z(0),\quad r_B=G_{d+2}-2.
\tag{14}
$$

Thus $r_B-r_A=G_d$. No depth enumeration or mathematical test is executed.

**Lemma 6.2 (All initialized old returns and the distinct initial targets).** These runs reach actual proper death handoffs with respectively

$$
\begin{array}{c|c|c|c|c|c|c}
& p&d&N&n=s=k&\delta&t_0\\\hline
A&0^d&d&0&r_A&0&10\,0^\infty\\
B&0^{d+1}&d+1&0&r_B&0&0^\infty.
\end{array}
\tag{15}
$$

Their whole current points are equal, their full owned initial boundaries are different, and their original $q_m(t_0)$ differ for every $m\ge1$.

**Proof.** Return zero is the real empty state in each original run. For every $1\le j\le d$ in A and $1\le j\le d+1$ in B, EVERY integer return

$$
G_j-1\le n\le G_{j+1}-2
\tag{16}
$$

has acquired prefix $0^j$, actual cursor/depth $j$, $N=0$, death clock $G_{j+1}-2$, sum $s=n$ and slack $G_{j+1}-2-n$. The first call physically reads zero and Returns at the first birth. At each zero-prefix death the next call actually reads the next zero and Returns at its child birth, after which calls are read-free through its inclusive death. Adjacent intervals (16) leave no missing integer. Induction with Lemma 1.1 proves every displayed old return. In A the one has not yet been read. Every old Emit at its pre-Advance index $i$ is $\operatorname{Low}(i)$ because the acquired prefix still has value zero; their old histories have different lengths and are hidden, not equated. Their whole points at old return $n$ are $Z(G_d+n)$ and $Z(n)$ by finite-core correctness.

Taking the last returns gives (15), with correct actual caches, empty pending fields and original bindings. At handoff,

$$
T^{r_A}Z(G_d)=Z(G_d+r_A)=Z(r_B)=T^{r_B}Z(0)=:Y_d.
\tag{17}
$$

At a death of depth $j$, (3) gives ordered wall labels

$$
\begin{cases}(2-G_j,\,2-G_{j-1}),&j\text{ even},\\
(2-G_{j-1},\,2-G_j),&j\text{ odd}.
\end{cases}
\tag{18}
$$

Indeed subtract $s=G_{j+1}-2$ from $A_j,B_j$ and use the recurrence. The first label owns $\chi_+$ and the second $\chi_-$, including the actual collapse at zero. Applying this at $j=d$ and $d+1$ describes both complete owned boundaries. Their positive arc lengths are $\alpha^d$ and $\alpha^{d+1}$, so the boundaries differ. Their unread tails in (15) differ at position zero and hence in every nonempty prefix. Both handoffs are genuine proper deaths from the original empty initialization. $\square$

**Lemma 6.3 (First actual Step and every future return).** The first post-handoff Step has the same actual public Emit/Advance/Return in both worlds, coalescing their depth, owned boundary and unread tail. Thereafter every finite continuation has equal true scalars and equal complete floor replies at EVERY finite precision, together with equal actual event prefixes.

**Proof.** Both calls start at their own death clocks. A physically Reads the one at original position $d$ and its forced zero at $d+1$, appending $10$. B physically Reads zero at $d+1$, appending $0$. Their first returned fields are

$$
\begin{array}{c|c|c|c|c|c}
&p'&D&N'&n'&k'\\\hline
A&0^d10&d+2&G_d&G_{d+1}-1&G_{d+3}-G_d-2\\
B&0^{d+2}&d+2&0&G_{d+2}-1&G_{d+3}-2.
\end{array}
\tag{19}
$$

Before Advance, A's Emit argument is $G_d+r_A=r_B$, equal to B's $r_B$. Both actually Emit $\operatorname{Low}(r_B)$, then Advance and Return. They have common sum $s=G_{d+2}-1$, common slack $G_{d+1}-1$, unread tail $0^\infty$, whole point $TY_d=Z(r_B+1)$, and birth boundary $\partial(d+2,G_{d+2}-1)$. Its ordered wall labels are $(1-G_d,1)$ for even $d+2$ and $(1,1-G_d)$ for odd $d+2$, with the respective $\chi_+,\chi_-$ ownership. Thus the side roles are included. Different original absolute times and $N$ values are retained.

For every completed local count $h\ge1$, inductively maintain a common $e_h\ge0$, initially $e_1=0$, with

$$
\begin{aligned}
p_{A,h}&=0^d10\,0^{e_h},&p_{B,h}&=0^{d+2+e_h},&D_h&=d+2+e_h,\\
N_{A,h}&=G_d,&N_{B,h}&=0,&s_h&=r_B+h,\\
n_{A,h}&=r_A+h,&n_{B,h}&=r_B+h,&t_{A,h}=t_{B,h}&=0^\infty,\\
k_{A,h}&=G_{D_h+1}-G_d-2,&k_{B,h}&=G_{D_h+1}-2,\\
\delta_h&=G_{D_h+1}-2-r_B-h.
\end{aligned}
\tag{20}
$$

The base is (19). At positive slack both next calls read nothing, Emit $\operatorname{Low}(r_B+h)$, Advance and Return, preserving depth and reducing slack once. At zero slack both actually Read the next zero at their common original cursor $D_h$, append it, preserve $N$, Emit that same Low value, Advance and Return with depth $D_h+1$ and birth slack $G_{D_h}-1$. These are precisely (1) and (4), preserving every offset and the reached nonnegative slack domain. Return empties scratch; original bindings persist. This proves (20) for every finite count, and finite-core correctness gives whole point $Z(r_B+h)$ throughout. The full boundary is the common (3) evaluated at $D_h,s_h$.

Thus local Step $j\ge1$ always gives the same $\operatorname{Emit}(\operatorname{Low}(r_B+j-1))$, Advance, Return. At every returned $h\ge1$ and EVERY finite $n$, the two actual services give the identical entire integer

$$
\left\lfloor2^n(b_++q_0\alpha^{D_h})\right\rfloor,
\tag{21}
$$

with identical prescribed frames and completion. This is equality of true values under one fixed configuration, without selecting matching errors or limiting future precision. $\square$

**Theorem 6.4 (Separate original-boundary and nonempty original-tail nonrecovery).** Under resonance $B\cap(B+q_0)\ne\varnothing$, no deterministic causal receiver is finite and exact on all actual handoffs for the original owned boundary. Separately, for EACH fixed $m\ge1$, none is finite and exact on that domain for $q_m(t_0)$. This already holds for the specified floor program (7).

**Proof.** Suppose such a receiver exists for one selected task. Lemma 6.1 uses its totality on the legal empty reference to choose a finite first-decision prefix, precision set $F$ and depth $d$. Use exactly that depth in (14)–(15), with $b_+$ fixed in both final original installations. Both receivers start in common source-independent state with the same public data, fixed acknowledgement, descriptor literals, valid continuing turn and local zero counts.

Induct along the finite reference prefix. Equal earlier observations force equal next actions and precisions. Each precision lies in $F$, so Lemma 6.1 gives the same entire integer, frame and completion. Local calculations, records, output prefixes, pauses, request counts, modes, possession checks and releases have the same inputs and declared effects.

If the reference completes its answer without a Step, both final worlds complete at the same prefix with the same answer. Lemma 6.2 gives different original boundaries and, separately, different original raw targets, so that selected task is wrong in at least one world. This includes immediate completion and empty $F$.

Otherwise both issue the same first Step. Lemma 6.3 matches every actual public event of that transaction, including an answer made during Emit. After Return its invariant matches every future arbitrarily precise Extent, repetition and actual Step. Induction on complete permitted actions now matches all finite computations, records, wrapper expansions, streamed outputs, modes, permissions, release outcomes, stopping positions and answers. Release ends the turn and supplies no uncounted new observation. Totality on final A supplies a finite answer also in B on the identical history; it cannot be correct on both different selected targets. Noncompletion instead violates totality. These cases exhaust the installed interface.

Every actual service and Read finishes, and every floor reply satisfies (6). Therefore the same impossibility holds for a receiver required correct on all closed-error traces. It does not assert that every specified error selector voluntarily gives these literals. The proof is applied independently to the boundary task and to each supplied $m\ge1$; raw nonrecovery is not inferred merely from boundary nonrecovery. $\square$

Both FINAL witnesses are proper deaths, but the finite first decision was forced using the EMPTY reference. A receiver promised properness need not stop or Step on that excluded reference. This negative proof therefore establishes no proper-only impossibility. That precise premise permits Section 4's proper positive.

**Proposition 6.5 (Stationary failure and the order of quantifiers).** Under resonance no stationary all-return decoder of $(d,b)$ can be finite and exact on every floor instance, despite exact scalar injectivity. The selected final active pair has only decoder-dependent finite initial agreement; its all-precision agreement begins after the first real Step.

**Proof.** A stationary exact decoder must finish on the empty reference. Its finite query set gives the upper room in Lemma 6.1. A sufficiently deep actual zero-prefix cut with hidden $b_+$ gives the same stopping observation and a different $(d,b)$, a contradiction. On a resonant reference the particular Section 3 decoder has $r_n\le0$ at every stage because $b_+\in B$ and $|u-b_+|\le\varepsilon$; its nontermination there is consistent with its stated scope.

For the active pair, the initial true gap is

$$
q_0(\alpha^d-\alpha^{d+1})=q_0\alpha^{d+2}>0.
$$

Choose a finite $n$ with $2^nq_0\alpha^{d+2}>1$. One unit-width half-open floor cell cannot contain two numbers that far apart, so their initial floor integers differ at that precision. No fixed pair is claimed initially equal at all precisions. Lemma 6.3 instead gives equality at all future precisions after its actual first Step. An infinite stationary interrogation is not a finite stopping protocol. $\square$

## 7. The all-return dichotomy, proper promise and changed information

**Theorem 7.1 (Exact finite-public-offset dichotomy).** For fixed public rational $q_0>0$ and finite nonempty $B\subseteq\mathbb Q_{\ge0}$, the following are equivalent:

1. $B\cap(B+q_0)=\varnothing$.
2. One source-independent deterministic causal receiver is finite and exact for the ORIGINAL owned boundary on every actual source, every finite initialized handoff, every hidden $b\in B$ and every trace satisfying (6).
3. For each fixed $m\ge1$, such a receiver is finite and exact for the ORIGINAL $q_m(t_0)$ on that full domain.

The same classification holds for correctness restricted to the specified floor program (7). For arbitrary $B$, including resonant $B$, the corresponding positive statements hold on the public proper-handoff promise. The $m=0$ task always has Proposition 2.1's zero-new-operation solution.

**Proof.** Under condition 1, Corollary 3.2 puts every actual original scalar outside $B$, including depth zero. Theorem 3.4 gives $d_0,b$ finitely on every error trace. Theorem 4.2 proves the boundary positive, treating an empty boundary separately. Theorems 5.1–5.2 prove each nonempty raw positive at the actual target-block Return. These are one fixed algorithm with the public finite request and data, independent of the hidden source, depth, slack or error trace. Under a proper promise Corollary 3.2 gives the same outside-$B$ premise for every alphabet, so these proofs apply without condition 1. Necessity on the all-return domain is Theorem 6.4, separately for each task, already on the fixed floor program. That program is a permitted trace generator for (6), and the positive handles it as well, giving the stated backend-specific iff. The zero case is Proposition 2.1. $\square$

For the concrete public example $q_0=1$, $B=\{0,1\}$, the empty reference has hidden $b_-=0$ and scalar one. At each selected $n$ its ENTIRE reply is $2^n$ and its cell is $[1,1+2^{-n})$. Choose $d$ with $\alpha^d$ below the finite minimum upper room. The two actual final death histories (14) with common hidden $b_+=1$ match all selected full integers, then coalesce as proved. Their original boundaries and every nonempty raw prefix differ. Under a proper promise, each scalar $b+\alpha^d$ is irrational and outside $\{0,1\}$, so the positive applies on every closed-error trace. This is an unexecuted specialization, not a numerical test.

A singleton alphabet is nonresonant because $q_0>0$. A publicly supplied finite depth bound makes the entire candidate list finite, and injectivity plus its finite positive separation proves stationary every-error recovery even under resonance. A publicly known empty cut instead gives the initialized event decoder directly and immediate whole-circle boundary. Neither disclosure is implicit in a private index, finite cardinality or a mere possible provenance member.

If the exact offset $b$ is independently disclosed, it also supplies a paid fixed-unit adapter. Request affine precision $n+2$, subtract $b$ rationally, project to nonnegative values, then round $2^n$ times that value to a nearest nonnegative integer with fixed tie rule. Projection cannot enlarge the distance from the true nonnegative $q_0\alpha^d$. Rounding adds at most $2^{-n-1}$, so total decoded error is at most

$$
2^{-n-2}+2^{-n-1}=3\,2^{-n-2}<2^{-n}.
$$

Forward every real Step and full event unchanged, charging queries, frames and arithmetic. This proves the adapter's scope, rather than assuming hidden knowledge of $b$. Extra authenticated old records or an added Wall/private exporter change the observation class and require their own actual installation and correspondence.

## 8. Optional independent random tapes with a common law

**Theorem 8.1 (Almost-sure exact finite success still fails under resonance).** Fix public $q_0,B,P$ and, for a raw task, one fixed $m\ge1$. Suppose the receiver additionally uses ONE probability space $(\Omega,\mathcal F,\mu)$ and ONE world-independent random tape law in every hidden source, configuration and handoff world of this public task. The law is independent of source, selected $b$, handoff, old history and old advice; no such advice is otherwise supplied. Tape access is measurable and causal: a next access/action depends only on public state, earlier permitted observations and already accessed tape data. Finite completion uses finitely many accesses/actions. For each actual world require its event of finite completion with the exact fixed target to be measurable and have measure one. Under these hypotheses resonance forbids an all-return receiver for the original boundary and, separately, each fixed nonempty original raw target.

**Proof.** BEFORE fixing any tape, take the countable family consisting of the one legal empty reference with $b_-$ and BOTH actual worlds A$(d)$, B$(d)$ of (14) with $b_+$ for EVERY integer $d\ge1$. For each world $W$, its measurable exact-finite success event $S_W$ has measure one under the SAME $\mu$. The complement of their countable intersection is a countable union of null sets, so that intersection has measure one and is nonempty.

Fix a tape in this intersection. Causal access gives a deterministic receiver that succeeds finitely on the reference AND every deep pair. Its finite reference first decision supplies a precision set and positive upper room, selecting some $d$ from that already included family. Equal histories force equal tape accesses and values as well as equal public actions. The entire no-Step/first-Step proof of Theorem 6.4 now applies to that selected pair, contradicting success on both. Repeat for each fixed $m$ rather than selecting a task after fixing the success family. The deterministic positive uses no tape and is trivially an almost-sure positive on its stated domains. $\square$

A common law and the full countable family before fixing tape are essential. Success only on the reference does not guarantee success on a subsequently selected pair. No bounded-error, statistical, expected-cost, empirical-noise, ML/NN or concentration statement follows from this zero-error extension.

## 9. Exact source counts, inherited Advance bounds and completion timing

For a positive run let $N_s$ be the successful original stationary precision. Its initial requests are exactly $1,\ldots,N_s$. A proper boundary request completes $h=t_1=\delta_0+1$ Steps, physically reads exactly $g_1$ new bits and makes

$$
Q_{\rm new}=N_s+t_1
\tag{22}
$$

new Extents, each with its own service completion. Its largest new precision is $\max\{N_s,n_c\}$. A boundary-only decoded empty cut instead makes $Q_{\rm new}=N_s$, with zero new Step/Read/Emit/Advance/producer-Return and no $n_c$. Each $m\ge1$ raw task, including empty initialization with $t_1=1$, has (22) and no later Extent. The zero-target task makes none of these new operations.

In the ORIGINAL actual tail let $w$ contain all complete blocks before the block containing position $m-1$. Put

$$
e=|w|,\qquad g\in\{1,2\},\qquad e<m\le e+g,\qquad
V=\sum_{j<e}G_{d_0+j}w_j.
$$

**Proposition 9.1 (Exact target clocks and raw Reads).** For every $m\ge1$ positive run, the exact numbers of new Steps, Emits, Advances and producer Returns are all

$$
h_m(t_0)=G_{d_0+e+1}-1-s_0-V\ge1.
\tag{23}
$$

The exact new raw Read count and raw bit payload are $e+g\in\{m,m+1\}$. At the SAME actual $p_0,r_0,b$, the all-tail, all-error worst Advance count is

$$
B_m=G_{d_0+m}-1-s_0,
\tag{24}
$$

attained by the all-zero tail. Empty initialization separately has $B_m=G_m-1$.

**Proof.** The actual target parent is $a=p_0w$, with $N_a=N_{p_0}+V$ and death clock

$$
k_a=G_{d_0+e+1}-2-N_{p_0}-V.
$$

The target call starts exactly at this clock and Returns at $k_a+1$. Subtracting the SAME actual $r_0$ gives (23). Positive child-clock increments give $k_a\ge k_{p_0}\ge r_0$, hence positivity. Theorem 5.2 stops precisely at this cut, and each real call contributes one complete triple, including read-free calls.

The actually acquired word is $w$ plus its complete target block, so its $e+g$ physical bits were each read once. There are $m+1$ exactly when the target is the first one of $10$. At its second zero there are $m$ Reads and the forced zero was actually read. Since $e\le m-1$ and $V\ge0$, (23) is at most (24). Every legal tail appends to the same actual $p_0$ and reaches the same $r_0$. The all-zero tail has $e=m-1,V=0$ and attains equality. Empty initialization uses $k_\varnothing=G_1-2=0$, giving the displayed formula without a negative index. All inclusive births/deaths remain in the proof. $\square$

These clock identities are supplied NORMAL/TARGET results, attained here through the finite-offset bridge. They are not new clock discoveries.

**Proposition 9.2 (Scoped per-selected-trace Advance optimum).** On either positive domain, every deterministic base Step/Extent decoder correct on all legal sources and all traces satisfying (6) pays at least $h_m(t_0)$ new Advances on EACH selected actual trace if the answer is Return-complete. The same bound holds for correctness restricted to the specified floor backend (7). Thus this positive rule attains the inherited Advance optimum and fixed-cut worst value $B_m$ in these classes.

**Proof.** Keep the SAME actual $p_0,r_0,b,q_0,B$ and the selected valid error trace. Choose an opposite-target legal tail as follows:

$$
\begin{array}{c|c|c}
\text{actual target position}&e&t_*\\\hline
0\text{ block}&m-1&w10\,0^\infty\\
10\text{ first one}&m-1&w0^\infty\\
10\text{ second zero}&m-2&w0\,10\,0^\infty.
\end{array}
\tag{25}
$$

All concatenations are legal complete blocks. Their requested prefixes differ; in the last row position $e+1=m-1$ becomes one, so the forced-zero target is genuinely changed. Actual attainment gives the same original cut on both initialized sources. They then really acquire the same $w$ before the target transaction.

Through $h_m-1=k_a-r_0$ completed Advances, their actual acquired prefix, depth, absolute count, $N$, clocks, caches, empty pending fields, public controls, installed rights and earlier events are identical. For any adaptive precision, the allowed complete reply integers are the same because true $d,b,q_0$ agree. Copy the selected valid integer, entire frame and completion. Each closed inequality is still valid, and the finite copied prefix extends to a full permitted trace, for example by later floor replies. Equal complete histories force equal local actions, records, requests and stopping choices. The first source distinction is the target transaction's actual Emit; no Extent is available inside that unfinished transaction.

A Return-complete answer with fewer than $h_m$ Advances lies wholly in this paired prefix. If it had issued the target transaction and charged it through Return, its Advance would already be counted. Hence such an answer gives the same result on different targets, contradicting robust correctness. The selected original trace was arbitrary, proving the per-trace bound. For (7), equal depth, offset and precision give the same ACTUAL full integer/frame, so the comparison belongs to that same backend without changing selectors. Proposition 9.1 supplies the matching upper bound and all-zero worst value. $\square$

For richer services this lower-bound transfer is conditional on matching ALL of their outputs, guards, modes, budgets, rights and successors from the same acquired fields. Genuine acquired-record LiveStep is a real Next; guarded Peek uses the same finite representative; every internal Seek/Tick/acquisition Step is counted. Actually installed acquired-field exports/archives give their same full fields. No arbitrary private exporter, Wall or source-advice service is implicitly added. These are TARGET Section 6's complete-response premises, not consequences of an operation's name.

A numerical error bound alone cannot prove an arbitrary fixed selector source-blind. A mathematical oracle allowed an unread advice bit can choose between $\lfloor y\rfloor$ and $\lfloor y\rfloor+1$, $y=2^n(b+q_0\alpha^d)$, to make the integer's parity equal that bit. Both integers are nonnegative and satisfy distance at most one from $y$, including integer endpoints. Thus (6) alone allows this advice choice. Obtaining the unread bit requires a separate access/configuration bridge; that oracle is not the installed no-Read floor service. Robust all-error correctness or an actual same-backend pairing proof supplies the required quantifier.

If an answer may finish during the target Emit, pre-target pairing generally forces only $h_m-1$ PRIOR Advances. The order is Read, Emit, Advance, Return; observing Emit does not imply that call's Advance has happened. A matching early upper bound additionally needs a genuinely known boundary and an installed synchronous finite Emit handler that finishes paid output before producer Advance. Event order alone does not provide this schedule. The present rule queries after Return through its first update and guarantees Return-complete $h_m$. An early output still leaves the issued transaction's Advance/Return debt. Section 6's negative matches intermediate events too.

For the negative family, final A pays exactly $r_A=G_{d+1}-2$ old Next/Emit/Advance/producer-Returns and $d$ old raw Reads/bits; B pays $r_B=G_{d+2}-2$ old triples and $d+1$ raw bits. Under PAID's two-bit event-symbol convention these are $6r_A$ and $6r_B$ event payload bits before framing. A no-Step answer has zero NEW source operations, although its stationary queries remain paid. In the moving branch the first new call pays two versus one raw Reads. At every completed $h\ge1$ in (20), their new raw counts are $2+e_h$ and $1+e_h$, and both have $h$ new triples and $6h$ event payload bits. Initialized cursors are both $D_h$, while original absolute counts remain $r_A+h$ and $r_B+h$. Each actual query and local computation/output is charged separately. The hypothetical reference is a legal world used in a totality proof, not an executed auxiliary run or a free installed sensor.

## 10. Complete component work and simultaneous digital space

Use a fixed finite number of sequential binary work tapes, paying each cell read, write or move. Grade-school finite integer arithmetic, tape scans, copies, framing, return positioning and scratch clearing are charged. There is no unit-cost arbitrary integer, infinite real, response table or unbounded-address primitive.

For the specified floor realization and specified positive receiver charge one finite initialized segment: installation, $r$ old driver Steps, $h$ receiver Steps and EVERY actual Extent in that segment. Old driver queries are allowed when permitted by the protocol. Define the following actual finite quantities.

- $k=|B|$; $L_q$ is the encoded rational unit length, $L_B$ the FULL public rational-list length, and $L_j$ the actual hidden-index length. The selected offset cache and any constant-count list copies are real stored data. $P$ is fixed installed digital program/convention length and $c$ total descriptor/control width.
- $d_{\max}$ is maximum actual acquired depth in the whole segment. $Q_{\rm new}$ is the literal receiver count in (22) or its stated empty cases. $Q_{\rm tot}$ counts ALL segment Extents, including old driver queries; it equals $Q_{\rm new}$ for Next-only old histories. $N_{\max}$ is the largest precision over ALL these queries, or zero if none.
- $D_{\max}$ is the largest receiver stationary cutoff $D_n$ actually reached, or zero if none. With the sum over actually attempted positive-$r_n$ stationary stages, put $K_{\rm scan}=k\sum(D_n+1)$.
- Fix the following digital framing/accounting convention. $I$ is the actual total number of bits read on installation/request/control input channels: full public rational encodings, hidden-index installation, $m$ where applicable, old and receiver command tags, precision fields and descriptors. Installation data are charged once as channel input; their preparation/validation and copies have the work terms below. Driver COMMAND ACQUISITION is included as these input scans, while arbitrary driver computation remains an additional component. Raw physical Read counts/payload are independent coordinates; any actual digital copying also pays its chosen input/output actions.
- $B_{\rm out}$ is the actual total bits written on the chosen digital result/service/event/control channels: complete integer parts, canonical frames, query completions, producer events, acknowledgements, actually installed refusals and final outputs. Output is streamed for the following space bound; no retained archive is silently included.

Let $\ell(t)=1+\lfloor\log_2(t+1)\rfloor$ be the supplied finite binary-length upper bound. Put

$$
\Omega=d_{\max}+D_{\max}+L_q+L_B+L_j+N_{\max}+\ell(m)+c+32,
\tag{26}
$$

omitting $\ell(m)$ for a boundary-only task.

**Theorem 10.1 (Conservative digital upper bound).** For this producer, floor service and positive receiver, with streamed output and discarded trace, a valid conservative bound is

$$
\begin{aligned}
C_{\rm digital}
&=O\!\left(P+L_q+L_B+L_j+I+
(r+h+d_{\max}+Q_{\rm tot}+K_{\rm scan}+1)\Omega^4+B_{\rm out}\right),\\
S_{\rm digital,peak}&=O(P+\Omega).
\end{aligned}
\tag{27}
$$

The space is the SUM of simultaneously present producer, floor-service and specified-receiver digital states. This is a scoped symbolic upper bound, without an optimality or measured-runtime assertion.

**Proof.** A coefficient pair representing $\alpha^e$ evolves by a fixed bounded-coefficient linear recurrence, so its bit lengths are $O(e+1)$. Every reached index is bounded by $d_{\max}$ or $D_{\max}$ up to the fixed additive classifier constant. Clearing rational/dyadic denominators adds at most the charged encoding and precision lengths; every operand has $O(\Omega)$ bits. Full reply integers satisfy

$$
a\le2^n(\max B+q_0)+1,
$$

so their bit lengths, including integer parts, are $O(N_{\max}+L_B+L_q+1)$. Quadratic square-sign tests and grade-school multiplication/division cost $O(\Omega^2)$ work and linear reused scratch. Coefficient generation uses at most $O(\Omega)$ iterations. A rational coefficient bracket for a floor target has endpoints AND width of $O(\Omega)$ bits. Bisection thus uses $O(\Omega)$ comparisons, rather than a number exponential in that width. Regeneration, bracket comparisons, scans and framing fit the conservative fourth power per query or listed loop.

Candidate examination performs exactly $k\sum D_n$ pair tests on the all-return domain and exactly $k\sum \max(D_n-1,0)$ pair tests on the proper-only domain, with both sums over actually attempted positive-$r_n$ stationary stages. In either domain it performs at most $k\sum D_n$ pair tests. A least-cutoff search from zero uses at most $\sum(D_n+1)$ tests over those same stages. Their COMBINED number is at most $2K_{\rm scan}$ for $k\ge1$; each separately is bounded by $K_{\rm scan}$. The constant two is absorbed in (27). Computing the minimum distance from ALL $B$ at each stationary stage adds at most $k$ comparisons per stage, including skipped stages; $k\le L_B\le\Omega$, so these fit the $Q_{\rm tot}\Omega^4$ term. Pairwise exact rational validation/deduplication on the paid encodings fits the preparation fourth-power term. These are finite tape scans, not unit-cost catalogue operations.

The $n_c$ precision search has finite iterations bounded by its eventual queried precision and indices $O(d_{\max}+1)$; it and the three-value preparation fit the precision/query/depth terms. Actual absolute count obeys $n\le k_p<G_{d_{\max}+1}$, and $G_j\le2^{j+1}$. Hence original counters, clocks and finite Low representatives have $O(d_{\max}+1)$ bits. Their finite greedy Zeckendorf arithmetic fits the same work bound. Each actual raw bit and Step/control frame is processed with paid scans, updates and clearing.

The stationary loops stream one coefficient pair, one candidate and a singleton count saturated at two, then finish the complete scan. They need no full scale table. The receiver's new query count is at most $N_s+t_1$, with $N_s\le N_{\max}$ and $t_1\le G_{d_0-1}$ on a proper cut, or one at an empty raw cut. Thus its counters also fit the displayed width. $Q_{\rm tot}$ is an accounting tally, not a required stored global counter: the stateless floor-query handler can complete each old request without storing the number of previous driver queries. Any old driver's cumulative counters/workspace belong to the separate driver component. An implementation retaining additional cumulative fields must add their actual sizes.

The actual new word $W$ has at most $d_{\max}$ bits, with $m\le d_{\max}$ when a nonempty raw task finishes. Producer prefix/caches, constant-count public-value copies, hidden index and selected-offset cache, receiver word/coordinates/local counters/control, descriptors and a constant number of rational/quadratic/floor-bracket registers coexist in $O(P+\Omega)$ bits. Scratch is reused and cleared; past events/replies are discarded. All scans, copies, positioning, installation preparation and actual I/O are included in (27). This proves the simultaneous digital-trio bound without transferring PAID's fixed-unit constants or UNIT's qualitative costs. $\square$

For a WHOLE supplied system add actual driver program/state/computation, non-digital installation/reference/binding/rights work, source provisioning $\iota_x$, generation/delivery $\gamma_x(d_{\max})$, raw/control transport and physical backend work. Arbitrary driver computation is not bounded by $I$. For another permitted error mechanism replace the floor-service bound by its actual service work/storage, including any additional mechanism state. An arbitrary alleged negative receiver has its actual finite local work, workspace, records and output added; observation equality supplies no polynomial bound on that code and no equality of private costs across worlds.

The full storage quantity is the maximum over time of the SUM of all coexisting producer, service, receiver, driver, source/backend, error-mechanism and retained-output/archive states. The digital-trio term bounds only its own simultaneous sum. One can add an upper bound for the other simultaneous sum, or conservatively the sum of those components' peaks; isolated peaks never justify dropping a component or equating worlds' storage. Source/backend storage is the actual $\sigma_x(d_{\max})$. Retained outputs or traces add their actual lengths and writing/copy costs.

Every reached cutoff, precision, operand, driver prefix and finite service is finite. There is no parameter-independent bound over hidden unbounded depths on queries, precision, whole frames, work, space or latency. The negative depth choice does not lengthen the already fixed public $b_+$ encoding, but all of its old driver calls and raw acquisition remain paid. No sequential contract supplies a finite generator or finite-cost infinite tape for every $x\in K$. Equality at every finite coordinate of a common infinite future is neither one finite completion of that future nor bounded output, constant storage or a uniform physical deadline. Advance optimality does not assert optimal query count, precision, raw representation, bit work, memory or physical cost.

## 11. Exact mathematical credit and the narrower increment

The named texts are conditional mathematical suppliers, each with its own observation, target and implementation scope. Their prior results retain those premises.

| Supplier | Reused results and exact comparison |
| --- | --- |
| [PAID, Sections 1–12][PAID] | Source-independent empty initialization, actual sequential acquisition, correct productive Next, physical forced-zero Reads, exact original-tail resumption, temporal/current-response guard, inclusive clocks, full owned-image coordinates and finite provenance. These supply Section 1 and the physical bridge, rather than new Fibonacci geometry or a new native-controller result. |
| [PAID, Sections 13–21][PAID] | Calibrated ordered Wall recovery and installed Park/Wall/Arm, unknown fixed-unit three-ratio classification, two-update full-lifetime recovery, earned LiveStep, guarded current DATA/Peek and paid moving Seek. Its known-unit stationary isolation is prior supply. Full physical calibration and persistent rights remain separate premises; its fixed-unit estimates are not the estimates in (27). |
| [PAID, Sections 22–30][PAID] | Unknown rational affine $b+q\alpha^d$, reliable first detected descent and its calibrated NEXT complete lifetime give attained-boundary recovery (Theorem 24.1) and live use (Corollary 24.2). Theorem 29.1 ALREADY proves deterministic initial-boundary nonrecovery for the weaker public-information domain with arbitrary hidden rational $q,b$, even on its fixed floor backend and actual proper deaths. Its legal proper reference forces either a no-Step completion or a first Step. A decoder-dependent common configuration makes the selected initial complete integers agree; the two deaths then really merge at one common child, so every future precision/event agrees. Theorem 30.1 preserves the attained/live positives. Historical open wording in Definition 24.3 does not supersede this final negative. Here $q_0$ and ALL finite offset VALUES are public: the new theorem classifies this stronger public input and does not claim PAID lacked its broad negative. |
| *Finite public rational unit catalogues and exact hidden-cut acquisition*, Sections 1–11 | The CURRENT finite-UNIT manuscript supplies global infinite-depth tail exclusion followed by complete finite isolation on EVERY error trace, its first-update boundary bridge, actual target invariant/counts and careful same-backend/robust/timing distinctions. Its current comparison explicitly credits PAID Sections 22–30 and Theorem 29.1, including both decision branches and preserved reached/live results. UNIT uses positive rational multiplicative scales, irrational power RATIOS and the single accumulation point zero; it even allows arbitrary finite-catalogue unit jumps BETWEEN Steps. Here the unit and offset are fixed, but additive separation requires irrational DIFFERENCES including zero depth and distance from EVERY member of $B$. Its algebraic-catalogue collision criterion is stationary only and does not by itself prove an active negative. The present result is an additive finite-union classification, not a multiplicative relabeling or a revision of UNIT's current credit. |
| [NORMAL, Sections 1–10][NORMAL] | Fixed-offset actual common-tail continuation, whole-word equality including side points, restriction injectivity, tail bijection to the full owned set, each-point finite provenance, first real branch-Emit separation, known-boundary event inverse and target clocks $h_m,B_m$. These are used with the true parameters earned here. |
| [NORMAL, Sections 11–17][NORMAL] | All initialized histories over each complete point, unbounded possible paid depths, finite causal event-only entrance/stopping-boundary nonrecovery, a natural-core fixed pair with permanently different boundaries and necessary unbounded supplementary-record range. Those event-only/projection results cannot substitute for matching a new Extent. Section 6 separately matches every full Extent, frame, event and control outcome. The current point, paid frontier and actual history remain distinct. |
| [TARGET, Sections 1–10][TARGET] | Fixed-unit direct original-tail acquisition, fresh-cut closed-error classification, full absolute-position raw/source invariant, physical target-block Return, $h_m,B_m$ and $m$ or $m+1$ Reads. Its three opposite-target cases, complete installed-operation pairing, robust-versus-same-backend quantifiers, unread-advice warning and Return-versus-synchronous-Emit distinction are consumed in Sections 5 and 9. Neither its clock nor its Advance lower-bound principle is new here. The raw negative in Section 6 independently separates original tails, rather than importing a boundary negative. |
| [CAPPED, Sections 1–11][CAPPED] | A fixed finite precision cap permits actual floor zero cells, a fixed different-target pair with equal whole current point and complete infinite allowed observations, explicit small-unit proper DEATH witnesses, and late proper witnesses for EVERY fixed unit. Those latter cuts need not both be deaths. Here no cap is imposed: initial agreement depends on a decoder's finite prefix and all-precision equality begins only after actual coalescence. The capped permanent-pair assertion is not transferred to an initial unbounded-precision cut. Known-boundary and unbounded-precision positives remain intact. |
| [DRIFT, Sections 1–14][DRIFT] | Fresh separated-interval classification below a SUPPLIED subcritical factor, actual common-schedule target-cost transfer, and the critical one-public-parity-program/common-hidden-configuration causal obstruction with a legal proper reference, finite floor margins and physical first-Step coalescence. Its finite hidden range does not supply exact public values. Here $q_0,b$ never drift and there is no parity schedule. A same-cut-tail argument forces a RAW decoder to Step, but cannot force a BOUNDARY decoder to Step; Section 6 explicitly retains the no-Step branch. No drift threshold is reclassified. |

The closer proposal history involving a positive-width interval of possible offsets has a different public domain. A freely chosen rational offset inside a finite reference cell and a legal proper reference can support that interval argument. A fixed finite $B$ need not permit such a choice. Its proper negative is therefore not an argument against Theorem 7.1's proper positive. The interval and older-UNIT comparisons reported in the proposal describe those supplied historical inputs; no absent older text is asserted identical to the current complete UNIT manuscript.

Quadratic conjugation, exact integer signs, geometric decay, finite separation, complete floor cells, causal same-response induction and factor-through-observation contradictions are standard intermediate tools. The narrower repository-relative increment is their concrete conjunction here: irrational differences at distinct nonnegative depths; effective isolation in a finite union of ADDITIVE chains away from its full accumulation alphabet; the exact all-return resonance iff and unconditional proper positive; and the legal EMPTY-reference/deep SAME-offset actual coalescence obstruction. Existing clocks, owned geometry, event inverses, exact target counts and live laws are credited applications. This is a conditional synthesis, without external literature exhaustion or worldwide-priority claims.

## 12. Independent meanings, information limits and remaining bridges

Space is the actual infinite point $T^{r_0+i}x$. Time is the actual Emit/Advance/Return order; the receiver has only the observed post-handoff suffix and its local completed counts. Boundary is the actual paid-frontier compatible region with its oriented walls and included concrete lifts; the empty frontier is the whole circle. Memory is the receiver's ACTUALLY retained public rational values, finite word/control/coordinate records and continuing binding/right. Unread tails, discarded events and a mathematical past are not free memory. These meanings do not assign each view a copy of the whole history.

The positive arrows use actual operations: finite public offset VALUES and stationary replies give exact depth/offset; the first physically acquired block and its measured local Steps give original and attained owned coordinates; the earned current record and real Emits maintain that boundary; the physical target-block Return supplies the original finite unread-tail target. Guarded finite current DATA and a genuinely moving Seek retain PAID's distinct attained-cut meaning and actual costs. These arrows do not identify the four full-view kernels or construct an effective infinite inverse.

Rational $q_0$ and offsets are essential to the difference/noncollision and proper outside-$B$ proofs given here. General real or algebraic parameters may create collisions or alter accumulation/effectivity conditions and require a new classification and representation contract. No transfer to them is asserted. Public depth bounds, exact-offset disclosure, known empty initialization, old authenticated records and complete-value publication are substantive different information inputs. Merely processing an insufficient old observation cannot add the distinctions it discarded.

Neither the stationary nor active procedure authenticates the actual old $p_0,r_0$, selects the true historical member, reconstructs the old archive or whole unknown source/current point, supplies physical wall phases in an unknown reference, rewinds the source, or creates/copies transferable authority. The same actual endpoint continues at its own precise unread tail. A possible history or printed descriptor is not a new right or a certified old counter. Under resonance both final counterexamples being proper cannot legalize the excluded empty reference for a proper-only promise.

All results assume the exact no11 carrier, endpoint-inclusive successor, actual initialized producer, stable $b$ and depth throughout each stationary search, fixed unit, known error resolution, same actual measured region, full nonnegative finite frames, arbitrary finite precision, productive reached services, exclusive serial control and persistent rights. Capped or saturated/modular responses, changing offset/unit during refinement, unknown error bounds, unseen concurrent Advance, non-Advance mutation, revocation, wrong regions, timing/identity/advice/padding fields and other source-dependent initial memory require other proofs. A failure of the present proof after changing premises is not a general impossibility theorem for those models.

The digital floor specification realizes only the declared finite rational abstract service. An independent physical affine sensor, proof of same-region calibration and error guarantees, arbitrary-real generators and provision of every infinite $x\in K$ remain separate implementation bridges. Native seed/payload/Stop controllers, original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization, arbitrary interior-cut and complete original-response tasks retain their own source, control, full-response and authority obligations. This text does not supply those conversions or settle general independent four-view recovery.

No physical impossibility, empirical ML/NN/noise claim, bounded-error statistical theorem, universal information/resource minimum, uniform physical deadline, constant-storage infinite execution, external priority, new axiom or Lean/D5/Blueprint/Reg/kernel certification is established. Optional almost-sure exact success has only Section 8's common-law scope. Later reached/live recovery remains positive under its original conditions even when initial recovery fails. A finite contribution at this interface does not complete the sustained general research objective.

[PAID]: RECURSIVE_RELATIONAL_OBSERVATION_PAID_ZECKENDORF_CURRENT_RETURN.md
[NORMAL]: RECURSIVE_RELATIONAL_OBSERVATION_EXACT_CURRENT_BOUNDARY_PROVENANCE.md
[TARGET]: RECURSIVE_RELATIONAL_OBSERVATION_UNCALIBRATED_TARGET_ACQUISITION.md
[CAPPED]: RECURSIVE_RELATIONAL_OBSERVATION_CAPPED_PRECISION_PERMANENT_BLINDNESS.md
[DRIFT]: RECURSIVE_RELATIONAL_OBSERVATION_BOUNDED_UNIT_DRIFT_IDENTIFIABILITY.md

## 追加锚（本行以下为增补区）

# Finite public rational unit catalogues and exact hidden-cut acquisition

A finite public catalogue of exact positive rational unit values supplies a stationary depth decoder even when the actual depth is unbounded and the unit may jump arbitrarily between producer Steps. The decoder excludes the entire infinite depth tail using a positive readout lower bound, then isolates one member of a finite union of scaled depth chains. Every permitted closed-error trace terminates. Combining that bridge with the actual producer clocks recovers the initial boundary after the first real block acquisition and obtains every finite initial unread-tail target at its physical target-block Return.

These are ordinary, unexecuted conditional symbolic mathematical arguments. The additional content is the finite-catalogue interface bridge and its one-update consequence. The clocks, owned boundary coordinates, event decoder, target costs and causal comparison methods are supplied results. No new Lean/kernel certification, executed implementation, external priority or universal resource optimum is asserted.

## 1. Actual producer and initial target

**Definition 1.1 (Carrier and supplied execution).** All indices are nonnegative integers, and raw positions run from low to high. Put

$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,
\qquad \alpha=(\sqrt5-1)/2,
$$

$$
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ for every }j\ge0\},
\qquad \mathcal B=\{0,10\}^{<\omega}.
$$

Thus $0<\alpha<1$ and $\alpha^2+\alpha=1$. Each infinite word has a unique parsing into complete blocks $0$ and $10$: a one takes its promised following zero. A nonempty complete prefix ends in zero and can be followed by every $t\in K$.

Write $Z(A)$ for the zero-padded finite Zeckendorf word of $A\ge0$, $f(x)=x_0$, $q_m(x)=(x_0,\ldots,x_{m-1})$ and $\operatorname{Low}(A)=f(Z(A))$. The endpoint-inclusive arithmetic successor $T$ clears positions below the first adjacent $00$, writes one at that pair's first position, and retains higher digits; a word with no $00$ is sent to $Z(0)$. Both pure alternating words belong to this domain. On the finite core, $T^hZ(A)=Z(A+h)$. This successor is distinct from positional deletion.

We use exactly [PAID, Definitions 1.2, 2.2 and Theorems 3.1–3.2][PAID]. Its sequential raw endpoint holds one actual fixed $x\in K$. A Read physically delivers its next bit and advances the raw cursor once. Every reached Read finishes and is paid, including a zero forced by a preceding one. Source-independent initialization installs the finite code, bindings and rights, starts with empty acquired prefix and source count zero, and gives a fixed acknowledgement without a Read or Advance.

For $p\in\mathcal B$ put

$$
d=|p|,\quad C_p=\{pt:t\in K\},\quad
N_p=\sum_{j<d}G_jp_j,\quad
M_p=G_{d+1}-N_p,\quad k_p=M_p-2.
\tag{1}
$$

The empty return has $p=\varnothing,n=d=0,k_p=0$. For a nonempty actual acquired prefix, its inclusive lifetime is

$$
b_p\le n\le k_p,\qquad
b_p+N_p=G_d-1,\qquad k_p+N_p=G_{d+1}-2.
\tag{2}
$$

Every $x\in C_p$ actually reaches every such return with exactly this acquired prefix. These are execution facts, rather than consistency tests for hypothetical caches.

One Step is one actual producer Next. At $n<k_p$ it reads nothing. At $n=k_p$ it reads its next complete block, using one physical Read for $0$ or two for $10$. With the resulting prefix $p'$ it calculates $\operatorname{Low}(N_{p'}+n)$ and actually performs Emit, Advance, Return, in this order. Advance increments the original absolute count once. The returned current point is $T^{n+1}x$; scratch and pending output are empty. The same endpoint remains exactly at its new unread raw tail. In particular,

$$
k_{p0}=k_p+G_d,\qquad k_{p10}=k_p+G_{d+1},
\tag{3}
$$

and appending $10$ at absolute raw position $d$ adds $G_d$ to $N_p$. Every reached finite transaction finishes. Queries, pauses and local computation cause no autonomous Advance. No infinite search for the raw source's first $00$ implements this producer.

**Definition 1.2 (Handoff and fixed initial-tail target).** A finite actual driver history ends at any original Return $(p_0,r_0)$ and transfers an already installed persistent exclusive Step/Extent turn. This includes return zero, births and deaths. It preserves the same producer, raw cursor, binding and source; the acknowledgement is fixed. The driver cannot concurrently continue. Release has only its declared control effect and supplies no uncounted driver motion.

Write

$$
x=p_0t,\qquad d_0=|p_0|,\qquad s_0=N_{p_0}+r_0.
\tag{4}
$$

The receiver gets $m\ge0$, the public data of Section 2, common programs and framing conventions, and actual continuing invocation rights. It does not receive $p_0,r_0,d_0,s_0$, their bounds, old events or command counts, private registers, raw responses or Read counts, source identity, wall phases, timing, work/storage observations, or tail-dependent old memory. Its local completed-Step count starts at zero. Public code and every genuinely public control datum are inspectable and belong to the observation.

The target is permanently $q_m(t)$ of this initial raw unread tail. It does not change when the current point becomes $T^{r_0+i}x$. The complete observation retains every chosen precision, entire integer reply and canonical frame, actual Emit values and Emit/Advance/Return order, local completion counts, and declared modes, possession outcomes and records derived from these data. Finite local computation, pauses and wrappers of installed operations are allowed. Naming an uninstalled operation creates neither that operation nor an informative refusal.

**Proposition 1.3 (Empty target).** For $m=0$, output the empty word immediately at the handoff. Make no Extent request, Step, Read, Emit, Advance or new producer Return. New source cost and query count are zero.

**Proof.** The first zero digits of every $t$ form the same empty word. Their output requires no source information or operation. The already completed handoff remains the current cut; local output completion is not a new producer Return. Any initialization, handoff or local output framing has its own cost and is not a new source operation. No calibration is required. $\square$

All target clocks, nontrivial target and lower-bound theorems below use $m\ge1$. We do not extend their formulas to $m=0$. Stationary depth acquisition is a separate task, and our target algorithm invokes it only after the empty-target case has been discharged.

## 2. Public values and a stable-cut measurement contract

**Definition 2.1 (Finite rational value catalogue).** The public input is a finite nonempty list of explicitly encoded positive rational numbers. Rational equality removes duplicate values; write the resulting set as $C$, with $k=|C|\ge1$. Complete numerator and positive-denominator encodings are public finite data. In particular

$$
c_{\min}=\min C>0,\qquad c_{\max}=\max C
\tag{5}
$$

are legitimately available. No bound on the hidden depth is supplied.

At every original returned count $n$, including driver returns, the actual unit $q(n)$ belongs to this same $C$. It is fixed during all queries and pauses at that cut. Only an actual Step can change it to the next value, including a read-free Step and every internal Next in a wrapper. Consecutive values may be any two elements of $C$. There is no subcritical variation promise. Although $c_{\max}/c_{\min}$ is a finite range bound, it need not be below $\alpha^{-1/2}$.

A finite implementation has a source-independent schedule program and finite private configuration, using the original absolute count and its own source-independent state. It is valid on every source, selects only members of $C$, and never inspects unread bits or changes source binding. All reached updates finish and are paid. For paired-run comparisons, the same program and configuration, initialized identically and following the same matched control history at the same original count, must give the same unit and schedule state. A unit identity, configuration digest, padding or installation-size channel is not silently available to the receiver.

The positive theorem also holds conditionally for any abstract $C$-valued schedule with stable cuts and finite reached services. It does not construct a finite program for every abstract schedule. Finite code, known range cardinality or hidden value names do not supply the public values in this definition.

**Definition 2.2 (Complete Extent).** At an actual Return of depth $d$ and count $n$, a request Extent$(\nu)$ is allowed for every finite integer $\nu\ge1$. It returns the complete canonical finite self-delimiting frame of a nonnegative integer $a$, with request identification and service completion. Set

$$
\varepsilon=2^{-\nu},\qquad u=a\varepsilon,\qquad
|u-q(n)\alpha^d|\le\varepsilon.
\tag{6}
$$

The integer part is included. No modular reduction, clipping, saturation or fractional-only projection is allowed. Errors may depend on the full past, be correlated, biased and nonnested, and attain either closed endpoint. Correctness quantifies over every such response trace. Every reached Extent finishes, performs no raw Read or Advance, and preserves the producer fields, binding and rights. Its completion is distinct from a producer Return; it is unavailable inside an unfinished Step.

The scale is the length $\alpha^d$ of the actual paid-frontier compatible phase region, with the whole circle assigned length one at depth zero. It is not the shorter wall distance, complement arc, chord or physical length of an infinite tape. The algebraic value of $\alpha$ and the meaning of resolution $2^{-\nu}$ are known reference assumptions. No phase origin is required by (6).

## 3. Effective isolation over all depths

**Lemma 3.1 (Rational scales do not collide across depths).** If $c,c'\in\mathbb Q_{>0}$ and $d,e\ge0$, then

$$
c\alpha^d=c'\alpha^e\quad\Longrightarrow\quad d=e\text{ and }c=c'.
\tag{7}
$$

**Proof.** For $h>0$, suppose $\alpha^h$ were rational. Conjugation in $\mathbb Q(\sqrt5)$ fixes rationals and sends $\alpha$ to $-\alpha^{-1}$. Hence $\alpha^h=(-\alpha^{-1})^h$. For odd $h$ the signs differ. For even $h$ the equality is $\alpha^h=\alpha^{-h}$, impossible since $0<\alpha<1$. A negative nonzero power being rational would make its positive reciprocal power rational. Thus every nonzero integer power is irrational. The displayed scale equality makes $\alpha^{d-e}=c'/c$ rational, forcing $d=e$ and then $c=c'$. This includes depth zero. $\square$

**Lemma 3.2 (Finite exact comparisons).** All comparisons between the dyadic data, catalogue scales and cutoffs below are decidable by finite integer arithmetic, including equality.

**Proof.** A finite power of $\alpha$ lies in $\mathbb Q(\sqrt5)$, by $\alpha^2=1-\alpha$. After positive denominators are cleared, each comparison reduces to the sign of $A+B\sqrt5$ for finite integers $A,B$. Zero terms are handled directly. Two nonzero terms of the same sign determine that sign. If $A>0>B$, compare $A^2$ with $5B^2$: greater, equal and smaller give positive, zero and negative, respectively. If $A<0<B$, the signs are reversed. These exhaust the cases. Finite coefficient arithmetic generates each power at a finite examined index. This is an algorithm specification; no comparison or power enumeration is executed here. $\square$

**Definition 3.3 (Stationary catalogue decoder).** Keep the actual source at one Return. For $\nu=1,2,\ldots$, request (6). If $a\le1$, continue to the next precision. Otherwise form the observed strictly positive lower bound

$$
\ell=u-\varepsilon=(a-1)\varepsilon>0.
\tag{8}
$$

Find the least integer $D\ge0$ satisfying

$$
c_{\max}\alpha^D<\ell.
\tag{9}
$$

Inspect the entire finite list of pairs

$$
(e,c)\in\{0,\ldots,D-1\}\times C.
$$

Retain exactly those satisfying the closed compatibility test

$$
|u-c\alpha^e|\le\varepsilon.
\tag{10}
$$

Stop only when, after this complete examination, exactly one pair remains, and return that pair. Otherwise discard that stage's scratch and refine. No intersection of past replies is needed.

**Theorem 3.4 (Global soundness and all-error finite stopping).** Under Definitions 2.1–2.2, the stationary decoder finishes at every actual cut on every permitted error trace and returns exactly $(d,q(n))$. It uses no Step, Read or Advance and needs no supplied depth bound.

**Proof.** First the cutoff search is finite for every $\ell>0$. If $\alpha\le1/2$, then $\alpha^2+\alpha\le3/4$, a contradiction. Thus $\alpha^2=1-\alpha<1/2$, and $\alpha^{2j}<2^{-j}$ for positive $j$. The powers tend to zero, so (9) is eventually true. Each finite test is exact by Lemma 3.2.

Let the actual stationary scale be $z=q(n)\alpha^d>0$. Validity gives $\ell=u-\varepsilon\le z$. More generally any pair compatible with (10) has scale at least $\ell$. If $e\ge D$, then

$$
c\alpha^e\le c_{\max}\alpha^D<\ell,
$$

so no such pair anywhere in the infinite state space is compatible. In particular the true depth is less than $D$, and the true pair passes (10). Therefore an accepted singleton is globally unique and is the true pair. The finite list is complete because of a proved tail exclusion, not because a bounded sample happened to be unique.

For termination, fix the actual $z$ only in the proof. Choose a finite $\overline D$ with

$$
c_{\max}\alpha^{\overline D}<z/2.
\tag{11}
$$

At every sufficiently large precision, $\varepsilon<z/4$, and every allowed reply obeys

$$
\ell\ge z-2\varepsilon>z/2>0.
$$

Thus $a>1$ and the least cutoff $D$ is at most $\overline D$. The fixed finite set

$$
F=\{c\alpha^e:c\in C,\ 0\le e<\overline D\}
\tag{12}
$$

contains $z$: otherwise $d\ge\overline D$ would contradict (11). Lemma 3.1 makes its scales pairwise distinct. If $F\setminus\{z\}$ is nonempty, let $\eta$ be the positive minimum of $|z-z'|$ over its members; otherwise take any $\eta>0$. Eventually also $2\varepsilon<\eta$. A false passing candidate would belong to $F$ and satisfy

$$
|z'-z|\le |z'-u|+|u-z|\le2\varepsilon<\eta,
$$

a contradiction. The true pair always passes. Consequently every reply at every sufficiently large precision, regardless of all earlier adaptive errors, yields exactly one pair. Increasing precision therefore stops finitely on every valid trace. The witnesses $z,\overline D,\eta$ are not receiver inputs or computed certificates. $\square$

Depth and current unit are recovered at this stationary cut. The scale depends on no $s$ coordinate. This theorem alone does not recover slack, an original prefix, an old absolute count, the full current infinite point, or an invocation right.

## 4. One actual block update recovers the initial boundary

**Definition 4.1 (Owned boundary coordinates).** For $d\ge1$, [PAID, Theorem 12.2, (38)–(44)][PAID] identifies the actual boundary by

$$
\partial(d,s),\qquad G_d-1\le s\le G_{d+1}-2,
\qquad \delta=G_{d+1}-2-s.
\tag{13}
$$

For an actual $(p,n)$, $d=|p|$ and $s=N_p+n$. To specify ownership, set $\phi=1/\alpha$, $e_j=[-j\phi]$ for integer $j$, and

$$
(A_d,B_d)=
\begin{cases}(G_{d-1},G_d),&d\text{ even},\\(G_d,G_{d-1}),&d\text{ odd}.
\end{cases}
$$

The positively oriented arc has length $\alpha^d$, initial wall $e_{A_d-s}$ and terminal wall $e_{B_d-s}$. It owns $\chi_+(A_d-s)$ and $\chi_-(B_d-s)$, respectively, where $\chi_\pm(1)=x_1^\pm$ are the supplied split-side points and $\chi_\pm(j)=Z(-j)$ for $j\le0$. All attained labels are at most one. At label zero ownership collapses to $Z(0)$; no artificial $x_0^\pm$ is retained. Empty initialization is the whole-circle boundary, represented separately by $(0,0)$, with slack zero. No $J_0$ or $G_{-1}$ is used.

**Definition 4.2 (First-update rule, used for $m\ge1$).** Decode the original cut by Theorem 3.4, obtaining the actual $d_0$. Start with $i=0$ and $W$ empty. Repeatedly complete one actual Step, increment $i$, and decode the new returned cut by the same theorem. If its depth is still $d_0$, append nothing. At the first new depth $D\ne d_0$, record $t_1=i$ and $g_1=D-d_0$, and append $0$ for $g_1=1$ or $10$ for $g_1=2$.

For $d_0\ge1$ output the initial coordinate and the attained coordinate

$$
s_0=G_{d_0+1}-1-t_1,\qquad (D,s)=(D,G_D-1).
\tag{14}
$$

For $d_0=0$, report the initial whole-circle boundary $(0,0)$ independently and the same attained birth formula. Retain the existing turn. If $|W|\ge m$, output its first $m$ bits at this unchanged returned cut; otherwise continue by Section 5.

**Theorem 4.3 (One-update bridge).** The rule finishes after the first actual post-handoff block acquisition. It recovers the true initial and attained owned boundaries and has physically read exactly $g_1\in\{1,2\}$ new raw bits. All intervening real read-free Steps remain counted.

**Proof.** Every stationary call returns the true depth even if the unit changes arbitrarily between Steps. Before any new read the producer leaves depth $d_0$ unchanged. The first read changes it by exactly the length of the actual acquired complete block, one or two. It can neither be falsely reported nor missed.

For a proper initial cut, (2) and (13) give initial slack $\delta_0=k_{p_0}-r_0=G_{d_0+1}-2-s_0$. Exactly $\delta_0$ read-free Steps precede the read Step: each increases count by one without changing its finite death clock, and the next call at death reads. Hence

$$
t_1=\delta_0+1=G_{d_0+1}-1-s_0,
\tag{15}
$$

which proves (14). The clock is finite, so this occurs after finitely many calls, each with finite stationary decoding. At that call's Return, its actual new child is at birth, giving $s=G_D-1$ by (2). The ownership formula in Definition 4.1 therefore describes the true initial and attained boundaries, including every wall collapse.

At empty initialization, $k_\varnothing=r_0=0$ and the first Step reads, so $t_1=1$, $D=g_1\ge1$, and the child again returns at birth. The initial boundary was independently $(0,0)$; no proper lifetime formula is invoked at depth zero. The forced zero in the $10$ case was physically read before Return. No other read occurs through this first update, proving the exact read count. $\square$

This is an acquisition upper bound, not a proof that waiting for one block is necessary for boundary identification. Knowing $(d_0,s_0)$ leaves the supplied proper historical fibre

$$
\{(p_{d_0}(N),s_0-N):0\le N<G_{d_0-1}\}
\tag{16}
$$

when $d_0\ge1$, where $p_d(N)$ is the finite padded Zeckendorf prefix. For $d_0\ge2$ this has multiple members. An arbitrary possible member is not the actual history. Neither the measured unit nor $t_1$ authenticates $p_0$ or $r_0$.

## 5. Event continuation and every finite raw-tail target

**Definition 5.1 (Continuation after the earned birth).** At a known current proper $(D,s)$ put $\sigma=G_{D+1}-2-s$. If $\sigma>0$, complete one real Step, retain its full triple, check Emit against $\operatorname{Low}(s)$, append nothing, and set $s$ to $s+1$.

If $\sigma=0$, complete one real Step and compare its Emit with the old-depth constants

$$
c_0=\operatorname{Low}(G_{D+1}-2),\qquad
c_1=\operatorname{Low}(G_{D+2}-2),\qquad c_0\ne c_1.
\tag{17}
$$

The $c_0$ branch appends $0$ and updates to $(D+1,G_{D+1}-1)$; the $c_1$ branch appends $10$ and updates to $(D+2,G_{D+2}-1)$. All right-hand sides use the old $D$. Increase the local completed count. Stop at the first Return with $|W|\ge m$ and output its first $m$ bits. No further Extent is needed.

The inequality in (17) is the actual child-split supply in [PAID, Definition 2.3 and Theorem 18.2][PAID], equivalently [NORMAL, Theorem 7.1 and Definition 8.2][NORMAL]. For the actual old parent depth $D$, its two children have different itinerary constants at its death coordinate. Their finite representatives are exactly the two Low arguments in (17), by (1)–(3). Thus this is an interpretation of a real Emit, with no private branch flag or raw getter.

**Theorem 5.2 (Same-source raw-tail invariant).** After $i$ completed Steps of Sections 4–5 and their classifications, a complete word $w_i$ satisfies

$$
\begin{aligned}
W&=w_i,&p_i&=p_0w_i,&d_i&=d_0+|w_i|,\\
\text{actual unread raw tail}&=\operatorname{tail}_{|w_i|}(t),&
n_i&=r_0+i,&\text{current point}&=T^{r_0+i}x,\\
N_{p_i}&=N_{p_0}+\sum_{j<|w_i|}G_{d_0+j}(w_i)_j.
\end{aligned}
\tag{18}
$$

The producer caches are precisely the caches of this actual prefix and count. Returned scratch and pending output are empty; the original binding and continuing rights persist. From the first-update Return onward, the receiver's $(D,s)$ is the true current coordinate.

**Proof.** At $i=0$ the word is empty and the actual handoff gives (18). In Section 4, unchanged decoded depth means no read; a depth increment of one or two is exactly the actual new block. All decoded stages are sound by Theorem 3.4. The first update gives the actual birth by Theorem 4.3.

Thereafter positive slack means the real producer is below death: it reads nothing, keeps prefix/cursor/tail, emits $\operatorname{Low}(s)$, and increments $s$ once. At zero slack it physically reads its own next block. Equation (17) identifies that block, and (2)–(3) give exactly the listed child birth. Appending its bits uses the original absolute raw weights, which yields the sum in (18). Every case has exactly one real Advance and its full Return; producer correctness identifies the current point and clears pending fields. Queries preserve these fields. Induction proves all claims without replacing an endpoint or a history member. This is the concrete parameter correspondence with PAID Theorems 3.2, 12.3, 18.2 and NORMAL's known-boundary decoder: their current depth and sum coordinate are our actual $D,s$, their slack is our $\sigma$, and their raw origin is the same actual $p_0w_i$. $\square$

**Theorem 5.3 (Finite target-block Return).** For every $m\ge1$, actual handoff, legal source, schedule and closed-error trace under Section 2, the phased rule is finite and outputs precisely the initial $q_m(t)$. Its source cut is exactly the Return of the Step physically acquiring the block containing initial-tail position $m-1$. Stationary classification and output may finish afterward at that same cut.

**Proof.** A finite raw position belongs to a finitely numbered block of the unique parsing. At each reached parent, its death clock is a finite integer at least its current count. Finitely many read-free Steps reach that clock; the next finite Step reads the next complete block. Its child death clock increases strictly by (3), so the same argument repeats lawfully. Only finitely many blocks through the target are needed. Section 4 uses finitely many calls with finitely many queries at each cut; Section 5 uses finite integer arithmetic and finite real Steps. Thus the whole procedure finishes.

By (18), $W$ is exactly the complete raw word acquired since the initial handoff. Every earlier block Return has $|W|<m$, whereas the target-block Return first has $|W|\ge m$. Classification there gives the requested prefix and does not Advance again. The proof applies to all-zero, finite-core, pure alternating, eventually alternating and all other no11 tails, including all split sides and inclusive cut equalities. Every used block is finite; there is no infinite alternation test or raw first-$00$ search. $\square$

The result is an initial-tail target, not the moving current spatial prefix. If an additional endpoint accepts genuinely acquired live records under [PAID, Definition 18.1][PAID], the earned $(D,s,i)$ and existing same-source right meet its current-data premise. PAID Theorems 18.2–18.3 then supply its LiveStep, guarded Peek, moving Seek and optional budgets. The present proof needs only base Step and internal finite record updates. It does not itself install any extra service or authority, and Seek answers the attained cut rather than rewinding the initial one.

## 6. Exact source counts and the phased query coordinate

Fix $m\ge1$ and the original actual handoff in (4). In the initial tail let $w$ consist of every complete block before the block containing position $m-1$. Put

$$
e=|w|,\qquad g\in\{1,2\},\qquad e<m\le e+g,
\qquad V=\sum_{j<e}G_{d_0+j}w_j.
\tag{19}
$$

The shifted value uses original raw positions; it is not the value of $w$ rebased at zero. Define the supplied target clocks

$$
h_m(t)=G_{d_0+e+1}-1-s_0-V,
\qquad B_m=G_{d_0+m}-1-s_0.
\tag{20}
$$

**Theorem 6.1 (Exact Return and Read counts).** The phased decoder uses exactly $h_m(t)\ge1$ new Step, Emit, Advance and producer-Return events. It physically reads exactly $e+g\in\{m,m+1\}$ new bits. At fixed actual $p_0,r_0$ and any common admissible source-independent schedule, its all-tail, all-error worst Advance value is exactly $B_m$, attained by the legal all-zero initial tail.

**Proof.** The actual target parent is $a=p_0w$, with $N_a=N_{p_0}+V$ and

$$
k_a=G_{d_0+e+1}-2-N_{p_0}-V.
$$

The Step beginning at this death count reads the target block and Returns at $k_a+1$. Subtract the same actual $r_0$ to obtain $h_m(t)$. The positive child increments (3) imply $k_a\ge k_{p_0}\ge r_0$, hence $h_m(t)\ge1$. Theorem 5.3 stops at precisely this cut, with no additional Advance. Each call contributes one actual triple, including every read-free Step. The acquired raw word is $w$ and the entire target block, so each of its $e+g$ bits was physically read once. This equals $m+1$ exactly for a target at the first one of $10$; at its second zero it equals $m$ and includes that zero's physical Read.

For the worst value, $e\le m-1$ and $V\ge0$ give $h_m(t)\le B_m$. Every legal tail can be appended to this same actual $p_0$ and reaches this same $r_0$, by (2). For $t=0^\infty$, $w=0^{m-1}$, $e=m-1$ and $V=0$, so equality holds. No alternate provenance member or new source clock was chosen. At the empty initial cut, $k_\varnothing=G_1-2=0$; the same calculation gives $h_m=G_{e+1}-1-V$ and $B_m=G_m-1$, without negative indices. At a death cut with the target in the next block, $h_m=1$. Birth equalities are also included by (2). $\square$

These formulas, the opposite-block construction below and their source-clock meaning are supplied by [NORMAL, Sections 7–9][NORMAL] and [TARGET, Sections 4–7][TARGET]. The catalogue bridge allows a receiver with the new public input to attain the same physical cut; the clocks are not new identities.

**Proposition 6.2 (Literal phased query count).** For $i=0,\ldots,t_1$, let $\nu_i\ge1$ be the successful precision of the stationary decoder at local returned cut $i$, including the original cut and the first-update Return. Then

$$
Q_{\rm Extent}=\sum_{i=0}^{t_1}\nu_i.
\tag{21}
$$

There are no queries after that first update.

**Proof.** Each stationary call restarts at one, increases precision once per request and stops at $\nu_i$, giving exactly $\nu_i$ requests. Section 4 makes one such call at each of these cuts, and Section 5 uses no Extent. All summands and their index set are finite by Theorems 3.4 and 4.3. $\square$

A variant decoding depth after every Step through the target also works, with query count $\sum_{i=0}^{h_m(t)}\nu_i$. Neither count is a query or precision optimum. At a stage with $a>1$, complete candidate examination in Definition 3.3 tests exactly $kD$ pairs, each by two closed inequalities, with cutoff search and coefficient generation additional work. Stages with $a\le1$ do no candidate examination. These comparison counts are not their bit costs.

## 7. Robust lower bound, full operations and completion timing

**Definition 7.1 (Comparison class).** A robust decoder is deterministic and causal, uses the common public $C,m$, public code and legitimately installed rights, and must be finite and correct on every legal source, actual hidden handoff, admissible source-independent catalogue schedule/configuration and response trace satisfying (6). Return-complete output finishes at a returned cut with no unfinished Step or pending transaction containing a Step. Equivalently for this lower bound, charge each issued source transaction through its eventual Advance and Return. Count every actual new producer Advance from the original handoff, including those in calibration, Seek, Tick or any lawful wrapper.

For correctness restricted to one backend, require a separate same-backend pairing condition: before the first different raw acquisition, equal acquired source history, finite caches, original counts, schedule/configuration, public controls and request histories must admit equal complete replies, guards, modes, permissions and observable successors in that backend. Deterministic dependence on these matched fields is sufficient. A numerical error inequality alone does not establish this condition.

**Lemma 7.2 (Opposite target and complete pre-target pairing).** Fix any actual $p_0,r_0,t$, admissible schedule/configuration and valid error trace. There is a legal alternative source at the same actual original handoff whose requested prefix differs and whose entire permitted observation can be matched until the target transaction. The pairing includes every returned cut through

$$
\rho=h_m(t)-1=k_{p_0w}-r_0
\tag{22}
$$

and the public event prefix before the target Emit.

**Proof.** Use the following legal complete-block tails, keeping $p_0,r_0$, public catalogue, program and private schedule configuration unchanged:

| Actual target position | Alternative $t_*$ |
| --- | --- |
| The $0$ block, $e=m-1$ | $w10\,0^\infty$ |
| The first one of $10$, $e=m-1$ | $w0^\infty$ |
| The second zero of $10$, $e=m-2$ | $w0\,10\,0^\infty$ |

All concatenations are legal because complete words end in zero or are empty. The requested position changes in every case. In the third row, position $e+1=m-1$ changes from the forced zero to one, as well as the change at $e$; the forced-zero target is not omitted.

By actual attainment, both original sources $p_0t$ and $p_0t_*$ reach this same acquired prefix and count from the original initialization. They then acquire the same $w$ before the target call. At all preceding paired returns keep equal actual $p,d,n,N_p,G_d,G_{d+1},k_p$, empty scratch/pending fields, receiver records, public parameters, lawful modes, budgets and installed permission outcomes. This does not equate the unread endpoint contents or entire current points.

The equalities hold at the original cut, and all old acquisitions were within the shared $p_0$. If the actual driver history contains legitimate queries, copy their valid full replies at the same depth and count; deterministic acquired-field services match there too. The same source-independent schedule program and configuration, including its matched private state, give exactly equal $q(n)$ at every matched original count. This equality is essential: catalogue membership alone would not imply it. There is no clock reset or configuration change at handoff.

An actual Next below death performs no Read and emits the same Low value. At a split before the target it reads the same complete block within $w$, including any forced zero; all caches and actual triple events again agree. Every internal Next in a wrapper is expanded and charged. The first different raw block is read in the target transaction; its first permitted public source distinction is the target Emit. No private cache query is installed inside that transaction.

For Extent at any earlier cut, equal $q(n),d$ give exactly the same set of allowed full nonnegative integers at the selected precision. Copy the fixed trace's entire integer, integer part and canonical frame. Every copied closed inequality remains valid. Adaptive, nonnested and correlated errors cause no exception: equal histories select the same next precision and test results. The copied finite prefix extends to a legal full trace, for example by later floor replies under the unchanged schedule. This is an all-error argument, not an assertion that every particular selector voluntarily copies the chosen literals.

The base interface, descriptor/possession checks, pauses and release outcomes now pair in full. For explicitly installed richer operations, the following exact scope is the full-operation transfer of [TARGET, Lemma 6.1][TARGET]. Each complete field, guard, mode, budget and right must depend only on the matched actually acquired fields and common configuration:

- Finite acquisition tests the same $k_p-n\ge D(L,H)$, where $D(L,H)=H$ at $L=0$ and $H+G_L-1$ otherwise. Its internal Steps are counted. Full Ready/DATA replies, actual time counters and retained finite records match. Guarded Peek uses $q_\ell(Z(N_p+n))$. Budgeted Tick is a real Step; exhausted budget and encodable depth refusals have the same frames.
- If Park/Wall is separately authorized, its actual nonempty-return guard, lock and acknowledgement match. The specified deterministic Wall of PAID (57) reads equal $d,N_p,n$ in the same reference and gives equal complete wall integers and frames. Old Arm, bounded Peek/Tick and Release/Resume have the same guards, budgets and declared outcomes. A different approximate Wall backend needs its own full-response premise.
- If a live record has actually been earned and accepted under its installed contract, its current $d,s,i$, caches, binding and budget are equal. LiveStep is a real Next. Live Peek uses the same complete guard and representative $q_\ell(Z(s))$, with identical parameter refusals. Seek tests the same guard and counts every internal real Step. A service crossing the target has already paid its target Advance when charged through Return. New Seek, LiveStep or release exits budget mode identically.
- Authorized acquired-field export or archives give equal complete $p,n$, caches, actual old replies, declared records, modes and descriptor fields. Local computations and literal outputs then have equal inputs. Neither arbitrary private-state/unit exporters nor unread-tail, identity, timing, advice or padding channels follow from this statement. An uninstalled name supplies no new refusal. A separately added catalogue service must prove its own full-response pairing.

These cases preserve the invariant. Equal complete histories force the same adaptive next action, parameter and stopping choice. Induction proves the asserted finite pre-target pairing. Actual endpoint contents stay in their own worlds; release cannot conceal free driver calls. $\square$

**Theorem 7.3 (Per-selected-trace sharp Return bound).** Every robust decoder in Definition 7.1 pays at least $h_m(t)$ new actual Advances on each selected actual history and every selected valid trace. The same statement holds for a specified backend satisfying its pairing condition. Thus the phased decoder attains the source-Advance optimum, and the fixed-cut all-tail robust worst value is $B_m$.

**Proof.** Suppose a Return-complete decoder finishes on the selected trace with $j<h_m(t)$ Advances. Then $j\le\rho$, so it has not completed the target transaction. If it had issued that transaction and charged it through Return, its target Advance would already have been counted. Therefore its complete answer history lies in Lemma 7.2's paired prefix. Determinism gives the same output and stopping choice on the alternative source, although the two $q_m$ differ. Extending the copied finite errors gives an admissible full trace there, contradicting robust all-source/all-error correctness. The originally selected trace was arbitrary, so this is a bound on each trace, rather than existence of one unfavorable rounding. Under the backend-specific premise the same paired history is supported by that very backend, giving the corresponding contradiction. Theorem 6.1 attains $h_m$ and its all-zero case forces $B_m$ for every such full-domain decoder. $\square$

The complete floor implementation in Section 8 satisfies same-backend pairing: equal original count, schedule/configuration state, selected unit, depth and precision give the same actual floor integer and canonical frame. Its deterministic controls read only matched acquired fields. This is stronger than merely satisfying (6).

Indeed, the bare error inequality allows a mathematical oracle to choose between $\lfloor y\rfloor$ and $\lfloor y\rfloor+1$ for $y=2^\nu q(n)\alpha^d$, choosing the parity of $a$ to equal an unread advice bit. Both integers are nonnegative and within one of $y$, including the closed integer endpoint. Such an oracle could reveal the bit without Advance. It is not the installed no-Read finite floor service: obtaining that advice requires another source-access or source-dependent configuration bridge. The example explains why robust quantifiers or proved source blindness are indispensable; it installs no advice service.

**Proposition 7.4 (Early output is a different completion rule).** For an answer allowed during the target Emit, the inherited general lower bound is $h_m(t)-1$ prior Advances. A matching upper bound requires a genuinely known boundary and an installed synchronous Emit handler that completes finite paid output before producer Advance. Our phased theorem guarantees Return-complete $h_m(t)$.

**Proof.** Pre-target observation equality excludes correct output before the target Emit. The serial calls producing it already require exactly $\rho=h_m-1$ completed Advances. But the target call's order is Read, Emit, Advance, Return, so observing Emit does not imply its own Advance has occurred. With a known boundary, (17) identifies the target block from that actual Emit. If the delivery implementation explicitly waits for a finite handler's output before proceeding, that output finishes after exactly the $\rho$ preceding Advances; the final call then still owes its Advance and Return. Visible event order alone does not install this waiting rule: a producer can Advance before the receiver processes an already delivered Emit. Section 4 also needs post-Return Extent to identify the first update. Hence no general early-answer matching upper bound for the uncalibrated phased rule follows. $\square$

## 8. A separately extended finite floor service and complete costs

**Definition 8.1 (Finite rational implementation).** Start with the actual PAID producer and its source-independent empty initialization. Additionally install the actual public rational catalogue and its complete encoding, a finite selector/update program with finite private configuration, current unit/index storage and the exclusive Step/Extent handoff protocol. All are paid. Initially select a catalogue member without consulting the raw source. After every completed original Step, use the updated original counter and the private source-independent schedule state to select the next member before enabling returned-cut queries. Read-free Steps and wrapper-internal Steps cause the same real update. No update reads unread bits or alters raw cursor, source semantics, clocks or emitted events. No unfinished Step admits Extent. Every reached update is required to finish.

At an actual Return of depth $d$, with the stored actual entry $q(n)$, the extended service computes

$$
a=\left\lfloor2^\nu q(n)\alpha^d\right\rfloor
\tag{23}
$$

and returns its entire canonical nonnegative integer frame and completion. This is a separate extension of [PAID, Definition 19.1 and (73)][PAID]. The unchanged formula with one fixed $A/B$ does not already implement arbitrary catalogue jumps.

**Proposition 8.2 (Finite realization and noninterference).** For each actually installed finite rational selector satisfying Definition 8.1, the floor service realizes (6) with finite reached computation and preserves the actual producer. It satisfies the same-backend condition of Section 7.

**Proof.** Finite rational encodings give exact selected values and finite $c_{\max}$. A finite power $\alpha^d$ has a finite quadratic representation. The nonnegative quantity $2^\nu q(n)\alpha^d$ is at most $2^\nu c_{\max}$, so finite rational arithmetic supplies an integer upper bracket. Binary search in that finite integer interval, using Lemma 3.2 for exact comparisons including equality, finds its floor. This covers depth zero and integer endpoints without a numerical equality oracle. The finite encoded response has error less than $2^{-\nu}$, hence satisfies the closed guarantee. Only already acquired depth and the installed unit/schedule state are read. Scratch and response framing do not move the raw endpoint or Advance the source. At matched acquired histories the same program/configuration and count give the same selected unit and every deterministic service/control field, so its full actual integer and frame match. The producer's original execution and precise unread-tail continuation are untouched. These are symbolic implementation specifications, not executed code or floor calculations. $\square$

A finite paid source-independent program such as the already supplied parity selector can have hidden finite configuration; the additional public value list must be actually supplied. Conversely arbitrary abstract $C$-valued sequences do not acquire finite generators merely because $C$ is finite. The conditional positive theorem separates this implementation obligation from its finite-response mathematical premise.

**Definition 8.3 (Accounting boundary).** The exact independent new logical coordinates are $h_m(t)$ producer triples, $e+g$ raw Reads and their bit payload, and (21) Extent requests/completions. The zero-target case has zero of all these. Full integer requests/replies and framing, service computations, catalogue search and local output remain paid even though they cause no Advance.

The public catalogue requires actual acquisition, rational validation/deduplication and storage; keep the complete value encodings, rather than merely $k$. Finite catalogue comparison work depends on its numerator/denominator lengths, all reached depths/cutoffs, quadratic coefficient sizes and the precisions used. Counting $kD$ pairs does not price multiplication, denominator clearing, sign tests, powers, counter scans or singleton storage. A streaming candidate scan may retain only one candidate and a count saturated at two, but still must complete the entire finite scan.

Whole-system work includes actual program/reference installation, channel and raw-source bindings, persistent rights and descriptor/possession checks; the private selector program/configuration and original-counter/unit update computation; every old driver Step, Read and received event; source provisioning, generation/delivery and backend service; producer finite prefix, caches and Low arithmetic; every requested precision and whole integer response, including large integer parts; scratch allocation, scans, copies, return positioning and clearing; receiver control, $W$, coordinate/local-count records; all literal results, refusals where actually installed and archives where actually retained. A public finite list does not make any of those costs zero.

Storage is the sum of simultaneously present source/backend, driver, producer, unit service, receiver and retained-output state. Private configuration still occupies storage even though hidden from the receiver. Keeping archives or multiple prefix copies adds their actual lengths. Equal observations do not imply equal private computation, storage or latency in two worlds. Reached finite services guarantee finite completion, not a uniform physical deadline. The source contract supplies no finite generator or finite-cost infinite tape for every unknown $x\in K$; PAID's separate $\iota_x,\gamma_x,\sigma_x$ source terms continue to apply.

No fixed-unit precision bound $n_*\le d_0+b_q+12$, $W_0$ estimate or Section 19 bit/space formula is transferred to arbitrary catalogue schedules or to Definition 3.3's finite-union search. A replacement quantitative analysis would need the actual catalogue and schedule encodings, update work, all cutoff/precision sizes and simultaneous components. Here only finiteness, the stated logical coordinates and the scoped source-Advance optimum are established. There is no parameter-independent bound over hidden depths, no query/precision/bit-memory optimum and no universal resource optimum.

## 9. Optional algebraic catalogue classification at a stationary cut

**Theorem 9.1 (Exact stationary collision criterion).** Let $C$ instead be a known finite set of distinct positive elements of $\mathbb Q(\sqrt5)$ with explicit rational-coefficient encodings and effective exact comparisons. Over the hidden-handoff/hidden-selector class allowing every constant choice from $C$, stationary depth recovery is possible if and only if

$$
c\alpha^d=c'\alpha^e\quad\Longrightarrow\quad d=e
\qquad(c,c'\in C,\ d,e\ge0).
\tag{24}
$$

Under this condition the current unit is also recovered. This criterion concerns stationary observation, without Step.

**Proof.** Positivity and exact comparison give a finite $c_{\max}$. Distinct values at the same depth cannot have equal scales. Condition (24) therefore makes all pair scales distinct. Definition 3.3 and its proof apply verbatim: observed positive $\ell$ excludes the entire tail, the fixed finite set (12) has positive separation, and Lemma 3.2 decides all quadratic tests. No rational-power argument is now needed because noncollision is the explicit assumption. Thus every error trace stops with the exact pair.

Conversely suppose a collision has $d\ne e$. The actual zero-source complete prefixes $0^d,0^e$ realize these depths at their births under the original producer; use return zero for depth zero. These are actual initialized histories by (2). Fix a common public program that selects a private constant catalogue entry. In one installation select $c$, and in the other select $c'$. Both configurations are finite and source independent, and both disclose the same public $C$ and code, acknowledgement and lawful stationary rights. Their floor services have the same true scale and hence the same whole integer/frame at every precision. No Step is taken, so all permitted stationary adaptive observations agree, whereas depth differs. No stationary procedure can recover both depths, even from the entire stationary observation. This proves necessity for the stated class; it does not claim that a further disclosed selector configuration remains hidden.

For example, the algebraic catalogue $\{1,\alpha\}$ has the collision $1\cdot\alpha^2=\alpha\cdot\alpha$. It is outside the main rational-value hypothesis. The collision gives no global active-target impossibility: later real Steps can change the observations, and an obstruction for all such active protocols would need a complete actual-interaction witness. We make no decision-procedure claim for checking (24) on an arbitrary presented catalogue, and no effective-comparison claim for arbitrary real values. $\square$

## 10. Existing suppliers, drift knowledge and the finite-cap boundary

**Proposition 10.1 (A finite cap still permits permanent target blindness).** For every nonempty public rational $C$ and fixed finite $N\ge1$, the base floor implementation restricted to precisions $1,\ldots,N$ has no finite exact deterministic initial-first-bit decoder on all hidden actual handoffs. Consequently it cannot uniformly recover $q_m(t)$ for any $m\ge1$. This holds even when the actual selected constant unit is disclosed.

**Proof.** This is the transfer of [CAPPED, Theorem 7.1][CAPPED]. Choose any $q\in C$ and keep it constant under the same public program/configuration in both worlds. Choose a finite $D\ge1$ with $2^Nq\alpha^D<1$, possible by the geometric decay proved in Theorem 3.4, and let $R=G_{D+1}$. Consider the hypothetical actual initialized run of $z=0^\infty$ through $R$ Steps and of $a=(10)^\infty$ through $R+1$ Steps. Every finite driver prefix finishes by the supplied productivity theorem.

At any actual nonempty return of depth $d\le D$, (2) would give $r\le G_{d+1}-N_p-2\le G_{D+1}-2<R$. The only empty return is zero. Hence both handoffs have depth greater than $D$ and are proper. They have the same complete current point, since

$$
T^Rz=Z(R)=T^{R+1}a,
$$

using $Ta=z$ and finite-core successor. The initial unread tails are $z$ and $a$: every acquired block on them is respectively $0$ or $10$. Their first target bits differ. All future depths remain above $D$, so at every allowed $\nu\le N$ and every later cut,

$$
0<2^\nu q\alpha^d\le2^Nq\alpha^D<1.
$$

The actual floor integer is permanently zero, with the same complete frame. Both complete current trajectories are $Z(R+h)$ and every real Emit/Advance/Return sequence agrees. Starting with the same public catalogue, cap, unit if disclosed, controls, acknowledgement and installed rights, induction on legal adaptive requests gives the same precision, whole reply, Step events, local records, mode, possession, pause, release and stopping choice. Uninstalled richer services are excluded. Thus every finite observation, and coordinatewise the whole permitted infinite observation of this fixed pair, is identical. Finite total correct output would be the same on two different first bits, a contradiction; waiting forever fails totality.

The two driver histories and every forced zero remain paid and hidden. These arbitrary-$q$ cuts need not both be deaths. CAPPED additionally proves two explicit death handoffs for its small unit $q_N=2^{-(N+1)}$, namely $(z;p,r)=(z;0,1)$ and $(a;10,2)$, both with current point $Z(1)$ and different unread first bits. That death strengthening transfers when the chosen public catalogue contains $q_N$; it is not asserted for every $q$. $\square$

The positive theorem permits arbitrarily large finite precision and terminates after finitely many such queries on each instance. It does not perform an infinite interrogation. The capped theorem holds even for a singleton public catalogue and one known fixed unit, so public value knowledge alone cannot replace unbounded finite resolution over unbounded hidden depths. It is an actual floor-backend result; a numerical error inequality alone cannot force every selector into permanent zero replies.

**Proposition 10.2 (Value knowledge and drift knowledge are distinct inputs).** The present result does not contradict [DRIFT, Theorem 3.1 and Sections 8–12][DRIFT]. The drift theorem is class-wide: for each supplied $1\le\beta<c=\alpha^{-1/2}$, certified finite constants permit a decoder; at $\beta\ge c$ no common finite exact decoder handles all permitted hidden schedule configurations. It is not impossibility for every individual generator advertised with a loose bound.

**Proof.** The drift positive theorem separates the possible one-Step ratio intervals $[\alpha^g/\gamma,\gamma\alpha^g]$ using a public certified $\gamma<c$ and fresh refinement. Our procedure isolates absolute scales $c'\alpha^d$ from explicit $c'\in C$ instead. It needs no separated ratio intervals. For example, $C=\{1,2\}$ allows factor-two jumps, greater than the critical factor since $\alpha>1/2$ implies $\alpha^{-1/2}<2$.

For the negative drift comparison, its single public parity program has $q(0)=q(1)=H$, then $HQ$ at even counts and $Hb$ at odd counts. The actual finite positive rational values $H,HQ,Hb$ belong to hidden configuration, constrained by $c<b<c^2$ and $b/c<Q<c$. Finite range cardinality three is not disclosure of those values. Its proof fixes the public program and configuration domain first, takes a legal reference configuration of that same program, and uses totality to obtain a finite stationary prefix at scale $H\alpha$ independent of $b,Q$. Only private $b,Q$ are then chosen to match that prefix with the second actual world. After the first Step the actual worlds coalesce in depth and common-tail boundary, and the common parity schedule gives identical all-precision future replies. Every selected witness even has its own hidden factor $\rho<c$, but no common supplied subcritical margin covers the public critical class.

If the final complete list $\{H,HQ,Hb\}$ is additionally disclosed, this changes the receiver's public input with that private choice. The reference-to-final argument can no longer infer an unchanged finite initial decision from code equality alone. Our decoder uses exactly this added public information, in particular $c_{\max}$ and rational cross-depth noncollision. Thus the two theorem domains differ at a concrete information premise. Conversely a public constant-unit generator remains actively decodable without any finite catalogue disclosure, by PAID/TARGET, so catalogue knowledge is sufficient rather than necessary for all active protocols. $\square$

A finite program need not even have finite range: the source-independent rational rule $q(n)=2^{-n}$ has finite description and infinitely many values. A known bound on cardinality, names of hidden parameters, or finite code alone therefore does not justify Definition 2.1. A program explicitly publishing the full finite values can supply that input, with its actual bytes and costs.

**Definition 10.3 (Exact mathematical credit and transfer).** The following five references designate the proof suppliers and comparison interfaces. Their complete scopes remain distinct.

| Supplier and scope | Content consumed and retained boundary |
| --- | --- |
| [NORMAL, Sections 1–10][NORMAL] | Actual same-tail fixed-offset continuation; equality of whole current points including side points; projected command comparison; restriction injectivity, the entire owned-set tail bijection and finite pointwise provenance; exact first event difference, known-boundary event inverse and $h_m/B_m$. These are used with the actual $D,s$ earned here. None of the clocks, classifiers or tail inverses is newly claimed. |
| [NORMAL, Sections 11–17][NORMAL] | Classification of all initialized histories over every complete point, unbounded paid depths, every-finite-horizon event ambiguity, finite causal entrance/stopping-boundary nonrecovery, a natural-core fixed pair with permanently distinct boundaries, and necessary infinite supplementary-record range. Their event-only observation excludes the new Extent input. Full current points, histories and paid boundaries remain different objects. |
| [PAID, Sections 1–12][PAID] | Productive source-independent sequential producer, finite Low arithmetic, physical forced-zero Reads, precise raw-tail restart, current DATA guard, initial acquisition/bounded use and scoped bit accounting; owned boundaries, historical ambiguity, authenticated same-run counter repair and exact coordinate transitions. This is the controller used here, rather than the distinct native seed/payload/Stop controller. |
| [PAID, Sections 13–21][PAID] | Calibrated ordered-wall acquisition and installed Park/Wall/Arm services; unknown fixed-unit stationary obstruction, closed three-ratio classification and two-update lifetime calibration; earned live update, guarded Peek, moving Seek and finite rational fixed-unit floor implementation. Proposition 20.2 already gives known-unit stationary isolation. A singleton public catalogue consumes that result. Section 19's fixed-unit code and estimates are not silently changed to arbitrary jumps. |
| [PAID, Sections 22–30][PAID] | The separate fixed affine contract $b+q\alpha^d$, unknown rational $b\ge0,q>0$, complete error replies, reliable first detected descent and its calibrated next complete lifetime; Theorem 24.1 recovers the genuinely attained owned boundary, and Corollary 24.2 supports current live use. Definition 24.3 formulates exact INITIAL-affine recovery; Theorem 29.1 settles its deterministic existence claim negatively, even for the specified finite rational floor backend, proper death handoffs and arbitrary finite adaptive precisions. Corollary 30.1 preserves the reached-boundary and live-use positives. Early missed updates are not certified absent, so first detected descent is not first real update. The catalogue theorem instead supplies explicit public finite rational VALUES and assumes no unknown additive offset: this different public information contract identifies every reached depth exactly, neither contradicts Theorem 29.1 nor supplies its negative result, and transfers none of the affine cost bounds. |
| [TARGET, Sections 1–10][TARGET] | Fixed-unit direct initial-tail acquisition without prior boundary recovery, fresh-cut three-ratio refinement, the actual target-block Return, exact raw-tail invariant, target clocks and physical $m$ or $m+1$ Reads; full installed-operation pairing, robust per-trace versus same-backend quantifiers, advice-selector warning, Return versus synchronous Emit-handler timing, and independent query/cost coordinates. Section 7 transfers its lower-bound machinery with the same original-count schedule/configuration in both runs. |
| [CAPPED, Sections 1–11][CAPPED] | Fixed-unit actual floor zero cells, two genuine death-cut witnesses at a selected small unit, every-fixed-unit late proper witnesses, whole-current-point and entire infinite allowed-observation equality with different initial raw targets; paid histories and preserved known-boundary/unbounded-precision positives. Proposition 10.1 is an application, not a new capped obstruction. |
| [DRIFT, Sections 1–14][DRIFT] | The moving-unit source/rights model, subcritical separated-interval positive theorem, full-history common-schedule target-cost transfer, optional two-update recovery, and critical same-public-program/common-private-configuration causal obstruction. Sections 8–12 keep the reference program and finite floor-cell selection fixed in the precise order described above. Public VALUE knowledge is an additional input; no drift theorem is reclassified or re-proved here as new. |

PAID Theorem 29.1's supplied construction depends on the proposed decoder's finite initial observation. Totality on an actual proper reference instance gives a finite prefix ending either in completion without a Step or in initiation of the first real Step. The finitely many initial precisions determine one common fixed rational configuration $(q_*,b_*)$ for two actual proper death handoffs, with different initial owned boundaries $\partial(1,1)$ and $\partial(2,3)$, whose complete initial floor integers and frames agree throughout that prefix. In the no-Step completion branch, the same finite observation forces the same answer. In the first-real-Step branch, both actual calls deliver Emit$(0)$, Advance, Return and coalesce at the same current point, depth, owned boundary and unread tail; under their common fixed configuration every subsequent complete reply and allowed event agrees at every finite precision. These are the supplier's two branches, not a fixed pair with all-precision equality already at the initial cut. The configuration is decoder-dependent; the theorem does not assert an obstruction for every preassigned configuration or every reply selector. Its specified-floor obstruction suffices to refute the all-source, all-configuration, all-error initial-recovery requirement. The catalogue's Section 7 retains its own all-source/all-error requirement and separate specified-backend pairing premise.

The standard intermediate tools are quadratic conjugation, exact integer signs, geometric decay, increasing rational precision, finite separation, causal same-response induction and the factor-through-observation contradiction. Their use is not a new general algebraic or computable-analysis principle. The added conjunction relative to these suppliers is the effective finite union of rationally scaled depth chains with global infinite-tail exclusion and every-error finite stopping, valid under arbitrary catalogue jumps, followed by initial boundary acquisition at the first real block update. Target costs and event/live laws are applications of existing results. No external literature exhaustion or worldwide priority is claimed.

## 11. Four meanings and unresolved implementation bridges

Space is the actual current infinite point $T^{r_0+i}x$; finite current DATA is a separate task from the initial raw-tail prefix. Time is the actual Emit/Advance/Return order, with only post-handoff local counts given to the receiver. Boundary is the actual paid-frontier compatible phase region and its owned wall lifts, with the empty frontier represented independently. Memory is the receiver's actually retained catalogue, finite word/control/coordinate records and held live binding/right; it does not include unread tails, discarded events or a mathematical past. No view is assigned a free copy of the full history.

The established arrows use actual data and operations: public rational values plus stable-cut approximate replies yield exact depth/current unit; depth observations across the first physical block update and its actual elapsed Steps yield the initial and attained boundary coordinates; the earned current record plus real events maintains that boundary; the initial-tail finite target is obtained by the actual target-block Return. Existing PAID guards then give finite current DATA only in their declared domain, and moving Seek pays for the actual source motion needed to reach a sufficient cut. These are not equality of the four whole-view kernels or an effective infinite inverse.

The recovered numerical coordinates alone do not recover the actual old prefix member, an authenticated original absolute count, old event archives, the whole infinite source/current point, physical wall phases in an unknown reference, or transferable permissions. A particular additional public schedule or installed exporter can supply extra distinctions, so we make no universal historical impossibility claim for every enriched interface. A guessed possible provenance member, printed endpoint name or coordinate proof is not authenticated history or a new right. The same real endpoint continues at its own precise unread tail; boundary recovery does not rewind it.

All positive results require the explicit finite public positive rational VALUES, stable unit and depth throughout each stationary search, membership in that catalogue at actual cuts, known $\alpha$ and error resolution, the same actual measured region, full finite integer frames, arbitrary finite precision, finite reached services, actual inclusive handoffs, exclusive serial control and continuing rights. Unit changes during stationary refinement destroy the fixed $z$ used in Theorem 3.4. Unknown error bounds, unseen concurrent Advance, non-Advance source mutation, revocation, source-identity/advice/timing fields, a wrong measurement region, or nonterminating services require separate proofs. Failure of the present algorithm under changed premises is not a general impossibility theorem for them.

The digital extension is conditional on actual finite schedule/update installation and paid source provision. It supplies no arbitrary-real sensor, physical calibration, generator for all infinite sources, uniform physical latency, constant storage under infinite continuation, or one finite completion of an infinite task. Optional live-record acceptance and richer services must be explicitly installed with their own complete-response and rights contracts. A tight catalogue/schedule-dependent bit/query/storage analysis, earlier optimal boundary acquisition and active classification for colliding algebraic catalogues remain separate questions.

The original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization, arbitrary interior-cut, full-response and native-controller tasks retain their own source, control and authority obligations. This finite interface extension does not materialize a conversion to those models or complete the sustained general space/time/boundary/memory research objective. No physical, empirical ML/NN/noise, probabilistic expected-cost, universal information-minimality or kernel-certified theorem is asserted.

[PAID]: RECURSIVE_RELATIONAL_OBSERVATION_PAID_ZECKENDORF_CURRENT_RETURN.md
[NORMAL]: RECURSIVE_RELATIONAL_OBSERVATION_EXACT_CURRENT_BOUNDARY_PROVENANCE.md
[TARGET]: RECURSIVE_RELATIONAL_OBSERVATION_UNCALIBRATED_TARGET_ACQUISITION.md
[CAPPED]: RECURSIVE_RELATIONAL_OBSERVATION_CAPPED_PRECISION_PERMANENT_BLINDNESS.md
[DRIFT]: RECURSIVE_RELATIONAL_OBSERVATION_BOUNDED_UNIT_DRIFT_IDENTIFIABILITY.md

## 追加锚（本行以下为增补区）

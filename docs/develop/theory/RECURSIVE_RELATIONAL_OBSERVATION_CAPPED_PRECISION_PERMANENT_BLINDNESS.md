# Permanent initial-target blindness under capped floor precision

A finite precision cap can leave an initial unread target permanently unidentified even when the receiver may advance the actual source without a bound. For the deterministic floor implementation of the Step/Extent interface, two genuinely reached proper handoffs can have different initial unread first bits, the same complete current point, and the same entire permitted future observation. One explicit pair consists of two death returns. A second construction works for every fixed positive rational unit by paying for sufficiently late handoffs.

These are ordinary conditional symbolic mathematical results, without new Lean/kernel certification. The source dynamics, producer and digital scale service are those of [Paid Zeckendorf observation at a current return][PAID]. The [current-boundary normal-form volume][NORMAL] already supplies event-only history and boundary ambiguity, including its Sections 11–17. The [uncalibrated target-acquisition volume][TARGET] supplies positive direct acquisition with unbounded adaptive precision. The contribution here concerns a different target on the richer, finitely capped interface; those existing results remain in force.

## 1. Actual source, complete blocks and returned states

All positions, depths and source times are nonnegative integers; digits are ordered from low to high. Put

$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,
\qquad
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ for all }j\ge0\}.
$$

Let $Z(A)$ denote the zero-padded finite Zeckendorf word of $A\ge0$, and let $f(x)=x_0$. The map $T$ finds the first adjacent $00$, clears all positions below its first position, changes that first zero to one, and retains higher positions. If no $00$ occurs, it returns $Z(0)$. In particular both pure alternating words are in the domain and map to zero. This is the endpoint-inclusive arithmetic successor, not positional deletion. On the finite core,

$$
T^hZ(A)=Z(A+h)\qquad(A,h\ge0).
\tag{1}
$$

Write $\alpha=(\sqrt5-1)/2$, so $0<\alpha<1$ and $\alpha^2+\alpha=1$. Use the distinct notations

$$
z=0^\infty=Z(0),\qquad a=(10)^\infty,
\qquad Y=10^\infty=Z(1).
\tag{2}
$$

Thus $a$ is infinite alternation, whereas $Y$ has only one nonzero digit.

Every word of $K$ has a unique parsing into blocks $0$ and $10$. On a one the next zero is promised, but passing it still requires a physical raw Read. Set

$$
\mathcal B=\{0,10\}^{<\omega},\qquad C_p=\{pt:t\in K\},
\qquad d=|p|,\qquad N_p=\sum_{j<d}G_jp_j,
$$

$$
M_p=G_{d+1}-N_p,\qquad k_p=M_p-2,
\qquad b_\varnothing=0,\qquad b_{u0}=b_{u10}=M_u-1.
\tag{3}
$$

Every nonempty complete block word ends in zero, so any $t\in K$ can follow it. The empty prefix has $N=0$, $M=2$, $k=0$.

The actual initialized producer of [PAID, Definitions 1.2 and 2.2][PAID] starts at empty prefix, raw cursor zero and time zero. Its installed program, bindings, rights and initial acknowledgement are source independent and paid. Initialization does no Read or Advance. The producer privately retains $p,r,d,N_p,G_d,G_{d+1},k_p$, its actual raw endpoint and binding. Scratch and pending output are empty at Return.

We use its existing correctness, productivity and attainment theorems, including both lifetime endpoints. At an actual return with complete prefix $p$ the raw endpoint is exactly at $d=|p|$, its unread tail is $\operatorname{tail}_d(x)$, its current denotation is $T^r x$, and

$$
b_p\le r\le k_p.
\tag{4}
$$

Every source in $C_p$ actually reaches each return in this interval with acquired prefix exactly $p$. The empty prefix occurs only at return zero. For nonempty $p$ the supplied clock identities are

$$
b_p+N_p=G_d-1,\qquad k_p+N_p=G_{d+1}-2.
\tag{5}
$$

The actual current boundary has coordinates

$$
\partial(d,s),\qquad s=N_p+r,\qquad
G_d-1\le s\le G_{d+1}-2,
\qquad \delta=k_p-r=G_{d+1}-2-s.
\tag{6}
$$

It is the oriented compatible phase arc of length $\alpha^d$ with its actually included wall lifts, not merely an unowned pair of phases. The initial boundary is the whole circle and is treated separately. A proper cut means $d\ge1$; a death return means $r=k_p$, equivalently $\delta=0$.

A Step is one real producer Next. Below death it reads nothing. At death it reads its next complete block, using one raw Read for $0$ and two for $10$, including the forced zero. With the resulting prefix $p'$ it computes $\operatorname{Low}(N_{p'}+r)$, where $\operatorname{Low}(A)=f(Z(A))$, and performs

$$
\operatorname{Emit}(f(T^r x)),\qquad \operatorname{Advance},\qquad \operatorname{Return}
\tag{7}
$$

in this order. Advance increments source time by one. Each reached Read and each finite transaction finishes. Queries and pauses do no autonomous Advance. Prefix and raw depth never decrease; one Step increases depth by at most two. The actual endpoint resumes at its own precise unread tail, as in [PAID, Theorems 3.1–3.2][PAID]. This does not equate the controller with the distinct native seed/payload/Stop controller.

## 2. The capped handoff and its complete public observation

Fix an integer cap $N\ge1$ and one positive rational configuration $q=A/B$, with finite positive integers $A,B$. The same installed deterministic service is used throughout the initialized past and future of each run:

$$
\operatorname{Extent}(n):\qquad
A_{d,n}=\left\lfloor2^nq\alpha^d\right\rfloor,
\qquad 1\le n\le N.
\tag{8}
$$

Here $d$ is this producer's actual acquired-depth cache. This is exactly [PAID, Definition 19.1, formula (73)][PAID], with the receiver restricted to the displayed finite precision range. It is not a selectable error literal or an adversarial replacement for the installed backend. Its finite quadratic arithmetic reads no unread raw bit, finishes each reached invocation and changes neither source time nor raw cursor.

A reply contains the full nonnegative integer in its canonical self-delimiting encoding, the request tag and prescribed fixed framing, followed by its service completion. It represents $A_{d,n}2^{-n}$ and satisfies

$$
\left|A_{d,n}2^{-n}-q\alpha^d\right|<2^{-n}.
\tag{9}
$$

There is no reduction modulo one, clipping, saturation or discarded integer part. The cap limits requested resolution; it does not clip reply numerators. No behavior for an out-of-cap request is added to the comparison.

A legal handoff follows [PAID, Definition 16.1][PAID]. An actual finite driver prefix ends at a producer Return and transfers one installed persistent exclusive continuation turn. Return zero is allowed. The receiver gets a fixed acknowledgement and starts its own local count at zero. It does not receive the driver command count, old events, $p,r,d,N_p$, wall data, a branch flag, source identity or source-dependent old client advice. The actual producer, raw endpoint, acquired prefix and private counters remain those reached by that run. The driver cannot act concurrently after transfer.

The permitted receiver is deterministic and causal, with the same source-independent initial state and common parameters in the compared worlds. Its source operations are Step and stationary Extent requests in the range (8). It can pause, perform source-independent local computation, check its installed descriptors and possession, stop, or release the turn according to the declared protocol. A Step can cross zero slack; this continuing right is not an Arm budget. Release has its common declared control effect and ends this turn; it does not supply a fresh informative handoff or hidden driver Advances.

The complete allowed observation retains every request and precision, full Extent integer and frame, fixed acknowledgement, real Emit value and Emit/Advance/Return order, local completed request and Step counts, and declared mode, possession and turn-control outcomes. Private raw responses, raw Read counts, work, storage, latency, absolute old source time, cursor/depth, private registers, endpoint contents or identity as advice, and pre-handoff events are excluded. Equality will cover all allowed fields, without projecting away any one of them. Equal descriptor literals express two lawful installations of the same source-independent protocol; they do not copy a right from an observed numeral.

Wall/Park, record export, original counter-bearing task replies, raw getters, private-register queries and the acquired-record interface of [PAID, Section 18][PAID] are not installed by this handoff. Naming one does not make it an operation or give it an informative refusal. No such uninstalled outcome is used below.

For a handoff world $W=(x,r)$ let $p(W)$ be its actually acquired prefix and define the fixed target

$$
\tau(W)=\bigl(\operatorname{tail}_{|p(W)|}x\bigr)_0.
\tag{10}
$$

This is the first raw bit unread at the initial handoff. It is neither the lowest digit of the current point nor a target reset after each Step. The theorem continues to hold when the same exact $q$ is publicly given to both receivers.

## 3. A permanent zero cell for the actual floor service

**Lemma 3.1 (Zero replies for a fixed small unit).** For every $N\ge1$, choose once and for all

$$
q_N=2^{-(N+1)}.
\tag{11}
$$

For every returned depth $d\ge0$ and every $1\le n\le N$, the actual reply integer (8) is zero. This remains true at every later returned cut, regardless of the number of Steps.

**Proof.** Since $0<\alpha^d\le1$,

$$
0<2^nq_N\alpha^d
=2^{n-N-1}\alpha^d\le\tfrac12<1.
\tag{12}
$$

The floor is exactly zero. Its error is $q_N\alpha^d<2^{-n}$, so it also satisfies the numerical specification (9). Every later depth is another nonnegative integer, hence the same inequality applies. Equal requested $n$ gives the same canonical zero integer and every prescribed framing field. The calculation establishes the installed deterministic reply, not merely permission to choose zero. It need not establish equal private arithmetic effort. $\square$

**Lemma 3.2 (Persistence at a late depth).** Fix any $q>0$ and $N\ge1$. If an actual handoff has depth at least $D$ and $2^Nq\alpha^D<1$, every permitted future Extent reply is zero.

**Proof.** At every later return its depth $d\ge D$, since the actual producer only extends its prefix. Thus

$$
0<2^nq\alpha^d\le2^Nq\alpha^D<1.
$$

Apply the same deterministic floor rule. $\square$

These are stationary-query conclusions as well: querying forever at one cut does not change its depth or its reply. Repetition is not independent noise sampling.

## 4. Explicit actually reached witnesses

**Proposition 4.1 (The empty/proper witness).** There are legal initial and proper handoffs with common complete current point $Y$, but different targets. With the unit (11) they have identical capped scale replies at every future return.

**Proof.** Hand off the source $Y$ at return zero. It has acquired nothing, its current point is $Y$, and its target is one. Separately initialize source $z$. Its first Next starts at the empty death return, physically reads zero, appends $p=0$, emits $\operatorname{Low}(0)=0$, Advances and Returns at $r=1$. Its depth is one and its unread tail remains $z$, so its target is zero. The first $00$ of $z$ starts at position zero, giving $Tz=Y$ exactly. The actual handoff permits return zero; a different Park service's proper-cut guard is irrelevant. Lemma 3.1 supplies the scale assertion. The private histories and initial boundaries are different. $\square$

**Proposition 4.2 (Two proper death returns).** The following handoffs are both genuinely reached from the stated source-independent producer initialization:

| World | Original source | Acquired prefix | $r$ | $d$ | $N_p$ | $s$ | $\delta$ | Initial unread tail | $\tau$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $W_0$ | $z$ | $0$ | $1$ | $1$ | $0$ | $1$ | $0$ | $z$ | $0$ |
| $W_1$ | $a$ | $10$ | $2$ | $2$ | $1$ | $3$ | $0$ | $a$ | $1$ |

Their complete current points are both $Y=Z(1)$. Their boundaries are respectively $\partial(1,1)$ and $\partial(2,3)$.

**Proof.** World $W_0$ is the actual one-call history in Proposition 4.1. For its prefix $0$, (5) gives $b_0=k_0=1$. Its handoff is therefore both birth and death, with the inclusive lifetime equality retained.

For $W_1$, the first Next on $a$ physically reads one and then its forced zero. It appends $10$, has $N_{10}=G_0=1$, emits $\operatorname{Low}(1)=1$, Advances and Returns at time one. The recurrence gives $G_2=3,G_3=5$, so $M_{10}=4$, $b_{10}=1$ and $k_{10}=2$. The next call starts strictly below $k_{10}$ and reads nothing. It emits $\operatorname{Low}(2)=0$, Advances and Returns at time two with acquired prefix still $10$ and raw cursor still two. This is precisely the inclusive death return, before the next acquisition. No convenient compatible state has been substituted for the initialized execution.

The raw tail after deleting the one actually acquired zero of $z$ is $z$. The raw tail after deleting the two actually acquired bits $10$ of $a$ is $a$. Hence their targets differ. Meanwhile $a$ contains no $00$, so the endpoint-inclusive dynamics gives

$$
Ta=z,\qquad Tz=Y,\qquad T^2a=Y.
\tag{13}
$$

These are equalities of complete infinite words, not just phase equalities. Thus the current points coincide. Formula (6) gives the listed distinct boundaries and zero slacks. The hidden driver histories contain respectively one and two actual transactions, with pre-handoff Emit words $0$ and $10$; those histories are not asserted equal. $\square$

The comparison can therefore impose the common promise of properness, or even the common promise of an initial death return, without revealing the target. Neither promise supplies the actual depth or boundary.

## 5. Exact future points and complete adaptive coupling

**Lemma 5.1 (One fixed pair for the entire future).** For the same two actual runs of Proposition 4.2 and every finite $h\ge0$, their current points after $h$ additional Steps are

$$
T^{1+h}z=T^hY=T^{2+h}a=Z(1+h).
\tag{14}
$$

Their local Step $j+1$ emits $f(T^jY)$ and then performs its own Advance and Return, in the same public order. Their unread raw tails remain $z$ and $a$, respectively.

**Proof.** Apply $T^h$ to the complete-word equalities (13), and use (1) for the final identification. Producer correctness and exact tail resumption identify these mathematical iterates with the actual initialized and resumed runs. Each reached call finishes, including on $a$; the producer never tries to recognize infinite alternation or find a nonexistent first $00$ in its raw source. Every future acquired block on $z$ is $0$, and every future acquired block on $a$ is $10$. Each forced zero in the latter is physically read. Removing any such finite acquired block word leaves the respective same infinite raw tail. Queries and pauses do not affect either calculation. $\square$

Their private states remain different. Already the first post-handoff Step reads one raw bit in $W_0$ and two in $W_1$. After $h$ Steps their actual absolute times are $1+h$ and $2+h$, while both local Step counts are $h$. Their depths, acquired words, endpoints, caches, Read counts, work and storage are not equated. Equation (14) concerns the actual complete current point and public trajectory, not the entire private producer state.

**Theorem 5.2 (Complete capped interaction equality).** For every $N\ge1$, install the same floor program and the same fixed unit $q_N$ in the two worlds of Proposition 4.2. For every deterministic causal receiver of Section 2, the complete permitted interaction is identical in both worlds. The pair is independent of the receiver and works for all finite future lengths and every infinite permitted continuation.

**Proof.** Initially the receiver has the same cap, source-independent state, program, descriptor literals, fixed acknowledgement, local zero counts and continuing exclusive right. It may also have the same exact $q_N$. Induct on the completed request prefix, retaining equal local state, observed fields, counts and mode. Determinism and causality give the same next request, parameter, computation, pause, release or stopping decision.

For Extent, the same requested precision lies in $1\le n\le N$ in both worlds. Lemma 3.1 gives the same actual integer zero, full frame and service completion, without moving either source. For Step, both continuing rights are valid, and Lemma 5.1 gives the same Emit value and intermediate Emit/Advance/Return sequence. Each local completed-Step count increases by one; the next current points agree. The private Read branch is not an allowed observation. Each invocation finishes in both worlds.

A pause has no source effect. Source-independent local computation and actual possession checks have the same inputs and declared outcomes. Release makes the same permitted mode transition and ends this turn; it does not create unobserved driver motion or a new informative protocol. These cases exhaust the installed interface. No uninstalled service or invented refusal is needed. They preserve the induction, including full integer frames, actual requests and local completion counts.

Every finite observation prefix therefore agrees, including public events inside a Step. Each coordinate of an infinite permitted transcript lies in such a finite prefix, so the entire infinite transcript agrees as well. This is equality of infinite sequences coordinate by coordinate. It does not assert that an infinite interaction finishes physically in finite time or at finite cost. $\square$

## 6. Permanent nonfactorization of the initial target

For a world $W$, a deliberately generous mathematical observation may contain its entire future current-point trajectory, every capped reply at every returned local cut, and the common source-independent control data:

$$
\Xi_{q,N}(W)=
\left((T^{r+h}x)_{h\ge0},
\left(\left\lfloor2^nq\alpha^{d_h(W)}\right\rfloor\right)_{h\ge0,\ 1\le n\le N},
\text{common control data}\right).
\tag{15}
$$

Here $d_h(W)$ is its actual depth after $h$ further Steps. The first component gives more than the receiver acquires; no whole-current-point getter is installed by this definition.

**Theorem 6.1 (Permanent initial-first-bit blindness).** For every $N\ge1$, on the actual floor backend with the one unit $q_N$, no mathematical function of (15) recovers $\tau$ on all legal handoffs. For each receiver of Section 2, no function of its whole permitted infinite transcript recovers $\tau$ on all legal handoffs. In particular there is no uniformly correct total deterministic causal initial-first-bit decoder in this interface, even if the input domain is restricted to proper death handoffs.

**Proof.** Lemmas 3.1 and 5.1 give

$$
\Xi_{q_N,N}(W_0)=\Xi_{q_N,N}(W_1),
\qquad \tau(W_0)=0\ne1=\tau(W_1).
\tag{16}
$$

A function recovering $\tau$ would have to assign both zero and one to this single input. This is impossible even for an uncomputable function of the infinite observation. Theorem 5.2 supplies the same collision for each receiver's complete adaptive transcript.

A total deterministic causal decoder must finish after finitely many operations on each world. The coupled observations give the same stopping decision and output, which cannot be correct in both. Waiting forever violates totality. Repeated or averaged scale queries do not help, since their literals are exactly the same deterministic zeros. The one pair in (16) survives all future Steps, so the conclusion is stronger than a separate finite-horizon obstruction for each chosen horizon. $\square$

The target of this theorem remains the initial raw bit. Actual future Emits are directly delivered, and the current lowest spatial bit is identical in the two worlds. Even the whole current point does not determine this hidden-cut target across different boundaries. A statement about recovering a boundary or history is a different task.

## 7. Every fixed positive rational unit has late blind handoffs

**Theorem 7.1 (Arbitrary fixed-unit strengthening).** For every positive rational $q$ and every integer $N\ge1$, the same deterministic floor service with that very configuration $q$ has two actual proper handoffs with different initial unread first bits and identical complete permitted future observations for every receiver of Section 2. They also have identical observations (15). Thus even exact prior knowledge of the fixed unit does not yield uniform initial-first-bit recovery over all legal hidden handoffs under a finite cap.

**Proof.** Fix $q,N$ before either source run. There exists a finite integer $D\ge1$ with

$$
2^Nq\alpha^D<1.
\tag{17}
$$

For completeness, $\alpha>1/2$, since otherwise $\alpha^2+\alpha\le3/4$. Hence $\alpha^2=1-\alpha<1/2$. Choose a positive integer $k$ with $2^k>2^Nq$ and set $D=2k$. Then $\alpha^D<2^{-k}$, proving (17). This is a symbolic existence argument, with no evaluated search.

Set the finite integer

$$
R=G_{D+1}.
\tag{18}
$$

Actually run original source $z$ for $R$ Next calls and original source $a$ for $R+1$ Next calls. Each finite prefix completes by producer productivity. At a nonempty actual return of depth $1\le d\le D$, (4) gives

$$
r\le k_p=G_{d+1}-N_p-2
\le G_{D+1}-2<R.
\tag{19}
$$

The only empty return has time zero. Therefore both selected handoffs have depth greater than $D$, and both are proper. These are actual initialized histories; (19) rules out shallow actual prefixes rather than assigning a convenient cache.

Their complete current points are

$$
T^Rz=Z(R),\qquad T^{R+1}a=T^Rz=Z(R).
\tag{20}
$$

The first run has acquired only $0$ blocks and leaves raw tail $z$; the second has acquired only $10$ blocks and leaves raw tail $a$. Their initial target bits are zero and one. At all later returns both depths remain greater than $D$, so (17) and Lemma 3.2 force every capped floor integer to remain zero.

Equality of current points in (20) gives the entire future current trajectory $Z(R+h)$ and the actual future Emit/Advance/Return sequence, exactly as in Lemma 5.1. The complete adaptive induction of Theorem 5.2 applies with the unchanged common $q$. Equation (15) is identical and the target differs, so the contradiction of Theorem 6.1 applies too. Giving this same $q$ to both clients preserves all equalities.

The driver lengths $R$ and $R+1$ depend on the fixed $q,N$, not on raw responses. They are real paid finite histories, with every Advance, Read and forced zero executed. Their counts are hidden by the handoff contract. No absolute clock is freely shifted. The configuration and rounding rule stay the same in both worlds for their entire initialized histories and futures. $\square$

These late cuts need not be death returns. The stronger common death promise is established by Proposition 4.2 for the explicit small unit. The theorem does not interchange these two assertions or claim zero replies at every unbounded precision for one positive unit.

## 8. Preserved positive recovery and separating information

**Proposition 8.1 (Known common boundary remains sufficient for finite tail targets).** With a genuinely known initial boundary $\partial(d,s)$, $d\ge1$, the existing event decoder recovers any finite initial-tail prefix. In particular its first bit is identified from the $(\delta+1)$-st future Emit, with that call counted through Return if return completion is required.

**Proof.** For the first $\delta$ Steps the actual producer is below death and reads nothing. The next call reaches death at known depth $d$. Its two possible Emit constants are

$$
c_0=\operatorname{Low}(G_{d+1}-2),\qquad
c_1=\operatorname{Low}(G_{d+2}-2).
\tag{21}
$$

They are different by the supplied child-split theorem, as used in [NORMAL, Theorem 7.1 and Definition 8.2][NORMAL]. The observed constant therefore identifies the actual next block $0$ or $10$, and hence the initial first bit. After each decoded block the same known-boundary update permits repetition, giving every finite target as already proved in [NORMAL, Sections 8–9][NORMAL]. Its exact fixed-length bound is $G_{d+m}-1-s$ for $m\ge1$; its finer per-tail stopping theorem retains its original domain and costs. We do not count these existing inverse results as new. $\square$

The witnesses in Proposition 4.2 have different initial depths and boundaries. A promise that both are proper, or both at death, is not possession of one known common boundary. Their identical next Emit constants may label different raw blocks because interpreting (21) uses the known depth.

**Proposition 8.2 (Unbounded precision separates the explicit pair).** At the unadvanced handoffs of Proposition 4.2, for every $q>0$ there exists a finite precision $n$ at which the actual floor replies differ.

**Proof.** Their true scales are $q\alpha$ and $q\alpha^2$, with positive difference

$$
q(\alpha-\alpha^2)=q\alpha^3>0.
\tag{22}
$$

Choose a finite $n$ with $2^nq\alpha^3>1$. If the two scaled values had the same floor integer $j$, they would both lie in $[j,j+1)$ and their difference would be less than one, a contradiction. In the capped zero example this precision necessarily exceeds $N$. $\square$

This is an existential separating query for this pair. It does not say that one literal universally identifies an arbitrary unknown unit, depth or cut, or that the receiver is given the required precision.

**Proposition 8.3 (The unbounded direct decoder is unaffected).** If all finite precisions $n\ge1$ are allowed, the existing direct target decoder recovers the initial unread first bit, and more generally each finite initial-tail prefix, on all legal handoffs without first learning the unit or boundary.

**Proof.** We recall its mechanism to identify the hypothesis changed by the cap. At each paused returned cut the scale $z'=q\alpha^d$ is positive. Refining until a literal numerator exceeds $64$ terminates: for sufficiently small $\varepsilon=2^{-n}$ every valid reply $u$ has $u\ge z'-\varepsilon>64\varepsilon$. Execute one real Step and query its new return at the same precision, obtaining $v$. The true scale ratio is one of $1,\alpha,\alpha^2$, according to the actual depth increment $0,1,2$.

The true candidate $c$ satisfies $|v-cu|\le(1+c)\varepsilon$. Distinct candidates differ by at least $\alpha^3>1/5$: indeed $\alpha>3/5$ follows from $\alpha^2+\alpha=1$. If two candidates passed, their difference times $u$ would be at most $4\varepsilon$, whereas $u>64\varepsilon$ makes it greater than $64\varepsilon/5$. Thus the candidate is unique and identifies the actual newly read block, including its physically consumed forced zero. Repeating from each actual returned cut reconstructs exactly the new raw blocks. Every finite target lies in a finite block, each next block is acquired after finitely many real Steps, and each refinement is finite. The decoder therefore stops at the actual return cut that acquired the target block, allowing its subsequent stationary query and output there. This is the existing theorem of [TARGET, Sections 2–4][TARGET], with its full-error positive quantifier; the actual floor service is one permitted implementation.

In our capped pairs every permissible numerator is zero, so the initial refinement threshold cannot be reached. The existence of arbitrarily high precision, used in this positive proof, is precisely what the capped interface removes. $\square$

The two-update boundary acquisition of [PAID, Sections 17–20][PAID] is likewise preserved under its unbounded-precision assumptions. A receiver that has genuinely acquired its live record can use its declared LiveStep, guarded Peek and moving Seek with their original rights and costs. The capped handoff does not manufacture that record or install those operations merely because their specifications exist elsewhere.

**Proposition 8.4 (Added actual records distinguish this pair).** For the base pair, an actually acquired initial-prefix record, exact initial depth, or authenticated same-run absolute completed-Advance count distinguishes the worlds. A separately installed and authorized read of the initial raw target would do so as well. The complete initial current point alone does not.

**Proof.** The respective prefix records are $0$ and $10$, the depths are one and two, and the absolute counts are one and two. Reading the fixed target returns zero and one. Each listed distinction is literal under its additional acquisition and authenticity premise. The current point is already the same $Y$ by (13), so giving that whole point preserves the collision. $\square$

These are separating data for a specified pair, not universal recovery theorems for all cuts. A possible historical witness, printed descriptor or mathematical inverse does not acquire an actual record, authenticate a count or create a raw-read right.

## 9. Same-run costs and the meaning of infinity

**Proposition 9.1 (Exact source-operation accounting).** At any handoff $(x,r)$ with actual depth $d$, and after a finite continuation of $h$ completed Steps with depth $d_h$, the actual cumulative and incremental vectors, in the order

$$
(\operatorname{Read},\text{raw delivered bits},\operatorname{Next},
\operatorname{Emit},\operatorname{Advance},\text{post-initialization producer Return}),
$$

are respectively

$$
(d,d,r,r,r,r),\qquad(d_h-d,d_h-d,h,h,h,h),
\qquad0\le d_h-d\le2h.
\tag{23}
$$

For $Q$ completed Extent requests there are separately $Q$ paid scale-service completions and no resulting raw Read or Advance.

**Proof.** Each actual raw bit passed by the sequential cursor is read once, including every forced zero. The cursor and acquired-prefix length are identical, giving the first two coordinates and their difference. Every real Next has exactly one Emit, Advance and producer Return. Initialization's fixed acknowledgement is not one of these triples. One Step acquires at most a two-bit block, giving the bound. Extent preserves the source fields by its actual service contract. $\square$

In the explicit proper pair the driver histories have one and two producer triples, and one and two raw Reads. For every finite post-handoff $h$, both worlds have exactly $h$ further source Advances but can have different additional Read counts. Hidden costs remain costs; their absence from the observation does not make them zero.

The rational $q_N$ has finite dyadic configuration length $O(N+1)$. A general rational $q$ retains its actual finite numerator and denominator storage. Actual installation of programs, configuration, endpoint bindings, continuing rights and handoff protocol is paid. So are driver command acquisition and execution, parsing and framing, full literal integer and event I/O, descriptor and possession checks, cache access, finite integer/quadratic arithmetic, scratch allocation/scanning/clearing, local counters and retained outputs. A zero reply does not imply zero service work.

For Theorem 7.1 the actual pre-handoff driver lengths are $R$ and $R+1$ from (18). These Advances and their raw acquisitions are part of the construction's cost, rather than free changes of coordinates. No minimum $D$, $R$, precision, query number, bit work, latency or storage is claimed.

The source contract has its separate provisioning, generation/delivery and backend storage terms, denoted $\iota_x$, $\gamma_x$ and $\sigma_x$ in [PAID, Section 8][PAID]. Driver storage, producer prefix and caches, private unit, scale-service workspace, receiver state and any archives or external retained material must be counted simultaneously. No equality of private work, memory or latency between the compared worlds is asserted. An infinite input is not supplied with a finite generator or finite-cost infinite tape by these theorems.

Every reached finite call and finite driver/receiver prefix completes under the contract. The entire infinite-future equality means that every finite coordinate agrees on the same fixed pair. It is not a finite physical completion, a uniform deadline, a bounded total output, or a constant-memory infinite execution. The collision includes intermediate public Emit events and therefore does not rely on postponing an answer until Return; the particular one-Advance distinction for early answers in [TARGET, Section 9][TARGET] does not resolve it.

## 10. Exact contribution relative to the existing results

The following are mathematical suppliers, with their original hypotheses and boundaries retained.

| Published source | Existing result used here | Added assertion in this volume |
| --- | --- | --- |
| [PAID, Sections 1–3, 7 and 12][PAID] | Endpoint-inclusive $T$, productive initialized sequential producer, physical forced-zero acquisition, correct Emit/Advance/Return, exact raw-tail continuation, attained inclusive clocks and owned boundary coordinates | The witnesses use those actual histories; none of these ingredients or endpoint identities is newly claimed. |
| [NORMAL, Sections 2–9][NORMAL] | Complete-word intertwinement, fixed-boundary tail bijection and finite provenance, exact first event difference, finite and per-tail known-boundary event inverses | The comparison changes the hidden initial boundary and initial unread target, while matching the complete current point. |
| [NORMAL, Sections 11–17][NORMAL] | All actual histories over each complete point; countably infinite possible paid boundaries with unbounded depth; finite causal entrance/stopping-boundary obstructions; a natural-core fixed pair with permanently distinct boundaries; necessary unbounded supplementary-record range | These are existing event-only history/boundary results. The new conjunction retains the actual additional capped Extent channel and proves a different initial-bit target remains permanently unresolved by that richer observation. No generic future-fibre or cardinality theorem is presented as new. |
| [PAID, Proposition 16.3][PAID] | Static finite-observation unknown-unit/depth ambiguity, with units allowed to differ between worlds | Here both compared worlds use the same deterministic backend and the same fixed unit; all future visible Steps are allowed. |
| [PAID, Sections 17–21][PAID] | Unbounded-precision two-update boundary acquisition, actual floor realization, acquired-record live updates, guarded finite DATA and moving Seek | The actual floor realization is reused. The finite cap produces permanent zeros, so the positive unbounded refinement hypothesis is unavailable. |
| [TARGET, Sections 2–8][TARGET] | Direct unbounded-precision initial-prefix acquisition, target-block costs, full-error lower bounds, and a same-floor-backend version before a fixed-cut target acquisition | Our obstruction varies hidden handoffs and survives the entire future; it is not the existing finite pre-target lower bound or merely a choice of another allowed error trace. |

The substantive conjunction is the explicit different-target actual pair, equality of the whole current trajectory, permanent equality of every capped literal from one floor program and unit, and complete adaptive equality with target nonfactorization. Theorem 7.1 strengthens the small-unit example to every fixed positive rational configuration using sufficiently late paid proper handoffs. The particular small-unit construction additionally retains two actual death cuts.

The normal-form volume already explains that event-only current-point fibres can hide histories and actual paid frontiers. Its fixed-pair boundary result does not assert that its pair has different initial unread first bits, or that an added Extent channel remains equal. Those are separate obligations discharged here. Conversely our first-bit collision does not replace its each-point history classification, exact cardinalities, boundary tasks or record-range theorem.

The factor-through-observation contradiction and ordinary causal reply induction are existing general mechanisms. Endpoint collapse, finite-core arithmetic, clock geometry, known-boundary event decoding, the floor backend and unbounded acquisition are also existing supply. The results here are a repository-derived conditional synthesis at this interface, without a claim of worldwide priority or exhaustive literature search. The three references bind to the named published volumes; no additional bibliography is needed to assert a broader result.

## 11. Applicability and remaining obligations

The negative theorem is for (8), the actual deterministic floor implementation with a fixed finite rational configuration. The numerical error inequality alone would not force an arbitrary selector to produce identical replies in two worlds. No theorem for every implementation satisfying an error bound follows from proving equality for this one backend. Neither rounding rule nor unit changes during a run, and the unit is independent of the unknown raw source.

All conclusions retain the no11 source promise, endpoint-inclusive $T$, exact clock-driven producer, actual initialized and reached returns, finite completion of reached raw and scale services, finite cap $1\le n\le N$, stationary queries, full nonnegative integer replies, continuing exclusive turn, and absence of autonomous or concurrent Advance. They exclude timing, Read-count, private-state, source-identity and old-advice channels. Enlarging the interface or changing these premises requires another comparison proof.

The impossible task is uniform recovery of the initial unread first bit over the legal hidden-handoff domain. The actual future spatial lowest digits are available as Emits. A known common boundary supports its existing finite-tail inverse. Unbounded adaptive precision supports its existing direct target decoder and boundary acquisition. Restricted source/cut promises can make the first bit known. None of these is negated by the present pair.

The distinctions between a complete current point, an initial unread tail, an actual acquired boundary record, a possible history and an authenticated actual history are essential. Complete current-point equality does not equate private producer states. Knowing a fixed unit or a death promise does not acquire an unknown cut. Recovering a boundary later does not rewind the source or change the original target. Printing data does not supply an endpoint, generate an infinite source, or copy a continuing right.

No whole infinite configuration, effective infinite inverse, historical selector, old absolute counter, original history archive or arbitrary raw-source getter is acquired. There is no conversion to an arbitrary native controller or unchanged original service, no new physical sensor or calibration, and no result for moving units, arbitrary noise, non-Advance mutation, concurrent clients or revocation. The finite-clock and rational digital hypotheses do not prove a physical impossibility, an ML/NN statement, a universal resource optimum or a kernel certificate. The general space/time/boundary/memory recovery programme and its source, full-response and persistent-authority bridges retain their separate unresolved obligations. This finite contribution does not complete the sustained research objective.

[PAID]: RECURSIVE_RELATIONAL_OBSERVATION_PAID_ZECKENDORF_CURRENT_RETURN.md
[NORMAL]: RECURSIVE_RELATIONAL_OBSERVATION_EXACT_CURRENT_BOUNDARY_PROVENANCE.md
[TARGET]: RECURSIVE_RELATIONAL_OBSERVATION_UNCALIBRATED_TARGET_ACQUISITION.md

## 追加锚（本行以下为增补区）

## 12. A fixed finite-core pair with precision uncapped after the first Return

**Definition 12.1 (mixed-precision observation).** Keep the initialized producer, persistent exclusive turn, full public framing and excluded channels of Sections 1–2. Fix public $q\in\mathbb Q_{>0}$ and $N\ge1$. Before the first actual Step, Extent requests have $1\le n\le N$; from that Step's Return onward, every finite $n\ge1$ is permitted. At every allowed returned cut the same stationary backend replies

$$
\operatorname{Extent}(n)=\lfloor2^nq\alpha^{D}\rfloor,
$$

where $D$ is the actual acquired depth. There are no Extent calls during a Step. All actual Emit/Advance/Return events and local request counts remain visible. Raw Read contents, their number and latency, private acquired history and registers, old absolute counts and pre-handoff events remain excluded. The target is the first bit of the tail unread at the initial handoff, or its fixed first $m\ge1$ bits; it never resets after a Step.

**Theorem 12.2 (one pair against every causal receiver).** For each such fixed $q,N$, there are two actually attained proper death handoffs on eventually-zero sources with different initial unread first bits and the same complete current point, whose entire permitted mixed-precision interactions agree for every deterministic causal receiver with common source-independent initial data. Consequently no such receiver is finite and correct for either original target on all legal handoffs. For any almost surely bit-outputting randomized receiver with one common world-independent random-tape law, its worst error on this same pair is at least $1/2$.

Proof. Choose once, independently of the receiver, a finite $d\ge1$ with

$$
2^Nq\alpha^d<1.
$$

Use exactly the actually initialized family of [Known unit, hidden offset, Lemmas 4.1–4.4](RECURSIVE_RELATIONAL_OBSERVATION_KNOWN_UNIT_HIDDEN_OFFSET_IDENTIFIABILITY.md#4-complete-actual-deep-family), with additive offset zero and unit $q$. Its two histories are

$$
\begin{array}{c|c|c|c|c}
 &x&p&r&\text{initial unread tail}\\\hline
 A&Z(G_d)=0^d10\,0^\infty&0^d&G_{d+1}-2&10\,0^\infty\\
 B&Z(0)=0^\infty&0^{d+1}&G_{d+2}-2&0^\infty.
\end{array}
$$

The supplier's inclusive attainment clocks give genuine proper deaths with $N_p=0$. The recurrence gives $G_d+r_A=r_B$, and finite-core succession gives equality of the whole words

$$
T^{r_A}Z(G_d)=Z(r_B)=T^{r_B}Z(0).
$$

Both sources have finite support. At the initial depths $d,d+1$, every permitted numerator is zero, since for $1\le n\le N$,

$$
0<2^nq\alpha^{d+1}<2^nq\alpha^d<1.
$$

Thus any number of stationary capped queries has equal complete replies. If a receiver never Steps, every allowed finite observed prefix still agrees; a common finite answer cannot give both different targets.

If it Steps, A physically reads $10$, including the forced zero, while B physically reads $0$. The supplier's first-Step calculation gives the common Emit $\operatorname{Low}(r_B)$ and, after Advance and Return,

$$
D_1=d+2,\qquad s_1=G_{d+2}-1,\qquad t_1=0^\infty,
$$

in both worlds. Their private values remain $N_A=G_d,N_B=0$ and $r_{A,1}=r_A+1,r_{B,1}=r_B+1$. They have not become the same private history. Nevertheless $N_A+r_{A,1}=N_B+r_{B,1}=s_1$, so the death slack $G_{D_1+1}-2-s_1$ agrees.

At any later matched Return the two worlds have the same depth, the same $s=N_p+r$ and the same unread zero tail. Positive slack makes both read nothing; zero slack makes both read the next zero. Each branch gives the same Emit, increments $s$ by one, and updates depth and slack identically. This is precisely the invariant of the supplier's Lemma 4.4. Hence at every later return and every finite precision, including those above $N$,

$$
\lfloor2^nq\alpha^{D_A}\rfloor
=\lfloor2^nq\alpha^{D_B}\rfloor.
$$

Causal induction over local actions, requests, replies and the events within Steps now gives full interaction equality. The first bits, and therefore every fixed nonempty initial prefix, differ. Equal finite outputs cannot be correct on both worlds; noncompletion fails the stipulated total recovery task.

For the randomized assertion, use one random tape $R$ with a law independent of the chosen world, also including any source-independent random initial state. Condition on each fixed tape: the preceding causal induction is pathwise and uses the same fixed pair. Thus the output-bit law is common to A and B. If $p$ is its probability of one, the error probabilities are $1-p$ in A and $p$ in B, and their maximum is at least $1/2$. Almost sure output is needed here to interpret these as the two bit-error probabilities. $\square$

This is a repo-derived application of the cited attained finite-core family and this volume's zero-cell estimate. It strengthens the precision schedule, not the source interface. Its quantifier order is $\forall q,N\ \exists(W_A,W_B)\ \forall D$; the pair does not depend on a receiver's queried precisions. No uncapped query is allowed before the first Step, and uncapping occurs only after its Return. Revealing the differing raw Reads, their count, timing or private history changes the observation and is outside this assertion. Equal allowed observations do not equate private costs or recover an original history; all supplier acquisition and resource boundaries remain in force.

## 追加锚（本行以下为增补区）

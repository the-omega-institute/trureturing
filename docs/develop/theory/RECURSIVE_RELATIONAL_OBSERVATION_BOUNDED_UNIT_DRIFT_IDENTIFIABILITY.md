# Sharp class-wide identifiability under bounded unit drift

A moving measurement unit changes the possible one-Step scale ratios from three points to three intervals. A publicly supplied subcritical drift bound keeps those intervals separated and permits exact acquisition of every finite initial raw-tail target. At the critical bound, a single public rational parity program already prevents any common exact finite decoder over its hidden configurations and actual hidden handoffs. The negative proof uses one common configuration in two genuinely initialized runs, literal agreement of a decoder's finite initial floor replies, and exact equality of every permitted future response after their first Step.

All results are ordinary conditional symbolic mathematics. The source, clocks and rights below are explicit hypotheses. No new Lean/kernel certification, physical implementation or external priority claim is made. The mathematical suppliers are [PAID][PAID], [NORMAL][NORMAL] and [TARGET][TARGET]. The moving-unit service is an extension of their fixed-unit model.

## 1. Source, physical acquisition and actual return cuts

Indices and times are nonnegative integers; digit positions run from low to high. Put

$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,
\qquad
\alpha=(\sqrt5-1)/2,
\qquad
c=\alpha^{-1/2}.
\tag{1}
$$

Thus $0<\alpha<1$ and $\alpha^2+\alpha=1$. The source space is

$$
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ for every }j\ge0\}.
$$

Write $Z(A)$ for the zero-padded finite Zeckendorf word of an integer $A\ge0$, $f(x)=x_0$, and $q_m(x)$ for its first $m$ digits. The endpoint-inclusive arithmetic successor $T$ clears positions below the first adjacent $00$, puts one at its first position, and leaves higher digits fixed. If there is no $00$, it sends the word to $Z(0)$. Both pure alternating words are included. This is not positional deletion. The supplied finite-core identity is

$$
T^hZ(A)=Z(A+h)\qquad(A,h\ge0).
\tag{2}
$$

Every $x\in K$ parses uniquely into blocks $0$ and $10$: a one is paired with its promised next zero. Set

$$
\mathcal B=\{0,10\}^{<\omega},\qquad
C_p=\{pt:t\in K\},\qquad
N_p=\sum_{j<|p|}G_jp_j,
$$

$$
M_p=G_{|p|+1}-N_p,\qquad k_p=M_p-2,
\qquad b_\varnothing=0,\qquad b_{u0}=b_{u10}=M_u-1.
\tag{3}
$$

A nonempty complete block word ends in zero and can be followed by every $t\in K$. The empty prefix has $N=0,M=2,k=0$.

Use exactly the initialized clock-driven producer of PAID Definitions 1.2 and 2.2. Its actual sequential endpoint holds one fixed source $x$. Each Read delivers the next original raw bit and moves the cursor by one; every reached Read finishes. Even a forced zero is physically read before the cursor passes it. There is no raw rewind, random access or skip. Initialization is source independent, reads nothing, performs no Advance and gives a fixed acknowledgement.

At a returned state the producer holds its actually acquired complete word $p$, absolute completed-Advance count $n$, raw cursor $d=|p|$, caches $N_p,G_d,G_{d+1},k_p$, its original endpoint and binding. Scratch and pending output are empty. The supplied attainment theorem states that every $x\in C_p$ actually reaches every cut

$$
b_p\le n\le k_p
\tag{4}
$$

with precisely that acquired $p$. The empty word occurs only at $n=0$. For $d\ge1$ the supplied identities are

$$
b_p+N_p=G_d-1,\qquad k_p+N_p=G_{d+1}-2.
\tag{5}
$$

One Step is one actual producer Next. If $n<k_p$, it reads nothing. If $n=k_p$, it reads the next complete block: one physical Read for $0$, two for $10$. With the resulting $p'$ it computes $\operatorname{Low}(N_{p'}+n)$, where $\operatorname{Low}(A)=f(Z(A))$, and actually performs Emit, Advance, Return in that order. Advance increases $n$ by one. The current point at a returned state is $T^n x$. The original raw endpoint remains at $|p|$ and resumes at its precise unread tail. Every finite run is productive, including on alternating sources; executing the producer does not search an infinite raw word for its first $00$.

The only one-Step depth increments are

$$
g\in\{0,1,2\};\qquad
k_{p0}=k_p+G_d,\qquad k_{p10}=k_p+G_{d+1}.
\tag{6}
$$

Appending $0$ leaves $N$ fixed; appending $10$ at cursor $d$ adds $G_d$. These clocks and their endpoint-inclusive actual reachability are supplied by PAID, rather than new clock formulas.

For completeness, the intrinsic proper boundary has coordinates $(d,s)$, with

$$
s=N_p+n,\qquad G_d-1\le s\le G_{d+1}-2,
\qquad \delta=G_{d+1}-2-s=k_p-n.
\tag{7}
$$

It is the actual paid-frontier compatible phase region, including ownership at both walls. With $\phi=1/\alpha$, $e_j=[-j\phi]$ for integer $j$, set $(A_d,B_d)=(G_{d-1},G_d)$ for even $d$ and $(G_d,G_{d-1})$ for odd $d$. The initial and terminal walls are $e_{A_d-s},e_{B_d-s}$, in positive arc order, and the arc length is $\alpha^d$. Their included lifts are respectively $\chi_+(A_d-s)$ and $\chi_-(B_d-s)$, where $\chi_\pm(1)=x_1^\pm$ and $\chi_\pm(j)=Z(-j)$ for $j\le0$. PAID supplies this ownership formula; $x_1^\pm$ are its two specified split-side points. At zero labels the owned point is $Z(0)$, not a fictitious split side. The empty frontier is the whole circle, with depth zero and slack zero, and is treated separately from (7). Birth and death returns in (4) are both included.

## 2. Moving-unit service, observation and target

**Definition 2.1 (An explicit extension).** Fix a public factor $\beta\ge1$. A schedule assigns a positive unit $q(n)$ to each original absolute completed-Advance count $n$, with

$$
\beta^{-1}\le\frac{q(n+1)}{q(n)}\le\beta
\qquad\text{for every }n\ge0.
\tag{8}
$$

The promise applies from initialization, including all driver calls before handoff. A unit is stable during all stationary queries and pauses at a returned cut. It changes only with an actual producer Step to the next count, including a read-free Step and every actual Next inside a wrapper. There is no unobserved autonomous Advance. Extent is unavailable inside an unfinished Step.

Finite rational implementations have a fixed finite program, finite private configuration and paid computation. The program uses the original counter and its own source-independent data, never unread source bits. It is valid on every raw source and neither selects nor replaces one. In particular $q(n)$ is not indexed by the number of externally named commands while ignoring internal Steps. Abstract positive real schedules may also be considered, conditional on the same stability and finite-response hypotheses. No finite generator or arbitrary-real arithmetic service for all such schedules is asserted.

At actual depth $d$ and count $n$, Extent$(\nu)$ for any finite integer $\nu\ge1$ supplies a complete canonical self-delimiting nonnegative integer $a$ with

$$
\varepsilon=2^{-\nu},\qquad u=a\varepsilon,\qquad
|u-q(n)\alpha^d|\le\varepsilon.
\tag{9}
$$

The reply includes the entire integer part, request identification, prescribed framing and service completion. There is no modular reduction, clipping or saturation. Each reached service finishes finitely and performs no raw Read or Advance. A service completion is distinct from a producer Return. Errors may be adaptive, correlated, biased and nonnested, subject to every closed inequality (9).

The intended region is always the producer's same actual paid-frontier compatible region. Its normalized length is $\alpha^d$, including length one at the empty frontier. This is not a chord, shorter circular wall distance, complement arc or material length of an infinite tape.

The rational floor realization of this extension is

$$
a=\left\lfloor2^\nu q(n)\alpha^d\right\rfloor.
\tag{10}
$$

It is finite exact rational/quadratic arithmetic for each finitely represented rational $q(n)$. PAID formula (73) instead contains one fixed $A/B$ throughout acquisition. Its unchanged fixed-unit backend does not implement (10) for varying units. An implementation must actually install, store, compute and pay for the schedule and every used unit. PAID's fixed-unit bit bounds are not automatically bounds for that extension.

**Definition 2.2 (Handoff and full observation).** A finite driver history from the original initialization ends at any actual returned cut $(p_0,r_0)$, including zero or a proper lifetime endpoint. It transfers a previously installed persistent exclusive Step/Extent turn, preserving the same producer, raw endpoint, cursor and binding. The receiver gets a fixed acknowledgement, the request $m\ge1$, common finite code and conventions, the public promise (8), and lawful continuing invocation rights. It starts in the same source-independent local state with local Step count zero. The driver no longer acts concurrently.

The complete observation includes each chosen precision, whole integer and frame, every actual Emit value and Emit/Advance/Return ordering, declared modes and possession outcomes, local completed-operation counts and records actually computed from this information. Arbitrary finite local computation, pauses, repetitions and wrappers composed of these operations are allowed. Every nested real Next is expanded and counted.

The handoff supplies no old event stream or command count, $p_0,r_0,d_0,s_0$, upper bound on those fields, private Read responses/counts, unit configuration, configuration encoding length, source identity, old tail-dependent client memory, work, storage or timing channel. Public schedule code is allowed to be inspected. Private data, code/configuration digests, installation-size observations and descriptor identity must not reveal the hidden configuration or history. Equal descriptor literals refer to two lawful installations; they do not copy a capability between worlds.

There is no automatically installed Wall, raw getter, authenticated absolute counter, origin-history service, full private-register exporter or acquired-record service. Naming an uninstalled command creates neither a service nor an informative refusal. Release has only its stated control effect, ending the turn; it creates no extra information or invisible driver continuation. Optional richer operations require their own actual installation, rights and full-response pairing premises.

Write

$$
x=p_0t,\qquad d_0=|p_0|,\qquad s_0=N_{p_0}+r_0.
\tag{11}
$$

The target is permanently the initial $q_m(t)$. Later source motion does not reset it to a prefix of the current point. At the empty handoff $r_0=d_0=s_0=0$; no $G_{-1}$ or $J_0$ is defined. A Return-complete answer finishes at a returned source cut with no pending Step transaction. Its cost $C_{\rm ret}$ counts every actual new producer Advance since the original handoff, including those inside legitimate wrappers. Queries, computation and output are paid but do not invent Advances.

## 3. The exact class-wide quantifiers

**Theorem 3.1 (Sharp threshold).** In the preceding observation model:

1. For each fixed public $1\le\beta<c$, there exist finite public constants and one deterministic decoder that, for every $m\ge1$, every legal source and actual handoff, every admissible schedule/configuration, and every finite-response trace satisfying (9), finishes finitely with $q_m(t)$. It stops at the source Return cut which physically acquired the target block. Its exact source-Advance count is $h_m(t)$ in Section 6.
2. For each $\beta\ge c$ and each $m\ge1$, no deterministic causal decoder is both exact and finite over all allowed hidden configurations, sources and actual handoffs. This already holds for the one public parameterized rational parity program of Section 8, its fixed public admissible configuration class and the one public floor backend (10). For each alleged decoder, one finite rational configuration is fixed before both actual compared initializations and is common to both runs. Even exact finite early answers and finite certification of the first actual depth increment are excluded in this base observation class.

The second claim is class-wide. It is not impossibility for every individual public generator admitted by a loose bound $\beta\ge c$. A public generator known to keep its unknown unit constant admits the supplied fixed-unit decoder even if its advertised bound is $c$.

For each fixed $\beta<c$, rational density supplies a finite rational $\gamma$ with $\beta\le\gamma<c$. The constants below can be part of finite decoder code; $\gamma=1$ is allowed at $\beta=1$. This is an existence statement for each fixed public bound, not an algorithm extracting a certified margin from an unspecified representation of an arbitrary real. An effective caller must supply certified finite constants, or a finite description that yields them. The proof uses no runtime real-number oracle for $\beta$.

## 4. A separated-interval closed-error classifier

Fix $1\le\beta\le\gamma<c$ with rational $\gamma$. For $g=0,1,2$ put

$$
L_g=\frac{\alpha^g}{\gamma},\qquad U_g=\gamma\alpha^g,
\qquad I_g=[L_g,U_g],\qquad
\Delta=\frac{\alpha}{\gamma}-\gamma\alpha^2>0.
\tag{12}
$$

Choose a public integer

$$
M>\max\left\{64,\frac{2(1+\gamma)}{\Delta}\right\}.
\tag{13}
$$

All constants are finite. Since $\gamma^2<1/\alpha$, the intervals are strictly ordered $I_2<I_1<I_0$. Their adjacent gaps are $\Delta$ and $\Delta/\alpha>\Delta$; the nonadjacent gap is larger.

**Lemma 4.1 (Fresh finite refinement).** At every current returned cut, query precisions $\nu=1,2,\ldots$ until the literal numerator first satisfies $a>M$. This search finishes on every permitted error trace.

**Proof.** At that fixed cut $z=q(n)\alpha^d>0$ does not change. There exists a finite $\nu$ with $\varepsilon<z/(M+1)$. Every allowed reply at that precision obeys

$$
u=a\varepsilon\ge z-\varepsilon>M\varepsilon.
$$

Consequently $a>M$, independently of how prior errors were selected. This argument requires neither a known lower unit bound nor knowledge of $d,n,z$. It is a termination proof, not a prescription to compute those hidden quantities. $\square$

**Definition 4.2 (One-Step rule).** Save the successful $u$, its precision and $\varepsilon$. Perform exactly one real Step through its actual Return, retaining all its events. Query that new cut at the same precision, obtaining $v$. Retain category $g$ exactly when

$$
L_gu-(1+\gamma)\varepsilon\le v
\le U_gu+(1+\gamma)\varepsilon.
\tag{14}
$$

**Lemma 4.3 (Exactly the actual category passes).** The rule returns the actual increment $g\in\{0,1,2\}$, including closed-error endpoints.

**Proof.** The new true scale is $rz$, where

$$
r=\frac{q(n+1)}{q(n)}\alpha^g\in I_g,\qquad 0<r\le\gamma.
$$

The two closed error inequalities give

$$
|v-ru|\le |v-rz|+r|z-u|
\le(1+r)\varepsilon\le(1+\gamma)\varepsilon.
\tag{15}
$$

Since $u>M\varepsilon>0$ and $L_g\le r\le U_g$, the actual category passes (14). If two ordered categories passed, subtracting their closest interval ends would imply

$$
\Delta u\le2(1+\gamma)\varepsilon.
$$

But (13) and $u>M\varepsilon$ give its strict reverse. Thus no second category passes, proving soundness and uniqueness. Both error balls and the classifier tests remain closed; no endpoint is discarded. $\square$

**Lemma 4.4 (Finite exact decisions).** Each test (14) is a finite exact comparison.

**Proof.** The measured values, $\varepsilon$ and $\gamma$ are rational, and $\alpha^2=1-\alpha$. Clearing positive denominators reduces each test to the sign of $A+B\sqrt5$ for finite integers $A,B$. If a term is zero or the two terms have the same sign, integer signs suffice. With opposite signs, compare $A^2$ and $5B^2$, using the original signs to choose the direction; handle equality separately. Integer arithmetic on finite representations terminates. Thus there is no approximate equality decision or infinite expansion oracle. $\square$

Each new round restarts the search at precision one. Positivity holds after every finite number of Steps, including repeated read-free Steps during which units shrink. For example $q(r_0+i)\ge q(r_0)\beta^{-i}>0$. The proof never assumes that one absolute precision remains adequate for a long lifetime or an unbounded acquisition. At $\gamma=1$ the existing PAID three-ratio classifier may be consumed directly; the additional content is the separated-interval bridge for moving units.

## 5. Direct physical acquisition of the initial tail

**Definition 5.1 (Decoder).** Keep a complete block word $W$, initially empty, and a local completed-Step count $i=0$. At each returned cut run Section 4, consuming the whole real Step and the post-Return query. Append nothing, $0$ or $10$ according as its unique category is $0,1,2$, and increase $i$ by one. At the first $|W|\ge m$, write the first $m$ digits of $W$ and stop. Otherwise restart fresh refinement at the current cut. Emit values remain fully delivered; the rule neither suppresses them nor substitutes a hidden branch flag.

**Theorem 5.2 (Actual raw-tail invariant).** After each completed round there is a complete word $w_i$ such that

$$
\begin{aligned}
W&=w_i,&p_i&=p_0w_i,&d_i&=d_0+|w_i|,\\
\text{unread raw tail}&=\operatorname{tail}_{|w_i|}(t),&
n_i&=r_0+i,&\text{current point}&=T^{r_0+i}x,\\
N_{p_i}&=N_{p_0}+\sum_{j<|w_i|}G_{d_0+j}(w_i)_j,&
s_i&=N_{p_i}+r_0+i.
\end{aligned}
\tag{16}
$$

The producer has precisely its original caches for those actual fields, empty returned scratch and pending output, the same binding and continuing invocation right. The receiver need not know the hidden fields of (16).

**Proof.** The claim holds at handoff. At a reached return the fresh search is finite by Lemma 4.1. One actual Next either reads no bit, physically reads a zero, or physically reads one and its forced zero. Lemma 4.3 identifies exactly that increment; hence the decoder appends exactly the actual complete block, or nothing. The raw cursor, unread tail and immutable origin prefix change by precisely its length. The actual absolute position weights give the displayed $N$ update. Exactly one Advance increases source time; supplied producer correctness gives $T^{r_0+i+1}x$ and Return clears pending fields. Both queries preserve all source fields. No binding is replaced and no right is reconstructed from a number. These facts prove the induction. $\square$

**Theorem 5.3 (All-source finite target-block stop).** For every actual handoff, admissible schedule and allowed finite-response error trace under a public $\beta<c$, the decoder finishes with the initial $q_m(t)$ at the source cut immediately after physically acquiring its target block.

**Proof.** The finite position $m-1$ lies in a finite-numbered complete block of $t$. At any current parent the death clock $k_p$ is finite and $n\le k_p$. Finitely many read-free calls reach $n=k_p$, and the next productive call reads its next complete block. Child death clocks increase by a positive $G$ weight in (6), preserving the legal reached domain. Repeating this argument for only the finitely many blocks through the target uses finitely many Steps. Every intervening cut has a finite fresh search, and every post-query finishes.

By (16), before acquiring the target block one has $|W|<m$; after its actual Return, for the first time $|W|\ge m$. The post-query identifies that physically acquired block, and the written prefix is exactly $q_m(t)$. Query and output work do not Advance the source beyond that cut. Pure or eventual alternation, eventual zero tails and every allowed split side have these finite blocks; no eventual-zero assumption or infinite first-$00$ search is used. $\square$

## 6. Exact source coordinates and the per-trace lower bound

Let $w$ comprise all complete initial-tail blocks before the block containing position $m-1$. Write $e=|w|$ and let the final block length be $g\in\{1,2\}$. Put

$$
e<m\le e+g,\qquad V=\sum_{j<e}G_{d_0+j}w_j.
\tag{17}
$$

The shifted value $V$ uses original absolute raw positions, rather than the weights of $w$ rebased at zero.

**Proposition 6.1 (Exact attained coordinates).** The decoder uses exactly

$$
h_m(t)=G_{d_0+e+1}-1-s_0-V\ge1
\tag{18}
$$

new Step, Emit, Advance and producer-Return events, and exactly $e+g\in\{m,m+1\}$ new physical raw Reads and raw payload bits. If the successful old-cut precision in round $i$ is $\nu_i$, its literal query count is

$$
Q_{\rm Extent}=\sum_{i=0}^{h_m(t)-1}(\nu_i+1).
\tag{19}
$$

**Proof.** The actual target parent is $a=p_0w$, with

$$
N_a=N_{p_0}+V,\qquad
k_a=G_{d_0+e+1}-2-N_{p_0}-V.
$$

Its target-acquiring call starts at $k_a$ and Returns at $k_a+1$. Subtracting the same actual $r_0$ gives (18). Positive child-clock increments and $k_{p_0}\ge r_0$ imply $k_a\ge r_0$, so $h_m(t)\ge1$. Theorem 5.3 stops at exactly that source cut. Every serial call contributes one of each producer event.

The actually acquired word is precisely $w$ followed by the entire final block, and each raw bit is read once, giving $e+g$. A target at the first one of $10$ pays one extra bit; a target at its second zero pays that physical zero and has exactly $m$ reads. Each round makes $\nu_i$ old-cut queries, because it restarts at one, and exactly one post-Return query. This proves (19), without a query optimum claim.

For the empty handoff $k_\varnothing=G_1-2=0$ and (18) becomes $G_{e+1}-1-V$, including its first target block. For a proper death handoff and an immediately next target block it is one. Birth and death equalities use the included attained interval (4); no negative weight index occurs. $\square$

**Theorem 6.2 (Robust full-history per-trace bound).** For every deterministic decoder correct and finite on all sources, actual handoffs, admissible schedules and allowed errors, fix any one actual $(p_0,r_0,t)$, schedule/configuration and valid error trace. Its Return-complete count satisfies $C_{\rm ret}\ge h_m(t)$. The same statement for correctness only on one specified backend requires a same-backend pairing premise; the source-blind floor service (10) satisfies it.

**Proof.** Keep that same actual prefix, handoff count, schedule program and configuration. According to the target's position choose a legal alternative tail

$$
\begin{array}{c|c|c}
\text{actual target}&e&t_*\\\hline
0\text{ block}&m-1&w10\,0^\infty\\
10\text{ first one}&m-1&w0^\infty\\
10\text{ second zero}&m-2&w0\,10\,0^\infty
\end{array}
\tag{20}
$$

All concatenations are legal complete blocks. The requested prefixes differ: in the third row, position $e+1=m-1$ becomes one rather than a forced zero, as well as changing position $e$. Both actual initialized sources reach the same original $(p_0,r_0)$ and then acquire the same $w$ before the target transaction. No convenient alternate member of an initial provenance fibre is substituted.

At every earlier returned cut their actual $p,d,n,N$, clocks, empty scratch, acquired records, modes and installed rights agree. The same source-independent schedule therefore gives exactly the same $q(n)$. For each adaptive precision the set of permitted complete integer replies in (9) is identical. Copy the selected trace's entire integer, its integer part and canonical frame to the alternate source. Every copied closed inequality remains valid. Actual earlier Emits and their Advance/Return order also agree by the producer rules. Deterministic local computation, stored replies, descriptor checks, pauses and wrappers have equal inputs. Every nested real Next is paired and counted. A release supplies no uncounted continuation.

If additional earned-field operations really are installed, this transfer includes them only under TARGET Section 6's complete pairing condition: their full outputs, guards, budgets, modes, rights and successors must be functions of these matched actually acquired fields. Then bounded Peek uses the same guarded finite representative, Tick/LiveStep is a matched real Next, and every internal acquisition/Seek Step is counted. Honest acquired-field export and archives have the same complete fields; no arbitrary private exporter or initial Wall information is granted. This optional extension is not needed for the base theorem.

The first possible source-event distinction occurs in the target transaction at relative call $h_m(t)$, its Emit preceding its Advance. Before it, causality gives the same adaptive decisions and outputs. A Return-complete stop with $j<h_m(t)$ Advances has no pending target transaction: invoking that transaction and counting it through Return would already include its Advance. Thus its whole history is within the paired prefix and forces the same answer on two different targets. The copied finite prefix extends to a valid full trace, for example by subsequent floor replies under the unchanged schedule. Robust all-error correctness is contradicted. This argument works for each selected original error trace.

It does not say that every fixed error selector voluntarily emits the copied integers. For the specified source-blind floor backend, however, equal $d,n,q(n)$ and precision give exactly equal actual floor integers and frames. Its deterministic acquired-field controls also pair, so the alternate history belongs to that same backend and the backend-specific lower bound follows. A numerical error bound alone is insufficient to prove source blindness of an arbitrary selector; an oracle allowed unread advice could encode it in the choice of allowed numerator. $\square$

**Corollary 6.3 (Fixed actual cut worst value).** For fixed actual $p_0,r_0$, the decoder's full-tail, all-error worst Advance count and the robust class's minimum such worst count are

$$
B_m=G_{d_0+m}-1-s_0.
\tag{21}
$$

The all-zero initial tail attains it. At the empty cut the value is $G_m-1$.

**Proof.** In (18), $e\le m-1$ and $V\ge0$, so $h_m(t)\le B_m$. For $t=0^\infty$, $w=0^{m-1}$, $e=m-1$ and $V=0$, giving equality. The per-trace bound applies to that actual tail for every robust decoder, while the positive rule attains (18) on every trace. All tails are compared at the same actual $p_0,r_0$ and common schedule. $\square$

The clock expressions (18), (21), the raw count, and opposite-block witnesses are supplied TARGET/NORMAL results. Their transfer here preserves the common moving schedule in the entire paired interaction. They are not new clock identities. They are source-Advance optima in the stated comparison class, not bit-work, memory, query, precision or latency optima. If answers may finish during a target Emit, the inherited general lower bound is $h_m(t)-1$ prior Advances. TARGET's matching early upper bound additionally requires a known boundary and an installed synchronous finite Emit handler that completes output before producer Advance. The present classifier requires its post-Return query and attains $h_m(t)$.

## 7. Optional two-update and live consequence

**Proposition 7.1.** Below threshold, apply the fresh classifier until the first two actual nonzero increments $g_1,g_2$ occur at local Step indices $t_1,t_2$. Then the existing PAID coordinate recovery applies:

$$
t_1=\delta_0+1,\qquad D=d_0+g_1,\qquad
t_2-t_1=G_{D-1},
$$

$$
d_0=D-g_1,\qquad s_0=G_{d_0+1}-1-t_1,
\qquad d_*=D+g_2,\qquad s_*=G_{d_*}-1.
\tag{22}
$$

At an empty initial cut $t_1=1,s_0=0$ are handled separately. Exactly $g_1+g_2\in\{2,3,4\}$ new raw bits are physically read through this second update; all intervening Steps remain paid.

**Proof.** The classifier identifies actual update positions. The first read follows exactly $\delta_0$ read-free Steps. After it the attained depth is $D\ge1$ at birth $s=G_D-1$, whose slack is $G_{D-1}-1$ by (7). The next read consequently occurs exactly $G_{D-1}$ further Steps later, including its last read Step. All those calls and fresh refinements are finite. Strict growth of $G_j$ identifies $D$ by a finite successive-weight search; (22) is the supplied clock inversion, and the next update again gives a birth. No fixed absolute precision is reused across the lifetime. $\square$

Only an actually earned boundary record under a genuinely installed acquisition/live contract, together with its retained same-source rights, supports PAID's subsequent event-based LiveStep, guarded Peek, truly advancing Seek and optional finite budget use. After that acquisition, its known-boundary event update needs no further Extent and is independent of subsequent unit drift. A guessed coordinate, a possible history, a direct decoded target word or a printed descriptor does not install a live service. Its original DATA guard, endpoint ownership, physical forced-zero reads, source motion and exact-tail resumption remain in force. The direct target decoder can stop at its first target block and need not wait for this calibration. These are consequences using supplied clock and live-interface mathematics.

## 8. One public parity program and its fixed configuration domain

For the negative theorem fix $\beta\ge c$ and $m\ge1$. Before considering a proposed decoder or its stationary behavior, fix and publish the following finite parameterized program $P$:

$$
q(0)=q(1)=H,\qquad
q(n)=\begin{cases}
HQ,&n\ge2\text{ even},\\
Hb,&n\ge2\text{ odd}.
\end{cases}
\tag{23}
$$

Its configuration is separately stored private rational data. Fix also its public admissible configuration class

$$
\mathcal C=\{(H,b,Q)\in\mathbb Q_{>0}^3:
 c<b<c^2=\alpha^{-1},\ b/c<Q<c\}.
\tag{24}
$$

These promises, the public floor code, source/producer conventions and handoff controls remain unchanged throughout the argument. The configuration values and encoding lengths are not public. No literals dependent on a decoder are later inserted into public code, and no configuration identity channel is present. The algebraic constraints describe the promised domain; $P$ itself merely uses rational arithmetic and the original absolute counter's parity. It needs no runtime irrational comparison. Rational density makes $\mathcal C$ nonempty for every rational $H>0$.

**Lemma 8.1 (Global source-independent legality).** Every member of (24) obeys (8) for every $\beta\ge c$, at all original absolute counts before and after any handoff.

**Proof.** The inequalities in (24) give

$$
1<Q<c<b,\qquad 1<b/Q<c,\qquad 1/c<Q/b<1.
\tag{25}
$$

The successive ratios of (23) are $1$ from zero to one, $Q$ from one to two, then $b/Q,Q/b$ alternately. All lie strictly in $(1/c,c)$, hence in $[1/\beta,\beta]$. Every value is a positive rational obtained from finite data. The program uses neither unread source bits nor a chosen source, and is valid on every source. There is no clock shift at handoff and no free omission of old driver Steps. $\square$

The proof will refute correctness and finiteness over just this fixed public family, so it also refutes them over the full allowed class. It does not need to compare different public generator programs.

## 9. Two actual proper death cuts with opposite initial targets

Define actual source histories symbolically as follows:

$$
x_A=0\,10\,0^\infty=Z(G_1),\qquad (p_A,r_A)=(0,1),
$$

$$
x_B=0^\infty=Z(0),\qquad (p_B,r_B)=(00,3).
\tag{26}
$$

**Lemma 9.1 (Actual entrance and full current-point equality).** Both cuts in (26) are proper death returns reached by the original initialized producer. Their initial tails are $10\,0^\infty$ and $0^\infty$, so their targets differ for every $m\ge1$. Their complete initial current points are the same

$$
Y=Z(G_2).
\tag{27}
$$

**Proof.** A's first driver Next at the empty death cut physically reads its first zero, appends $0$, Emits, Advances and Returns at one. Its clock is $k_0=G_2-2=1$. Thus it is the inclusive proper death return $(0,1)$.

B's first call similarly reads a zero. Its second starts at $k_0$ and physically reads its second zero, giving prefix $00$ at return two. The new clock is $k_{00}=G_3-2=3$; its third call is read-free and Returns at three. Thus its actual prefix is still $00$, at its proper death return. This uses the initialized execution, rather than selecting compatible registers without a run. The two old histories pay respectively one and three actual driver triples, and one and two raw Reads; their old events are hidden, not equated.

Deleting these actually acquired raw prefixes gives the stated tails. By the finite identities $G_2=G_1+1=3$ and (2),

$$
T Z(G_1)=Z(G_1+1)=Z(G_2)
=T^3Z(0).
\tag{28}
$$

This is equality of entire infinite digit points, not equality only after phase projection. $\square$

The source-independent installation, public $P$ and floor code, fixed handoff confirmation, public $\beta,m$, modes, framing and rights are the same in these possible worlds. Actual raw sources, hidden cut fields and old paid histories differ.

## 10. A finite stationary prefix under that same public program

Suppose a deterministic decoder $\mathcal D$, receiving the public data already fixed in Section 8, is exact and finite on every configuration in (24), every source and every legal hidden handoff, using floor replies. Fix any rational $H>0$ and choose one legal reference configuration $(H,b_{\rm ref},Q_{\rm ref})\in\mathcal C$.

Consider the hypothetical A run of (26) with this reference configuration and this exact public $P$. At A's stationary cut $q(1)=H$, independently of $b_{\rm ref},Q_{\rm ref}$. Every requested precision therefore returns

$$
a_\nu=\lfloor2^\nu H\alpha\rfloor.
\tag{29}
$$

**Lemma 10.1 (Finite first-Step prefix, without a public-code change).** This reference interaction reaches a first actual Step after a finite complete stationary history and a finite set $F$ of queried precisions.

**Proof.** The decoder cannot correctly stop before any Step. Replace A's initial unread tail by $0^\infty$ at the same actual cut $(0,1)$, retaining exactly the same $P$, reference configuration and floor backend. The stationary depth and unit, all public information, modes and complete replies are identical, but the first target bits differ. A deterministic early stop would therefore violate all-source exactness.

If the reference interaction never issued a Step, either it would stop incorrectly as just shown, or it would continue forever in stationary queries, pauses or local computation. The latter violates finiteness on this legal reference run. Consequently a first Step occurs after finitely many actual local actions and requests. Their precision set $F$ is finite, possibly empty. Its existence is established under the same public program and same public configuration domain that will be used for the final witnesses. $\square$

The entire stationary A response rule (29), not merely a chosen finite subset, is independent of the later selected $b,Q$. Thus replacing the reference private data by any other legal private $b,Q$ preserves this finite prefix and its first-Step decision on A. This is a mathematical totality argument about hypothetical histories; it is not execution of a decoder, schedule or floor computation.

Since $H$ is nonzero rational and $\alpha$ is irrational, $H\alpha$ is irrational. For each $\nu\in F$ its lower floor-cell margin

$$
\eta_\nu=H\alpha-a_\nu2^{-\nu}>0
\tag{30}
$$

is strictly positive, and its upper floor boundary is also strict. Choose $\mu>0$ smaller than every one of these finitely many lower margins; if $F$ is empty choose any $\mu>0$. Rational density supplies a rational $b$ with

$$
c<b<c^2,\qquad
0<\delta=H(\alpha-b\alpha^2)
=H\alpha^2(c^2-b)<\mu.
\tag{31}
$$

Choose rational $Q$ with $b/c<Q<c$, possible because $b<c^2$. The final data $(H,b,Q)$ belong to the same public class (24). Fix them once, before both actual initialized driver runs in (26). They are common to both worlds at all absolute counts. They are not changed during a run, and selecting them as an existential witness after analyzing $\mathcal D$ is not a schedule that adapts to unread source bits.

**Lemma 10.2 (Literal initial full-integer agreement).** The two final worlds give the same complete floor replies and the same first-Step decision for the selected initial adaptive history.

**Proof.** A's scale is $H\alpha$. At B's actual count three and depth two, its scale is $Hb\alpha^2=H\alpha-\delta$. For every precision $\nu\in F$, (30)–(31) give

$$
a_\nu2^{-\nu}<H\alpha-\delta<H\alpha
<(a_\nu+1)2^{-\nu}.
\tag{32}
$$

Both values lie in the same full dyadic floor cell, so the actual floor service gives exactly the same entire integer $a_\nu$, including all integer-part bits and canonical framing. The selected finite A interaction is unchanged from its reference one. Induction on its stationary actions now gives the same requests, precisions, replies, local records and first-Step decision in B. Empty $F$ needs no cell comparison. No fractional residue is substituted for the integer and no initial all-precision equality is claimed. $\square$

## 11. First-Step coalescence, every future precision and causal contradiction

**Lemma 11.1 (Actual coalescence after one Step).** In A the first new Step reads $10$ and Returns at prefix $010$, depth three, $N=G_1$, absolute count two. In B it reads $0$ and Returns at prefix $000$, depth three, $N=0$, absolute count four. Both resulting boundaries have $s=G_3-1$ and both unread tails are $0^\infty$.

**Proof.** Both start at their actual death clocks. Thus A performs two physical Reads, including its forced zero, while B performs one. The original position-one weight in A is $G_1$; B's prefix has no ones. The finite initial-weight identities give $G_1+2=G_3-1=4$. Hence $N+n$ agrees at the depth-three birth. Both actual initial points are $Y$, so producer correctness gives the same first Emit $\operatorname{Low}(G_2)$, followed by each run's own Advance and Return, leaving both current points at $TY$. The different private Read counts are paid and excluded by the observation contract. Finally (23) gives $q(2)=q(4)=HQ$. $\square$

**Lemma 11.2 (All-future complete response equality on this one pair).** For every local completed-Step count $i\ge1$, the two actual returned depths agree, say $D_i$, their units agree, and their floor replies agree at every finite precision. Every future actual source-event prefix agrees as well.

**Proof.** At $i=1$ Lemma 11.1 gives the same proper boundary and common actual raw tail. NORMAL's same-boundary/common-tail continuation applies to the actual initialized histories $(010,2)$ and $(000,4)$. Alternatively, induct directly on the clock rules. Equal positive slack makes both calls read-free and reduces slack by one. Equal zero slack and the common tail makes both read the same next $0$ or $10$, with the same cursor, depth increment and child birth slack. Shared blocks preserve equality of remaining tails. Each productive Next truly Returns. This proves equal depths and relative branch times for every finite continuation, without replacing either original endpoint or cursor.

The full points also agree after every Step: both started at $Y$ and really Advance by $T$. At local Step $j\ge1$ both therefore Emit

$$
f(T^{j-1}Y)=\operatorname{Low}(G_2+j-1),
\tag{33}
$$

then Advance, then Return. This uses the supplied finite-core successor on whole points, not an omitted event projection.

At local completed count $i\ge1$, the actual absolute counts are $1+i$ and $3+i$, differing by two and both at least two. Their parity is the same, so the one common program gives

$$
q(1+i)=q(3+i)=\begin{cases}
HQ,&i\text{ odd},\\
Hb,&i\text{ even}.
\end{cases}
\tag{34}
$$

Consequently at every such cut, for every finite $\nu\ge1$, the entire common integer is

$$
\left\lfloor2^\nu q(1+i)\alpha^{D_i}\right\rfloor,
\tag{35}
$$

with identical framing and service completion. Repetition and arbitrarily high precision change none of the equalities. Each reached rational-unit computation, finite quadratic floor service and source call finishes. The equality is of allowed observations, not private old absolute counters or historical prefixes. $\square$

**Proof of Theorem 3.1, negative direction.** Start with the identical source-independent receiver state, fixed handoff confirmation, public code, promises and installed rights. Lemma 10.2 matches its selected finite initial stationary interaction. The first complete Step agrees by Lemma 11.1. Every subsequent legal Step/Extent action agrees by Lemma 11.2 at every requested precision. Equal observations and common public code force equal local computation, records, wrapper calls, pauses, modes, stopping decisions and outputs, by induction on arbitrary finite adaptive actions. Every wrapper's actual source calls are included; no operation or integer field is suppressed.

If the decoder finishes on both worlds, its answer is the same, whereas (26) gives different initial $q_m(t)$ for every $m\ge1$. If it fails to finish on either, its asserted totality fails instead. This contradiction refutes the putative decoder over the fixed public family (23)–(24) and hence over the declared class. Equality includes the intermediate Emit events, so allowing an answer before a final Return does not repair the contradiction.

The same proof excludes a universally finite exact certificate of the first actual depth increment. Before any Step, the same-cut alternative used in Lemma 10.1 has different next physical blocks and prevents a correct finite prediction without a Step. Totality then forces a finite first-Step prefix under the fixed reference program. The final two worlds have actual first increments two and one, yet their finite selected initial interaction and all subsequent observations agree. A finite certificate must therefore fail exactness or finiteness on one. This is a global causal obstruction on actual initialized runs, not an inference merely from overlapping neighboring ratio intervals. The witnesses are legal at $\beta=c$ by Lemma 8.1 and remain legal for every larger $\beta$. $\square$

Together with Sections 4–6 this proves the class-wide sharp threshold.

## 12. Critical equality and the quantifiers that must remain distinct

For a fixed selected decoder, its initial precision set $F$ is finite and determines the rational witness. The scales $H\alpha$ and $Hb\alpha^2$ are unequal. Sufficiently fine stationary floor queries would separate this particular pair: if two numbers differ by $\delta>0$, choose finite $\nu$ with $2^\nu\delta>1$; two numbers in one common unit-width floor cell have difference less than one. Thus no single rational pair here is claimed to have equal initial replies at every precision. Infinite stationary interrogation would not satisfy finite acquisition. In contrast, the same selected pair has exact equality at every future precision after its first Step, as well as every future event. These two assertions have different quantifiers.

Every selected witness actually has a rational uniform factor

$$
\rho=\max\{Q,b/Q\}<c,
\qquad 1<\rho,
\tag{36}
$$

and all its ratios lie in $[1/\rho,\rho]$. At the critical public promise, no such $\rho$ or uniform subcritical margin is supplied to the receiver. Therefore a different finite decoder for each supplied $\beta<c$ is compatible with no one decoder for the union of hidden-margin classes. A fixed supplied $\gamma<c$ restricts that union: its ratio bounds on $Q,b/Q$ would force $b\le\gamma^2<c^2$, precluding the arbitrarily small (31) needed against an arbitrary finite initial prefix. Strict actual inequalities with an undisclosed margin are not the positive theorem's public uniform margin.

The existing result in [*Permanent initial-target blindness under capped floor precision*][CAPPED] concerns a different restriction. It keeps a fixed positive rational unit and limits requests to $1\le\nu\le N$. A fixed actual pair can then have identical complete infinite permitted observations, using permanently zero floor replies; sufficiently late paid proper handoffs give such pairs for every fixed positive rational unit. Here all finite precisions are permitted and units vary under (8). The obstruction is to a common finite stopping decoder; the initial equality is chosen for that decoder's finite prefix and becomes all-precision equality only after the first Step. Neither statement is substituted for the other.

## 13. Paid resources and implementation boundaries

The exact new source coordinates below threshold are (18), the $e+g$ physical raw Reads, and (19) finite completed queries. Handoff acknowledgements, query completions and output are separately paid. At answer time the actual source is $T^{r_0+h_m(t)}x$; post-Return classification and writing the answer do not move it further. This does not inspect the old point without Advance or provide a rewind.

In the negative witness, A pays one old driver call and one old raw bit; B pays three old calls and two old raw bits. Their first new calls pay two versus one raw bits, respectively, and one actual producer triple each. Every later actual call, query and full integer frame remains paid. Equal replies need not mean equal private work, latency, storage or old history.

Whole-system accounting includes actual source provisioning, generation/delivery and backend storage; producer, driver and receiver work; program and reference installation; raw/channel bindings and continuing rights; private schedule configuration and its encoding lengths; counter, parity, rational unit-update and floor arithmetic; every request's precision encoding and complete reply integer/frame; event I/O; descriptor, possession and mode checks; comparisons; scratch allocation, scans, return positioning and clearing; literal output, copies and any retained archive. Simultaneously present producer, schedule service, receiver, driver, source backend and retained-output storage must be added. Hiding $H,b,Q$ from the receiver does not remove their storage cost.

For (23), only finite rational data, parity and exact finite quadratic arithmetic are needed for each reached query. A positive value in $\mathbb Q(\sqrt5)$ can be bracketed by a finite integer bound from its rational coefficients and $2<\sqrt5<3$, then its floor found by finite integer search with exact sign comparisons. This is a finite arithmetic specification, not execution or a uniform resource bound. Every selected configuration and reached precision is finite. General finite rational schedule programs additionally need their promised reached unit computations to finish. Abstract real schedules require the stated finite-response hypothesis; finite code for arbitrary real units is not supplied.

PAID Section 19's fixed-unit $n_*$ and $W_0$ bounds do not transfer to arbitrary moving schedules. A quantitative replacement must include the actual schedule program/configuration, computation, every reached unit's numerator/denominator sizes and all used precisions. Very small units require arbitrarily fine refinement; very large units require arbitrarily large full integer replies. No uniform finite latency, work, storage, hidden-depth bound or source-provisioning bound is proved. The Advance optimum is not a universal resource optimum or a precision/query optimum.

## 14. Mathematical suppliers and remaining scope

The following relative bindings designate the three mathematical proof suppliers and the existing capped-precision comparison result. Their claims keep their own hypotheses.

| Source | Existing content used | Additional content here |
| --- | --- | --- |
| [NORMAL Sections 1–10][NORMAL] | Actual common-tail continuation and whole-point equality, fixed-boundary tail normal form, precise first event separation, opposite-block witnesses and known-boundary target clocks | Common-tail continuation is used only after the two critical worlds actually coalesce. The target clocks remain inherited. |
| [NORMAL Sections 11–17][NORMAL] | Classification of all initialized histories over each full point, unbounded possible paid frontiers, finite causal event-only entrance/stopping-boundary obstruction, a fixed natural-core pair with all-future boundary separation, and the necessary unbounded supplementary-record range | These prior event-only results are not reclassified as the present full-Extent obstruction. The rational moving schedule also matches all actual scale replies. |
| [PAID Sections 1–3, 7, 10–12][PAID] | Sequential initialized execution, productivity, forced-zero acquisition, finite arithmetic, exact raw-tail restart, inclusive lifetimes, intrinsic boundaries and wall ownership | Those actual clocks realize both death handoffs and the coalesced birth; no compatible but unexecuted state replaces them. |
| [PAID Sections 13–21][PAID] | Calibrated ordered Wall acquisition, installed rights and guards, unknown fixed-unit classification, two-update clock inversion, earned live use, finite rational fixed-unit backend (73) and its scoped bit bounds | Definition 2.1 explicitly extends the unit service. The new separated intervals handle moving units; unchanged fixed-unit code and bit bounds are not assigned that capability. |
| [TARGET Sections 2–10][TARGET] | Stable-cut positivity refinement, finite exact comparisons, direct physical target-block stop, actual raw-tail invariant, exact Advance/raw/query coordinates, full-operation per-trace pairing, robust versus backend-specific quantifiers and early-output distinctions | Each cut now uses the drift interval bridge. Its common-schedule pairing transfers the supplied bound, rather than inventing a new clock or lower-bound principle. |
| [CAPPED Sections 1–11][CAPPED] (comparison result) | Fixed-unit finite-cap floor zero cells, a fixed actual different-initial-target pair with equal full current points and complete infinite permitted observations, and the every-fixed-unit late-handoff strengthening; known-boundary and unbounded-precision positives remain in force | Here all finite precisions are allowed with bounded moving units: decoder-dependent initial agreement under one public program and one common rational configuration is followed by first-Step all-precision coalescence. The fixed-cap infinite-future obstruction remains a distinct existing result. |

The additional mathematical conjunction is separated-interval classification under a supplied subcritical margin, fresh refinement at every actual cut, and the critical rational common-program/common-configuration finite-stop obstruction with full integer replies and full future events. The same-public-program reference history and decoder-dependent initial floor-cell selection are necessary parts of that proof. Ordinary causal reply induction and factor-through-observation contradictions are existing tools. These are repository-derived conditional mathematical arguments; no exhaustive literature search, worldwide priority or new kernel certification is asserted.

Known empty initialization or a genuinely known initial boundary admits the supplied event decoder independently of unit drift. An actual authenticated absolute count, unit/configuration disclosure, complete private record, initial calibrated Wall readout, raw getter, source identity or timing service changes the observation class and can distinguish the displayed witnesses. The theorem is about arbitrary unknown actual handoffs on the specified interface. It does not deny decoding for every restricted generator, source or cut family. Acquiring a later common boundary does not retrospectively identify the initial paid frontier or initial target.

The critical worlds already have the same entire current point. Recovering that point's finite DATA is different from recovering their different initial unread tails. No finite output supplies an entire unknown infinite source, whole current point, historical selector, old event archive or authenticated origin count. A mathematical inverse, possible provenance member or printed descriptor does not create a binding, sensor, source, record exporter or continuing right. All optional live operations retain both their earned-data and installed-rights premises.

Stability during stationary queries, known $\alpha$ and error resolution, positivity, the same actual measurement region, finite reached services, exclusive serial source control and persistent rights are substantive conditions. Drift during stationary refinement, unknown error bounds, unobserved concurrent Advance, source mutation outside Advance, revocation, a wrong or moving measurement region, additional hidden response fields and independent physical instruments require separate hypotheses and proofs. No arbitrary noise, stochastic/expected-cost, ML/NN, physical impossibility or universal information-minimality result is implied.

Original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization, arbitrary interior-cut and native-controller tasks retain their own source, full-response, control and authority obligations. This model is not a conversion to those interfaces. General independent space/time/boundary/memory recovery, physical calibration/realization, external novelty and uniform schedule-dependent bit complexity remain separate unproved obligations. A single finite-target theorem does not complete the sustained research objective.

[PAID]: RECURSIVE_RELATIONAL_OBSERVATION_PAID_ZECKENDORF_CURRENT_RETURN.md
[NORMAL]: RECURSIVE_RELATIONAL_OBSERVATION_EXACT_CURRENT_BOUNDARY_PROVENANCE.md
[TARGET]: RECURSIVE_RELATIONAL_OBSERVATION_UNCALIBRATED_TARGET_ACQUISITION.md
[CAPPED]: RECURSIVE_RELATIONAL_OBSERVATION_CAPPED_PRECISION_PERMANENT_BLINDNESS.md

## 追加锚（本行以下为增补区）

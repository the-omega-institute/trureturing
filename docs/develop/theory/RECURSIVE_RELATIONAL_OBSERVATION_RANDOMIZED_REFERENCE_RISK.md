# Randomized Reference budgets and original owned-boundary risk

Fix an already public positive rational unit and any prescribed nondegenerate bounded rational interval for a single hidden rational offset. In the serial Step/Extent/Reference model specified here, an almost surely terminating randomized receiver with a uniform finite almost-sure cap on completed pre-Step References has infimum exact original-boundary success at most one half. More precisely, for every positive error allowance there are two genuine initialized worlds, sharing one rational offset and chosen before the random tape is revealed, whose success probabilities sum to at most one plus that allowance. Separately, uniform success strictly above one half forces the supremum of the expected pre-Step Reference count to be infinite.

These are ordinary conditional symbolic results for the stated digital source and observation model. No executed mathematical validation, Lean/kernel verification or physical realization is asserted. The existing deterministic all-closed-error recovery theorem remains finite on each instance. Its lack of a uniform pre-Step budget is compatible with both results below.

The mathematical source abbreviations are KNOWN, *Known public unit and bounded hidden offset: initial-target nonidentifiability*, Sections 1–17, and [PAID, *Paid Zeckendorf observation at a current return*][PAID], Sections 1–41. Their actual execution, owned geometry and deterministic constructions are credited inputs. The additional argument is high-probability finite interval renewal on actual initialized carriers, followed by a tape-independent merger pair and a separate legal stopping reduction.

## 1. Actual source, initialization and producer

All digit indices, times and depths are nonnegative integers; digits run from low to high. Put

$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,
\qquad \alpha=(\sqrt5-1)/2,\qquad \phi=1/\alpha,
$$

$$
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ for all }j\ge0\}.
$$

Write $Z(A)$ for the zero-padded finite Zeckendorf word of the nonnegative integer $A$, and $\operatorname{Low}(A)=Z(A)_0$. The endpoint-inclusive arithmetic successor $T$ finds the first adjacent $00$, clears positions below the first position of that pair, puts one there and retains higher digits. If no such pair exists, it gives $Z(0)$; in particular both pure alternating words map to zero. This is the supplied arithmetic successor. Its finite-core identity is

$$
T^hZ(A)=Z(A+h)\qquad(A,h\ge0).
\tag{1}
$$

Every $x\in K$ uniquely parses into complete blocks $0$ and $10$. For a finite complete block word $p$ define

$$
\mathcal B=\{0,10\}^{<\omega},\qquad C_p=\{pt:t\in K\},\qquad
 d=|p|,\qquad N_p=\sum_{j<d}G_jp_j,
$$

$$
M_p=G_{d+1}-N_p,\qquad k_p=M_p-2,
\qquad \mathfrak b_\varnothing=0,\quad
\mathfrak b_{w0}=\mathfrak b_{w10}=M_w-1.
\tag{2}
$$

The birth clock $\mathfrak b_p$ is distinct from the calibration offset $b$ below. A nonempty complete block word ends in zero, so every tail in $K$ may follow it.

One actual fixed $x\in K$ supplies a private sequential raw endpoint. Read at cursor $d$ physically delivers $x_d$ and increments the cursor. Every reached Read finishes in finite time and is paid, including the zero forced by a preceding one whenever the cursor passes it. There is no raw skip, rewind, random access or receiver raw getter. The source-independent paid installation fixes finite programs, endpoint bindings, framing and continuing exclusive rights.

Original initialization has $p=\varnothing$, raw cursor and absolute time zero, deterministic initial caches and a fixed acknowledgement, called return zero. It performs no Read or Advance. At a returned state the producer retains its actual $p$, absolute completed-Advance count $i$, raw cursor $d=|p|$, caches $N_p,G_d,G_{d+1},k_p$, original endpoint and binding; scratch and pending output are empty. The supplied attained domain is

$$
\mathfrak b_p\le i\le k_p.
\tag{3}
$$

Every source in $C_p$ actually attains every return in this inclusive interval with that acquired word. The empty word occurs only at return zero. For nonempty $p$ the clock identities are

$$
\mathfrak b_p+N_p=G_d-1,\qquad k_p+N_p=G_{d+1}-2,
\qquad k_{p0}=k_p+G_d,\quad k_{p10}=k_p+G_{d+1}.
\tag{4}
$$

Step is one real Next of this same producer. If $i<k_p$ it reads nothing. If $i=k_p$, it reads the actual next block: one Read for $0$, or Read of $1$ and then its forced $0$ for $10$. Appending $0$ keeps $N_p$ fixed; appending $10$ at original cursor $d$ adds $G_d$. With the resulting prefix $p'$ the producer computes $\operatorname{Low}(N_{p'}+i)$, actually Emits that bit, Advances once, and Returns at time $i+1$. No query can intervene in this transaction. Only Advance moves the represented source.

At every return the whole current point is $T^ix$ and the exact unread raw tail is $\operatorname{tail}_{|p|}x$. Every finite continuation is productive and is the suffix of that same initialized run. These are the execution and exact-tail results of PAID Definitions 1.2, 2.2 and Theorems 3.1–3.2. They include alternating sources; executing Next does not search their infinite raw words for a nonexistent $00$. Finite Low arithmetic uses ordinary finite Zeckendorf expansion with paid work.

A driver makes a genuine finite initialized sequence of Next calls and hands over the already installed exclusive persistent turn at an actual Return. The driver then ceases concurrent activity. The receiver begins with a source-independent local state, fixed acknowledgement and local Step count zero. A proper handoff has $p\ne\varnothing$; a proper death handoff additionally has $i=k_p$. The negative results need only these proper deaths.

## 2. Full original owned boundary

The phase coordinate consumed from PAID Sections 7, 10–12 is

$$
H(x)=\left[\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j\right]
\in\mathbb R/\mathbb Z,\qquad e_m=[-m\phi]\quad(m\in\mathbb Z).
$$

For $d\ge1$ put

$$
J_d=\{G_d-1,\ldots,G_{d+1}-2\},\qquad
(A_d,B_d)=
\begin{cases}(G_{d-1},G_d),&d\text{ even},\\
(G_d,G_{d-1}),&d\text{ odd}.
\end{cases}
$$

For $s\in J_d$, the full record $\partial(d,s)$ describes the positively oriented arc of length $\alpha^d$ from $e_{A_d-s}$ to $e_{B_d-s}$. It includes precisely the following lifts at the ordered initial and terminal walls:

$$
\chi_+(A_d-s),\qquad\chi_-(B_d-s),
$$

$$
\chi_+(m)=\begin{cases}x_1^+,&m=1,\\Z(-m),&m\le0,\end{cases}
\qquad
\chi_-(m)=\begin{cases}x_1^-,&m=1,\\Z(-m),&m\le0.\end{cases}
\tag{5}
$$

Here $x_1^+=(10)^\infty$ and $x_1^-=(01)^\infty$ are the distinct supplied side points at $e_1$. All attained wall labels are at most one. Every lift at every interior phase is included, including both sides of any interior split phase. If $U(\partial)$ is the resulting subset of $K$, the supplied full-image formula is

$$
d=|p|,\quad s=N_p+i\in J_d,\qquad
 U(\partial(d,N_p+i))=T^iC_p.
\tag{6}
$$

Thus the target records the region, ordered walls and their concrete owned lifts, rather than just unowned phases or length. These coordinates uniquely identify a proper attained boundary. The empty initialization record is represented separately by $(0,0)$, with whole-circle region and no walls; no negative Fibonacci index is used there. At a proper returned state the slack is

$$
\delta(d,s)=G_{d+1}-2-s=k_p-i.
\tag{7}
$$

The task is exact recovery of the boundary at the original handoff, denoted $\partial_0$. Later Steps never replace this target by a later boundary. A description of a later genuinely reached boundary, a possible historical member, a current point, an authenticated absolute counter and a continuing right are different objects.

## 3. Fixed public calibration, two serial ports and observation menu

**Definition 3.1 (Public data and immutable private offset).** Fix before the receiver arbitrary finite rational public data

$$
q_0\in\mathbb Q_{>0},\qquad u,v\in\mathbb Q,\qquad 0\le u<v,
\qquad B=\mathbb Q\cap[u,v].
\tag{8}
$$

Publish both parameterized programs and their source-independent serial protocol. Each world installs one rational $b=C/F\in B$, $C\ge0,F>0$, before original empty initialization and independently of raw-source access. It remains fixed during all old driver work, handoff and future operations. There is no bound on its finite denominator or encoding length. The receiver may depend on all public data and on a proposed resource bound, but gets no private calibration advice. The same programs are lawful on every source in $K$ for each permitted $b$.

At an actual returned acquired depth $d\ge0$ and any requested finite integer $n\ge1$, the specified lower-bound backend is exactly

$$
\operatorname{Extent}(n)=\lfloor2^n(b+q_0\alpha^d)\rfloor,
\qquad
\operatorname{Reference}(n)=\lfloor2^nb\rfloor.
\tag{9}
$$

Extent reads its own actual-depth cache, not a depth supplied to or by the receiver. Reference reads the same immutable $b$. Neither does a raw Read or Advance. Each supplies the entire canonical finite integer, including its integer part, requested precision, request identifier, fixed complete frame and service completion. Integer encoding retains signs as fields where applicable; these particular values are nonnegative. Nothing is reduced modulo a power of two, saturated or truncated. Configuration-dependent padding or acknowledgement fields supply no advice.

These are finite digital programs. For Extent, $\alpha^d$ has a finite quadratic-field representation. Clearing positive rational and dyadic denominators reduces sign comparisons to $U+V\sqrt5$ with finite integers $U,V$. Zero and common-sign cases use integer signs; opposite signs use comparison of $U^2$ with $5V^2$, retaining the original signs and explicitly handling equality. A finite coefficient bracket and integer binary search specify the floor. Reference uses the finite quotient $\lfloor2^nC/F\rfloor$. These inherited symbolic implementations supply no unit-cost real oracle. Their arithmetic has not been executed here.

**Definition 3.2 (Seriality and complete accessible history).** Use the full observation rules of KNOWN Section 13 and PAID Definitions 27.1, 36.1–36.3. Queries occur only at returned cuts. Each has one finite whole reply transaction. There is no cancellation, overlap, restart creating another outstanding query, query inside Step, or new request or Step inside an unfinished query. An early final answer or termination at an allowed proper reply prefix is permitted. Whole-frame equality entails equality of every permitted prefix. Every intermediate actual Emit bit, Advance and Return of Step is observed in order; a final answer during Step is allowed under that same event-prefix convention.

The receiver observes all requests and finite precisions, whole integer frames and their prefixes, identifiers and service completions, fixed acknowledgements, actual Emit values and event order, local completed-operation counts, its tape responses, local computations/records/output fragments, and the declared source-independent modes, descriptor/possession checks and release/control results. Identical descriptor literals are paired with separately valid actual permissions. Printing a descriptor creates no right.

Private raw responses and physical Read counts, acquired $p,d,N_p,k_p$, old absolute time and events, source identity, unread endpoint contents, private calibration encoding/size/digest, installation size, hidden service work/storage and physical delays are excluded observations but retain their costs. There is no timing channel, extra source-related initial advice, Wall, raw getter, rewind, authenticated old counter, old-record or private-state exporter, new spatial sensor, concurrent driver or autonomous Advance. Naming an unavailable command installs neither that command nor an informative refusal. Pauses and local work do not advance the source. Release has only its declared control effect, ends the turn, and supplies neither invisible source motion nor a fresh informative handoff.

Derived programs expand into these primitives and local work. PAID Definition 18.1 and Corollary 24.2 apply only to legitimately earned current records, with their original DATA guards, budget conditions and same-source calling rights. They supply no initial state query. Every primitive Reference or Step inside a wrapper remains real and counted.

The receiver's input menu is this protocol, the common random tape and the listed source-independent controls. Task-result output has no extra external feedback channel: no result sink reads tentative output and sends source-relevant data, commands, scheduling advice or rights back to the receiver. Source requests and control effects remain actual actions. This explicit output condition is used only where the stopping proof emulates tentative task-result writes. Adding interactive result-sink feedback requires a separate simulation argument.

## 4. Random tapes, completion resource and claims

**Definition 4.1 (One measurable causal law).** A randomized receiver $D$ is a causal finite program with one probability space $(\Omega,\mathcal F,\mu)$ for its random tape. The law can depend on $D$ and the common public data, but is independent of the source, hidden $b$, depth, old driver history and all old source advice. Tape access is measurable, and each completed finite computation accesses only finitely many tape symbols. Arbitrary correlation among symbols is allowed; independence, identical distribution and reseeding are not assumed. Valid finite input/tape/output histories and the termination, count and exact-correctness events used below are measurable. Comparing worlds always uses the same $\omega$ under this one law.

Let $\mathcal W$ be the class of genuine initialized proper-death worlds with (8)–(9) and the protocol above. Define the nonnegative, possibly extended integer count

$$
B_D(W,\omega)=\#\{\text{completed primitive Reference replies before first actual Step initiation,
 or before termination if there is no Step}\}.
\tag{10}
$$

A request, header or proper payload prefix is not a completion. An actually completed frame counts even if discarded or followed immediately by a terminal decision. All macro-internal primitive completions count. References after first actual Step initiation are unrestricted. By seriality no Reference can complete inside Step, so its initiation, Advance and Return give the same cutoff count. Write

$$
s_D(W)=\mu\{\omega:D\text{ outputs the exact original owned }\partial_0\text{ on }W\}.
$$

Per-world almost-sure totality means $D$ terminates after finite actual operations and local work with probability one on each $W\in\mathcal W$. A uniform finite almost-sure cap means that one integer $K\ge0$ satisfies

$$
\forall W\in\mathcal W:\quad \mu\{B_D(W)\le K\}=1.
\tag{11}
$$

This does not assume a common full-measure good-tape set over all worlds.

**Theorem 4.2 (Bounded-cap original-boundary risk).** Fix (8), both programs and the protocol before $D$. For every $D$ with per-world almost-sure totality and (11), and every $0<\varepsilon<1$, there are a single rational $b_*\in(u,v)$ and two actual worlds $A,B\in\mathcal W$ with that same offset, chosen before revealing the tape, such that their original owned targets differ and

$$
s_D(A)+s_D(B)\le1+\varepsilon.
\tag{12}
$$

They have a measurable event of mass at least $1-\varepsilon$ on which their entire selected predecision histories agree. If a first Step is issued, its actual public events match and all future allowed observations match, including unrestricted later References. Consequently

$$
\inf_{W\in\mathcal W}s_D(W)\le\tfrac12.
\tag{13}
$$

In particular no fixed uniform success guarantee $p>1/2$ is possible. A cap on every tape is a stronger covered hypothesis. Neither an attained minimizing world at success at most exactly one half nor failure at every separately fixed private offset is asserted. Attainability of success exactly one half is not settled.

**Theorem 4.3 (Separate expected-budget impossibility).** If $D$ is per-world almost surely total and $s_D(W)\ge p$ for every $W\in\mathcal W$ for one fixed $p>1/2$, then

$$
\sup_{W\in\mathcal W}\mathbb E_\mu[B_D(W)]=\infty.
\tag{14}
$$

The supremum may be infinite even though every individual run terminates almost surely. This claim has its own stopping/Markov proof in Section 10; unbounded worst-case counts alone do not imply (14).

## 5. Measurable finite-history tightness

**Lemma 5.1 (Finite statistics on a retained event).** If $A$ is measurable and a measurable nonnegative integer statistic $M$ is finite almost surely on $A$, then for each $\delta>0$ there is a finite integer $N$ with

$$
\mu(A\cap\{M>N\})<\delta.
\tag{15}
$$

Proof. The sets $A\cap\{M\le N\}$ increase to $A$ up to the null set where $M$ is infinite. Continuity of measure from below gives (15). This is the standard tightness fact for an almost-sure finite integer statistic. No conditional probability or independence is involved. $\square$

A finite causal machine-history event is measurable by Definition 4.1. First-event indices, finite request precisions, finite frame-prefix lengths and maxima of recorded action lengths are measurable through countable unions and intersections of such events. Restricting them to a previously retained measurable event preserves measurability. That retained event need not be a stopping-time event. We use no optional-stopping assertion and no fresh conditional randomness.

## 6. Whole-world realization of simultaneous finite cells

For an integer $a$ and finite $n\ge1$, put

$$
C(n,a)=(a2^{-n},(a+1)2^{-n}).
\tag{16}
$$

A certified family consists of tape-indexed finite no-Step causal histories, each obeying $D$ on its assigned unchanged tape and the legal public controls, and one nonempty rational open interval $I=(L,U)\subseteq(u,v)$. Every selected whole frame at either port in every history has $I\subseteq C(n,a)$ for its integer $a$ and precision $n$. If a history ends inside a reply, include a selected whole-frame extension of its observed prefix. A history ending at first Step initiation stops at that command cut before subsequent producer events. The initial interval $(u,v)$ itself is allowed. Certification is sufficient support, not a characterization of all compatible worlds.

**Lemma 6.1 (One actual carrier for the whole family).** Every certified family has one genuine initialized proper-death world with rational offset and stationary Extent value both in $I$, the latter irrational, reproducing every family history on its assigned tape. The family can be uncountable.

Proof. Put $\beta=(L+U)/2$. Choose a finite positive integer $t$ with

$$
q_0 2^{-t}<(U-L)/4,\qquad h=2t.
\tag{17}
$$

Since $\alpha^2+\alpha=1$ and $\alpha>1/2$, we have $\alpha^2<1/2$ and $\alpha^{2t}<2^{-t}$. The Archimedean property supplies (17), and therefore

$$
L<\beta<y:=\beta+q_0\alpha^h<\beta+(U-L)/4<U.
\tag{18}
$$

The offset $\beta$ is a permitted rational. Quadratic conjugation sends $\alpha$ to $-\phi$. If $\alpha^h$ were rational it would equal its conjugate, whereas $|\alpha^h|<1<|(-\phi)^h|$. Thus $y$ is irrational, and lies strictly inside its dyadic floor cell at every finite precision. Irrationality belongs to the stationary Extent centre, not to the actual installed offset.

Install $b=\beta$ in both ports before original initialization of $x=0^\infty$. Drive this actual producer for exactly $G_{h+1}-2$ old Next calls. For each $1\le j\le h$, its acquired prefix at every return in

$$
G_j-1\le i\le G_{j+1}-2
\tag{19}
$$

is precisely $0^j$, with depth/cursor $j$, $N=0$, birth $G_j-1$ and death $G_{j+1}-2$. Indeed the first real call reads the first zero and returns at depth-one birth. At each parent death the next real call reads exactly the next zero and returns at the child birth by (4); below death calls read nothing. The inclusive intervals are consecutive and start at return one. This proves (19) by induction on the actual acquired blocks, retaining original endpoints and caches. Every old call at pre-Advance index $i$ Emits $\operatorname{Low}(i)$, Advances and Returns. Its whole current point at return $i$ is $Z(i)$ by (1). All these finitely many calls complete by the supplied productivity theorem.

The handoff is consequently a genuine proper death with prefix $0^h$, cursor/depth $h$, $N=0$ and time $G_{h+1}-2$. Its Reference true value is $\beta$, its stationary Extent true value is $y$, and both belong to $I$.

For every selected frame, (18) and $I\subseteq C(n,a)$ give the exact required floor integer at its respective port. Entire fixed encodings, identifiers and permitted prefixes agree. On each unchanged tape, induct over that history: identical earlier observations give identical next requests, precisions, tape accesses/responses, local work, output fragments and decisions; the actual port supplies the selected frame. Public controls and actually valid rights match, and no Step has moved the source. An unfinished last frame is supported by its whole extension without delivering or counting its completion. This pointwise induction uses one fixed $\beta,y$ for all histories, without enumerating tapes or intersecting probability-one sets indexed by them. It proves the lemma. $\square$

## 7. High-probability renewal at a finite completion cap

**Lemma 7.1 (A common high-mass first-decision certificate).** Under per-world almost-sure totality and (11), for each $0<\varepsilon<1$ there exist a nonempty rational open interval $I_*\subseteq(u,v)$ and a measurable $E_*$ with $\mu(E_*)\ge1-\varepsilon$, carrying certified finite histories through first Step initiation or prior terminal decision. Histories include a selected whole extension of any unfinished final frame. Recorded action lengths, local event/prefix lengths and finite precisions have common finite bounds. The interval, event and supporting worlds are chosen from $D,\mu,K,\varepsilon$ and the public data before any tape is revealed.

Proof. Choose $\delta>0$ with $(2K+2)\delta<\varepsilon$. At stage $j=0,\ldots,K$ retain a measurable set $G_j=H_j\mathbin{\dot\cup}A_j$. For $H_j$, keep histories through the first decision, meaning first Step initiation or prior termination/final answer. For $A_j$, keep between-transaction histories with exactly $j$ completed References, no Step and no terminal decision. One rational open interval $I_j$ certifies all selected frames, and all recorded lengths and precisions have finite common bounds. Initially $G_0=A_0=\Omega$, $H_0=\varnothing$, histories are empty and $I_0=(u,v)$. By Lemma 6.1 and its replay induction, any lawful stationary world whose two true values belong to $I_j$ reproduces every retained prefix on its own tape.

For the first phase at stage $j$, choose one fixed actual carrier $W_j$ by Lemma 6.1, with rational offset $\beta_j$ and irrational stationary Extent value $y_j$, both in $I_j$. Replay the prefixes from $D$'s original local initialization. On each active tape continue on this fixed world until first Step initiation, terminal decision, or the next Reference request initiation with its finite precision determined. Almost-sure totality on this very world makes that event finite on almost every active tape: failure would leave an infinite stationary sequence of Extents/local work/controls/output, or a permanent computation or receipt stall, without termination. Release cannot supply unseen motion or new informative entry.

On the finite paths take a measurable integer statistic bounding total recorded action length, new Extent precisions, any pending Reference precision, finite local event/prefix lengths and tape accesses through this cut. Include the actual whole-frame extension if termination occurs during an Extent reply. Its precision and literal frame are finite. Lemma 5.1 supplies a deterministic finite $N_j$, enlarged if necessary to at least one and to cover older bounds, such that discarding paths exceeding these bounds loses less than $\delta$ of absolute $\mu$-mass. Discard the null failure set as well. Previously decided tapes remain without loss.

Define simultaneously

$$
J_j=I_j\cap\bigcap_{1\le n\le N_j}
 C(n,\lfloor2^ny_j\rfloor).
\tag{20}
$$

Every interval in this finite intersection has rational endpoints and contains $y_j$ strictly, because $y_j$ is irrational. Hence $J_j$ is nonempty rational open. It certifies every older frame by $J_j\subseteq I_j$, every new Extent frame and unfinished Extent extension, and one compatible whole Reference frame at every possible pending precision. This is one simultaneous intersection for all pending precisions, not separate nonemptiness assertions with no common point. The irrational centre is used only for this interval shrink; no irrational private offset is installed. Move new first decisions into $H$; all other retained paths are pending Reference initiations.

For the second phase choose one new fixed actual carrier $W_j^+$ by Lemma 6.1 with both its rational offset $\beta_j^+$ and its stationary Extent value in $J_j$. It reproduces the entire preceding retained history on each unchanged tape from original local initialization. At any pending precision $n\le N_j$ its actual Reference integer is precisely $\lfloor2^ny_j\rfloor$, since $\beta_j^+\in J_j$. Thus one carrier supplies the selected genuine whole frames for all these differing requests and histories.

Follow each pending tape during this one transaction until an early terminal decision or actual frame completion. No further query or Step can occur inside it. A permanent local or receipt stall without decision would contradict almost-sure totality on this fixed $W_j^+$; reached service frames are finite. A second application of Lemma 5.1 retains uniformly bounded finite receipt histories, at an additional absolute mass loss less than $\delta$, with the null stall set discarded. The whole selected frames were already certified, so no further interval shrink is needed during receipt.

A terminal decision at a proper prefix before completion adds no completion and joins the decided set. If completion occurs first, count it immediately, including when a terminal decision follows immediately. For $j<K$, retain such a terminal path as decided and any other completed path as the next active set with $j+1$ completions; equivalently a terminal transition just after completion may be handled at the start of the next phase. Put $I_{j+1}=J_j$. Previous decided histories stay certified because intervals only shrink. Finitely many previous bounds and the new bounds remain finite. Each supporting-world replacement is a different complete initialized world used for replay; no actual run has changed its own calibration, source or old history.

At $j=K$, any pending path completing this Reference has $K+1$ actual completions before any Step or prior terminal decision on the single actual world $W_K^+$. That event is null by (11) for this world. Delete it, including every path deciding immediately after that completion. All other retained active paths have reached a first decision, possibly inside this unfinished last Reference frame; no positive active mass remains. If active tapes disappeared earlier, stop at that earlier interval, discarding any residual null active set. At most two losses below $\delta$ occurred at each of at most $K+1$ stages, so the resulting event satisfies

$$
\mu(E_*)\ge1-(2K+2)\delta>1-\varepsilon.
\tag{21}
$$

Its histories have a common final certificate $I_*$ and finite bounds because there were only finitely many stages. In particular $K=0$ permits initiation of a first Reference and a proper-prefix answer with zero completions; a completed first frame is instead removed by the cap. The resource was never replaced by request initiation.

All sets are measurable causal-history events restricted by finite Boolean operations and finite-statistic thresholds. The only discarded null sets arise from totality or a cap on finitely many fixed actual carriers, at most two per stage. Previously decided tapes incur no fresh loss. The losses are absolute masses under the same $\mu$, not conditional loss estimates or fresh-noise assumptions. No correctness event has been used. No common full-measure set over all possible worlds, uncountable intersection, limiting reply stream, zero unit, infinite depth or irrational-offset totality premise occurs. Threshold choices may be existential and noncomputable from an arbitrary tape law. They define a witness argument, not an implementable query policy. $\square$

## 8. One fixed rational offset and the genuine all-future pair

**Lemma 8.1 (Actual pair supporting every retained history).** Each certificate $I_*=(L,U)$ of Lemma 7.1 supports a single rational $b_*$ and two actual initialized proper-death worlds with different original owned boundaries, common selected predecision histories on $E_*$, and actual first-Step/all-future observational merger.

Proof. Put $b_*=(L+U)/2$ and choose a finite $d\ge1$ with $q_0\alpha^d<U-b_*$. Any additional prescribed finite lower depth bound can also be imposed, using $\alpha^{2t}<2^{-t}$ and the Archimedean property. Then

$$
L<b_*<b_*+q_0\alpha^{d+1}<b_*+q_0\alpha^d<U.
\tag{22}
$$

Fix this one rational offset before both following original initializations. The already public $q_0$ has not been reduced. Use the actual sources and actual old driver counts

$$
x_A=0^d10\,0^\infty=Z(G_d),\qquad x_B=0^\infty=Z(0),
\qquad r_A=G_{d+1}-2,\quad r_B=G_{d+2}-2.
\tag{23}
$$

Install the same programs, $b_*$ and source-independent public protocol in both worlds. The zero-prefix lifetime induction (19) applies through depth $d$ in A and through depth $d+1$ in B. For every such $j$ and every return $G_j-1\le i\le G_{j+1}-2$, the actual prefix is $0^j$, cursor/depth $j$, $N=0$, death $G_{j+1}-2$, slack $G_{j+1}-2-i$, and owned boundary $\partial(j,i)$. Whole current words are respectively $Z(G_d+i)$ and $Z(i)$. Thus the genuine handoffs are

$$
\begin{array}{c|c|c|c|c|c}
 &p&\text{cursor/depth}&N&i=k=s&\text{exact unread tail}\\\hline
 A&0^d&d&0&r_A&10\,0^\infty\\
 B&0^{d+1}&d+1&0&r_B&0^\infty.
\end{array}
\tag{24}
$$

They retain original endpoints, caches and actual provenance, with empty returned scratch. Their old Reads are $d$ and $d+1$, and old Next/Emit/Advance/Return counts are $r_A,r_B$. Their respective chronological old Emits are $\operatorname{Low}(i)$ for $0\le i<r_A$ or $0\le i<r_B$. These unequal old histories are hidden at handoff, not equated. Productivity makes every specified finite old run actual and finite.

By the recurrence $r_B-r_A=G_d$, and (1) gives equality of whole infinite current words before any phase quotient:

$$
T^{r_A}Z(G_d)=Z(G_d+r_A)=Z(r_B)=T^{r_B}Z(0).
\tag{25}
$$

Nevertheless their original targets are $\partial(d,r_A)$ and $\partial(d+1,r_B)$, of distinct positive lengths $\alpha^d,\alpha^{d+1}$. At a depth-$j$ death their ordered wall labels are explicitly

$$
(a_j,c_j)=\begin{cases}(2-G_j,2-G_{j-1}),&j\text{ even},\\
(2-G_{j-1},2-G_j),&j\text{ odd}.
\end{cases}
\tag{26}
$$

They own $\chi_+(a_j)$ and $\chi_-(c_j)$ at the respective walls, with every interior fibre as in (5)–(6). This follows by substituting $s=G_{j+1}-2$ in those wall formulas. These are actual original full boundaries, not two choices of historical representative for one boundary.

Both initial Extent values and the common Reference value lie in $I_*$ by (22). On each $\omega\in E_*$, causal replay therefore gives exactly its retained predecision history in both final worlds: all adaptive requests and precisions, whole frames and permitted prefixes, tape accesses/responses, local computations/records/output fragments, controls and valid right checks. A first-Step history matches the initiation command before any later producer event. The pair and its common $b_*$ are fixed for the whole event before tape revelation. Initially unqueried precisions are not asserted equal.

If a first Step is issued, A physically Reads $1$ at original position $d$ and its forced $0$ at $d+1$, whereas B Reads its next $0$ at original position $d+1$. A appends $10$ and adds $G_d$ to $N$; B appends $0$ and keeps $N=0$. Their actual pre-Advance Low arguments are

$$
G_d+r_A=r_B=0+r_B.
\tag{27}
$$

They Emit the same actual $\operatorname{Low}(r_B)$, then Advance and Return. Their real child states are

$$
\begin{array}{c|c|c|c|c|c}
 &p_1&D_1&N_1&i_1&k_1\\\hline
 A&0^d10&d+2&G_d&r_A+1&G_{d+3}-G_d-2\\
 B&0^{d+2}&d+2&0&r_B+1&G_{d+3}-2.
\end{array}
\tag{28}
$$

Both cursors are $d+2$, both exact unread tails are zero, their whole current word is $Z(r_B+1)$, their common sum coordinate is $r_B+1=G_{d+2}-1$, and their common slack is $G_{d+1}-1$. Their full owned child boundary is $\partial(d+2,r_B+1)$. Writing $D=d+2$, its ordered labels are $(1-G_d,1)$ for even $D$ and $(1,1-G_d)$ for odd $D$, with the respective $\chi_+,\chi_-$ owners. The actual old offsets and different hidden Read counts have not been overwritten. A final decision inside this Step already sees identical permitted public prefixes; no query is allowed inside it.

For every $h\ge1$ completed new Steps retain an integer $e_h\ge0$, with $e_1=0$, and the invariant

$$
\begin{aligned}
p_{A,h}&=0^d10\,0^{e_h},&p_{B,h}&=0^{d+2+e_h},&D_h&=d+2+e_h,\\
N_{A,h}&=G_d,&N_{B,h}&=0,&s_h&=r_B+h,\\
i_{A,h}&=r_A+h,&i_{B,h}&=r_B+h,\\
k_{A,h}&=G_{D_h+1}-G_d-2,&k_{B,h}&=G_{D_h+1}-2,\\
\sigma_h&=k_{A,h}-i_{A,h}=k_{B,h}-i_{B,h}
 =G_{D_h+1}-2-r_B-h\ge0.
\end{aligned}
\tag{29}
$$

Both actual cursors equal $D_h$, both exact unread tails are zero, both whole current words are $Z(r_B+h)$, and both full current boundaries are $\partial(D_h,r_B+h)$. Each retains its original endpoint, provenance and own caches/time.

The first Step proves the base. If $\sigma_h>0$, both real Next calls read nothing, use the common Low argument $r_B+h$, Advance their own times, Return and decrease both slacks by one. If $\sigma_h=0$, both physically Read the next zero at common original cursor $D_h$, append it, preserve their respective $N$ values, Emit with that same Low argument and Advance. Both death clocks increase by $G_{D_h}$, giving new depth $D_h+1$ and common slack $G_{D_h}-1$. In this case set $e_{h+1}=e_h+1$; otherwise retain $e_h$. These cases exhaust the runtime, preserve every displayed offset, the actual tails and owned transport, and are finite by productivity. Induction proves (29). In particular new Step $j\ge1$ has public sequence

$$
\operatorname{Emit}(\operatorname{Low}(r_B+j-1)),\quad
\operatorname{Advance},\quad\operatorname{Return}.
\tag{30}
$$

At every matched returned cut $h\ge1$, every finite precision $n$ gives exactly the same two integers in the two worlds:

$$
\lfloor2^n(b_*+q_0\alpha^{D_h})\rfloor,
\qquad \lfloor2^nb_*\rfloor.
\tag{31}
$$

Full frames, identifiers, prefixes and completions match. Induct over every finite future command/event prefix on the same tape. Equal histories give equal next actions and tape responses; (29)–(30) match real Steps, (31) matches both ports, and source-independent controls/right checks match. Local counts, computations, streamed outputs and decisions consequently match. If a current record is legitimately earned, its current coordinates, DATA guards, finite representatives and budgets match, and its continuing right is actually valid separately in each world. Every primitive inside its derived programs is already covered by the induction; none supplies an initial getter or exports unequal private history.

Every coordinate of an infinite permissible future lies in a finite prefix, so this proves coordinatewise all-future equality without claiming finite completion of infinite interaction. Hidden backend work, latency, physical Reads and old fields are not equated. The same actual pair is used throughout, with no later precision-dependent reselection. All-precision equality begins after this real first-Step merger. $\square$

## 9. Risk integration on the fixed pair

Proof of Theorem 4.2. Lemmas 6.1–8.1 select $I_*,E_*,b_*,d,A,B$ without using correctness. Let $T_A,T_B$ be the measurable almost-sure finite-termination events for these two fixed actual worlds and put

$$
E=E_*\cap T_A\cap T_B.
$$

Only two probability-one totality events have been intersected; thus $\mu(E)=\mu(E_*)\ge1-\varepsilon$. For each $\omega\in E$, a no-Step terminal decision gives the same entire task output by stationary replay. A first-Step branch has the matched intermediate events and the entire future of Lemma 8.1 on this same tape. Finite termination then gives the same final output, including any earlier streamed fragments or decisions inside a query or Step frame.

The original targets differ. Hence, writing $C_A,C_B$ for the exact-correctness events, pointwise

$$
\mathbf1_{C_A}+\mathbf1_{C_B}\le1\quad\text{on }E,
\qquad
\mathbf1_{C_A}+\mathbf1_{C_B}\le2\quad\text{on }E^c.
$$

Integrating on the one common probability space gives

$$
s_D(A)+s_D(B)\le\mu(E)+2\mu(E^c)
=2-\mu(E)\le1+\varepsilon.
\tag{32}
$$

Thus at least one actual world has success at most $(1+\varepsilon)/2$. If $p>1/2$ were a uniform lower bound, choose $0<\varepsilon<2p-1$; then $2p\le s_D(A)+s_D(B)\le1+\varepsilon<2p$, a contradiction. Arbitrarily small $\varepsilon$ gives the infimum (13), without asserting attainment at exactly one half or failure for each separately fixed $b$.

Correctness entered only through the two-indicator inequality. No event of success merely $p<1$ was treated as full measure. In particular KNOWN Theorem 9.1's countable probability-one intersection for the smaller Extent-only interface is not an argument for this bounded-error conclusion. The worlds here are chosen before the tape, rather than a bad world chosen after observing each tape. $\square$

## 10. Legal stopping and the separate expectation result

Proof of Theorem 4.3. Suppose instead there were a finite constant $C$ with $\mathbb E[B_D(W)]\le C$ for every $W\in\mathcal W$, while $D$ is per-world almost surely total and $s_D(W)\ge p>1/2$. Choose an integer $M\ge1$ with

$$
C/M<p-1/2.
\tag{33}
$$

Construct $D[M]$ using the same unchanged tape law and public inputs. It emulates $D$ from its original local state, forwarding every real source request, actual producer event, complete frame, completion, release/control operation and right check in the original order. Add a counter of actual primitive Reference completions before the first actual Step, including those inside wrappers. Disable its guard permanently when first Step is initiated; all later References are unrestricted.

At the $M$-th pre-Step Reference completion, intercept after the actual complete frame and before resuming the emulated $D$ or starting any next request. That Reference transaction has ended and the producer is at a returned cut. Stop the emulation and output a fixed canonical boundary guess, for example $\partial(1,1)$, then terminate. This completed-frame stop cancels no request, initiates no extra Reference or Step, overlaps nothing and interleaves no action inside Step. It needs no new source information or right.

To produce one final task result when $D$ has already streamed tentative fragments, direct only its task-result writes into finite paid private buffering while preserving all their source-independent virtual local effects. Source requests, events and controls are forwarded as just described; they are not buffered or replaced. If emulated $D$ terminates first, freeze it, disable the guard and publish exactly its finite buffered output. If the completion guard wins first, discard the tentative buffer and publish the canonical guess. No extra random symbols are needed. This preserves the emulated input sequence because Definition 3.2 supplies no result-sink feedback channel and physical emulation delay is not an observation. A different interactive-output model is not silently covered.

A final decision inside an unfinished query does not cancel that transaction or start another. During finite terminal output/flush retain the original allowed early-termination semantics; if terminal handling instead drains the one already issued finite frame without resuming $D$, that too initiates no request. At most one additional completion can occur, by seriality. Already forwarded control effects remain in force. If a Step is pending, its actual mandatory Emit/Advance/Return work is retained; its initiation has already frozen the count. An early task answer does not erase a Read or any remaining issued source work.

Consequently $D[M]$ has the conservative pointwise cap $M+1$ on completed pre-Step References, including exceptional tapes and terminal flush. Before the guard, fewer than $M$ have completed. At its trigger there are $M$ and no outstanding successor query. If an emulated early halt wins, at most the one outstanding frame can additionally complete during terminal handling, and no new request starts. After first-Step initiation the resource no longer changes. No sharper truncation cap is needed.

On each tape where $D$ terminates and $B_D(W)<M$, the guard does not interrupt it before its terminal decision. Virtual local effects, source observations and tape accesses match through that decision, and $D[M]$ gives exactly its answer. A pending Reference completing only during later flush cannot retroactively spoil this agreement: the guard has already been disabled. Thus the possible loss of an originally correct answer is contained in $\{B_D(W)\ge M\}$ apart from the null nontermination set. The distinction is between actual completion and mere initiation of the last unfinished frame.

The new receiver is per-world almost surely total: either the guard triggers at a finite completed cut, or the same almost-sure finite emulation ends and the finite output plus any already issued finite terminal work finishes. Finiteness is used only for reached actual services and the supplied productive producer, not arbitrary internal or limit states. Buffer length is finite on every actual finite prefix, with no uniform length bound assumed.

All stopping and count events are measurable. Markov's inequality for the original nonnegative completion count gives, for every fixed actual world,

$$
\mu\{B_D(W)\ge M\}\le\frac{\mathbb E[B_D(W)]}{M}\le C/M.
$$

Therefore

$$
s_{D[M]}(W)\ge s_D(W)-\mu\{B_D(W)\ge M\}
\ge p-C/M>1/2
\tag{34}
$$

uniformly in $W$. But $D[M]$ is almost surely total, has the uniform finite cap $M+1$, and uses the same world-independent tape law. Theorem 4.2 contradicts (34). This proves (14). The proof neither bounds request initiation by completion of that same request nor infers infinite expectation just from an unbounded pathwise worst case. $\square$

## 11. All-closed-error scope and the preserved positive

The larger two-port contract permits arbitrary jointly adaptive, correlated and nonnested closed-error replies $a,c\in\mathbb N$ with

$$
|a2^{-n}-(b+q_0\alpha^d)|\le2^{-n},\qquad
|c2^{-n}-b|\le2^{-n}.
\tag{35}
$$

Each floor in (9) has error strictly smaller than $2^{-n}$ and is a permitted instance. A receiver required to satisfy the same totality, success and uniform resource guarantee for every allowed joint reply trace must satisfy it for these two fixed programs. The two negatives therefore refute that universal-all-error requirement by subclass inclusion. They do not assert failure for every individually specified nonfloor selector or assign a probability distribution to service errors. Repeated floor replies are not independent noise samples.

PAID Theorem 37.1, restricted exactly as KNOWN Section 14 by $q=q_0$ and $b\in B$, already supplies a deterministic finite-per-instance receiver for every allowed joint trace of (35), including empty entry. Its exact target is the original full owned boundary and it also obtains a genuine reached record with retained calling rights. No new positive receiver or implementation is claimed here.

For its exact resources, it requests stationary paired Extent/Reference precisions until $a-c>2048$. With $z_0=q_0\alpha^{d_0}>0$, the first accepted index $n_*$ is finite and satisfies

$$
n_*\le\min\{n\ge1:2^nz_0>2050\}.
\tag{36}
$$

Retaining that Reference reply, later Extent differences have error at most $2\,2^{-n_*}$. The existing three-ratio test and complete lifetime between the first two actual block updates recover the original coordinates and a genuine reached boundary. The actual resources supplied by PAID (134)–(143) are

$$
\begin{array}{c|c}
\text{resource}&\text{actual count}\\\hline
\text{pre-Step Reference completions}&n_*\\
\text{later Reference calls}&0\\
\text{Extent calls}&n_*+m\\
\text{real Steps / producer triples}&m\\
\text{new physically Read raw bits}&g_1+g_2\in\{2,3,4\},
\end{array}
$$

$$
m\le2G_{d_0+1},\qquad d_*\le d_0+4.
\tag{37}
$$

Forced zeros are included. Original setup, old driver work and all finite framing/arithmetic remain paid. The case $d_0=0$ uses its separate original $(0,0)$ rule. The bound (36) depends on the actual instance and is not a uniform expected or almost-sure cap over all depths. Thus fixed public $q_0$ can still permit this instance-dependent recovery without contradicting either theorem.

## 12. Exact paid coordinates and whole-system limits

For the final pair of Section 8, use the coordinate order

$$
(\operatorname{Read},\text{raw payload bits},\operatorname{Next},
\operatorname{Emit},\operatorname{Advance},\text{postinitial producer Return}).
$$

Its genuine old vectors are

$$
(d,d,r_A,r_A,r_A,r_A),\qquad
(d+1,d+1,r_B,r_B,r_B,r_B).
\tag{38}
$$

Through $h\ge1$ completed new Steps the incremental vectors are

$$
(2+e_h,2+e_h,h,h,h,h),\qquad
(1+e_h,1+e_h,h,h,h,h).
\tag{39}
$$

Indeed each old zero is read once; the first new blocks use two Reads in A and one in B; thereafter (29) appends exactly $e_h$ actually read zeros in each. Every completed Next contributes one of each producer event. Total raw cursors become $D_h$ in both worlds, but total triple counts remain $r_A+h,r_B+h$ and differ by $G_d$. Under PAID's fixed two-bit code for $E_0,E_1,A,R$, old producer payloads are $6r_A,6r_B$ and new completed-Step payload is $6h$ each, before framing. Initialization/handoff acknowledgements and both kinds of service completion are separate. With no new Step the six new source coordinates are zero, while port calls and local output/work still cost.

An answer inside a Step is charged for actually performed events and any remaining work of the issued transaction. Neither observational equality nor an early answer equates or erases hidden physical Reads, backend work, workspace or latency.

Every public rational $q_0,u,v$ and private rational $b$ has actual finite encoded payload. Program/reference/framing installation, endpoint and persistent-right binding, driver command acquisition/computation, every genuine old call, actual source provisioning/generation/delivery/storage and retained archives remain paid. So do every refinement or repetition, finite precision, whole integer and its integer part, sign/framing/identifier field, completion, control check, refusal actually in the protocol, local comparison/scan/copy/clearing operation, tape access/generation and output fragment. Excluded observation channels are not zero-cost components.

For the specified floors the finite arithmetic component bounds of KNOWN Section 11 and PAID Sections 25, 36, 38 apply with $q=q_0$. To make the scope of that reuse explicit, for a finite actual producer/service segment let $D_{\max}$ be maximum initialized acquired depth, $N$ maximum requested precision or zero if none, $Q$ completed Extent calls and $R$ completed Reference calls. Let $B_q,B_b,B_I$ be actual payload lengths of $q_0,b,(u,v)$, $c$ descriptor/control width and $P$ installed program/convention length. Put

$$
\Lambda=D_{\max}+B_q+B_b+B_I+N+c+32.
$$

On a fixed finite number of paid sequential binary work tapes, each specified floor has conservative $O(\Lambda^3)$ bit work and $O(\Lambda)$ reused scratch. Rational Reference division fits that same upper bound. The inherited Extent proof generates quadratic coefficients of $O(D_{\max}+1)$ bits, clears finite denominators, uses $O(\Lambda)$ exact sign comparisons in finite integer bisection and grade-school $O(\Lambda^2)$ work per comparison. All reply widths, including integer parts, are $O(N+B_q+B_b+1)$; exact zero is handled before squaring. This is a credited symbolic finite service bound, not a computation performed here.

Accordingly a conservative producer/service/control bound through old $r_i$ and new $h$ completed Steps in world $i$ is

$$
O\!\left(P+B_q+B_b+B_I+I_i+
(r_i+h+D_{\max}+Q+R+1)\Lambda^3+B_{{\rm out},i}\right),
\tag{40}
$$

with $O(P+\Lambda)$ simultaneous producer/service/configuration/scratch bits before the other components are added. $I_i,B_{{\rm out},i}$ are full actual chosen inputs/outputs, including emitted prefixes of unfinished transactions where present; any issued unfinished service also retains its actual work. This is the direct sum of the supplied finite components with counted rational Reference services. It does not bound arbitrary receiver computation, and no optimum is asserted.

The stopping wrapper adds an $O(\log(M+1)+1)$-bit counter/mode, paid comparisons/updates and emulation work, and its actual simultaneous tentative-result buffer. Writes, copies, clearing/discarding, final flush and the canonical guess all cost. Each finite prefix has finite buffering, with no uniform size bound. The wrapper creates no source primitive or new right; it preserves mandatory transactions and passed forced zeros. Arbitrary correlated tape-law access is a premise, not a free bounded-cost random generator.

Whole peak storage adds all coexisting receiver state/workspace, driver state, source backend, random-tape backend, buffer, protected/isolated but still present state and retained outputs to the simultaneous producer/service state. Whole work adds their actual provisioning, generation, control and physical costs. Separate component peaks cannot replace this sum. No uniform bound is obtained on offset denominator/encoding, selected depth, old driver work, witness construction, precision, Extents, later References, receiver work/space, randomness supply or physical backend/latency. The renewal thresholds need not be computable from the tape law. Every carrier and final witness is finite and initialized; that existential statement supplies neither a receiver implementation nor a uniform quantitative witness algorithm.

## 13. Exact supplier roles and mathematical increment

The source texts below are credited under the exact interfaces stated in them. Embedded linked volumes, Lean declaration names, Scribes and external citations in those texts are opaque references here; their targets were not independently accessed or authenticated. Their stated geometry/execution results are conditional mathematical suppliers, not new kernel certificates.

| Supplied sections | Exact role and transfer boundary |
| --- | --- |
| KNOWN Sections 1–2 | Same no11 source, $\alpha,G_j$, already public $q_0$, prescribed rational offset interval, whole floors, actual initialized producer and complete owned boundary. These determine the present world class. |
| KNOWN Sections 3–8, especially Lemmas 4.1–4.4 and 5.1 | Deterministic original-boundary and separate raw-prefix tasks, genuine deep family, every old interval, owned death walls, actual first-Step and full-future invariant, legal irrational Extent centre and finite-cell placement. Section 8 separates finite initial matching from post-Step all-precision equality and preserves reached positives. Section 8 above consumes these actual source facts explicitly. |
| KNOWN Section 9, Theorem 9.1 | Probability-one nonrecovery on the smaller Extent-only interface via a countable intersection of full-measure correctness events. It supplies no present bounded-error or expected-budget inference. |
| KNOWN Sections 10–12 | Exact-offset disclosure adapter, full component/old-new accounting and scoped attribution. Disclosure changes information; component bounds do not bound arbitrary decoders or physical backends. |
| KNOWN Sections 13–14 | Same-offset Reference, serial whole frames, primitive completion resource, proper-prefix early answers and the exact restriction of PAID 37.1 to $q=q_0,b\in B$. These supply the interface and preserved positive. |
| KNOWN Sections 15–17, Lemmas 15.1–15.2 and Theorem 16.1 | Deterministic whole-initialized-world realization/renewal and fixed-public-unit uniform-cap negative, including unfinished frames. The new Lemma 7.1 retains high probability simultaneously across tape-indexed histories under per-world almost-sure premises. The deterministic theorem alone does not establish (12) or (14). |
| PAID Sections 1–9, especially Definitions 1.2, 2.2 and Theorems 3.1–3.2 | Empty source-independent initialization, physically sequential Read including forced zeros, productive clock-driven Next, finite-core correctness, exact actual-tail resumption, finite response guard, scoped earliest stop, bounded use and paid finite arithmetic/backend accounting. Those existing acquisition/continuation results are not new here. |
| PAID Sections 10–12 | Full current owned fibres, exact boundary coordinates, historical ambiguity, authenticated-counter repair and intrinsic transport. Whole-point equality and current-region equality do not identify actual private histories. |
| PAID Sections 13–15 | Calibrated ordered Wall acquisition and explicit installed digital service. That separate observation port is absent at this blind handoff; its positive and reduced-input obstructions remain in their original scopes. |
| PAID Sections 16–21, especially 16.1, 17.1–17.3 and 18.1–18.3 | Persistent exclusive handoff, hidden multiplicative-unit ratio/complete-lifetime inversion, real Emit branch interpretation, legitimately earned current-record programs and resource/rights obligations. Their positive inversion is consumed only after its required error transport, as PAID 37.1 already proves. |
| PAID Sections 22–26 | Affine fixed configuration, difference detection, locally calibrated next complete lifetime, reached recovery and continuing guarded use with full costs. Their reached target remains possible. The provisional question at 24.3 is settled for its weaker deterministic no-Reference interface by PAID 29.1; it is not treated as still open. |
| PAID Sections 27–30 | Full observations and floor/all-error quantifiers, actual shallow proper-death merger and full-future control induction, no-Reference original-boundary negative and preserved reached positives. The small hidden $q$ chosen after a deterministic prefix in 29.1 cannot prove a result at each already public fixed $q_0$. |
| PAID Sections 31–35 | Owned same-depth intersections, genuine-origin monitored supplemental preparation, complete receiver-accessible cut, binary residue and finite event inverse. Those use an explicit authentic historical record channel absent here; their positives and paid costs are neither imported as free initial advice nor contradicted. |
| PAID Sections 36–37 | Same-$b$ Reference, original owned target, serial completion/early-answer convention and the all-joint-closed-error finite-per-instance positive with resources (134)–(143). The parameter restriction is exactly $q=q_0,b\in B$. |
| PAID Sections 38–41 | Two finite floors and deterministic Reference-resource obstruction. The static family uses varying $q_d=1/F_d$, and the final shallow pair uses a small $q_*$ selected after a prefix; neither is the fixed-public-unit randomized claim. Its unbounded deterministic count conclusion also needs the new stopping reduction to imply an expectation obstruction. Definition 41.3 preserves the separate original targets and interfaces. |

The addition is source-specific simultaneous family support, high-mass renewal on finitely many actual carriers, a pair chosen before tape revelation and bounded-error indicator integration, together with the legal completion-stopping bridge to uniform expectations. Standard continuity of measure from below, measurable causal histories, finite unions of null sets, union bounds, indicator integration and Markov's inequality are reused. So are rational midpoints/density, Archimedean decay, quadratic conjugation, dyadic cells, finite integer/quadratic arithmetic and causal replay. No new general probability principle, exhaustive literature search or global novelty claim is made.

## 14. Quantifiers and remaining boundaries

The order of choices is essential: fix public $q_0,u,v$, programs and protocol; fix $D$ and its one world-independent law; fix $K$ and $\varepsilon$ for the bounded-cap theorem; choose finitely many probability thresholds, supporting carriers and the retained event; choose one final rational $b_*$, finite $d$ and both actual initialized worlds; only then reveal $\omega$. Tape-indexed histories describe the event for these fixed choices. No world is chosen separately after a revealed tape. Totality and caps are invoked only on finitely many real carriers and the two final worlds, never an uncountable full-measure intersection.

No totality premise uses $q_0=0$, irrational private calibration, an infinite-depth limit, an infinite-precision call or an unrealized formal reply stream. The small signal comes from finite real paid depth with $q_0$ fixed. Supporting carriers may differ between proof stages; the offset never changes within an actual run. Both true initial values are strictly within the same final open interval inside the prescribed public interval. Initially these values are unequal: their difference is $q_0\alpha^{d+2}>0$. Sufficiently fine unqueried stationary precision can separate them. Only the selected finite histories agree on a high-mass event; all-precision equality begins after the actual first Step.

The risk result is an infimum over the declared hidden-offset/world class. It does not supply a minimizing world at exactly one half, failure for every separately fixed offset, attainability at one half, an optimal quantitative risk/resource tradeoff, or a theorem about every individual nonfloor selector. Expected and almost-sure caps are different resource hypotheses. The second result uses the explicit no-result-feedback model and its completion-based simulation, rather than a general statement about all interactive outputs.

The only new target theorem here concerns full ORIGINAL owned-boundary recovery. No new raw-prefix nonrecovery theorem is submitted merely because the displayed pair also has different original tails. There is no exact calibration reconstruction, actual private $(p,i,N_p)$ recovery, authenticated old counter, whole infinite raw/current-source recovery, history exporter, restored entrance configuration or rewind. Genuine later current records and their lawful finite guarded use retain their existing positive results and actual rights.

Extra historical records, disclosed offset, initial Wall/raw access, timing/configuration advice, result-sink feedback, informative new handoff, changed source/region promises, revocation, concurrent clients and non-Advance mutation alter the hypotheses and require new arguments. Equality of printed names, compatible provenance or numerical values cannot replace actual source association and lawful operations.

The original exact-$p_J$/all-response FIB task, actual-joint/common-parent relation-generation obligations, global 8-versus-9 and 9-sufficiency questions, strict 19.2 target, native seed/payload/Stop controller, fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization, complete original-response and arbitrary interior-cut tasks retain their separate scopes. No bridge from (12) or (14) to their settlement is supplied. No general independent space/time/boundary/memory inverse, physical same-region reference, universe-level impossibility, universal resource optimum or sustained whole-goal completion follows. There is no theorem about empirical neural-network performance, all learning, training quality or physical noise averaging. Any interpretation as representation/interface insufficiency is conditional on precisely the observation and resource model proved here.

[PAID]: RECURSIVE_RELATIONAL_OBSERVATION_PAID_ZECKENDORF_CURRENT_RETURN.md

## 追加锚（本行以下为增补区）

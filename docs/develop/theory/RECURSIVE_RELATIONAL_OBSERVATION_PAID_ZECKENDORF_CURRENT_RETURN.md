# Paid Zeckendorf observation at a current return

> Mathematical reference input. The results below have ordinary proofs; no new Lean certification is asserted. This continuation treats an operational object distinct from the supplying native controllers: a sequential-input, productive representation of the endpoint-inclusive Zeckendorf successor. The parent RRO volume exceeds the single-volume capacity.

## 1. Carrier, paid entrance and the continuing task

**Definition 1.1 (Standing source and cited suppliers).** All indices are nonnegative integers. Set

$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,
\qquad
K=\{x\in\{0,1\}^{\mathbb N}:\forall j\ge0,\ x_jx_{j+1}=0\}.
$$

Digits are ordered from low to high. Write $Z(N)$ for the zero-padded finite Zeckendorf representation, $q_L(x)=(x_0,\ldots,x_{L-1})$, and $f(x)=x_0$. The map $T$ is exactly [RRO Definition 20.1][RRO]: at the first adjacent $00$, clear all lower positions and put one at its first position, retaining higher digits; if no $00$ occurs, return $Z(0)$. Thus both $(10)^\infty$ and $(01)^\infty$ map to zero. Positional deletion is not $T$.

Use the following previously proved facts, with their full endpoint conventions. RRO20.6 identifies $q_L$ with the length-$(G_L-1)$ future lowest-digit observation up to a bijective relabeling. RRO20.7 gives the itinerary conjugacy

$$
\Phi(x)=(f(T^i x))_{i\ge0},\qquad \Phi T=S\Phi.
$$

RRO24.2 supplies translated finite precision and the representative $q_L(Z(N_p+k))$ when its stated uniform prefix condition holds. RRO35.1–35.2 supply the more finely placed block-cylinder clocks used here; those clocks and their endpoint witnesses are prior results, not new claims of this volume.

**Definition 1.2 (Sequential source contract and initialization).** One actual, fixed $x\in K$ supplies a private sequential endpoint to the producer. Its sole input operation is $\operatorname{Read}$: at cursor $d$ it delivers the one raw bit $x_d$ and changes that cursor to $d+1$. Every reached Read is required to finish in finite time and is paid. There is no random access, rewind, skip, state query, itinerary query or spatial-response operation on this endpoint. Even a zero forced by a preceding one is physically read if the cursor is to pass it. The no11 property is an input promise, not an algorithm for recognizing an arbitrary infinite input.

The observer has a different endpoint: a live, exclusively bound continuation channel to this producer. Its visible producer events are only

$$
\operatorname{Emit}(b),\quad \operatorname{Advance},\quad \operatorname{Return}.
$$

Their actual order is visible. Private raw responses, read counts, numeric registers and computation delays are not observations on this channel. In particular elapsed wall time is not an additional source channel. Return counts are source-operation counts, not a claim about constant physical latency. A logical source advance occurs only at Advance; no autonomous source advance happens during observation, query computation or a pause.

Initially the producer has read no raw bits. Its finite registers are $(p,n)=(\varnothing,0)$ and fixed derived caches; the observer initializes its own empty prefix and zero counter. Program, endpoint names and initial rights are fixed independently of $x$: only the private raw responses vary with the source. A fixed finite program and the actual endpoint bindings and rights are installed and paid as in Section 8. Initialization finishes with an actual fixed acknowledgement, called return zero. It performs no raw Read or Advance. This source-independent initialization prefix is omitted from subsequent producer-triple counts and is included in initialization/output cost. Those rights persist through pauses and are neither inferred from the bit sequence nor minted by a decoder. Source provisioning is exactly the sequential contract above. Construction of a whole unknown infinite source, a finite generator for every $x$, and finite-cost installation of an infinite tape are not supplied by it. Backend provisioning and generation costs remain separate explicit summands in Section 8.

**Definition 1.3 (Current task and its full finite response).** Fix requested depth $L\ge0$ and continuation horizon $H\ge0$. At an actual returned source time $r$, a legal bounded client may ask for the current $q_\ell$ at any $0\le\ell\le L$, or advance, with at most $H$ advances in total. Queries may be repeated and chosen from preceding answers. Every advance must give its actual emitted bit and an actual next return; the final source is the current source after those advances. A query changes neither source time nor the raw cursor. A finite command sequence is required; the horizon alone does not bound the number of repeated queries.

The maximal data response for this task at $z=T^r x$ is

$$
\mathcal R_{L,H}(z)=
\left(v_H(z),\ (q_L(T^jz))_{0\le j\le H}\right),
\qquad
v_h(z)=(f(T^iz))_{0\le i<h}.
\tag{1}
$$

All shorter query outputs are truncations, and every bounded adaptive output transcript is determined by (1). The task includes the successive source-time counters and the finite returned registers specified below. It does not ask to print an entire infinite successor or the unread raw source. A continuation handle remains a live object with its original rights, not a recovered infinite datum.

Put

$$
s_L=G_L-1,\qquad
D(L,H)=
\begin{cases}
H,&L=0,\\
H+s_L,&L\ge1.
\end{cases}
\tag{2}
$$

For $L\ge1$, RRO20.6 shows that equality of (1) is exactly equality of $v_{H+s_L}$. Indeed, the time intervals of length $s_L$ beginning at $0,\ldots,H$ cover every index $0,\ldots,H+s_L-1$, and $s_L\ge1$. For $L=0$ the spatial answers are empty and (1) is just $v_H$. These are applications of the existing partition identity; they do not install an oracle for (1).

## 2. A productive clock-driven source representation

**Definition 2.1 (Clock notation and finite arithmetic).** Let $\mathcal B=\{0,10\}^{<\omega}$, with unique parsing into the displayed blocks. For $p\in\mathcal B$ put

$$
d=|p|,\quad N_p=\sum_{j<d}G_jp_j,\quad
C_p=\{x\in K:q_d(x)=p\},\quad
M_p=G_{d+1}-N_p,\quad k_p=M_p-2.
\tag{3}
$$

For the empty word $M_p=2$ and $k_p=0$. By RRO35.1, $\Phi(C_p)$ is a temporal atom precisely at lengths

$$
b_p\le n\le k_p,\qquad
b_{q0}=b_{q10}=M_q-1,\quad b_\varnothing=0,
\tag{4}
$$

and its next split is into $C_{p0},C_{p10}$. The child labels satisfy

$$
M_{p0}=M_p+G_d,\qquad M_{p10}=M_p+G_{d+1}.
\tag{5}
$$

In particular all $x\in C_p$ have the same itinerary coordinates below $k_p$, and the two sources $p0v,p10v$, $v=(01)^\infty$, first differ in their itineraries at $k_p$. Every integer at least two occurs once as a label $M_p$.

The finite operation $\operatorname{Low}(A)=f(Z(A))$ is evaluated by ordinary integer arithmetic. Generate consecutive Fibonacci weights up to the first one above $A$, then greedily subtract in decreasing order. Keep consecutive weights and recover the preceding weight by subtraction. After a selected $G_j$ with $j\ge1$, the residual is below $G_{j-1}$, so the next weight is not selected. At $G_0=1$ the final residual is zero; for $A=0$ the empty expansion already has zero residual. Thus the resulting digits are legal and have value $A$; the usual uniqueness of finite Zeckendorf expansions identifies them with $Z(A)$. Retain or output the required low digits, padding by zeros. This is the standard finite Zeckendorf algorithm, also represented in the pinned upstream `Mathlib.Data.Nat.Fib.Zeckendorf`; it is not an infinite-state response primitive. The bit costs of actually carrying out these steps are included in Section 8.

**Definition 2.2 (The clock-driven lazy runtime).** A returned producer state consists of $p\in\mathcal B$, the source-time counter $n$, the private raw cursor $d=|p|$, the live raw endpoint and its binding, and deterministic caches $N_p,G_d,G_{d+1},k_p$. Caches are updated by (3)–(5). Scratch and pending output fields are empty at Return. The initial state is the one in Definition 1.2.

A call $\operatorname{Next}$ from a returned state performs the following finite transaction.

1. If $n<k_p$, do no raw Read. If $n=k_p$, perform one Read at $d$. On bit zero append the block $0$. On bit one perform a second Read, check the promised zero, and append $10$. Update $p,d$ and the caches to this child. There is no returned state with $n>k_p$ in the reached domain. The check only describes the promised domain; no recognition theorem for inputs outside $K$ is asserted.
2. With the resulting prefix $p'$, calculate $b=\operatorname{Low}(N_{p'}+n)$ by the finite arithmetic of Definition 2.1. Actually emit $\operatorname{Emit}(b)$.
3. Actually perform Advance by incrementing the lazy source's time field to $n+1$. Clear scratch, emit Return, and enable the next call. Its returned prefix is $p'$.

The source is stored in a productive representation, not as an eagerly rewritten infinite positional tape. Its denotation at a returned state, with actual unread tail $z_j=x_{d+j}$, is

$$
\llbracket p,n,z\rrbracket=T^n(pz).
\tag{6}
$$

The origin prefix is immutable except for extension by paid input; Advance changes the current object (6). A requested finite spatial answer is calculated from acquired finite data only when the guard in Section 4 licenses it. Section 3 proves that every emitted bit and represented advance agrees with the exact $T$, including alternating sources. This representation and controller are new premises, and are not identified with the NativeAcquiredPrefix controller or an in-place infinite-tape machine.

**Definition 2.3 (A source-blind temporal observer).** The observer maintains its own $(\widehat p,n)$, initially empty and zero. It receives the event triples, checks their order, and acts on Emit at source time $n$ as follows.

If $n<k_{\widehat p}$, keep the prefix. If $n=k_{\widehat p}$, calculate the two finite bits

$$
a_0=\operatorname{Low}(N_{\widehat p}+n),\qquad
a_1=\operatorname{Low}(N_{\widehat p}+G_{|\widehat p|}+n).
\tag{7}
$$

Choose child $\widehat p0$ when the received bit is $a_0$, and child $\widehat p10$ when it is $a_1$. On Advance increment the counter, and at Return retain the resulting state. The two bits in (7) are unequal by the split statement in Definition 2.1. Thus the rule uses the received event and finite arithmetic, not a hidden branch flag or a source answer. Nonbranch emissions can also be checked against their finite representative; this optional check has the same bounds as a producer emission.

The mathematical event trace exists whether or not it is archived. The observer can discard every processed triple after updating this finite record. No full-history storage is a premise.

## 3. Actual acquisition, source correspondence and exact resumption

**Theorem 3.1 (Every finite run has its actual temporal and raw fibers).** For every $x\in K$ and every $n\ge0$, $n$ successive Next calls finish. At the $n$-th return:

$$
\begin{aligned}
\text{the emitted bit word}&=v_n(x),\\
\widehat p=p,\qquad x&\in C_p,\qquad b_p\le n\le k_p,\\
\text{the paid raw word}&=p,\qquad \text{raw cursor}=|p|,\\
\text{current source}&=\llbracket p,n,\operatorname{tail}_{|p|}x\rrbracket=T^nx.
\end{aligned}
\tag{8}
$$

For every attained public temporal trace at a fixed return $n$, its source fiber is exactly this $C_p$. Its finite producer registers are the deterministic registers specified in Definition 2.2, and are reconstructed by the observer from the events and its initialized binding. This assertion excludes the unread endpoint's contents; it does not reconstruct an infinite source from a finite word.

Proof. At time zero $p$ is empty and (8) holds. Suppose it holds at time $n$. If $n<k_p$, the common temporal prefix of $C_p$ includes coordinate $n$. The finite point $Z(N_p)=p0^\infty$ belongs to $C_p$, so its value there is $f(T^nZ(N_p))=\operatorname{Low}(N_p+n)$. The producer therefore emits the correct bit without a Read. The same temporal atom survives at length $n+1\le k_p$.

If $n=k_p$, the raw endpoint is exactly at $|p|$. Its next one or two actual bits choose the unique next block of $x$; the no11 promise justifies the checked zero. The resulting $p'$ is an actual longer raw prefix. Its cylinder is one of the two new temporal atoms, born at

$$
b_{p'}=M_p-1=k_p+1=n+1.
$$

RRO35.1 says its points agree in coordinate $n$, whereas the two children have different such coordinates. Choosing $Z(N_{p'})\in C_{p'}$ proves that the producer's finite arithmetic gives the actual emitted bit, and proves that (7) reconstructs the same child at the observer. By (5), $k_{p'}\ge n+1$. There are at most two Reads, and all remaining work is finite integer computation. Each call terminates under the sequential service contract.

Advance changes (6) to $T^{n+1}(p'\operatorname{tail}_{|p'|}x)=T^{n+1}x$. Clearing scratch gives exactly the stated returned fields. This proves the induction. RRO35.1 identifies the temporal atom of $v_n(x)$ as the entire $C_p$, including both sides of every split endpoint. Hence all and only the sources in that cylinder give the same trace at the fixed return, and by the just-proved acquisition rule they also give exactly the raw word $p$ and cursor $|p|$. No observed read count was used in the observer's argument. $\square$

**Theorem 3.2 (Restart at the exact unread tail).** Let a run of Theorem 3.1 have returned at $(p,n)$ with cursor $d$. For every $m\ge0$, running $m$ more Next calls from that actual state on $\operatorname{tail}_d x$ gives precisely the suffix of the initialized $(n+m)$-call run: the same raw acquisitions, chronological events, finite returned fields and current point $T^{n+m}x$. It reads no earlier raw coordinate. Every finite continuation is productive, including from the two alternating sources and after their images have reached the natural core.

Proof. The first new Read, when reached, asks exactly for coordinate $d$ of the original source. Before it, the stored clocks and finite arithmetic determine all events without input. After a block is consumed, the new raw cursor is $d+1$ or $d+2$, and the remaining endpoint is exactly the corresponding tail of the old one. All finite register updates are deterministic. Induction on the additional Next calls therefore gives identical events and fields in the restarted and uninterrupted runs. Theorem 3.1 gives the stated current point and finiteness at each induction step. It made no eventual-zero assumption. In particular neither recognizing an infinite alternating word nor locating its nonexistent first $00$ is performed. $\square$

This source-specific restart proof has the same prefix/tail structure as the already supplied `native_acquired_prefix_cylinder` and `native_acquired_prefix_resumption`, including their private `next_native_spec` and `raw_tail_add` helpers. Those existing declarations and their owning Scribe establish real raw-stream execution and full native resumption under their original controller. They are positive prior supply. Here the new work is the clock-driven controller, its correspondence (8) to the distinct $T$, and the current-return stopping and use results below.

## 4. Exact acquired-response condition

**Theorem 4.1 (Current-return response sufficiency, with an actual obstruction).** Let $(p,r)$ be any attained return of the unrestricted Next run of Theorem 3.1. For every $L,H\ge0$, the following are equivalent:

$$
\begin{gathered}
\mathcal R_{L,H}(T^r x)\text{ is constant for }x\in C_p;\\
\text{the acquired public temporal trace determines that response};\\
r+D(L,H)\le k_p.
\end{gathered}
\tag{9}
$$

When these conditions hold, all maximal spatial answers are explicitly

$$
q_L(T^{r+j}x)=q_L\bigl(Z(N_p+r+j)\bigr)
\quad(0\le j\le H),
\tag{10}
$$

and the first $H$ actual advance emissions are $\operatorname{Low}(N_p+r+j)$, $0\le j<H$. These expressions are finite computations on the observer's earned prefix; their evaluation cost is not suppressed.

Proof. Theorem 3.1 identifies the exact acquired fiber as $C_p$. By Definition 2.1 all its itineraries agree below $k_p$. If $r+D\le k_p$, their future words of length $D$ starting at $r$ are equal. Definition 1.3 identifies precisely those future words with equality of the full data response, proving sufficiency. Taking the representative $Z(N_p)\in C_p$ proves (10) and the emission formula.

For necessity suppose $r+D>k_p$. The two actual sources

$$
\xi=p0v,\qquad \xi'=p10v
\tag{11}
$$

belong to $C_p$, have exactly the same already emitted trace, and their itineraries first differ at $k_p\ge r$. If $L=0$, then $D=H$ and that difference is among the next $H$ emitted bits. If $L\ge1$, then $D=H+s_L$. Some integer $j\in[0,H]$ has

$$
j\le k_p-r<j+s_L.
$$

For example take $j=\min\{H,k_p-r\}$. The two length-$s_L$ future words beginning at $r+j$ differ. RRO20.6 then makes their current $q_L$ answers at that cut different. Thus (1) is not constant. This also covers an equality at the next branching index: length $D$ includes indices through $r+D-1$, so the sufficient inequality is non-strict exactly as written. For $D=0$ all responses are empty and $r\le k_p$ always holds. $\square$

**Theorem 4.2 (No fixed positive current-answer observation length).** For every fixed $r\ge0$ and every $L\ge1$, the length-$r$ past observation $v_r$ does not determine $q_L(T^r x)$ on all $K$. The same failure holds for the task of $H\ge1$ actual future emissions with $L=0$.

Proof. RRO35.1 supplies a unique $p$ with $M_p=r+2$, hence $k_p=r$ and $C_p$ a temporal atom at length $r$. Its endpoint pair (11) has the same past and different next bits. For positive $L$ the present $q_L$ contains that different lowest digit; for positive $H$ the future output contains it. Equivalently apply (9) with $D>0$ and slack zero. This is an obstruction for stopping at that one predetermined source time on every source. It is compatible with an adaptive protocol that stops different sources at different earlier returns and then pauses them. $\square$

## 5. Total attainment and the precisely scoped earliest stop

**Definition 5.1 (Acquisition protocol).** The observer reads the finite request $(L,H)$, computes $D$ by (2), and initially tests the return at zero. At every actual Return with its independently reconstructed $(p,r)$, it tests

$$
\operatorname{Ready}_{L,H}(p,r)\quad\Longleftrightarrow\quad k_p-r\ge D.
\tag{12}
$$

If false it invokes the next Next call on its live bound channel. If true it stops invoking Next, computes (10) for $j=0$, writes the current $L$-digit answer with its return counter and task parameters, and retains $(p,r,L,H)$ and the live binding. The stop is therefore selected from real chronological observations. No raw-source-based stop flag, target selector or precomputed semantic response is delivered to the observer.

**Theorem 5.2 (All-source finite attainment and paid acquisition bounds).** For every $x\in K$ and every finite $L,H\ge0$, Definition 5.1 stops at an actual return $r=r_x(L,H)$ and returns $q_L(T^r x)$. If $D=0$ it stops at zero and reads nothing. If $D>0$, put

$$
a=\min\{d\ge0:G_d\ge D+1\}.
\tag{13}
$$

Then, in the very same run,

$$
\begin{aligned}
r&\le G_{a+2}-1\le5D-1,\\
\#\operatorname{Read}=|p|&\le a+3,\\
\#\operatorname{Emit}=\#\operatorname{Advance}=\#\operatorname{Return}&=r.
\end{aligned}
\tag{14}
$$

There are at most two Reads in any one Next, and at most $a+3$ acquired blocks. No raw read is needed for any of the following $H$ advances or authorized spatial queries. The raw reads in (14) are actual paid bits, including every forced zero passed by the cursor.

Proof. Consider the block prefixes of the actual $x$, with lengths increasing by one or two. Let $q$ be the first prefix whose digit length $d$ is at least $a$. It exists and $a\le d\le a+1$. If the protocol has already stopped there is nothing to prove. Otherwise the unrestricted run reaches the split of $C_q$, at emission index $k_q$, and returns after that emission at

$$
r'=k_q+1=M_q-1.
$$

For either selected child $q'$, (5) gives

$$
k_{q'}-r'\in\{G_d-1,G_{d+1}-1\},
\tag{15}
$$

which is at least $G_a-1\ge D$. Thus the protocol stops no later than this particular actual return. Its time satisfies

$$
r'\le G_{d+1}-1\le G_{a+2}-1.
$$

The consumed child has length at most $d+2\le a+3$. Prefix lengths only increase, and Theorem 3.1 says each consumed bit was paid exactly once. This proves the raw bound, including if stopping occurred earlier. For $D>0$, $a\ge1$, $G_{a-1}\le D$, and $G_a\le2D$; for $a=1$ use $G_0=1,G_1=2$, and for $a\ge2$ use the recurrence and minimality. Consequently $G_{a+2}=2G_a+G_{a-1}\le5D$, proving (14).

At the stopping return, (12) gives $r+H\le k_p$ since $D\ge H$. The following $H$ Next calls all start at indices strictly below $k_p$, so none reaches the branch-read case. Theorem 4.1 supplies the current answer and every later authorized spatial answer; queries do not consume input. $\square$

**Theorem 5.3 (Earliest return in the temporal observation class).** Fix $L,H$ and the public event channel of Definition 1.2. Among deterministic protocols which see only this chronology from initialization, can pause only at its returns, and must give the correct data response (1) for every $x\in K$ on every trace where they stop, Definition 5.1 stops at the earliest possible return on each actual trace. This is a zero-error observation result. It asserts neither minimal bit work nor minimum raw reads among all source representations.

Proof. On the returned trace with prefix $(p,r)$, a source-blind protocol has exactly the same information for every source in $C_p$, by Theorem 3.1. If (12) fails, the two sources (11) give the same complete observed chronology and distinct required responses, by Theorem 4.1. A deterministic protocol must make the same stop decision and give the same response on that trace, and therefore cannot stop there correctly on all its compatible sources. If (12) holds, Definition 5.1 computes the response. It tests every return, proving the asserted earliest property.

Within the lifetime of one $C_p$, the slack $k_p-r$ decreases by one at each return. Thus a first successful positive-demand stop can occur only at the birth of a child immediately after a split; waiting inside a previously insufficient atom cannot help. This is a consequence of the criterion, not an additional assumption of the protocol. Private raw observations, an extra timing channel, probabilistic error, a different output alphabet, lookahead emission without its Advance, or a different task lie outside the comparison class. $\square$

## 6. Retained use, complete declared returns and continuation

**Definition 6.1 (Retained state and lawful bounded interface).** At the attained return retain the actual finite record

$$
\mathfrak m=(p,n,L,h;\kappa),\qquad n=r,\quad h=H,
\tag{16}
$$

where $\kappa$ is the already held live binding and continuing invocation right. Numeric caches and its actual canonical framing may also be retained; they are deterministic functions of the listed data. The receiver owns this record, the producer owns its matching finite state, and the sequential endpoint remains at $|p|$.

A bounded $\operatorname{Peek}(\ell)$, $0\le\ell\le L$, actually calculates and outputs $q_\ell(Z(N_p+n))$ without changing (16). A bounded $\operatorname{Tick}$ with $h>0$ invokes the real producer Next, consumes its event triple, updates the receiver's $n$ to $n+1$ and $h$ to $h-1$, and retains the resulting record. An encodable out-of-range depth or an exhausted bounded Tick gives a framed refusal with no source operation and no state change; the finite request syntax is specified in Definition 8.1. Thus legality depends on the explicit request and remaining budget, rather than on an inferred hidden state. Processing and writing refusals is paid too.

An explicit $\operatorname{Resume}$ leaves the bounded-task interface and re-enables unrestricted Next under the original continuing right. It does not reset $n$, reconstruct the old raw input, or change the raw endpoint. Another finite request may instead run Definition 5.1 from the present observer record, testing the present actual return before taking further Next calls. Total attainment remains true: if its current atom is insufficient, continue to any later actual block split whose parent depth meets its new (13); such a split exists and has finite index. This is finiteness from an arbitrary retained return, not a new uniform bound measured from a reinitialized source.

**Theorem 6.2 (Same-run acquired use and complete declared successors).** For every source and request in Theorem 5.2, every finite adaptive bounded command sequence of Definition 6.1, before exiting by Resume or a new request, stays lawful in its declared domain and gives precisely the data response of the actual successive points $T^n x$. After $j\le H$ accepted Ticks its full declared returned state is

$$
\begin{aligned}
\text{producer: }&(p,r+j,|p|,N_p,G_{|p|},G_{|p|+1},k_p;
\text{same raw binding and unread tail}),\\
\text{receiver: }&(p,r+j,L,H-j;\kappa),\\
\text{current source: }&T^{r+j}x.
\end{aligned}
\tag{17}
$$

Every source in the acquired cylinder gives the same finite registers, permissions and bounded output data here. The unread source itself is held by the service and need not be equal between compatible worlds. On Resume, the exact continuation of Theorem 3.2 applies to this actual state, with the same unread tail. The printed finite answer alone supplies neither that tail nor a replacement continuation right.

Proof. Maintain, after $j$ accepted Ticks,

$$
k_p-(r+j)\ge (H-j)+s_L\quad(L\ge1),
\qquad
k_p-(r+j)\ge H-j\quad(L=0).
\tag{18}
$$

It holds initially by (12). Peek is correct by Theorem 4.1 at the indicated current time, and preserves (18). An accepted Tick starts below $k_p$, since the remaining advance budget is positive, so it reads nothing. Theorem 3.1 gives its correct actual emission and current-source advance. Both sides of (18) decrease by one, giving the invariant at its genuine return. It also gives the unchanged $p$ and cursor in (17). Refusals preserve everything and print only the specified refusal. This induction applies to adaptive commands because each next action uses the already correct preceding data and the same explicit finite legality rule. The field descriptions include all declared finite returned caches, empty scratch and persistent bindings. Theorem 3.2 supplies unrestricted resumption; no equality of unread tails across different worlds is inferred. $\square$

**Theorem 6.3 (Current reconstruction is not entrance reconstruction).** At the successful return, the entrance prefix $p$ and the current answer (10) have different roles. Even when $L=1,H=0$ and the first raw block is $10$, the protocol stops at $r=1$ with $q_1(x)=1$ and $q_1(Tx)=0$.

Proof. The first returned cylinder is $C_{10}$, whose label is $M_{10}=4$ and $k_{10}=2$. Its slack at return one is one, so (12) holds for $D=1$. The finite representative has $N_{10}=1$, hence the returned spatial answer is the low digit of $Z(2)$, namely zero. The entrance prefix instead has low digit one. All points of that cylinder share this current answer by Theorem 4.1. $\square$

## 7. Four independently specified expressions on the common run

**Definition 7.1 (Spatial configuration, chronological time, phase boundary and memory).** At the acquisition return or during bounded use under one fixed public request $(L,H)$, use these meanings separately. The underlying producer run is a prefix of the unrestricted run. Task parameters and the position within the declared bounded interface are common context, not additional raw-source observations.

| View | Selected object |
| --- | --- |
| Space $\mathsf S$ | The current infinite positional configuration $T^r x$; the task readout is its finite $q_L$. It includes no history, origin cursor or right. |
| Time $\mathsf T$ | The actual ordered producer event triples from initialization through return $r$. It includes no raw responses, private fields, delays or future forecasts. |
| Boundary $\mathsf B$ | The oriented walls of $H[T^r U]$, with each endpoint's actually included current lift, where $U$ is the set of legal completions of the actual raw word physically consumed by the sequential service. It describes the phase region still allowed by that paid input frontier and the no11 promise, without selecting a temporal trace or reading a retained record. At return zero the region is the whole circle and has no walls. This is an acquisition-region boundary, not a material boundary of an infinite digit tape. |
| Memory $\mathsf M$ | The acquired finite receiver record (16), its actually retained caches and live binding/right. It excludes the unread tail and discarded event triples. |

Here, with $\phi=(1+\sqrt5)/2$, $\alpha=\phi^{-1}$ and $\lambda=-\alpha$, use the independent phase map from RRO20:

$$
F(x)=\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j,\quad H(x)=[F(x)],
\quad e_i=[-i\phi],\quad HT=RH,\quad R(\theta)=\theta+[\phi].
\tag{19}
$$

The meanings select positions, actual event order, geometric walls and retained callable information. None is defined as an inverse of another, and none is assigned a free copy of the entire run.

**Theorem 7.2 (Current boundary transport and the supplied recovery directions).** On each noninitial attained return with temporal atom $C_p$, the current compatible phase region is the proper closed arc

$$
\Gamma_{p,r}=R^r\left([S_p+\lambda^d(-\alpha),\ S_p+\lambda^d\alpha^2]\right),
\quad
S_p=\sum_{j<d}(-1)^{j+1}\alpha^{j+2}p_j,
\tag{20}
$$

where the interval's real endpoints are put in increasing order before projection. Its two walls and their included current lifts can be computed from the acquired events using finite integer labels. In particular $\mathsf T$ determines $\mathsf B$ and the acquired-prefix data $(p,r)$. With the fixed task/budget context of Definition 7.1 it determines the finite content of $\mathsf M$; together with the held initialization right, it supplies the actual retained state of Section 6. At a successful stop it determines the finite spatial response (1), with the exact condition (9). Memory supplies those same responses and the lawful continuation of Theorem 6.2. Task parameters or a newly issued capability are not inferred from producer event bits alone.

Proof. The actual paid-prefix part of Theorem 3.1 gives $U=C_p$; its temporal-fiber part separately proves that this same region is the region allowed by the chronological observations. RRO20.2 gives $H[C_p]$ as the projected interval in (20), of length $\alpha^d<1$. Equation (19) therefore proves (20) as an equality of actual images. To specify endpoint ownership rather than just phases, denote the entrance arc's left and right endpoint indices by $i,j$, with included lifts $x_i^+,x_j^-$ as in RRO24.2's cylinder formula. They are temporal cuts at return $r$, so $1\le i,j\le r+1$. Under $T^r$, their included current lifts are respectively

$$
\begin{cases}x_{i-r}^+,&i>r,\\ Z(r-i),&i\le r,\end{cases}
\qquad
\begin{cases}x_{j-r}^-,&j>r,\\ Z(r-j),&j\le r.\end{cases}
\tag{21}
$$

These are precisely RRO24.2's split-side transport and collapse formulas. Every interior current phase has its full fiber in $T^rC_p$: a split phase $e_m$ has its two preimages $x_{m+r}^{\pm}$ in the entrance interior, and every nonsplit phase has a lift in that interior. At a wall the entrance cylinder has exactly its stated one endpoint lift, giving exactly (21). Thus the boundary calculation has not silently included the wrong side of a split wall.

The indices themselves require no real-number oracle. At the first split the cylinders $0,10$ have walls $e_2,e_1$ and $e_1,e_2$, respectively. On subsequently splitting $p$, the new interior wall is $e_{M_p}$. Its two children inherit one old wall each. In real coordinates the $10$ child lies on the lower side for even $|p|$, and on the upper side for odd $|p|$; the $0$ child occupies the other side. This determines the ordered endpoint labels recursively by (3), prefix parity and two integer updates per branch. Translation and (21) then determine the current walls and ownership by finite arithmetic. Such optional wall-label output is charged in Section 8.

For memory contents under the fixed request, the first return satisfying (12) is identifiable in the observed trace. Call it $r_0$. During the bounded-use domain the remaining budget is exactly $H-(r-r_0)$, since every subsequent producer triple is one accepted Tick and queries change no record field. Thus the stated context does not conceal an unknown source-dependent budget. The other asserted directions are Theorem 3.1's event decoder and Theorems 4.1 and 6.2. Recovering the finite contents of a held record does not recreate its right on a different endpoint. $\square$

**Theorem 7.3 (Limits of the view conclusions).** No finite attained event trace, acquired finite memory content or boundary region above determines the entire current infinite spatial configuration over its compatible source fiber. Consequently the proved arrows do not establish arbitrary four-view inversion. The bounded spatial-response condition also cannot be substituted for whole-current-state recovery.

Proof. Every nonempty $C_p$ contains infinitely many finite padded sources $Z(A)$: extend $p$ by arbitrarily distant isolated ones, retaining its separating final zero. At any fixed $r$, their current points are the distinct $Z(A+r)$. They have the same acquired temporal trace and therefore the same finite memory contents and compatible-region boundary. Nevertheless their full spatial configurations differ. For the empty initial prefix the same argument applies. The actual endpoint right held in memory is additional initialized authority and is not an output of either geometric walls or spatial digits. No converse recovery of that authority is proved. $\square$

## 8. Operations, bits, storage, output and initialization

**Definition 8.1 (Resource model and complete accounting convention).** Use a fixed finite number of sequential binary work tapes for the producer and receiver, and paid bit input/output channels. Reading, writing or moving one tape cell costs one bit action. Standard binary comparison, addition, subtraction and copying of $w$-bit integers cost $O(w)$ bit actions with this fixed number of tapes. Scratch allocation, zeroing, copying, clearing and return positioning are charged. No unit-cost arbitrary integer, infinite real, unbounded-address operation or response-table primitive is present.

Let $P$ be the fixed program's installation length and $c$ the total actual bit length of the raw endpoint, continuation-channel and rights descriptors. They are copied and bound at initialization for $O(P+c)$ bit work and space, including their equality checks; each later invocation or client request may additionally pay $O(c)$ for descriptor use/checking. Rights persistence and correct endpoint supply are explicit interface premises, not theorems of authentication from mere bit equality. Let $\ell(t)=1+\lfloor\log_2(t+1)\rfloor$, a valid upper bound for ordinary binary payload length. A nonnegative integer field can be self-delimited as its binary-length unary header followed by its binary payload, costing at most $2\ell(t)+1$ bits. Counts and tags are fully framed. Each producer triple uses six bits under a fixed two-bit code for the four symbols $E_0,E_1,A,R$.

After the correctly framed initial $L,H$, a client command has a fixed tag and, for Peek, exactly $\ell(L)$ binary depth bits. This width encodes every legal depth and can also encode out-of-range depths, which receive the specified refusal. Integers not encodable in that width are outside this request syntax. Thus refusing an arbitrarily long malformed integer frame is not a hidden storage obligation of this interface.

Let $I$ be the actual finite request-input length, including the initial $L,H$, all later query depths and command tags. Let $Q$ be the number of query/refusal requests processed after acquisition, and let $h\le H$ be the number of accepted Ticks. Let $B_{\mathrm{out}}$ be the actual number of bits written to the chosen result channels, including the acquisition answer, frames, time-counter fields when requested, all later answers, event triples and refusals. Optional memory export serializes its actual $p$, counters and descriptors, and adds their complete framed length to $B_{\mathrm{out}}$; it cannot export or copy a live right merely by printing its name. Optional trace archival allocates and writes its full actual length. Optional explicit materialization of (1) writes all its bits and is a different output choice from retaining its callable finite record.

For an actual external implementation of the sequential endpoint, let $\iota_x$ denote its provisioning work, $\gamma_x(d)$ the backend work to generate/deliver the first $d$ requested raw bits, and $\sigma_x(d)$ its peak retained storage through that prefix. They include any already installed unknown source material and are not set to zero. The bounds below are relative to the sequential-input contract: add these actual external costs when claiming the cost of a whole jointly supplied system. No finite upper bound for those quantities on all $x\in K$, and no finite generator for an arbitrary infinite binary source, is asserted. If Read is itself the accounting primitive, its count and bit payload remain the separate exact coordinates in (14). Finiteness of reached services is the input promise, not a wall-clock deadline.

**Theorem 8.2 (One-run complete finite acquisition and use bounds).** For the actual acquisition and bounded-use phase of Theorems 5.2 and 6.2, ending before Resume or a new request, define $a$ by (13), also using $a=0$ when $D=0$, and put

$$
W=a+\ell(L)+\ell(H)+32.
\tag{22}
$$

The producer and observer can be implemented by the finite arithmetic and tapes just specified so that, for the same run,

$$
\begin{aligned}
T_{\mathrm{local}}&=O\left(P+c+I+(r+h+Q+1)(W^2+c)+B_{\mathrm{out}}\right),\\
V_{\mathrm{local,peak}}&=O(P+c+W),
\end{aligned}
\tag{23}
$$

when output is streamed and the event trace is discarded after processing. The actual initial program/binding setup and all parameter preparation are included. Raw-service coordinates are $d=|p|\le a+3$ Read operations, exactly $d$ raw delivered bits, with no additional Reads in bounded use; operation counts are (14), followed by exactly $h$ additional producer triples and $Q$ request responses. If full output or trace is required to remain locally retained, add its actual retained bit length to the storage in (23), and pay the writes/copies. Producer and receiver coexist in these bounds; separate storage peaks are not substituted for their simultaneous sum.

Whole-system work additionally includes $\iota_x+\gamma_x(d)$, and whole-system peak storage additionally includes $\sigma_x(d)$ and any external retained output. These are explicit parts of the cost model, not an unexplained free infinite source.

Proof. First suppose $D>0$. For $L\ge1$, $D+1=H+G_L$, so $a\ge L$; for $L=0$ no positive spatial digits are needed. Through bounded use, (14) gives

$$
n\le r+H\le6D-1,\qquad
d\le a+3,\qquad
N_p<G_{d-1}\le G_{a+2}\le5D
\tag{24}
$$

for nonempty $p$. The strict value bound for a complete block prefix is the finite-value range used in RRO35.1. Thus $N_p+n<11(D+1)\le11G_a$. Since $G_{a+6}\ge13G_a$ and $G_j\le2^{j+1}$, every necessary finite representative and every Fibonacci weight used to expand it has $O(a+1)$ bits and index at most $a+7$. Counters, endpoint labels, request parameters and cursor lengths fit in $O(W)$ bits. The same conclusion for candidate calculations (7) follows by applying the bound to either child of a reached branch; their lengths are at most $a+3$ on the bounded run and their evaluation time is the actual pre-advance index. Fixed small extra weights are harmless within (22).

Computing $G_L,D$ and the first threshold $a$ uses $O(L+a+1)$ successive additions on $O(W)$-bit integers, hence $O(W^2)$ bit work and $O(W)$ workspace. A greedy finite representative uses $O(W)$ weight steps, with a constant number of $O(W)$-bit scans per step, and therefore $O(W^2)$ bit work. Consecutive weights can be generated and then recovered backwards with two registers, so a whole Fibonacci table is not stored. The low-to-high output is formed by writing the finite $O(W)$-digit word to scratch and scanning it backwards, then padding the requested zeros. This costs $O(W+\ell)$ additional work for depth $\ell\le L\le W$, with all scratch clearing charged.

There is one such computation per producer emission, at most two per observer branch decision, and at most one per Peek/current answer. There are at most $d\le a+3$ observer branch decisions and at most $r$ of them, each followed by a real triple. Event processing, cache updates, Ready tests, bounded counter updates, boundary-label updates if requested, descriptor checks and scratch clearing add $O(W+c)$ per relevant event/request or per consumed digit. They fit (23), together with initialization, actual request reads and actual output writes. An invalid encodable depth request uses its complete fixed-width input scan, descriptor/range test and framed refusal; its width is at most $W$.

The two copies of $p$, the producer and receiver counters/caches, constant-count arithmetic work registers, output staging buffer, endpoint descriptors and both control states occupy $O(P+c+W)$ simultaneous bits. Scratch is reused, cleared and charged; neither the temporal word nor a full table of future responses is retained. Optional full trace archival through acquisition has exactly $6r$ event bits before its own file framing; retaining it therefore adds that actual length. A literal maximal profile (1) has $H+(H+1)L$ data bits before its framing, whose writing/retention must be added when requested. Its computation by the stated representative method takes an additional $O((H+1)W^2)$ work; it is not included as free output in a callable-record request. Export of (16) has $O(d+W+c)$ framed bits and the same linear copy work. For $D=0$, $L=H=0$, $r=d=0$, and only finite parameter/binding/current-empty-answer work remains. This also satisfies (23). $\square$

The local bounds are constructive upper bounds. The two actual endpoint sources in Theorem 4.1 prove the observation obstruction, not a universal bit, storage or input-read optimum. In particular this runtime deliberately pays for the zero following a read one so that its actual sequential cursor is at a complete block boundary. No claim says that paying that forced bit is information-theoretically necessary under every different sequential representation. Under arbitrary unbounded resumption, prefix lengths and time counters can grow without bound; a fixed program does not imply bounded retained memory.

## 9. Prior ownership and remaining mathematical boundaries

**Definition 9.1 (Source comparison and status of the synthesis).** The clock-driven acquisition/current-use package is `repo-derived`: its ordinary proofs are Theorems 3.1–8.2. Its contribution is the conjunction of real sequential acquisition, source-blind chronological decoding, exact current-response slack, all-source adaptive attainment, zero-error earliest return in the stated channel, and read-free bounded current use with exact raw-tail resumption and finite-bit accounting. It is not a new discovery of Fibonacci cylinder geometry or Sturmian coding, and no worldwide originality claim is made.

| Prior source | Supplied content and the transfer boundary |
| --- | --- |
| [RRO20.1–20.7, RRO24.2][RRO] | All-$K$ endpoint-inclusive $T$, phase and split-side geometry, exact temporal/spatial partitions, translated precision and finite representatives. The arithmetic evaluation here reuses them. A fixed entrance-prefix modulus alone does not select an attained current-return cut or execute this sequential service. |
| [RRO35.1–35.2][RRO] | Complete block-cylinder lifetimes $[b_p,k_p]$, labels, child recurrences, exact next-split witnesses and forced temporal gaps. These are essential published suppliers. Neither these clocks nor the endpoint pair (11) is counted as new mathematics. The paid runtime and stopping/use theorem establish the operational conjunction built from them. |
| [NativeAcquiredPrefixCylinder][NAPC] and [owning Scribe][NAPCB]; [State][NAPS], [Reconstruction][NAPR] and their owning Scribes | Actual native raw-stream scheduling, exact paid-prefix fibers, full native returned state, legal operations and exact unread-tail restart already exist. Private scheduling/append/tail helpers are part of that existing supply. Its arbitrary binary raw domain and seed/payload/Stop controller are distinct from the present no11 origin and Zeckendorf-successor Advance. No original native operation or theorem is claimed missing, or identified with the new controller. |
| [Infinite successor continuity][CONT] and its [Scribe][CONTB] | Formalized finite-prefix continuity for the exact first-$00$ successor, including its zero result when no pair exists. Reading the declaration is not a new compile or certification of this theorem package. |
| [OA §§12–17][OA] | Actual unknown-source acquisition, receiver association, retained lawful use and attained-return four-view recovery under $\iota$ are positive supply. Its ordered-tree updates, sites and rights differ from a chronological lowest-digit successor channel. No arbitrary-interior or original-$Q$ inverse is inferred here. |
| [AIF4.4][AIF], [CSA6.3–6.4, 7.3, 8.3][CSA], [PVC4.4, 5.7, 6.5, 7.1–7.3][PVC] | Actual consumed-input replay, separate whole-storage four-view kernels, installed acquired calls, paid conversion, return and later use already exist with their complete control, binding, installation and enlarged-task premises. Those positive services are neither absent nor automatically an implementation of this $T$. |
| [Zeckendorf archive §§496, 502][Z] | Retained finite archive queries, continuing availability and complete literal-output/read/storage costs already have constructive positive theorems on their finite archive domain. Here the unknown input is an infinite positional source and only the paid acquired raw prefix is installed in local finite memory. No generic archival capability is claimed new. |
| Berstel, [*Sturmian and Episturmian Words*, §3.1, pp. 30–31][BERSTEL] | `literature-attested`: lower/upper mechanical conventions and rotation coding; not a raw-source acquisition or current-return implementation theorem. |
| Bellissard–Julien, [*Bi-Lipshitz Embedding of Ultrametric Cantor Sets into Euclidean Spaces*, §2.1, pp. 4–5][BJ] | `literature-attested`: reducing nonbranching vertices of a weighted rooted tree preserves its boundary. The arithmetic clock labels and split witnesses used here belong to RRO35.1, rather than to this general construction. |
| Pinned mathlib [finite Zeckendorf module][MATHLIB] | `literature-attested`: finite canonical representation, greedy greatest-Fibonacci construction and uniqueness. It is reused inside an ordinary finite-bit calculation, not cited as an acquired infinite-source service. |
| [Fibonacci atomic generation, Definitions 2.1–2.2][FIB] | Two atom symbols come with ordered binary construction and a chosen interpretation. The two raw blocks here additionally need order, a sequential service, clocks, finite arithmetic/control and persistent rights. No reduction of all relations to two uninterpreted symbols or universal minimality is asserted. |

The repository's itinerary stabilization and inverse-limit completion theorems have different hypotheses and conclusions: abstract consistency/separation does not by itself supply this sequential controller. The cited primary literature supplies the precise classical ingredients in the table; it is not used as evidence for a general acquisition impossibility.

**Definition 9.2 (Remaining obligations).** The following claims are outside the proved package. The boundary view is a geometric uncertainty boundary on the same source run, not an arbitrary material boundary; no independent boundary-to-memory or boundary-to-full-space converter is installed. No finite memory or temporal trace reconstructs every unread digit. Finite requested $L,H$ are essential; a uniform infinite-horizon response has not been acquired. Source provisioning outside the paid sequential contract has no uniform finite cost theorem. Revocation, concurrent clients, source mutation outside Advance, extra timing observations and arbitrary interior-cut inversion require different hypotheses and proofs. No implementation in the old native controller, unchanged original-$Q$ service, eager infinite-tape rewrite or physical-world realization follows. All earlier fixed-model, fixed-initialization and parked-consumer statements retain their own exact domains. This is one bridge from actual temporal acquisition to finite current spatial use; the full four-expression programme remains open.

[RRO]: RECURSIVE_RELATIONAL_OBSERVATION.md
[Z]: CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md
[OA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ONLINE_ACQUISITION_ACTUATION.md
[AIF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_INPUT_FRONTIER_AND_REPLAY.md
[CSA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md
[PVC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md
[FIB]: FIBONACCI_ATOMIC_RELATION_GENERATION.md
[NAPC]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.lean
[NAPCB]: ../../../Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.scribe.cs
[NAPS]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.lean
[NAPR]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.lean
[CONT]: ../../../D5/S1/Digit/Infinite/SuccessorContinuity.lean
[CONTB]: ../../../Blueprint/D5/S1/Digit/Infinite/SuccessorContinuity.scribe.cs
[BERSTEL]: https://ligm.univ-eiffel.fr/~berstel/Articles/2007SturmianThessalonique.pdf
[BJ]: https://arxiv.org/pdf/1202.4330v2
[MATHLIB]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/Nat/Fib/Zeckendorf.lean

## 追加锚（本行以下为增补区）

## 10. Converse classification of an attained current boundary

The boundary in Section 7 is a current object. It records the oriented phase arc allowed by the paid prefix and the lift owned at each of its two walls. This section asks exactly what that object determines when the producer has already returned. It does not replace the producer record, the unread endpoint, or the continuing right.

**Definition 10.1 (Attained cuts, boundary records and their current fibres).** Let

$$
\mathcal A=\{(p,r):p\in\mathcal B,\ b_p\le r\le k_p\}.
\tag{25}
$$

The empty word contributes the single pair $(\varnothing,0)$. Every $(p,r)\in\mathcal A$ is attained by every source in $C_p$ at return $r$ of the unrestricted run in Theorem 3.1. Write

$$
U_{p,r}=T^r(C_p).
\tag{26}
$$

For $(p,r)\in\mathcal A$, let $\partial_{p,r}$ be the oriented closed arc $H[U_{p,r}]$ together with the included current lift at each wall, as transported by (21). The interior of an arc includes every lift over an interior split phase; at a wall only its recorded included lift is retained. If $\partial$ is any such boundary record, define $U(\partial)$ by this same rule. Thus

$$
U(\partial_{p,r})=U_{p,r}.
\tag{27}
$$

This is a definition from the current boundary itself. It does not mention a historical prefix, an elapsed counter, a producer register, or a capability.

For a finite $t$, put

$$
\delta(\partial)=\max\{t\ge0:\ v_t\text{ is constant on }U(\partial)\}.
\tag{28}
$$

The maximum is taken only for an attained boundary record. The empty boundary has $U=K$ and $\delta=0$.

**Theorem 10.2 (Exact current-wall invariant and loss of provenance).** For every $(p,r)\in\mathcal A$,

$$
\delta(\partial_{p,r})=k_p-r.
\tag{29}
$$

Consequently the boundary preserves the exact number of future lowest-digit events that are uniform over its current compatible fibre. It does not, in general, preserve the pair $(p,r)$ that produced that fibre.

**Proof.** Theorem 35.1 gives that all points of $C_p$ have the same itinerary below coordinate $k_p$ and that the two children $C_{p0}$ and $C_{p10}$ contain points whose first difference is exactly $k_p$. The conjugacy $\Phi T=S\Phi$ shifts this statement by $r$. Hence all points of $U_{p,r}$ agree below coordinate $k_p-r$, while the images of the two displayed split witnesses differ at that coordinate. This proves (29), including the case $r=k_p$. Equation (27) transfers the assertion from the producer notation to the independently defined boundary record. The second assertion follows from the explicit collision below. $\square$

**Definition 10.3 (Boundary provenance fibre).** For an attained boundary record $\partial$, define

$$
\operatorname{Prov}(\partial)=\{(p,r)\in\mathcal A:\partial_{p,r}=\partial\}.
\tag{30}
$$

This is a historical fibre of the boundary map, not a fibre of the current source map. If $\partial$ is proper, let $d(\partial)$ be the unique integer satisfying

$$
\operatorname{length}(H[U(\partial)])=\alpha^{d(\partial)}.
\tag{31}
$$

For the empty boundary set $d(\partial)=0$.

**Theorem 10.4 (Finite and exact classification of the attained provenance fibre).** If $\partial$ is an attained proper boundary, then

$$
\operatorname{Prov}(\partial)=
\left\{(p,r)\in\mathcal A:
\begin{array}{l}
|p|=d(\partial),\\
R^rH[C_p]=H[U(\partial)],\\
\text{the endpoint lifts transported by (21) equal those of }\partial
\end{array}\right\}.
\tag{32}
$$

In particular, $\operatorname{Prov}(\partial)$ is finite and

$$
|\operatorname{Prov}(\partial)|\le G_{d(\partial)-1}\qquad(d(\partial)\ge1).
\tag{33}
$$

For $\partial=\partial_{\varnothing,0}$ the provenance fibre is the singleton $\{(\varnothing,0)\}$.

**Proof.** By Theorem 35.1 the phase length of a nonempty block cylinder $C_p$ is $\alpha^{|p|}$, and rotation does not change length. Since $0<\alpha<1$, equality of lengths forces $|p|=d(\partial)$. At a fixed $p$, two distinct values $r\ne r'$ cannot give the same proper oriented arc: otherwise the proper arc would be invariant under the nonzero rotation $R^{r-r'}$. An irrational rotation has no invariant proper finite-endpoint arc, because every endpoint orbit is infinite. There are exactly $G_{d-1}$ block words of digit length $d\ge1$, by the finite Zeckendorf count in Theorem 20.2. This proves (32) and (33); the empty case is immediate from $k_{\varnothing}=0$. $\square$

The bound is genuinely nontrivial. At depth two, the two actual cuts

$$
(p,r)=(00,2),\qquad (p',r')=(10,1)
\tag{34}
$$

have the same boundary record. Indeed, $H[C_{00}]$ is the oriented arc from $e_2$ to $e_3$, while $H[C_{10}]$ is the oriented arc from $e_1$ to $e_2$. Since $R e_m=e_{m-1}$ for $m\ge2$, both current arcs are the oriented arc from $0$ to $e_1$. Their endpoint ownership is also equal: for $C_{00}$, (21) sends the included lifts $x_2^+$ and $x_3^-$ under $T^2$ to $Z(0)$ and $x_1^-$; for $C_{10}$ it sends $x_1^+$ and $x_2^-$ under $T$ to the same two current lifts. Both pairs are attained, since

$$
b_{00}=2,\qquad b_{10}=1,\qquad k_{00}=3,\qquad k_{10}=2.
$$

Their common boundary has $\delta=1$ by (29), but its two historical descriptions have different acquired raw prefixes and different actual operation counts. Thus the loss is finite provenance ambiguity, not a whole-current-source ambiguity and not a claim that a missing API makes recovery impossible.

**Definition 10.5 (Boundary-only finite DATA).** For finite $L,H$, define the current/continuation DATA of a current point $y$ by

$$
\operatorname{DATA}_{L,H}(y)=
\left(v_H(y),\ (q_L(T^j y))_{0\le j\le H}\right).
\tag{35}
$$

This deliberately contains no absolute source-time counter, acquired prefix, private register, unread endpoint, binding, or right. A boundary record is said to admit DATA$(L,H)$ when this value is constant on $U(\partial)$.

**Theorem 10.6 (Exact quantified boundary-only response domain).** For every attained boundary $\partial$, every $L,H\ge0$, and

$$
D(L,H)=
\begin{cases}
H,&L=0,\\
H+G_L-1,&L\ge1,
\end{cases}
\tag{36}
$$

the following are equivalent:

$$
\begin{aligned}
&\operatorname{DATA}_{L,H}\text{ is constant on }U(\partial),\\
&\partial\text{ alone determines one finite DATA value for every actual cut realizing it},\\
&D(L,H)\le\delta(\partial).
\end{aligned}
\tag{37}
$$

When (37) holds, write the common value as $\operatorname{DATA}_{L,H}(\partial)$. This is a boundary-only finite current/continuation response; it is not the complete task response of Section 6, because it omits absolute counters, returned registers, the unread source and authority.

**Proof.** Choose any $(p,r)\in\operatorname{Prov}(\partial)$. By (29), $U(\partial)$ is a current fibre with uniform itinerary length $\delta(\partial)=k_p-r$. If $D\le\delta$, the first $D$ future lowest-digit outputs agree on that fibre. Theorem 20.6 identifies a length-$G_L-1$ lowest-digit word with the current $L$-digit prefix, and the intervals beginning at times $0,\ldots,H$ cover exactly the first $D$ coordinates. Thus every component of (35) is constant, including the case $L=0$.

Conversely, if $D>\delta$, the two child witnesses inside $U(\partial)$ supplied in the proof of Theorem 10.2 first differ at coordinate $\delta$. When $L=0$, that difference lies among the next $H$ outputs. When $L\ge1$, the length-$G_L-1$ window beginning at some $j\le H$ contains coordinate $\delta$; Theorem 20.6 then gives different $q_L(T^j y)$ values. Hence DATA is not constant. Equality of DATA for all actual realizations of a boundary is exactly constancy on the common set $U(\partial)$, proving all three equivalences. $\square$

**Corollary 10.7 (Finite boundary decoding, conditional on boundary possession).** On the domain $D(L,H)\le\delta(\partial)$, the value $\operatorname{DATA}_{L,H}(\partial)$ can be selected from finitely many current temporal atoms. If $D=0$ it is the empty response. If $D\ge1$, enumerate the $D+1$ arcs cut by $e_1,\ldots,e_{D+1}$, use the oriented boundary and its endpoint ownership to select the unique atom met by $U(\partial)$, and apply the finite relabeling of Theorem 20.6 to obtain the $q_L$ entries. All labels and the finite table are generated by the integer recurrences of Sections 2 and 7; no exact-real source or whole-response oracle is used.

This corollary is a conditional decoder for an already possessed finite boundary record. It does not install a boundary exporter, acquire a wall, create a selector, or supply a continuation right. Any such service requires its own actual endpoint, initialization, binding and output contract, with its work and storage added to the costs of Section 8.

**Theorem 10.8 (An independently possessed operation counter repairs the finite historical loss).** Suppose an actual boundary record $\partial_{p,r}$ is accompanied by an independently retained counter $c$ whose interface contract authenticates that it is the number of completed producer Advances from the same initialization and run. Then $c=r$, and the pair $(\partial_{p,r},c)$ determines the unique provenance pair $(p,r)$. It also determines the finite event word $v_r(x)$ and the deterministic finite producer fields of Definition 2.2 under the fixed task context. It does not determine the unread tail, the live endpoint binding, or the continuing right.

**Proof.** The counter gives $r=c$. Translate the current oriented arc backwards by $R^{-c}$. Its length gives the unique digit length $d$ in (31). The depth-$d$ cylinder phase intervals have disjoint interiors and the endpoint ownership formula of Theorem 20.2 assigns each boundary to one and only one block word $p$. Hence $p$ is unique, and $(p,c)$ is the only possible element of $\operatorname{Prov}(\partial)$ with that counter. Theorem 3.1 then reconstructs the paid raw word, the finite event word through return $c$, and all deterministic finite registers from $p$ and $c$; Theorem 6.2 gives the same conclusion for the declared fixed bounded interface.

The counter is an already held fact about the same producer, not a number inferred from a phase wall. It therefore adds historical provenance but no raw datum. The unread endpoint and its binding/right are excluded from the reconstructed finite words by Definition 7.1 and remain independently held capabilities. A freely supplied or unauthenticated integer would not satisfy the theorem's premise. $\square$

The collision (34) shows why the counter condition is substantive: boundary alone cannot choose between counts one and two, while boundary plus the actual counter does. The theorem is a repair of finite historical loss only. It neither reconstructs the entire infinite current configuration nor changes the original complete task, whose absolute counters, returned registers, unread endpoint and authority remain separate obligations.

## 11. Scope, suppliers and remaining boundary

The new content is the converse package (25)–(37): the exact current uniformity depth $\delta$, the finite provenance classification and collision, the quantified boundary-only DATA factor, and the counter-assisted recovery of $(p,r)$ under an authenticated same-run operation interface. The forward construction, current wall transport, finite response guard, bounded use and tail resumption are reused from Sections 3–7. RRO20.2, RRO20.6, RRO24.2 and RRO35.1 supply the phase intervals, endpoint ownership, temporal/positional equivalence and branching clocks. Boundary Dynamics 36.1–36.4 supplies the distinction between a current-image kernel and a full dynamic or authority-preserving recovery. NativeAcquiredPrefixCylinder supplies a positive exact-tail analogue under its own controller; PVC supplies a positive B-to-M/T service under its different native history and installation contract. Neither supplier is silently identified with this current-wall boundary.

The boundary-only decoder is mathematical and conditional on possession of the finite boundary record. No native acquisition, exporter installation, receiver authority, free counter, full current reconstruction, complete register recovery without the fixed task context, or whole-source response oracle is claimed. The remaining gap is an independently installed current-boundary acquisition/conversion service, and the full four-expression programme still requires its original source, continuation and authority clauses.

## 追加锚（本行以下为增补区）

## 12. Exact coordinates and equicardinal historical fibres

**Definition 12.1 (Signed wall labels).** Extend the phase notation to every integer by $e_m=[-m\phi]$. This extension does not give a two-point fibre to a nonpositive label: $H^{-1}(e_m)=\{Z(-m)\}$ for $m\le0$. For $m\le1$ define the two wall-ownership conventions

$$
\chi_+(m)=\begin{cases}x_1^+,&m=1,\\ Z(-m),&m\le0,\end{cases}
\qquad
\chi_-(m)=\begin{cases}x_1^-,&m=1,\\ Z(-m),&m\le0.\end{cases}
\tag{38}
$$

For $d\ge1$ put

$$
(A_d,B_d)=
\begin{cases}
(G_{d-1},G_d),&d\text{ even},\\
(G_d,G_{d-1}),&d\text{ odd},
\end{cases}
\qquad
J_d=\{G_d-1,\ldots,G_{d+1}-2\}.
\tag{39}
$$

All arcs below have the positive orientation induced by increasing real phase. Their initial and terminal walls are ordered by this orientation, not by the numerical order of representatives in $[0,1)$. The boundary meaning remains Definition 7.1: the actual paid-frontier compatible region, with its included current lifts.

**Theorem 12.2 (Closed classification and exact historical cardinality).** Every proper attained boundary has unique coordinates $(d,s)$ with $d\ge1$ and $s\in J_d$. Its oriented arc has length $\alpha^d$, initial wall $e_{A_d-s}$ and terminal wall $e_{B_d-s}$, and includes exactly the lifts

$$
\chi_+(A_d-s),\qquad \chi_-(B_d-s)
\tag{40}
$$

at those respective walls. Denote this record by $\partial(d,s)$. For every $(p,r)\in\mathcal A$ with $p\ne\varnothing$ its coordinates are

$$
d=|p|,\qquad s=N_p+r.
\tag{41}
$$

For $0\le N<G_{d-1}$ let $p_d(N)$ be the $d$-digit, zero-padded Zeckendorf word of $N$. It is a complete block word. The entire historical fibre, without additional exclusions, is

$$
\operatorname{Prov}(\partial(d,s))
=\{(p_d(N),s-N):0\le N<G_{d-1}\}.
\tag{42}
$$

In particular, every boundary of depth $d$ has exactly $G_{d-1}$ historical descriptions, and their return counts are precisely the consecutive integers

$$
s-G_{d-1}+1,\ldots,s.
\tag{43}
$$

There are exactly $G_{d-1}$ distinct attained boundaries at that depth. The boundary preserves $d$, the sum $N_p+r$, and

$$
\delta(\partial(d,s))=G_{d+1}-2-s\in\{0,\ldots,G_{d-1}-1\}.
\tag{44}
$$

It forgets the individual $N_p$ and $r$ whenever $d\ge2$. The empty boundary still has the singleton provenance fibre of Theorem 10.4.

Proof. The finite value bijection in RRO20.2 and RRO35.1 gives exactly the words $p_d(N)$ for $0\le N<G_{d-1}$: these are the legal words of length $d$ ending in zero. Their birth times have the additional identity

$$
b_p+N_p=G_d-1.
\tag{45}
$$

Indeed, if $p=q0$, then $N_p=N_q$ and $b_p=M_q-1=G_d-N_q-1$. This also covers $d=1$, $q=\varnothing$. If $p=q10$, then $d\ge2$, $N_p=N_q+G_{d-2}$ and $b_p=G_{d-1}-N_q-1$; use $G_d=G_{d-1}+G_{d-2}$. The definition of $k_p$ gives $k_p+N_p=G_{d+1}-2$. Thus the attained inequalities $b_p\le r\le k_p$ are exactly $s\in J_d$, independently of $N_p$.

To obtain the walls, $Z(N_p)=p0^\infty$ and $HZ(N_p)=[N_p\phi]$ give $[S_p]=[N_p\phi]$. The Fibonacci identities

$$
(-\alpha)^{d+1}\equiv-G_{d-1}\phi\pmod1,
\qquad
(-\alpha)^{d+2}\equiv-G_d\phi\pmod1
\tag{46}
$$

follow from $F_n\phi=F_{n+1}-(-\alpha)^n$, $G_j=F_{j+2}$; this identity follows by the Fibonacci recurrence and its first two values. The two real endpoints in (20), in increasing order, therefore have entrance indices $A_d-N_p,B_d-N_p$. Rotation by $r\phi$ subtracts $r$ from both indices, giving the walls in (40). The positive arc has length $\alpha^d$ by (20), including when its representatives cross zero.

Because $s\ge G_d-1$ and $A_d,B_d\le G_d$, both current indices are at most one. Formula (21) gives exactly (38) and (40). All interior phase fibres are still included by Theorem 7.2. Thus ownership is a consequence of attainment and the wall roles; it is not an extra historical bit. The singleton assertion at $m\le0$ follows from the split-phase classification of RRO20.2: $e_m=H(Z(-m))$ is not $e_i$ for any $i\ge1$, by irrationality of $\phi$.

Conversely, choose any $s\in J_d$ and any $N$ in the displayed finite range. Identity (45) and the upper lifetime identity show that $(p_d(N),s-N)$ is attained. Its return count is nonnegative: $G_d-1\ge G_{d-1}-1\ge N$. Theorem 3.1 realizes it on every source in its nonempty cylinder. Its boundary is exactly (40), independently of $N$. This proves existence of every specified record, not merely consistency of wall labels.

Equality of two records forces equality of $d$ by their positive lengths. At fixed $d$, equality of their initial walls gives $[(s-s')\phi]=0$, hence $s=s'$. Equation (41) and the finite value bijection now prove (42), its exact cardinality and (43). The interval $J_d$ has $G_{d+1}-G_d=G_{d-1}$ elements, giving the boundary count. Equation (29) gives (44). At $d=1$, $J_1=\{1\}$ and the sole history is $(0,1)$; both the birth and last lifetime return are included. At $d=2$, $s=2,3$ each has both histories $N=0,1$, including collision (34). For every larger $d$, (45) uses non-strict inequalities at both ends, so no lifetime endpoint is removed. $\square$

**Theorem 12.3 (Transport of the intrinsic coordinates).** If $s<G_{d+1}-2$, one actual Next from any cut represented by $\partial(d,s)$ reads no raw bit and has current compatible boundary

$$
\partial(d,s+1).
\tag{47}
$$

Its emitted bit is $\operatorname{Low}(s)$, and its endpoint ownership follows $\chi_\pm(m)\mapsto\chi_\pm(m-1)$. At $s=G_{d+1}-2$, the next paid block selects exactly one of

$$
\partial(d+1,G_{d+1}-1),\qquad
\partial(d+2,G_{d+2}-1),
\tag{48}
$$

for blocks $0$ and $10$ respectively. Boundary alone cannot select that block or its next emitted bit. These assertions hold for every member of the historical fibre (42), with its actual unread tail and authority retained separately.

Proof. In the first case $r<k_p$ by (44). Definition 2.2 leaves $p$ fixed and increments $r$, hence $s$ increments by one. The common finite representative is $Z(N_p+r)=Z(s)$, giving the emission. Rotation subtracts one from each wall index; (21) gives $x_1^\pm\mapsto Z(0)$ and $Z(a)\mapsto Z(a+1)$, proving the ownership statement even at collapse. At the last return $r=k_p$, the runtime reads its next complete block. For $p0$, the new $N$ is $N_p$; for $p10$ it is $N_p+G_d$. Inserting $r+1$ gives respectively $s+1=G_{d+1}-1$ and $s+G_d+1=G_{d+2}-1$. These are the births at the new depths by (45). The two actual child witnesses of Theorem 10.2 give different next emissions at this cut. Thus (48) is a pair of genuine source-selected possibilities, not a deterministic boundary-only action beyond the uniform horizon. Theorem 3.2 continues each actual tail; nothing here replaces one history in (42) by another during execution. $\square$

## 13. Finite acquisition from approximate ordered wall phases

**Definition 13.1 (Calibrated paired-wall replies).** The reference is the circle $\mathbb R/\mathbb Z$ with the exact origin $[0]=HZ(0)$, positive orientation, unit circumference, and the fixed known constant $\phi$. The constant has the finite algebraic specification $\phi^2=\phi+1$, $\phi>1$; its infinite expansion is not stored or supplied as a real-number oracle. This is a declared reference of the digital coordinate model, not an unknown physical calibration to be inferred from replies. Write

$$
\operatorname{dist}_{\mathbb T}([a],[b])=\min_{k\in\mathbb Z}|a-b-k|.
\tag{49}
$$

An acquisition target is one fixed, paused proper attained boundary. Let its ordered phases be $\theta_-,\theta_+$. For a requested integer precision $n\ge1$, a valid reply is the pair of $n$-bit integers $(a_n,b_n)$, $0\le a_n,b_n<2^n$, such that, with $\varepsilon_n=2^{-n}$,

$$
\operatorname{dist}_{\mathbb T}([a_n2^{-n}],\theta_-)\le\varepsilon_n,
\qquad
\operatorname{dist}_{\mathbb T}([b_n2^{-n}],\theta_+)\le\varepsilon_n.
\tag{50}
$$

Both inequalities refer jointly to the same target and reference throughout the call. No independence, unbiasedness, nesting or preferred rounding is required. The two wall roles are distinguished by the reply positions; their numerical order may be reversed. No winding number, real interval lift, historical prefix, absolute operation counter, exact integer wall label, depth or depth bound is supplied. The attained-class promise is substantive: these replies do not certify that promise for an arbitrary source.

**Definition 13.2 (Finite candidate selection).** Request precisions $n=1,2,\ldots$. At stage $n$, compute the rational number

$$
\ell_n=\operatorname{dist}_{\mathbb T}([a_n2^{-n}],[b_n2^{-n}])-2\varepsilon_n.
\tag{51}
$$

If $\ell_n\le0$, request the next precision. Otherwise enumerate $1\le j\le2n$ and $t\in J_j$. Retain a candidate $(j,t)$ exactly when its two ordered phases in (40) both satisfy (50) for the received pair. Count retained candidates up to two, keeping one candidate in workspace. Accept only when exactly one candidate remains after this finite enumeration; return its exact record (40). In every other case request the next precision. The rule uses the single current reply; it need not archive earlier replies.

All these comparisons are exact finite arithmetic. For example represent $\alpha=\phi-1$ and each candidate phase by the fractional part of an element of $\mathbb Z[\phi]$. Circular comparisons reduce to the three possible integer shifts $-1,0,1$ of a difference of representatives in $[0,1)$. After clearing the dyadic denominator, signs reduce to signs of integers plus integers times $\sqrt5$; signs and equality are decided by integer signs and a comparison of squares. Integer parts are found by bounded integer binary search. In particular the exact-zero wall and a reply on the boundary of its error ball cause no undecidable real equality test.

**Theorem 13.3 (All-reply exact acquisition without a supplied depth).** For every proper attained target $\partial(d,s)$ and every sequence of valid replies (50), Definition 13.2 terminates and returns precisely that boundary, including its endpoint ownership. If $N$ is the accepted precision, then

$$
1\le N\le d+5.
\tag{52}
$$

No distinct proper attained boundary is compatible with the accepted reply pair. The acquisition determines the whole finite provenance set (42); it does not select its actual historical member.

On a fixed finite number of binary work tapes, excluding the service that supplies the replies, the receiver can perform this acquisition with

$$
\begin{aligned}
\text{bit work}&=O\bigl(P+4^N(N+c+1)^4\bigr),\\
\text{simultaneous stored bits}&=O(P+c+N),\\
\text{request/reply traffic}&=O\bigl(c+N(c+N+1)\bigr).
\end{aligned}
\tag{53}
$$

Here $P$ counts the fixed installed program and conventions and $c$ bounds endpoint/lease descriptor widths. Precision requests are self-delimiting binary integers; a reply has exactly $2n$ coordinate bits plus framing. An exact result represented by $(d,s)$, its two signed labels and the finite descriptions in (38) fits $O(c+d+1)$ bits and is included in the storage/work bounds. Explicit listing of every historical member, DATA output or archival of replies is additional output, not included in (53). No optimality is asserted.

Proof. First the finite search excludes no compatible attained boundary. For any candidate depth $j$ compatible with a reply, the triangle inequality gives

$$
\alpha^j\ \ge\
\operatorname{dist}_{\mathbb T}(\theta_-^{\rm candidate},\theta_+^{\rm candidate})
\ \ge\ \ell_n.
\tag{54}
$$

If $\ell_n>0$, it is a multiple of $2^{-n}$ and hence is at least $2^{-n}$. Since $\alpha^2<1/2$, $\alpha^{2n}<2^{-n}$. Thus (54) forces $j<2n$. In particular the true boundary is in the finite search whenever the search is attempted. An accepted singleton consequently is the true record and excludes every other attained record, including candidates of unbounded depth. This is a global exclusion over the stated class, rather than uniqueness inside an arbitrarily truncated list.

It remains to prove a uniform stopping bound over all valid replies. Put $n=d+5$ and $\varepsilon=2^{-n}$. The true two-wall circular distance is

$$
g_d=\min\{\alpha^d,1-\alpha^d\}
=\begin{cases}\alpha^2,&d=1,\\ \alpha^d,&d\ge2.\end{cases}
$$

Because $\alpha>1/2$,

$$
4\varepsilon=2^{-d-3}<\alpha^{d+2}\le g_d.
\tag{55}
$$

The received wall distance is at least $g_d-2\varepsilon$, so $\ell_n\ge g_d-4\varepsilon>0$. Now let $(j,t)$ be any compatible candidate. Each of its wall phases is within $2\varepsilon$ of the corresponding true wall. Subtract the ordered phases in the circle; the positive arc offsets are $[\alpha^j]$ and $[\alpha^d]$. Their circular distance is therefore at most $4\varepsilon$.

For $j\ne d$, ordinary lengths satisfy $|\alpha^j-\alpha^d|\ge\alpha^{d+2}$: among larger $j$ the smallest difference is $\alpha^d-\alpha^{d+1}=\alpha^{d+2}$, and among smaller $j$ it is $\alpha^{d-1}-\alpha^d=\alpha^{d+1}$. Also $|\alpha^j-\alpha^d|<\alpha$, so the distance via the other side of the circle is greater than $1-\alpha=\alpha^2\ge\alpha^{d+2}$. Hence their circular distance is at least $\alpha^{d+2}$, contradicting (55). This proves $j=d$ without any external depth information.

For two distinct coordinates $t,s\in J_d$, their initial-wall displacement is $[(t-s)\phi]$, with $0<|t-s|\le G_{d-1}-1$. The existing golden finite-precision separation theorem, applied to integer labels with horizontal displacement budget $Q=G_{d-1}$ and to the nearest integer, gives

$$
\operatorname{dist}_{\mathbb T}([(t-s)\phi],0)
>\frac1{\sqrt5 Q+1}>\frac1{4Q}\ge2^{-d-2}.
\tag{56}
$$

This uses precisely the real integer-pair gap in [IrrationalSlopeFaithfulness][ISF], including its private `golden_finite_precision_stable`, not a previously supplied circle decoder. The last inequality uses $G_{d-1}\le2^d$. Compatibility would instead bound this distance by $2\varepsilon=2^{-d-4}$. Thus $t=s$. At $d=1$ there is already only one member of $J_1$, so that case requires no separation comparison. The stage $d+5$ has exactly the true candidate and accepts. Earlier accepted stages are correct by the first paragraph. Formula (40), rather than an unobserved side bit, determines endpoint ownership under the attained promise. Formula (42) gives the historical set; its multiplicity prevents selecting the actual member for $d\ge2$.

For the finite bounds, stage $n$ examines at most

$$
\sum_{j=1}^{2n}|J_j|=\sum_{j=1}^{2n}G_{j-1}=G_{2n+1}-2<2^{2n+2}
$$

candidates. All Fibonacci values, search coordinates and coefficients of $\alpha^j$ for $j\le2n$ have $O(n)$ bits; $G_j\le2^{j+1}$ suffices. The integer part of $(t-A_j)\phi$ can be bracketed between integers of magnitude $O(G_{2n+1})$ and determined by $O(n)$ exact sign comparisons. Each comparison uses $O(n)$-bit integer arithmetic and at most grade-school multiplication, costing $O(n^2)$ work and $O(n)$ scratch. Generating coefficients, testing the two circular error balls, scanning/incrementing counters and framing records fit a conservative $O((n+c+1)^4)$ work per candidate. Powers, consecutive Fibonacci weights, one coordinate, one saved candidate and a count saturated at two suffice; the candidate list is not stored. Exact comparisons avoid an unbounded numerical-refinement subroutine. Summing the geometric candidate bounds through $N$ gives the first line of (53), and reusing scratch gives the second. Precision requests cost $O(c+\log(n+2))$ bits and replies $2n+O(c+1)$ bits. Their sum gives the third line. The final exact labels have magnitude $O(G_{d+1})$, and $d<2N$ at acceptance by (54), so their finite encodings fit the same bounds. $\square$

**Theorem 13.4 (Information used by the paired calibrated contract).** On the full proper attained class, one initial wall, one terminal wall, or the unordered pair of wall phases cannot replace the ordered pair in Definition 13.1. Even exact knowledge of the selected single wall's included lift does not repair the first two failures. If the reference has an arbitrary unknown additive rotation, paired ordered phases cannot identify $s$ at a depth with $G_{d-1}>1$. These are obstructions for these specific reduced inputs, not a lower bound over all acquisition interfaces.

Proof. The distinct records $\partial(1,1)$ and $\partial(3,4)$ both have initial phase $e_1$ and included lift $x_1^+$. The distinct records $\partial(1,1)$ and $\partial(2,3)$ both have terminal phase $e_0$ and lift $Z(0)$. The records $\partial(1,1)$ and $\partial(2,2)$ have the same unordered phase set $\{e_0,e_1\}$ but opposite wall roles and different positive lengths $\alpha,\alpha^2$. All these records are attained by Theorem 12.2. Finally, at a fixed $d$, the phases for $s'$ are obtained from those for $s$ by the common rotation $[(s'-s)\phi]$. Allowing the unknown reference rotation to differ by its negative gives identical paired readings for distinct $s,s'\in J_d$. Exact collisions also give identical arbitrarily precise reply sequences, so finite precision cannot repair any of these losses. The original calibrated paired contract retains exactly these omitted distinctions; no minimality claim about other possible readouts follows. $\square$

## 14. A common-source digital wall service and retained use

**Definition 14.1 (An explicit extended endpoint model).** Use the actual source, producer and sequential raw endpoint of Definitions 1.2 and 2.2. Add a finite digital service at this producer and a receiver with the acquisition rule of Definition 13.2. Initialization installs fixed finite programs, the reference of Definition 13.1, named channels and persistent permissions, all independently of $x$, and pays for them. Producer registers, raw cursor and receiver workspace start exactly as in Definition 1.2, with no acquired word; the receiver additionally has precision counter one and empty boundary storage. A fixed acknowledgement completes initialization. No source-specific wall, digit, seed, task table or future output is installed at initialization.

A driver can invoke the original Next on the actual producer and can issue Park at any proper returned cut. Every Next, raw Read and output remains paid. The driver may receive the original event triples on its own channel; the wall receiver does not subscribe to them or observe driver command counts. Computation delays and elapsed physical time are not additional observations. Park is an authorized command on the already bound current producer, not a selector that searches for an unknown source satisfying a desired boundary. Its guard checks a returned, nonempty paid prefix. It excludes further driver Next calls until release and transfers the declared service turn to the receiver, which gets only a fixed Paused acknowledgement on its prebound channel. The target is this same current paid-frontier boundary. No new raw read, Advance or history copy occurs in Park. Parking the initial empty frontier has a typed refusal and is outside the proper-target theorem.

During the pause, Wall$(n)$ is an authorized, paid readout action. The service reads its actual finite caches $d=|p|$, $N_p,r$ and computes $s=N_p+r$, the two phases in (40), and their canonical representatives $u_-,u_+\in[0,1)$. It sends the $n$-bit numerators

$$
a_n=\lfloor2^n u_-\rfloor,\qquad b_n=\lfloor2^n u_+\rfloor.
\tag{57}
$$

This uses exact quadratic-integer comparisons as in Definition 13.2, with explicit equality handling at phase zero. It is finite digital arithmetic on already acquired finite producer registers. It reads neither the unread source nor an infinite current configuration, and supplies no exact-label query. Its phase and reference convention are public fixed code. Wall changes only charged service scratch and channel state; it preserves $p,r$, the current source, unread cursor/tail and permissions. A completed Wall return restores the same paused state. The receiver obtains the exact boundary by actual paid replies, writes the finite record (40), discards its approximation scratch and keeps that record with its actual channel permission. A lease is a permission on this one exclusive connection and mode; it is not a hidden timestamp, operation counter or historical label.

The model permits finite arbitrary driver command prefixes ending in Park. No source-dependent infinite command word is part of initialization. Driver input acquisition, its output reception and its actual computation, if any, have their own costs. There is one common actual source throughout; the sender's registers, target boundary, reply coordinates, receiver record and later actions refer to this run, rather than to separately chosen realizations.

**Theorem 14.2 (Installed digital acquisition and its complete resource boundary).** Every initialized run of Definition 14.1 that parks after a finite positive number $r$ of completed Next calls admits finite wall acquisition of its actual boundary. If the actual prefix has length $d$, the service produces valid replies (50), and the receiver finishes after $N\le d+5$ Wall calls with exactly $\partial_{p,r}$ and the retained permission. Every proper attained boundary of Theorem 12.2 occurs in such a run. No historical member is chosen by the receiver's computation.

In the same run, through acquisition, there are exactly $r$ producer triples, $d$ paid raw-bit Reads, one successful Park, $N$ Wall requests with their $N$ returns, and the finite initialization/selection acknowledgements. The total coordinate traffic is $N(N+1)$ bits, with the framing, requests, permissions and final exact-record output additionally charged as in (53). The earlier producer stream contributes its existing $6r$ event bits before framing; driver commands, the $d$ raw replies and their transport are separate paid traffic. The digital service has additional work

$$
O\bigl(N(d+N+c+1)^3\bigr)
\tag{58}
$$

and reusable workspace $O(d+N+c+1)$ bits. For the producer, service and receiver together the simultaneous digital storage is $O(P+c+d+N)$. If the driver uses workspace or retains outputs, or the backend stores the source, their actual simultaneous storage $S_{\rm driver},S_{\rm backend}$ is added: the full estimate is $S_{\rm driver}+S_{\rm backend}+O(P+c+d+N)$. No bound on those two summands or on a separately requested archive is implicit.

One full accounting of bit work is

$$
\begin{aligned}
C_{\rm init}+C_{\rm driver}+C_{\rm backend}
&+O\bigl((r+d+1)(d+c+1)^2\bigr)\\
&+O\bigl(4^N(N+c+1)^4+N(d+N+c+1)^3\bigr).
\end{aligned}
\tag{59}
$$

$C_{\rm init}$ is actual finite installation/binding/reference-program cost, $C_{\rm driver}$ includes actual driver command acquisition and any computation/retained archive, and $C_{\rm backend}$ includes actual source provisioning, generation, input service and any additional physical storage/transport costs. Initialization code occupies the $P$ stored bits. The displayed digital terms include their input/output scans and scratch clearing. There is no uniform bound on arbitrary backend latency or on the creation of all infinite $x\in K$, and no claim that a later arbitrary Resume obeys the initial acquisition bounds (14).

Proof. Theorem 3.1 gives actual $p$, cursor $d$, current source $T^rx$ and attainment. The digital service computes the independently defined boundary of this actual paid frontier by Theorem 12.2. Rounding (57) has ordinary absolute error less than $2^{-n}$ and hence satisfies the circular inequalities (50), including a coordinate equal to zero. Pausing and exclusive access make those two replies and every later reply jointly valid for the same target. Theorem 13.3 therefore proves termination, exact selection and retention. Given $(d,s)$, take any history in (42), any source in its cylinder, and run exactly its prescribed $r$ Next calls before Park. Theorem 3.1 realizes that history and therefore this boundary. This establishes the claimed all-boundary domain. The same reasoning shows why the convenient witness $(0^d,s)$ used for an existence calculation is not a claim that the actual producer had prefix $0^d$ or counter $s$.

There are exactly $d$ Reads and $r$ triples by Theorem 3.1. Park and Wall perform no further ones. Summing $2n$ coordinate bits over $n=1,\ldots,N$ gives $N(N+1)$. At a service call, coefficients of its phase coordinates have $O(d)$ bits; multiplication by $2^n$ gives $O(d+n)$-bit integer coefficients. Integer-part search for a canonical phase costs $O(d)$ sign tests, and binary search for its $n$-bit rounded value costs $O(n)$ more. Each sign test is grade-school integer arithmetic on $O(d+n)$ bits. Two walls, cache scans, framing and scratch clearing fit $O((d+n+c+1)^3)$ work and $O(d+n+c+1)$ workspace. Summing gives (58). Caches and scratch are reused; they do not retain the $N$ replies or the past event word.

For completeness, the original finite prefix also has the digital work term shown in (59). Every earlier prefix has length at most $d$, every earlier time is at most $r\le k_p<G_{d+1}\le2^{d+2}$, and its finite representative has value at most $N_p+r=O(G_{d+1})$. Each emission's greedy calculation and each block-cache update thus fit $O((d+c+1)^2)$ bit work by the finite arithmetic of Section 8. There are $r$ emissions and $d$ consumed raw bits, with finite fixed-width event/command processing; this gives $O((r+d+1)(d+c+1)^2)$. Raw generation and non-digital input costs remain in $C_{\rm backend}$, and driver acquisition/computation is not erased by this producer bound. Adding (53) and (58) proves (59). The producer keeps its actual $p,r$ and raw binding, while the receiver keeps only its boundary and permission; their combined digital storage has the stated size. Nothing bounds any optional driver archive by this storage estimate. $\square$

**Definition 14.3 (Bounded installed use after acquisition).** With its retained permission, the receiver may request Arm$(L,H)$ for finite nonnegative $L,H$. The actual paused producer admits it exactly when $D(L,H)\le\delta$, using its actual $k_p-r$; the receiver can compute the identical guard from (44). Admission installs the stated finite budget and returns a fixed acknowledgement. It supplies no historical prefix or absolute counter. The permitted subsequent finite command sequences are Peek$(\ell)$, $0\le\ell\le L$, and at most $H$ Tick calls, with the same refusal and budget conventions as Section 6. The receiver's DATA output is calculated from its acquired boundary by Corollary 10.7, rather than by a new query to the unread raw endpoint. Tick performs the actual original Next, delivers its emitted bit and return acknowledgement, and updates the receiver record by (47). The digital endpoint projects to these declared fields; the actual producer retains all its original fields. No complete-counter-bearing task response is attributed to the boundary-only receiver.

**Theorem 14.4 (Guarded common-source use and route agreement).** In Definition 14.3, Arm is legal exactly on the DATA domain of Theorem 10.6. After $j$ accepted Ticks, $0\le j\le H$, the retained boundary is $\partial(d,s+j)$, the actual source is $T^{r+j}x$, the remaining budget is $H-j$, and its decoded answers agree with the actual source's spatial and temporal DATA. The producer has the same prefix $p$, same raw cursor and exact unread tail as at Park. Every such finite adaptive command sequence terminates without an additional raw Read. Release/Resume on the retained actual producer has precisely the continuation of Theorem 3.2.

Proof. Equations (29) and (44) identify the producer and receiver guards with the condition of Theorem 10.6. At each allowed Tick before budget exhaustion, $\delta-j\ge H-j>0$, so Theorem 12.3 gives (47) and a read-free actual Next. After that Tick both slack and remaining advance budget decrease by one, preserving (18); Peek leaves them unchanged. Induction gives the stated source, boundary and budget for any adaptive finite command sequence. At every resulting cut the producer route, the chronological route of Theorem 7.2 and the newly acquired-boundary route describe the same $U_{p,r+j}$. Theorems 4.1 and 10.6 therefore make their DATA values equal, and Corollary 10.7 evaluates that common value. Its possible computational provenance witness is irrelevant to the actual selected run because DATA is constant on the whole current fibre. Endpoint transport agrees by (40) and (47), including collapse to $Z(0)$. The actual unchanged cursor and tail give Theorem 3.2 on Release/Resume.

The finite decoder's work, literal DATA/query-output lengths, command scans, actual Tick execution, refusal outputs and any retained output archive are charged in addition to (59). Their finiteness follows from Corollary 10.7 and the finite command sequence; no new conversion-complexity bound is asserted. Rights are those installed and retained in Definition 14.1, and are never decoded from coordinates. In particular the statement reuses the existing DATA and continuation theorems; their evaluation and the capability handoff are not additional mathematical novelty. $\square$

## 15. Suppliers, distinctions and remaining recovery conditions

**Definition 15.1 (Attribution and exact comparison domain).** The exact coordinate and equicardinality theorem (39)–(45), its source-specific transport, and finite all-reply recovery (50)–(56) from approximate geometric input are `repo-derived`. The digital wall service is a finite realization of that input contract in an explicitly extended model. It is not a claimed improvement over direct exact-label export. The sender's forward wall calculation, exporter installation in itself, scalar separation, old DATA evaluation and counter repair are not counted as new mathematical results. No worldwide priority claim or new Lean certification is made.

| Supplier | Reused content and distinction |
| --- | --- |
| This volume §§2–8 and §§10–11 | The paid sequential producer, event-only observer, forward walls, finite bit arithmetic, exact slack, conditional DATA, finite provenance search and authenticated-counter repair are existing results. Equation (45) makes the earlier upper bound an equality for every proper attained boundary and identifies the full fibre without searching over historical prefixes. The new receiver acquires exact walls from finite-precision phase replies; it is not an event subscriber recomputing exact labels. |
| [RRO20.2, 20.6, 24.2, 35.1][RRO]; [Zeckendorf381–383][Z] | Exact finite value ranges, endpoint-inclusive cylinder geometry, block lifetimes, split-side transport/collapse and finite prediction are indispensable existing suppliers. Equations (40) and (47) specialize their exact endpoint conventions to the full attained class. Neither positional deletion nor arbitrary source mutation replaces the stated $T$. |
| [SignedSeriesFibres][SSF] and its [owning Scribe][SSFB] | The exact real seam fibres, injective seam indexing and all other singleton fibres are positive supply. Its private `prependBlock` and the local `parse`, affine recurrences, fibre and classification proofs are included in that supply. They do not assert current historical equicardinality or install noisy-wall acquisition. |
| [Golden slope separation][ISF] and its [owning Scribe][ISFB]; [GoldenHurwitzBound][GHB] | Existing irrational integer-pair injectivity and finite horizontal-budget gap, including private `slope_encoding_injective_of_irrational`, `golden_finite_precision_stable`, `two_lt_sqrt_five` and `golden_form_ne_zero`, supply (56). The private proofs are not treated as absent interfaces. The new step obtains a finite candidate-depth bound from the two geometric walls themselves and proves all-reply stopping; scalar separation alone does not do this. |
| [Arithmetic tomography][ATISF] and its [Scribe][ATISFB] | Irrational linear-observer injectivity is already available for all integer pairs. Exact real injectivity does not give an unbounded-depth noisy circle decoder without the width argument (54). |
| [MechanicalPhaseCalibration][MPC] and its [Scribe][MPCB]; RRO Context Geometry §33 | Local mechanical-word mismatch under separated moving cuts, and jointly calibrated noisy phase estimates under their common-source hypotheses, are existing results. Neither supplies an unknown winding count, reference calibration or the attained-boundary class promise used here. Definition 13.1 uses only circular errors and ordered wall roles, with the reference explicitly fixed. |
| [NativeAcquiredPrefixCylinder][NAPC], [State][NAPS], [Reconstruction][NAPR] and their owning Scribes | Actual native paid-prefix execution and unread-tail restart, including private `next_native_spec`, `prefix_cons`, `raw_tail_add` and the driver proofs, are credited. Their seed/payload/Stop controller differs from this producer. The reconstruction Scribe explicitly distinguishes its mathematical normal form from a retained runtime archive. |
| [PVC §§5–7][PVC], [CSA §§6–8][CSA], [AIF §§4,9][AIF], [Zeckendorf496/502][Z] | Direct native B-path-table to M, archive-to-T, whole-view kernels, installed paid conversion, acquired calls and continuing queries already exist. They use different input objects and history models. Definition 14.1 supplies the concrete same-run mapping for current phase walls; it does not claim those earlier services were missing or automatically apply them to a new interface. |
| [InterfaceKernelCriterion][IKC] and its [Scribe][IKCB]; [predictive quotient][PCQ] and its [Scribe][PCQB]; Boundary Dynamics §§36.1–36.6 | Actual-image factorization and dynamic kernel obligations are existing abstract results. The coordinate classification, exact stopping over the infinite depth class, and paid input realization here discharge concrete obligations rather than add a generic quotient/replay wrapper. |
| [FiniteOneStepFutureMemory][FOFM] and its [Scribe][FOFMB] | Finite-state all-laws one-step expectation sufficiency, pullback closure and minimum quotient dimension are positive supply, including private `separating_laws`. They do not give recursive invariant closure, a bit-memory optimum or a Zeckendorf wall/history decoder. |
| Brattka–Gherardi–Pauly, [*Weihrauch Complexity in Computable Analysis*, Definition 9][WCA] | `literature-attested`: computable metric spaces and Cauchy representations supply the standard viewpoint of increasingly precise rational names. The dyadic replies (50), attained-class isolation and bound (52) are proved here for the stated source, not attributed to this general representation definition. |
| Pinned [mathlib Zeckendorf module][MATHLIB] | `literature-attested`: finite canonical Zeckendorf representation, greatest-Fibonacci construction and uniqueness. These remain the arithmetic suppliers for $p_d(N)$ and finite representatives. Exact quadratic sign tests and grade-school integer arithmetic are standard intermediate mechanisms, not claimed discoveries. |

**Definition 15.2 (Scope of the acquired recovery).** The independently specified current boundary has a finite, exactly classified historical kernel. The acquired receiver record recovers that boundary and its guarded finite DATA; the actual retained endpoint executes the corresponding authorized actions on the same source. These statements provide a boundary-to-finite-memory acquisition direction under weaker geometric input than exact labels. They do not make all four views mutually invertible: an actual historical member of (42), absolute chronology and original producer fields remain ambiguous without the separately authenticated counter of Theorem 10.8. A computational witness in (42) is never historical evidence. Whole infinite space remains unrecovered by Theorem 7.3, and the full continuation beyond the finite DATA horizon still depends on the actual unread source.

The wall channel is an explicitly new digital operation on producer caches with source-independent initialization. It is not available on the original event-only endpoint of Definition 1.2. The construction proves its finite realization in this digital model, rather than merely postulating a symbolic inverse. Installation of an independent physical wall sensor, acquisition of the specified physical reference and a proof that its errors concern this same paused compatible region remain separate bridges. Unknown reference rotation/scale/orientation, moving targets, arbitrary or falsely promised wall pairs, revocation, concurrent clients and non-Advance source mutation are outside (50). No sensor, capability, calibration or backend is supplied by the uniqueness proof. Finite programs here have source-indexed storage growing with $d$; no uniform bounded memory, source-cost optimum, physical impossibility or universal two-generator reduction follows.

All original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization and complete-response obligations retain their own exact scopes. In particular Native Source Call Task Recovery §§10.1/10.3/10.4, Native General Cut Acquisition §9.4 and OA §§11.3/17 are not settled by this different digital endpoint. The full common-relation programme, including general independent space/time/boundary/memory recovery with actual acquisition, rights and continuing use, remains unresolved.

[SSF]: ../../../D5/S1/Digit/Infinite/SignedSeriesFibres.lean
[SSFB]: ../../../Blueprint/D5/S1/Digit/Infinite/SignedSeriesFibres.scribe.cs
[ISF]: ../../../D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.lean
[ISFB]: ../../../Blueprint/D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.scribe.cs
[GHB]: ../../../D5/S1/Depth/GoldenHurwitzBound.lean
[ATISF]: ../../../D5/S3/Observer/ArithmeticTomography/IrrationalSlopeFaithfulness.lean
[ATISFB]: ../../../Blueprint/D5/S3/Observer/ArithmeticTomography/IrrationalSlopeFaithfulness.scribe.cs
[MPC]: ../../../D5/S1/Words/Mechanical/MechanicalPhaseCalibration.lean
[MPCB]: ../../../Blueprint/D5/S1/Words/Mechanical/MechanicalPhaseCalibration.scribe.cs
[IKC]: ../../../D5/S3/ObserverMemory/Refinement/InterfaceKernelCriterion.lean
[IKCB]: ../../../Blueprint/D5/S3/ObserverMemory/Refinement/InterfaceKernelCriterion.scribe.cs
[PCQ]: ../../../D5/S3/ObserverMemory/RefinementClosure/PredictiveCompletionMaximalInvariantQuotient.lean
[PCQB]: ../../../Blueprint/D5/S3/ObserverMemory/RefinementClosure/PredictiveCompletionMaximalInvariantQuotient.scribe.cs
[FOFM]: ../../../D5/S3/ObserverMemory/Prediction/FiniteOneStepFutureMemory.lean
[FOFMB]: ../../../Blueprint/D5/S3/ObserverMemory/Prediction/FiniteOneStepFutureMemory.scribe.cs
[WCA]: https://arxiv.org/html/1707.03202v3

## 追加锚（本行以下为增补区）

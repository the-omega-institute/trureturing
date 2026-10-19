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

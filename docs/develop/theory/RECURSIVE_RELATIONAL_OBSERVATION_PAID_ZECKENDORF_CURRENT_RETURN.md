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

## 16. 无相位原点、未知固定单位的主动尺度合同

**定义 16.1（同一付费来源上的接入点）。** 沿用定义1.2、2.2的实际来源 $x\in K$、顺序原始端点、Next、初始化与返回语义。驱动者完成任意有限个 Next 后，在某个实际返回 $(p,r)$ 将独占调用轮交给接收者。允许 $r=0$；此时 $p=\varnothing$。交接只返回固定确认，不披露驱动命令数、原始位、$p,r,d,N_p$、任何墙标或未来输出。接收者的本地计数从零开始。其本地第 $i$ 次 Step 就是对这个原生产者实际调用一次 Next，完整交付原来的 Emit、Advance、Return，随后仍持有同一端点的调用权。查询间与返回后的等待没有自主 Advance；只有完成的 Step 改变来源。交接后驱动者不得并发调用。

调用权、程序、通道及独占轮的转交协议在源无关初始化时实际安装并付费。交接不创造权利，不重置来源、原始游标或生产者寄存器。接收者取得的是原端点的一轮持续调用权，允许在原有零余量切面继续 Next；它没有被限制在定义14.3的 Arm 预算内。释放可将这一轮交回驱动者。程序不依赖接入点，交接不按所需边界选择某个有利来源。定理量化所有 $x\in K$ 和所有实际返回接入点。

记接入时的边界为 $\partial_0$。对非空 $p$，记其真实但未提供给接收者的坐标为 $(d_0,s_0)=(|p|,N_p+r)$。空前沿单独用 $(d_0,s_0)=(0,0)$ 表示，并记其边界为空、兼容相位区为整圈。为统一尺度记号，置

$$
E(d)=\operatorname{length}\bigl(H[U_{p,r}]\bigr)=\alpha^d
\quad(d\ge0),\qquad
\delta_0=\begin{cases}0,&d_0=0,\\G_{d_0+1}-2-s_0,&d_0\ge1.\end{cases}
\tag{60}
$$

整圈的归一化长度为一；$E$ 读的是实际兼容区的弧长，不是两墙间的较短圆周距离、弦长、弧长补集或某条无限数字带的物理长度。对于 proper 区域，所选区域仍是定义7.1的实际付费前沿区域，包含既有端点所有权。读取其长度不会提供墙角色或相位。

**定义 16.2（未知单位的近似尺度读口）。** 服务私有地保留一个固定正有理数 $q=A/B$，$A,B$ 为正整数。同一接入与主动取得全过程使用同一个 $q$，它与未知原始输入无关；接收者既未收到 $q$，也未收到其上下界、分子分母或描述长度。尺度读口的单位是自己的输出单位：在当前返回的实际深度 $d$，请求 Extent$(n)$，$n\ge1$，得到非负整数 $a$ 的完整有限自定界编码，满足

$$
\left|a2^{-n}-q\alpha^d\right|\le2^{-n}.
\tag{61}
$$

Extent 不读原始位、不发 Advance、不改变 $p,r$，每次有限返回。它没有模一、溢出或饱和：当 $q\alpha^d>1$ 时，整数部分也须实际发送并收费。各次误差可依赖全部已发生的调用与回复，不要求嵌套、独立、无偏或特定舍入。每次回复只约束它自己的当前切面；一次 Step 后，下一回复必须指向刚达到的付费前沿。同一深度期间的各次读数与不同深度的读数共同服从一个固定 $q$。

该接收者不读任何墙的相位。即使另有仪器使用任意未知加性原点，该原点也不进入 (61)，无需估计。这里仍有实质性的参考承诺：已知 $\alpha$ 的有限代数定义、读数分辨率 $2^{-n}$ 的含义、正尺度、同一兼容区及固定单位。未知单位不等于误差界也未知。任意实数物理传感器不由本定义自动实现；第19节给出这一合同在有理数数字服务上的有限实现。

**命题 16.3（静止尺度输入与主动合同的区别）。** 已知单位时，精确 $E(d)$ 确定深度，却不区分同一 $J_d$ 中不同的 $s$。允许未知正有理单位时，仅靠保持目标静止的 (61)，不存在一个在所有允许回复上有限停止、对所有输入精确恢复深度的统一程序。因此，本节的主动操作不能由一次静止的“有理单位消去”替代。本命题只论这个静止尺度通道。

证明。第一句由 $0<\alpha<1$ 与 (60) 得到；在 $G_{d-1}>1$ 时，同深度的所有 $s$ 有相同尺度。第二句甚至在给定深度 $d\ge1$ 的某个实际边界上取固定 $q=1$，也可导出反证。为每个被请求的精度选择离真实尺度最近的非负 dyadic 数，误差至多 $2^{-n-1}$。假设程序在这条允许回复序列的某个有限前缀后停止；设它请求过的最大精度为 $N$。另选 $d'\ne d$，由正有理数稠密性选 $q'>0$ 使

$$
|q'\alpha^{d'}-\alpha^d|<2^{-N-2}.
$$

同一有限回复前缀对第二个尺度的误差严格小于 $2^{-n}$。定理12.2实际实现两个深度的边界，两个服务各自在整段期间保持自己的固定有理单位。因此程序作出同一决定，却必须给出两个深度。有限个调用都未发生时同样无法区分。这个反证允许单位在两个比较世界中不同，没有在一个世界中改变单位；它不否定定理13.3的有原点、有已知单位且有序双墙输入。证毕。

## 17. 两次付费更新之间的完整寿命给出精确取得

**引理 17.1（有限误差下的三种尺度比）。** 置

$$
\mathcal C=\{1,\alpha,\alpha^2\}.
\tag{62}
$$

一个实际 Step 前后尺度之比恰属于 $\mathcal C$：未读取新原始块时为一，读取块 $0$ 时为 $\alpha$，读取块 $10$ 时为 $\alpha^2$。这也包括空前沿的第一步。设前后实际尺度为 $z,cz$，$c\in\mathcal C$，同精度的回复实数为 $u,v$，各自绝对误差至多 $\varepsilon$。保留且只保留满足

$$
|v-c'u|\le(1+c')\varepsilon
\quad(c'\in\mathcal C)
\tag{63}
$$

的候选。若 $u>64\varepsilon$，则恰有一个候选，且它为真实 $c$。包含误差球边界的回复也适用。

证明。尺度比是原始前缀长度增量与 (60) 的结果；读取强制零也计入长度。真实 $c$ 满足 (63)，因为
$|v-cu|\le|v-cz|+c|z-u|\le(1+c)\varepsilon$。
由 $\alpha^2+\alpha=1$ 及其正根范围可得 $\alpha>3/5$，故三候选中最小的两两差为 $\alpha^3>1/5$。若 $c',c''$ 均保留，则

$$
|c'-c''|u\le(2+c'+c'')\varepsilon\le4\varepsilon.
$$

而 $u>64\varepsilon$ 使左侧严格大于 $64\varepsilon/5$，矛盾。候选的真实性与唯一性均用允许的闭误差不等式证明，没有挑选有利舍入。证毕。

**定义 17.2（无已知深度或单位的取得程序）。** 接收者在接入点保持暂停，依次请求 Extent$(n)$，$n=1,2,\ldots$。将回复解释为 $u=a2^{-n}$；在首次满足

$$
u>1024\,2^{-n}
\tag{64}
$$

时固定这个精度 $n_*$、$\varepsilon=2^{-n_*}$ 与最后的 $u$，丢弃更早回复。然后重复：执行一个真实 Step，本地计数 $i$ 加一，暂停于其返回，请求一次 Extent$(n_*)$ 得到 $v$，按 (63) 分类，并以 $v$ 替换 $u$。类别一记作不更新，类别 $\alpha$ 记作长度增量一，类别 $\alpha^2$ 记作长度增量二。收到的发射位正常交付；这个取得程序不使用它来选类别，也不存整个事件词。

在前两次非一类别出现时分别记录本地序号 $t_1,t_2$ 及长度增量 $g_1,g_2\in\{1,2\}$。第二次后停止 Step 并保留同一调用权。由 $w=t_2-t_1$ 顺次生成 Fibonacci 权重，寻找唯一 $D\ge1$ 使

$$
w=G_{D-1}.
\tag{65}
$$

输出接入边界与已达到边界的精确有限描述：

$$
\begin{aligned}
d_0&=D-g_1,&
s_0&=G_{d_0+1}-1-t_1,\\
d_*&=D+g_2,&
s_*&=G_{d_*}-1.
\end{aligned}
\tag{66}
$$

$d_0=0$ 时输出空边界；否则按 (40) 输出 $\partial(d_0,s_0)$。达到边界为 $\partial(d_*,s_*)$。使用的代数比较均按定义13.2的二次整数符号方法执行；(64) 本身就是整数 $a>1024$。本程序的定理域内 (63) 一定恰有一个类别，(65) 一定命中；不对违反来源或尺度承诺的任意输入声称成功或有限拒绝。

**定理 17.3（所有实际来源、所有允许误差的初始与达到边界恢复）。** 对每个 $x\in K$、每个实际返回接入点以及每个满足 (61) 的回复序列，定义17.2有限停止。它精确恢复接入边界和停止时的实际达到边界，包括 (38)、(40) 的端点所有权。令 $m=t_2$，则

$$
\begin{aligned}
t_1&=\delta_0+1,\\
t_2-t_1&=G_{d_0+g_1-1},\\
d_*&=d_0+g_1+g_2\le d_0+4,\\
m&\le2G_{d_0+1}.
\end{aligned}
\tag{67}
$$

在这同一次取得中恰有 $m$ 次实际 Step 及 $m$ 个原生产者事件三元组，新增原始 Read 恰为 $g_1+g_2\in\{2,3,4\}$ 次；每个被经过的强制零均实际读取。Extent 调用恰为 $n_*+m$ 次。取得既不需要 $d_0$ 的上界，也不需要 $q$ 的编码或上界。

证明。初始实际尺度 $z_0=q\alpha^{d_0}>0$。当精度足够大时，任一允许回复均有 $u\ge z_0-2^{-n}>1024\,2^{-n}$；所以 (64) 有限达到。固定精度后，$z_0>1023\varepsilon$。

先沿原生产者的真实运行考虑前两次原始块读取。在这段运行中，深度最多增长四。由 $\alpha>3/5$ 得
$\alpha^4>81/625>1/8$。故直至第二次更新后的所有当前真实尺度均大于 $1023\varepsilon/8$，每个对应回复大于 $64\varepsilon$。引理17.1于是正确区分每一步的三个类别。这个论证同时给出归纳闭合：在真正第二次读取前不会出现虚假的更新，也不会漏掉真正更新，故程序确实恰在真实第二次更新处停下。

对非空初始前沿，定理12.3、(44) 给第一次新原始块读取前恰有 $\delta_0$ 次不更新 Step，下一次读取，故 $t_1=\delta_0+1$。空前沿在第一步读取，结论也成立。此后新深度 $D=d_0+g_1\ge1$，切面恰在出生位置 $s=G_D-1$。出生余量为

$$
G_{D+1}-2-(G_D-1)=G_{D-1}-1.
\tag{68}
$$

因此从这次更新到下一次更新，实际 Step 数恰为 $G_{D-1}$。这段包括出生后的全部不读取步与下一次读取步，不能少计末步。所有中间 Next 按定理3.1有限返回，到达零余量后再一次 Next 也有限；所以两次更新确实在有限步内发生。

$G_j$ 严格递增，(65) 因而唯一命中真实 $D$。公式 (66) 的第一项随即恢复真实 $d_0$。非空时由 $t_1=G_{d_0+1}-1-s_0$ 恢复真实 $s_0$；空时 $t_1=1$，同式得到 $s_0=0$。第二次更新再次出生，给出真实 $(d_*,s_*)$。定理12.2的唯一坐标与端点公式给两个精确边界，而非仅给同长度的弧。没有在接收者侧借用私有 $p,r,N_p$。

若 $d_0\ge1$，(44) 给 $t_1\le G_{d_0-1}$，而 $D\le d_0+2$ 给 $G_{D-1}\le G_{d_0+1}$。若 $d_0=0$，$t_1=1$，$D\in\{1,2\}$，所以 $m\le3\le2G_1$。这证明 (67) 的统一上界。两次更新以外均无原始读取；定义2.2在两次更新分别读 $g_1,g_2$ 个真实位。最初精度寻找没有 Step，随后每次 Step 恰有一次尺度读取，故各项精确计数成立。证毕。

**推论 17.4（真实选择与回溯的范围）。** 任一历史成员 $(p,r)$ 实现同一接入边界时，定理17.3仍在它自己的真实未读尾上执行，所得停止边界可以因真实后续块而异。接收者取得 $\partial_0$ 后，可以按 (42) 计算其整个历史纤维，但没有选择其中实际的 $(p,r)$，没有恢复接入前的绝对操作数。程序停止时来源是实际 $T^{r+m}x$；回溯输出不使来源回到 $T^rx$，也不恢复其无限配置。

证明。定理17.3逐源证明，$g_1,g_2$ 来自各自真实的块选择，而非一次预选完成。边界恢复的是唯一 $(d_0,s_0)$，(42) 对 $d_0\ge2$ 仍有 $G_{d_0-1}$ 个历史成员；本程序没有输出其中某个历史作为实际历史。程序保留的 $m$ 只是交接后的实际增量；$r$ 不由它提供。当前来源的式子来自同一生产者的 $m$ 次 Next 与定理3.1。对无限配置，取固定驱动前缀与第19节的向下舍入实现；同一停止原始字 $p'$ 的所有无限完成给相同的此前事件、深度序列和尺度回复，却按定理7.3含有不同的当前无限配置。所以不存在由本取得输出在整个允许类上恢复无限配置的结论。证毕。

## 18. 取得后跨更新的实际可调用状态

**定义 18.1（取得后的活记录与接口）。** 在第二次更新的真实 Return，接收者保留

$$
\mathfrak a=(\partial_0,d,s,i;\kappa),
\qquad(d,s,i)=(d_*,s_*,m).
\tag{69}
$$

$\partial_0$ 是接入边界的有限坐标描述，$i$ 是从交接起的本地 Step 数，$\kappa$ 是实际持有的同源调用权。也可保留递推权重缓存；它们不是历史证据。尺度读数、精度寻找记录和已处理事件都可丢弃。后续接口为：

- LiveStep：调用一次真实 Next，交付其实际三元组，更新 (69)。此调用不受旧有限 DATA 余量限制。
- Peek$(\ell)$：当 $G_\ell-1\le\delta(d,s)=G_{d+1}-2-s$ 时计算并写出当前 $q_\ell$，否则固定格式拒绝。$\ell=0$ 合法。此调用不移动来源。
- Seek$(L,H)$：在当前切面测试 $D(L,H)\le\delta(d,s)$；若不满足，连续执行真实 LiveStep，直到首次满足，再写出当前 $q_L$ 与实际本地计数，并保留当前边界和调用权。
- 可选 Arm$(L,H)$：仅在相同 DATA 守卫成立时装入剩余预算 $H$，随后有限 Peek/Tick 使用定义14.3的预算语义。每次合法 Tick 真实执行一次 Next，按定理18.2更新 $(d,s,i)$ 并递减预算。一次新 Seek、LiveStep 或释放显式退出该预算模式。

命令使用固定标签；各非负整数参数单独采用定义8.1的二进制长度一元头加二进制负载的自定界编码。与旧 Arm 后的固定宽度 Peek 不同，新无预算 Peek 的 $\ell$ 也须如此付费输入。可选预算模式可沿用旧固定宽度语法；模式标志与全部预算字段实际存储。对不移动来源的 Peek／Arm，先比较参数：正深度请求若 $L\ge d$，或 Arm 的 $H>\delta$，即拒绝，再对其余参数生成权重并测试完整守卫；Peek 在此取 $L=\ell,H=0$。这只是同一守卫的提前失败测试，避免为巨大而必拒绝的参数展开巨大权重。输出均实际写入。合法有限语法中的拒绝不改变来源或权利；不对无终止畸形帧声称有限处理。Seek 是移动来源、再给达到切面答案的任务；它不是在原固定切面上无条件回答的 Peek。接收者也可释放独占轮，生产者保留原有限字段与真实未读尾。它不能把打印出的 $\kappa$ 名字交给另一个端点而制造可调用权。

**定理 18.2（含零余量分支的同源活更新）。** 在 (69) 的每个达到切面，LiveStep 都合法并有限返回，不需要新的尺度读数或已知 $q$。设其真实发射位为 $b$。若 $\delta(d,s)>0$，接收者更新为 $(d,s+1,i+1)$，且 $b=\operatorname{Low}(s)$，没有原始 Read。若 $\delta(d,s)=0$，令

$$
a_0=\operatorname{Low}(s),\qquad
 a_1=\operatorname{Low}(s+G_d).
\tag{70}
$$

则 $a_0\ne a_1$。$b=a_0$ 恰对应真实块 $0$，更新为
$(d+1,G_{d+1}-1,i+1)$；$b=a_1$ 恰对应真实块 $10$，更新为
$(d+2,G_{d+2}-1,i+1)$。前者恰付一个原始 Read，后者恰付两个。更新后的边界、端点所有权和表示中的实际来源分别为定理12.3的边界及 $T^{r+i+1}x$。

证明。对实际私有返回 $(p,r+i)$，始终有 $d=|p|$、$s=N_p+r+i$。正余量时定理12.3直接给出无读取运输与实际发射。零余量时原生产者读取自己的真实下一个块。定义2.2的两个发射计算分别为
$\operatorname{Low}(N_p+r+i)$ 与
$\operatorname{Low}(N_p+G_d+r+i)$，正是 (70)。它们不等，是定义2.3中由真实分裂见证证明的差异；没有另发一个私有分支标志。接收者以真实发射位选择真实分支，(48) 给新坐标。定理3.1、3.2保证有限返回、正确当前来源和原始尾的精确续接。端点由 (40) 随当前坐标计算，因而与真实墙运输一致。对后续调用归纳即得结论。证毕。

**定理 18.3（任意有限新任务的主动取得与有限进展）。** 从任一取得后的活记录，给定任意有限 $L,H\ge0$，Seek$(L,H)$ 对每个实际来源有限停止，所有所写空间答案都属于真正达到的同一来源切面。令 $D=D(L,H)>0$，$a=\min\{j:G_j\ge D+1\}$，调用前深度为 $d$。若当前不满足守卫，则本次 Seek 的额外 Step 数与停止深度 $d'$ 满足

$$
\begin{array}{c|c|c}
 &\text{额外 Step 数上界}&\text{停止深度上界}\\\hline
d\ge a&G_{d-1}&d+2\\
d<a&G_{a+2}-1&a+3
\end{array}
\tag{71}
$$

新增原始 Read 恰为实际深度增加 $d'-d$。$D=0$ 或当前已充分时零步停止。由此任意有限自适应的上述合法命令序列均有限完成；这并不为无限个命令提供一次有限总完成时间。

在每个满足守卫的当前边界上，Peek 及可选有预算使用的答案，可以直接用代表 $Z(s)$ 计算，并与真实来源、原事件解码路线及既有边界 DATA 路线一致。没有额外原始读取的断言只适用于正余量的 LiveStep 和已经装入的有限预算段，不适用于一般 Seek 或零余量 LiveStep。

证明。若当前深度 $d\ge a$，不充分时在 $\delta+1\le G_{d-1}$ 步后读取下一块。新生深度 $d+g$ 的余量为 $G_{d+g-1}-1\ge G_a-1\ge D$，故一定不晚于该返回停下。若 $d<a$，在真实逐块扩展中取第一个长度 $b\ge a$ 的父前缀；长度每次增加一或二，故 $a\le b\le a+1$。若未更早停下，继续到其下一次分裂后的出生返回。其余量至少 $G_b-1\ge D$，子长度至多 $a+3$。该实际绝对返回数由 $M_p-1=G_{b+1}-N_p-1\le G_{a+2}-1$ 控制；从当前非负绝对返回出发的增量也不超过它。每个有限 Step 都由定理18.2在同一端点执行，原始游标的增长恰为长度增加，所以 (71) 包含实际强制零与真实读取数。参数 $a$ 是程序计算的有限阈值，不是未取得的来源深度。

若 $d\ge1$，定理12.2允许计算见证历史 $p=0^d,r=s$。在守卫成立时，定理10.6使整个 $U(\partial(d,s))$ 上的 DATA 相同；定理4.1对这一见证给出当前答案 $q_\ell(Z(s))$，以及预算内后继答案 $q_\ell(Z(s+j))$。实际来源在同一个 $U$ 中，所以这些值就是实际答案。这里用的是共同当前纤维上的常值性，没有把见证 $0^d$ 冒充实际已读字。

定义18.1每个命令或保持当前真实记录、或执行刚证明有限的一段真实 Step；定理18.2归纳保存其对应。可选预算模式再复用定理14.4的余量不变量。有限自适应序列的下一个请求虽依赖先前答案，仍是一个有限参数请求，因此逐次应用上述证明。释放时没有改写来源或游标，原端点由定理3.2继续其真实尾。证毕。

**例 18.4（实际零来源上的尺度分离）。** 取真实 $x=0^\infty$，在返回 $r=2$ 接入。实际前缀 $00$、深度二、$s=2$。随后前两次更新的本地序号为 $t_1=2,t_2=5$，增量均一；尺度比依次为

$$
1,\alpha,1,1,\alpha.
\tag{72}
$$

任意隐藏正有理 $q$ 及任意允许回复下，程序得到 $w=3=G_2$、$D=3$，由 (66) 恢复接入 $\partial(2,2)$，并在真实返回七取得 $\partial(4,7)$。这些值由原时钟符号递推得出，不需要执行数值实验。

同一零来源在返回三接入时，初始尺度仍为 $q\alpha^2$，边界却为 $\partial(2,3)$；其第一次更新在本地第一步。所有静止初始尺度读数可相同，而一次实际 Step 后前者不收缩、后者收缩。这个区别是同源动作揭示的 $s$，不是旧历史纤维中选真实前缀的办法。例子只说明判据的实际含义；定理17.3的证明没有选零来源作为全来源的替身。

## 19. 数字实现、同次运行的流量与存储

**定义 19.1（尺度服务的有限实现及收费对象）。** 初始化安装定义16.1的接入／释放模式与 Extent 程序，私有单位配置为实际有限整数对 $(A,B)$。程序在生产者返回后读自身当前缓存 $d$，以整数对表示 $\alpha^d\in\mathbb Q(\sqrt5)$，用精确符号比较产生

$$
a=\left\lfloor2^n(A/B)\alpha^d\right\rfloor.
\tag{73}
$$

这给 (61) 的一个实际实现，而定理17.3仍覆盖 (61) 允许的全部舍入。服务也可从所有满足 (61) 的非负整数中按任意实际误差机制选择：除整数端点情形外只有向下与向上两个整数，整数端点另允许相邻整数；验证选择仍是同一精确比较。实际选择／误差机制的额外工作和储存由其后端承担。证明不要求或推断它的概率分布。

尺度服务读的是这一个生产者当前缓存，其正确性来自 (60)，不是从另一个历史上导入的理想尺度。它对接收者不输出 $d$ 或 $q$。初始化时只装源无关的有限配置、程序、真实绑定与权利；在返回零时尚无任何已读原始字。源后端仍按定义8.1另计，任意 $x\in K$ 的无限材料不由本服务制造。

令 $b_q$ 为正整数 $A,B$ 的通常二进制长度之和，故
$2^{-b_q}<q<2^{b_q}$。让 $c$ 控制本次全部端点、模式与权利描述符的位宽，$P$ 为固定程序及约定的安装位数，采用定义8.1的固定数目顺序二进制工作带。整数、请求、回复、确认、拒绝和精确记录均须完整分帧；处理、拷贝、定位、清零及解除调用轮都收费。没有单位代价的无限实数、任意大整数或任意地址操作。

**定理 19.2（主动取得的同次完整数字费用）。** 对定理17.3的一次运行，令接入前驱动者已完成 $r$ 次 Next、实际已读长度为 $d_0$。令 $m=t_2$、$n=n_*$，并置

$$
W_0=d_0+b_q+n+c+32.
\tag{74}
$$

同次运行满足

$$
 n\le d_0+b_q+12.
\tag{75}
$$

截至取得返回，生产者总共完成 $r+m$ 个三元组、恰读 $d_*=d_0+g_1+g_2$ 个原始位；其中交接后的坐标恰如 (67)。成功交接一次，Extent 共 $n+m$ 次，每次有自己的返回；初始化、驱动者输入及交接确认另有完整有限帧。接收者不必保存事件档案或全尺度回复列。

在这种实际数字实现中，除实际源后端、驱动者自身计算与额外档案外，一种保守的联合上界为

$$
\begin{aligned}
C_{\rm digital}
 &=O\left(P+b_q+I+(r+m+d_0+n+1)W_0^3+B_{\rm out}\right),\\
S_{\rm digital,peak}
 &=O(P+W_0),\\
B_{\rm extent+control}
 &=O\left((n+m+1)(c+n+b_q+1)\right).
\end{aligned}
\tag{76}
$$

$I$ 计实际数字请求输入，$B_{\rm out}$ 计实际选择写出的全部结果及事件、确认、拒绝位。第三行计交接后的尺度请求／回复及 Step 控制帧；此外原始回复恰为 $d_*$ 位，生产者事件负载恰为 $6(r+m)$ 位，各自的通道分帧和描述符也实际收费。结果中的初始与达到边界、相应标签和本地计数合计 $O(d_0+c+1)$ 位。若要求列出全部历史成员、字面 DATA、原始字、驱动者或接收者的完整档案，其实际生成、输出和同时保留长度另加。

完整系统工作须再加实际安装／绑定的非数字费用、驱动者的命令取得／计算及源后端的 $\iota_x+\gamma_x(d_*)$；峰值存储须再加实际同时存在的驱动者工作区、$\sigma_x(d_*)$、误差机制及外部保留输出。$q$ 的私有配置 $b_q$ 已计在数字存储内，不能借“不发给接收者”将其删去。若 Read 是计价原语，Read 次数与其真实位负载作为独立坐标保留；任何额外传输、物理测量或生成费用也不由 (76) 抵消。

证明。$\alpha>1/2$ 与 $q>2^{-b_q}$ 给
$z_0=q\alpha^{d_0}>2^{-d_0-b_q}$。在精度 $d_0+b_q+12$，任一允许回复满足
$u/\varepsilon>2^{12}-1>1024$，故有 (75)。这是证明中的事后界，不是接收者的先验输入。

直到停止，真实深度不超过 $d_0+4$。每个生产者的绝对返回数小于 $G_{d_*+1}\le2^{d_*+2}$，所有原始前缀、计数、$N_p$、时钟与有限代表都有 $O(d_0+1)$ 位。尺度回复的整数满足 $0\le a\le2^{n+b_q}+1$；即使误差机制选择最大允许整数，也只有 $O(n+b_q+1)$ 位。二次整数表示的 $\alpha^d$ 系数有 $O(d+1)$ 位，乘 $A$、清分母 $B2^n$ 后所有符号比较使用 $O(W_0)$ 位整数。分子平方等 grade-school 运算耗 $O(W_0^2)$ 位操作、$O(W_0)$ 可复用空间。以 $O(W_0)$ 次符号比较二分取得 (73)，加上生成幂系数、读缓存、分帧和清零，每次 Extent 可用 $O(W_0^3)$ 位操作、$O(W_0)$ 空间完成。

接收者每次只保留上一尺度整数和新整数，(63) 至多三个精确比较，使用相同宽度。在第二次更新前，它只需本地计数、第一更新时间与两个增量；不保存 $m$ 个三元组。由 (67)，这些计数有 $O(d_0+1)$ 位。按 (65) 生成权重只需相邻两个权重与计数，不必存表，耗 $O((d_0+1)^2)$ 位操作。初始 $n$ 个尺度请求与 $m$ 个后续请求均已计数。每帧的整数与描述符长度之和为 $O(c+n+b_q+1)$，所以给出第三行。

接入前后的原 Next 数字计算可用第8节的有限贪心算法，每步 $O((d_0+c+1)^2)$ 位操作；全部前缀扩展、输入、事件与控制处理至多再按 $r+m+d_0+1$ 个这样的项计。$n\le W_0$，初始尺度寻找、安装 $q$、候选比较、末尾记录输出都被第一行覆盖。生产者的原始前缀、服务的私有单位、接收者两份尺度寄存器、各自控制、缓存与复用 scratch 同时存在，仍总共 $O(P+W_0)$ 位。加入源后端与驱动者实际项才得到完整系统费用，不能将两个组件分别取峰再忽略其同时存在。有限服务承诺只保证每个已到达调用有限结束，没有给物理等待的统一期限。证毕。

**定理 19.3（后续任意有限调用的资源与真实游标）。** 取得后执行任意有限的定义18.1命令序列，令 $J$ 为全部新增真实 Next 数，包括 LiveStep、Seek 内部 Step 和预算内 Tick，$Q$ 为请求数，$d_{\max}$ 为该段实际最大原始深度。设 $L_{\max},H_{\max}$ 为这段有限请求所用的最大参数，无相应参数时取零；记 $\ell$ 如定义8.1，并置

$$
W=d_{\max}+b_q+\ell(L_{\max})+\ell(H_{\max})+c+32.
\tag{77}
$$

不再请求 Extent 的上述实现，其新增本地工作与同时数字存储分别可取

$$
\begin{aligned}
C_{\rm use}&=O\left(I+(J+Q+1)(W^2+c)+B_{\rm out}\right),\\
S_{\rm use,peak}&=O(P+W).
\end{aligned}
\tag{78}
$$

该段新增原始 Read 恰为 $d_{\max}-d_*$，额外生产者事件恰为 $J$ 个三元组。达到的生产者完整有限字段始终是定义2.2在真实 $(p',r+m+J)$ 的原字段，原始端点恰在 $|p'|=d_{\max}$，绑定未替换，未读尾恰为 $\operatorname{tail}_{d_{\max}}x$。接收者只持有 (69) 的更新及显式预算字段，没有获得未披露的历史字段或全源。

证明。深度单调，真实每块各读一次，故新增原始计数精确。绝对返回数小于当前 $G_{d+1}$，本地计数也不超过它；其二进制宽度与所有权重、有限代表均为 $O(W)$。定理18.2每步的 (70)、权重与边界更新可用第8节的相邻权重贪心算法，$O(W^2)$ 位工作、$O(W)$ 空间。对立即拒绝的 Peek，若 $\ell\ge d$，正深度下已有 $G_\ell-1>\delta$，可先以二进制比较拒绝，无需生成巨大 $G_\ell$。合法 Peek 有 $\ell\le d-1$，计算并写出其实际有限代表在同一界内。

Seek 的阈值准备通过相邻权重迭代；停止时 $D+1\le G_{d'-1}$，故 $a\le d'-1\le d_{\max}$，所生成的权重指标与位宽都在 $O(W)$ 内。$L=H=0$ 不生成阈值；正 $L$ 时 $a\ge L$，同样控制 $G_L$ 的生成。静止 Arm 则先执行定义18.1的参数比较，只有 $L<d$、$H\le\delta$ 时才计算余下守卫，因此巨大但必拒绝的参数也不引入超出 (77) 的权重。Seek 内部每个 Step 都计入 $J$，不存在免费循环。装入／递减预算、请求扫描、拒绝、源调用描述符与 scratch 清零计入 (78)。每次只生成被请求的当前答案，不预先物化全部 $H+(H+1)L$ 位的 DATA 表；若要求该表，则另加其实际计算、写入与保留费用。

最后的真实字段与尾由逐步应用定理3.2及18.2得到。服务私有 $q$ 即使此段不再使用也仍算其实际保留的 $b_q$ 位；初始边界描述的位数不超过 $O(d_{\max}+1)$。输出流可丢弃；实际保留档案、驱动者、源及物理后端工作／存储仍按定理19.2另加。本界是对这一有限实际段的事后上界，并非初次取得的四次新原始读取界可反复免费使用。证毕。

## 20. 独立四表示、输入域增益与适用边界

**定义 20.1（本合同的四种意义与已证箭头）。** 空间仍是实际 $T^{r+i}x$ 的无限位置配置，时间仍是实际 Emit、Advance、Return 的先后；接收者只计交接后的次数，未取得接入前事件。边界仍是生产者实际付费原始前沿的当前兼容相位区及其墙上所含 lift，空前沿为整圈。记忆是实际保留的 (69)、预算、有限缓存与活权利，不含丢弃事件或未读原始尾。这四者分别选择位置、事件顺序、几何允许区和可持续调用记录，没有将每个视图都定义为全历史的副本。

定理17.3建立的是“实际尺度读数与本地付费动作时序”的联合取得箭头：它得到接入边界及实际达到边界的有限记忆。时序在这里不是免费给出的目标寿命标签；$t_1,t_2$ 是每次真实 Step 返回后取得、按 (63) 识别的更新位置。定理18.2使取得边界的更新与同一源的实际事件动力交换；定理18.3在原 DATA 守卫内给空间读数与时间发射的路线一致，并在不足时以真正移动来源的 Seek 取得新的有限任务域。空间本身不提供调用权；有限边界或记忆也不等于无限空间。

**命题 20.2（与已知单位和已供参考任务的准确比较）。** 下列输入与能力差别属于定理的假设，不能彼此替换。

| 合同 | 取得前给接收者的观测 | 动作与所得结果 |
| --- | --- | --- |
| 定义13.1、14.1 | 有已知原点、方向及单位的有序近似双墙相位 | 同一 proper 目标全程暂停；有限恢复其坐标，旧 Arm 守卫内使用 |
| 已知单位的单尺度 | $q$ 已知的当前 $q\alpha^d$ 的近似值 | 静止时可分辨离散深度；单尺度没有 $s$，不是有序双墙的替代输入 |
| 定义16.1–16.2 | 仅一个近似尺度通道；无相位、深度、单位值或单位界 | 独占地推进真实 Next；两次更新后回溯初始边界并取得实际新边界；继续 LiveStep 与有限 Seek |

证明。第一行恰为旧定义的范围。第二行的精确深度单射由命题16.3；近似取得可在已知 $q$ 下逐精度隔离 $q\alpha^d$：正的读数下界先排除足够大深度，再在剩余有限集合隔离真实值；同深度的不同 $s$ 始终同值。第三行由定理17.3、18.2、18.3。若给第三行关闭 Step，仅保留静止尺度，则命题16.3的深度障碍重新出现。这表明新的输入减少与新的控制权共同承担增益；不是宣称第三行在全部资源坐标上支配第一行。证毕。

已证的实质增益是未知固定有理单位、无相位原点的整个实际达到类上的主动精确取得，以及它与同一付费端点跨更新继续运行的组合。未知单位与无相位输入没有被重新命名为已校准双墙；不需要发送源深度、完整历史或精确墙标。两次读取新块之间的完整实际寿命补足静止尺度所丢的离散深度，第一次更新时间补足同深度的 $s$。为此真实支付时间推进和至多四个新原始位，而旧暂停任务不需要推进。第18节的 DATA 计算、贪心展开、合法尾续接和 (70) 的分支发射供应均是既有结果的实际消费，不单独计为新数学。

本构造只为所声明任务解释所需资源：一个正尺度参考及其误差分辨率、同源固定单位、完整返回顺序、独占真实 Next、两个更新时刻的计数，以及持续存在的绑定／权利。被消去的是接收者侧的单位数值和相位原点，未被消去的是这些操作与关系。没有证明两次更新、常数1024、四个新位、所给时间或存储上界最优；也没有把两种块符号的名字当作无序、无控制的普适最小生成元。

**定义 20.3（不能从本合同推出的边界）。** 初始边界恢复不选择 (42) 的实际历史成员；本地计数不等于从原初始化开始的认证计数；回溯边界不回滚来源。整个无限当前配置和原始未知无限输入没有恢复，任意无限任务也没有一次有限完成证明。每个有限命令序列有有限运行，不意味着所有有限序列有一个统一的空间或物理时间上界；原始前缀、深度及计数可以不断增长。

如果单位在取得中未知地变化，实际尺度比为 $(q_{i+1}/q_i)\alpha^g$，(62) 不再是代码表。例如一次本来不读取的 Step 若将有理单位加倍，真实尺度比成为二，(63) 在足够精度下没有候选。这里只说明固定单位在该证明中的具体用途，不推出所有变化单位协议均不可能。若有未观察到的并发 Advance，则 $t_2-t_1$ 不再是同一完整寿命，(65) 的证明同样失效。任意持续运动目标、任意错误区域／弧长补集、未认证来源承诺、revocation 与并发客户端均无本节定理。

尺度比与有限寿命的观察证明在数学上只使用固定 $q>0$；若另一个实际实数传感器确实满足 (61) 及每次有限返回，同一正确性与停止论证可条件地应用。但 (73) 只实现有限有理配置，不制造任意实数单位的生成器，也不证明物理仪器校准、空间区域读出或任意实数读口可供。单位可无限小或大，(75) 因而含实际 $b_q$；接收者事前没有统一位成本界。未知加性相位原点没有被恢复：本结果输出的是原定义中内禀坐标的边界，而非未建桥的物理仪器坐标。

## 21. 来源与未决义务的原范围

**定义 21.1（供应及本节内容的归属）。** 第16–20节为 `repo-derived` 的普通数学推导，不作新的 Lean 核验或世界原创性声明。下表给出承担证明的既有供应与不作的迁移。

| 来源 | 精确消费与界限 |
| --- | --- |
| 本卷定理3.1、3.2、4.1及第8节 | 真实原始流、每次 Next 的有限性、实际表示 $T^rx$、强制零费用、尾续接与有限贪心算术。没有重新证明它们，也未给无限后端免费生成器。 |
| 本卷定理12.2、12.3，RRO20.2、20.6、24.2、35.1 | 内禀坐标、闭端点、完整寿命、出生余量与实际新块的运输。新取得用实际寿命测量识别未知深度，不将时钟倒代本身称作新发现。 |
| 本卷第13–15节 | 旧已校准双墙全回复译码、数字 Park/Wall 与守卫内使用，是正面既有供应。新的实际尺度／Step 合同改变了观测与控制，并没有改判旧未知旋转碰撞或其暂停域。 |
| [NativeAcquiredPrefixCylinder][NAPC] 及 owning Scribe、State、Reconstruction | 真实付费前缀与完整状态、准确未读尾重启及其私有调度／尾引理是既有供应；其 controller 不是本卷的算术 successor。 |
| [SignedSeriesFibres][SSF] 与 owning Scribe；[Golden slope separation][ISF] 与 owning Scribe | 前者提供真实 seam 的端点分类，已通过旧墙公式消费。后者含私有有限预算分离供应，但本节不以未界定的标号穷举或该标量间距代替主动寿命取得。 |
| [FibonacciFactorCompletion 的坐标桥][FFC-COORD] 与 owning Scribe，及 BranchStorage、EndpointNecessity、FixedGraphMargin、OriginalPieces、UnboundedReturnCount、UnboundedCriticalStorage | 原 OperationOmega 量化全路径、支撑与仿射递推；坐标桥得到同一合法 digit stream 的 $3p$ 位删除坐标，支撑有界性迫使其 series 相等。其余模块在各自 literal、误差、尾与完整状态合同下供给实际实现及必要界。它们没有将位置删除输送为本卷的 $T$，本节不借它们名字声称算术续接、未知单位恢复或新的下界。 |
| [PVC][PVC]、[CSA][CSA]、[AIF][AIF]、[OA][OA] | 已有实际转换、独立 view 意义、取得、绑定与继续合法调用。第16节明确给本卷新端口的实际对应，不把“已有 converter”误当缺失，也不从这些不同历史模型自动导入本节桥。 |
| [Boundary Dynamics §§36.1–36.6][BD-ACTIVE]，InterfaceKernelCriterion 与 predictive quotient | 实际像、输出／合法性／后继不变性及反向历史的附加条件是已有判据。本节给具体同源实现与停止证明，不新增通用商包装，未主张四个全视图核相等。 |
| [Weihrauch Complexity in Computable Analysis, Definition 9][WCA] | `literature-attested`：可计算度量空间及 Cauchy 表示解释逐精度名字。这里只用作近似输入的标准背景；固定单位下三比隔离、两次更新的全来源停止与实际付费实现均由上文证明，不归给通用表示定理。 |

[FIB common-parent geometry][FIB-PARENT-ACTIVE] 的 $J/M$ 三次共同父及两种已实现混合子，和 [FIB acquired-record field reconstruction][FIB-FIELD-ACTIVE] 的严格二次低响应域，使用不同的矩阵源、gain、观测与停止规则；本节没有建立到 (60) 的对应，不转移其精确实数唯一性为有限位尺度译码器。它们各自的共同第五历史、一般取得域下降及有效有限位解码未决域保持不变。

本卷第9、11、15节列出的原范围继续成立。新端口不是原事件专用接口自动拥有的能力，也不是旧暂停端口在不改变许可下自行增加的权利；旧 $G_{\rm gc}$、original-$Q$、parked-consumer、unchanged-initialization、完整原响应与任意 interior-cut 义务均保留原假设。已经证明的尺度取得与活接口不结算那些模型，也不结算一般四表示相互恢复。长期共同关系结构目标仍包括这些缺口与独立物理实现桥。

[FFC-COORD]: ../../../D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.lean
[BD-ACTIVE]: RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md
[FIB-PARENT-ACTIVE]: https://github.com/the-omega-institute/trureturing/blob/4c1cd22ecfc184551487ff80c0baaed324f1274d/docs/develop/theory/FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md
[FIB-FIELD-ACTIVE]: https://github.com/the-omega-institute/trureturing/blob/4c1cd22ecfc184551487ff80c0baaed324f1274d/docs/develop/theory/FIB_QUADRATIC_RECORD_FIELD_RATIONAL_RECONSTRUCTION.md

## 追加锚（本行以下为增补区）

## 22. 未知加性零点的仿射尺度合同与两个恢复任务

**定义 22.1（同源固定仿射读口）。** 保留定义1.2、2.2、16.1的全部实际接口：任意固定 $x\in K$，从原空前沿初始化的时钟生产者，在任意有限实际返回 $r$ 交接独占持续调用轮；每个到达的原始 Read 有限完成，经过的一后的强制零也实际读取。只有实际 Next 中的 Advance 推进来源，每次 Step 仍完整交付实际 Emit、Advance、Return，暂停、Extent 及内部计算均不推进。交接确认、程序、绑定和权利安排与源无关，不发送深度、历史、绝对计数、原始读取数或延迟。接收者只计交接后的 Step，不能倒带、重读初始切口或请求私有状态。

将 (61) 的读口替换为以下仿射合同。私有配置为固定有理数

$$
q=A/B>0,\qquad b=C/F\ge0,
\qquad A,B,F\in\mathbb N_{>0},\quad C\in\mathbb N.
\tag{79}
$$

四个整数在初始化时实际安装，与原始源无关；同一运行中不随调用、来源推进或误差选择改变。接收者不知道它们，也没有它们的上下界或编码长度。沿用定义16.2的整数编码约定：Extent$(n)$，$n\ge1$，返回完整有限非负整数 $a$，其解码读数为 $u=a2^{-n}$，满足

$$
|u-(b+q\alpha^d)|\le\varepsilon_n,
\qquad\varepsilon_n=2^{-n},\qquad \alpha=(\sqrt5-1)/2.
\tag{80}
$$

误差约束施于这个 dyadic 解码值，不施于未缩放的整数码 $a$。整数部分不取模、不溢出、不饱和；全部有效位均发送并收费。每次 Extent 在同一个生产者的当前真实返回有限结束，不读原始位，也不发 Advance。各次误差可以依赖全部过去，允许闭误差端点，不要求独立、嵌套、无偏或指定舍入。共同承诺是同一 $q,b$、同一当前付费区域的 $\alpha^d$ 和已知绝对误差 $2^{-n}$。未知仿射零点 $b$ 是读口的加性零点，不是另给一个可观察的相位原点。

**定义 22.2（入口目标、达到目标与活记录）。** 接入时的真实但未提供坐标记为 $(d_0,s_0)$，空前沿取 $(0,0)$；入口目标是定义16.1的 $\partial_0$。本地第 $i$ 次 Step 返回后的当前来源为 $T^{r+i}x$，真实付费前沿的边界记为 $\partial_i$。达到恢复要求接收者在某个有限实际返回 $m$ 输出当时的 $\partial_m$，包括区域、墙角色及两墙所含的具体 lift，并仍实际持有同一来源的持续调用权 $\kappa$。这不要求 $\partial_m=\partial_0$，也不把来源移回入口。

达到后的接收者记录取

$$
\mathfrak a_{\rm aff}=(d,s,i;\kappa).
\tag{81}
$$

它是 (69) 的当前部分；静态字段 $\partial_0$ 未取得，不用一个任选历史或边界填充。生产者仍保留自己的原有限寄存器、实际原始前缀和未读端点，(81) 不宣称把这些私有历史字段全部复制给接收者。第18节的 LiveStep、Peek、Seek 及可选 Arm/Tick 只消费当前部分和显式预算，故可对 (81) 使用相同定义；其权限来自实际交接，不能由输出记录创造。

## 23. 相邻差分、逐级首次检测与一次局部校准

**引理 23.1（闭误差差分与下一次下降的统一下界）。** 在一个实际 Step 前后各以同一精度 $n$ 读一次 (80)，记读数为 $u,v$，观测下降为 $h=u-v$。若步前真实深度为 $d$，该步新增原始长度为 $g\in\{0,1,2\}$，则真实下降和误差满足

$$
\Delta=q\alpha^d(1-\alpha^g),\qquad
|h-\Delta|\le2\varepsilon_n.
\tag{82}
$$

故严格测试 $h>2\varepsilon_n$ 从不把不续块的 Step 判为续块；$\Delta>4\varepsilon_n$ 时一定检测到真实续块，包括任意允许的误差端点。如果一次检测给出

$$
\lambda=h-2\varepsilon_n>0,
\tag{83}
$$

则 $\Delta\ge\lambda$。设该续块长度为 $g_1\in\{1,2\}$，到紧接着的下一次真实续块为止配置不变，下一块长为 $g_2\in\{1,2\}$。下一次真实下降满足

$$
\frac{\Delta_{\rm next}}{\Delta}
=\alpha^{g_1}\frac{1-\alpha^{g_2}}{1-\alpha^{g_1}}
\in\{\alpha,1,\alpha^3,\alpha^2\},
\qquad
\Delta_{\rm next}\ge\alpha^3\lambda>\lambda/5.
\tag{84}
$$

证明。固定 $b$ 在相减中精确抵消，两个绝对误差的差至多 $2\varepsilon_n$；固定 $q$ 和定义2.2的块长给 (82)。$g=0$ 时 $\Delta=0$，所以 $h\le2\varepsilon_n$；正下降大于 $4\varepsilon_n$ 时，$h\ge\Delta-2\varepsilon_n>2\varepsilon_n$。所有严格号均来自判据本身，没有去掉误差球边界。由 $h-\Delta\le2\varepsilon_n$ 得 (83) 的下界。第二个续块前深度恰为 $d+g_1$，将两个下降相除得到 (84)。用 $\alpha^2=1-\alpha$ 逐一代入四种 $(g_1,g_2)$ 即得所列集合；$\alpha>3/5$ 给 $\alpha^3>1/5$。本引理不由一次下降识别 $g_1$，也不把不同来源各自可达的比值拼在一起。证毕。

**定义 23.2（只使用实际相邻返回的取得规则）。** 接收者从交接后的本地计数零开始，执行以下两段有限帧交互，所有 Step 都是同一独占生产者的真实 Next。

第一段的阶段编号为 $j=1,2,\ldots$。在阶段 $j$，置 $n_j=j^2$，于当前暂停返回请求 Extent$(n_j)$ 得 $u_j$；执行恰一个 Step，完整交付其实际三元组，本地计数成为 $j$；再暂停并请求 Extent$(n_j)$ 得 $v_j$。当且仅当

$$
h_j=u_j-v_j>2\,2^{-j^2}
\tag{85}
$$

时结束第一段，记首次命中的本地调用号为 $\tau$，并计算 $\lambda=h_\tau-2\,2^{-\tau^2}>0$。未命中的读数与已处理事件可以丢弃。未命中只表示没有证实本步续块，不被记录为“本步没有续块”。

在第 $\tau$ 次 Step 的当前 Return 保持暂停，以有限整数比较选择

$$
n_* =\min\{n\ge \tau^2:32\,2^{-n}<\lambda\},
\qquad \varepsilon_*=2^{-n_*}.
\tag{86}
$$

请求一次 Extent$(n_*)$ 作为新的步前基线 $u$，令 $w=0$。第二段重复：执行一个真实 Step，保留这一调用的 Emit 位 $e$ 直至测试结束，完整交付 Advance、Return；令 $w$ 加一；在其当前返回请求 Extent$(n_*)$ 得 $v$。若 $u-v\le2\varepsilon_*$，以 $v$ 替换 $u$ 后继续；否则在这一真实 Return 保持暂停，记 $t_2=\tau+w$、$e_*=e$，不再请求仿射读数。选择精度不做 Step，不给来源推进时间；两个相邻固定精度测试可以共用中间返回的同一个读数。

**定理 23.3（任意源、任意允许误差的有限首次检测与紧邻下一次检测）。** 对所有定义22.1的 $x$、实际接入返回、固定 $q,b$ 和满足 (80) 的全部自适应回复序列，第一段在有限 $\tau\ge1$ 结束，且其第 $\tau$ 次 Step 确为真实续块。(86) 以有限算术完成，且

$$
\tau^2\le n_*\le \tau^2+6.
\tag{87}
$$

第二段不产生虚假续块，并恰在第 $\tau$ 次 Step 之后的下一次真实续块返回结束，中间没有漏检续块。

证明。无误报由引理23.1直接得到。为证明第一段有限，沿尚未停止时的真实运行记阶段 $j$ 步前深度为 $d_{j-1}$。每步最多增加二，故

$$
d_{j-1}\le d_0+2(j-1).
$$

在真实续块阶段 $j$，由 $1-\alpha^g\ge\alpha^2$ 及 $\alpha>1/2$，

$$
\Delta_j\ge q\alpha^{d_0+2j}>q\,2^{-d_0-2j}.
\tag{88}
$$

取某个有限整数 $h_0\ge0$ 使 $q>2^{-h_0}$；它只用于证明，不提供给接收者。对一切充分大的 $j$，整数不等式 $j^2>d_0+h_0+2j+2$ 成立，故 (88) 给 $\Delta_j>4\,2^{-j^2}$。例如从 $j_0=d_0+h_0+4$ 起均成立。在任何有限返回，当前前缀的死亡时钟有限；顺次 Next 在有限步后必到死亡再真正读下一块，空前沿则下一步即读。因此若第一段尚未结束，阶段 $j_0$ 以后必在有限步遇到一次真实续块。该阶段由引理23.1必命中，矛盾于永不结束。每个此前 Read、Next、Extent 和整数计算都有限，故这是一个实际有限搜索，不是已知深度或单位界下才存在的停止点。平方精度保证 (88) 中可能的指数下降仍被误差压过；仅说“逐渐加精度”不足以替代此估计。

同精度整数码之差使 $h_\tau-2\,2^{-\tau^2}$ 是 $2^{-\tau^2}$ 的正整数倍，故 $\lambda\ge2^{-\tau^2}$。取 $n=\tau^2+6$ 即有 $32\,2^{-n}=2^{-\tau^2}/2<\lambda$，证明 (87)，也给 (86) 的有限搜索界。

第一命中是真实续块，其后的前沿处于出生返回。在下一次真实续块之前，深度和仿射真值不变，任意两个所用读数的差均至多 $2\varepsilon_*$，即使误差相互依赖也不可能误报。下一次真实续块的下降由 (84)、(86) 满足

$$
\Delta_{\rm next}>\lambda/5>(32/5)\varepsilon_*>4\varepsilon_*.
\tag{89}
$$

所以该调用必被检测。其出现由同一有限死亡时钟和生产性保证。此归纳只保证本次相邻下一续块的完整识别；没有把同一个固定精度无条件推广到无限多次以后越来越小的下降。证毕。

## 24. 完整寿命、真实发射与达到边界的持续使用

**定理 24.1（未知仿射零点下的达到恢复）。** 定义23.2对定义22.1的所有实际源、所有接入点、所有固定配置及所有允许回复有限停止。令 $D$ 是第一命中续块后的真实深度，$g\in\{1,2\}$ 是第二段结束调用的真实块长，则接收者仅用已经取得的数据恢复

$$
w=G_{D-1},\qquad
d_*=D+g,\qquad s_*=G_{d_*}-1,\qquad
m=\tau+w.
\tag{90}
$$

它输出准确的当前 $\partial_m=\partial(d_*,s_*)$、(38)、(40) 的墙角色及实际拥有的 lift，保留同源活记录 $(d_*,s_*,m;\kappa)$。生产者的真实当前来源是 $T^{r+m}x$，实际未读端点是 $\operatorname{tail}_{d_*}x$，其原字段与绑定未被替换。该结果不输出入口边界。

证明。由定理23.3，两次命中确为相邻的两个真实续块，且第一次返回后深度 $D\ge1$，坐标恰为 $(D,G_D-1)$。定理12.3及 (68) 给出生余量 $G_{D-1}-1$。先完成这些不读取的 Step，再完成下一次真正续块的 Step，恰用

$$
(G_{D-1}-1)+1=G_{D-1}
$$

次调用；定义23.2的 $w$ 正好计全这段寿命，包括末次 Emit、Advance、Return。严格递增且无界的 $G_j$ 可用相邻两个权重顺次生成，有限且唯一地找到满足 $w=G_{D-1}$ 的 $D$。$D=1$ 时 $w=G_0=1$，没有中间不读取调用，末步仍计入。

尚须识别末次续块的长度，差分测试本身没有给这个标签。其调用前的真实坐标为 $s^-=G_{D+1}-2$。定理18.2的两个不同常值为

$$
c_0=\operatorname{Low}(G_{D+1}-2),\qquad
c_1=\operatorname{Low}(G_{D+1}-2+G_D)
=\operatorname{Low}(G_{D+2}-2),\qquad c_0\ne c_1.
\tag{91}
$$

与已经保留的实际 $e_*$ 比较，$e_*=c_0$ 给 $g=1$，$e_*=c_1$ 给 $g=2$。这里使用的是结束该完整寿命的“下一次续块调用”中的那个真实 Emit：它已在第二次检测前实际发生，保留至 $D$ 算出后才解释。不是请求未来位、另做免费调用，或把任意中间不续块的 Emit 当成分支标签。由出生转移 (48) 得 (90) 的新坐标。

定理12.2据当前坐标唯一给完整边界，故恢复的是实际拥有墙点的区域，不是任取同长度的弧，也不假设相位映射在分裂墙上单射。定理3.1、3.2保证每次 Step 是对原来源的真实执行，新增原始字来自它自己的真实尾；暂停计算没有换成 (42) 中的另一历史。生产者最终字段仍为原运行在 $(p_m,r+m)$ 的字段，$|p_m|=d_*$，接收者不需知道 $p_m,N_{p_m}$ 或 $r$。这些事实给原始游标、当前来源及持续绑定的结论。证毕。

**推论 24.2（不再查询仿射读口的有限活使用）。** 从定理24.1的记录出发，任意有限、可自适应的第18节 LiveStep、Peek、Seek 及合法可选预算命令序列均有限完成，不需要新的 Extent，也不需要恢复 $q,b$ 或 $\partial_0$。每个当前边界及其端点归属按真实事件更新，每个写出的空间答案属于所注明的真正达到切面。

证明。定理18.2只用当前 $(d,s,i)$、实际下一 Emit 和持续权利；正余量时不读原始位，零余量时用 (70) 识别同一个生产者实际新读的块。因此 (81) 逐步保持真实对应。定理18.3的 Seek 有限进展、原 DATA 守卫 $D(L,H)\le\delta(d,s)$、代表 $Z(s)$、拒绝与预算论证均只消费这一当前记录，不消费 (69) 的静态 $\partial_0$ 字段。逐命令归纳即得有限序列结论，包括零余量、纯交替来源和墙点塌缩。Seek 仍可能付费移动来源，它不在原暂停切面无条件回答；释放也不复位源或复制权利。证毕。

**定义 24.3（精确剩余的入口义务）。** 在同一个 (79)–(80) 合同下，入口问题是：是否存在一个源无关的因果接收者，对所有 $x\in K$、所有实际有限返回接入点、所有固定有理 $q>0,b\ge0$ 及全部允许回复序列，经过有限实际操作停止，并精确输出原 $\partial_0$，包括墙角色和拥有的 lift？允许它选择有限精度、暂停、内部计算及真实 Step，观察全部约定的交接后事件；不额外提供初始重读、rewind、深度、绝对计数、私有字段或计时。此存在命题及其否定在这里均保持 open。

定义23.2的 $\tau$ 只是首次被证实的续块，并非首次真实续块。此前 (85) 不命中与某次真实下降 $\Delta\le4\,2^{-j^2}$ 相容；初始尺度可任意小，有限粗精度没有排除这种情形。故 $\tau$ 之前的未知续块数及长度没有被该证明恢复，不能把 $D$ 减去一个已知首块长就当成 $d_0$，也不能把 $\tau$ 当成 $\delta_0+1$ 来使用 (66)。两次命中间的完整寿命只标定第一命中之后的 $D$。达到处没有初始读口副本，原端点也没有倒带。以上解释限定这个构造的结论；它不是对所有其他因果接收者的不可能性证明。若要否定上述入口存在命题，仍须给出满足同一有限误差合同、各自固定有理配置、全部实际事件和合法有限自适应交互的完整不可区分见证，不能用一个精确实数碰撞或尚未核清的有限误差候选替代。

## 25. 同次实际运行的读取、数字服务与继续费用

**定义 25.1（有限仿射服务及计费参数）。** 保留定义8.1、19.1的固定数目顺序二进制工作带、有限帧、描述符与调用检查。令 $b_q$ 为 $A,B$ 的实际二进制负载长度之和，$b_b$ 为 $C,F$ 的相应长度之和，零的负载长度取一。私有配置共 $b_q+b_b$ 位，不能因接收者不知道它们而省略。$P$ 包含固定程序、帧约定、仿射服务及接入／释放协议的安装位；$c$ 控制同时实际存在的端点、模式与权利描述符长度。

一种满足 (80) 的实际数字服务读取自身当前深度缓存，以定义13.2、19.1的精确二次整数算术计算

$$
a=\left\lfloor 2^n\left(C/F+(A/B)\alpha^d\right)\right\rfloor.
\tag{92}
$$

它不查询另一个来源、不输出 $d,q,b$，也不取得原始位。该实现的误差严格小于 $2^{-n}$；定理23.3、24.1仍对 (80) 的全部闭误差回复成立。若后端采用其他允许回复选择机制，须另计它实际增加的计算、存储与传输，不把这个机制假定为免费。初始化仅增加源无关的有限服务配置和程序，原始 cursor-zero、空前沿、return-zero、不做初始 Read／Advance 的规则保持定义1.2；这个显式扩展不等于在一个不许扩展初始化的旧接口中已经拥有 Extent。

**定理 25.2（完整取得的同次精确逻辑数与数字上界）。** 在定理24.1的同一次实际运行中，接入前有 $r$ 次 Next 和 $d_0$ 个原始已读位。记第一命中号 $\tau$、第一命中后深度 $D$、第二块长 $g$、固定精度 $n_*$、$w=G_{D-1}$ 及 $m=\tau+w$。则

$$
\begin{aligned}
Q_{\rm Extent}&=2\tau+1+w,\qquad N=\max n=n_*\le \tau^2+6,\\
\#\operatorname{Step}_{\rm after\ handoff}
&=\#\operatorname{Emit}_{\rm after\ handoff}
=\#\operatorname{Advance}_{\rm after\ handoff}
=\#\operatorname{Return}_{\rm producer,after\ handoff}=m,\\
\#\operatorname{Read}_{\rm after\ handoff}
&=d_*-d_0=D+g-d_0,\qquad d_*\le d_0+2\tau+2.
\end{aligned}
\tag{93}
$$

截至取得返回，原生产者总三元组数为 $r+m$，原始 Read 与交付位数均恰为 $d_*$。每个被经过的强制零包括在内；第一段漏检的真实续块也包括在内，不能沿用 (67) 的“最多四个新位”。Extent 的 $Q_{\rm Extent}$ 个实际返回与交接确认、初始化确认另外分帧，不算作源 Advance 或生产者三元组。

置

$$
\Omega=d_*+b_q+b_b+N+c+32.
\tag{94}
$$

对于 (92) 的数字实现，流式输出并丢弃已处理事件时，一组保守上界为

$$
\begin{aligned}
C_{\rm digital}
&=O\left(P+b_q+b_b+I+
(r+m+d_*+Q_{\rm Extent}+1)\Omega^3+B_{\rm out}\right),\\
S_{\rm digital,peak}&=O(P+\Omega),\\
B_{\rm affine+control}
&=O\left((Q_{\rm Extent}+m+1)(c+N+b_q+b_b+1)\right).
\end{aligned}
\tag{95}
$$

$I$ 是实际数字请求输入，$B_{\rm out}$ 是实际选择写出的全部结果、事件、确认及其帧。第三行专计交接后的仿射请求／回复、Step 控制与交接帧；原始回复的 $d_*$ 位及生产者三元组负载 $6(r+m)$ 位另列，并实际支付各自通道 framing。最终边界标签与本地计数有 $O(d_*+c+1)$ 位。若要求保留全部轨迹、仿射回复、原始字副本、历史成员列表或完整 DATA 表，其实际生成、输出与同时存储另加。

完整系统还须加实际安装／绑定的非数字费用、驱动者自身命令取得与计算、源后端的 $\iota_x+\gamma_x(d_*)$；同时峰值存储另加驱动者实际工作区、$\sigma_x(d_*)$、额外误差机制及外部保留输出。逻辑 Read 原语的计价和实际位负载保持独立坐标；没有把无限源的配置、材料或生成器视为零成本。

证明。第一段每阶段恰两次 Extent 与一次 Step，共 $2\tau$ 和 $\tau$ 次；固定精度基线一次，随后 $w$ 次 Step 各读一次，得第一行及 $m$。所有原始位恰在真实续块中顺次读一次，深度单调，故新增 Read 是游标差。第一段最多 $2\tau$ 位，第二段恰下一块 $g$ 位，给深度界。未知早期续块不需要另猜计数，已被该游标差完整记账。

有 $2^{-b_q}<q<2^{b_q}$、$0\le b<2^{b_b}$。任意允许回复的整数码满足

$$
0\le a\le2^n(2^{b_b}+2^{b_q})+1,
\tag{96}
$$

故宽度为 $O(N+b_q+b_b+1)$；大的加性零点虽然在 (82) 中消掉，仍扩大实际回复和配置，不能在费用中消掉。$\alpha^d$ 的二次整数系数有 $O(d+1)$ 位；清除 (92) 的分母后，所有整数有 $O(\Omega)$ 位。相邻幂系数生成、grade-school 乘除与二次符号比较使用 $O(\Omega)$ 可复用空间，每次符号比较至多 $O(\Omega^2)$ 位动作，有限整数区间的二分取整至多 $O(\Omega)$ 次比较。因而每次 Extent 的保守界为 $O(\Omega^3)$ 工作和 $O(\Omega)$ 空间。

第一段阶段号和本地计数不大于 $m$；达到时 $r+m\le k_{p_m}<G_{d_*+1}$，所以这些计数及全部生产者缓存只有 $O(d_*+1)$ 位。生成 $j^2$、比较 (85)、计算 dyadic $\lambda$ 及选择 (86) 均是有限宽度整数操作，不要求保存前面 $j$ 个读数。第二段只保留一个基线、当前回复、$w$ 和最新 Emit；解出 $D$ 的权重搜索至多 $O(d_*^2)$ 位动作，(91) 用既有有限 Low 算术。原 Next、原始前缀扩展、scratch 清空、请求定位与完整 I/O 由第8、19节的相同有限算术界计入 (95)。生产者前缀、四个私有配置整数、接收者两份读数、计数、缓存、所有描述符及工作区同时存在，其和仍为 $O(P+\Omega)$；这不是分别取各组件峰值后遗漏并存项。每个帧宽由 (96) 控制，给第三行。最后加上真实源、驱动者和保留输出才是完整系统费用。证明中的停止界依赖实际 $q$ 与初始深度，(93)–(95) 是实际同次运行的界，不给独立于 $q,d_0$ 的统一最坏取得成本或物理时限。证毕。

**推论 25.3（后续使用仍付真实新增费用）。** 对推论24.2的一段有限使用，令 $J$ 为所有新增真实 Next 数，$Q_u$ 为有限请求数，$d_{\max}$ 为实际最大深度，$L_{\max},H_{\max}$ 为该段所用最大参数，无相应参数取零。以定义8.1的 $\ell$ 置

$$
W=d_{\max}+b_q+b_b+\ell(L_{\max})+\ell(H_{\max})+c+32.
\tag{97}
$$

该段 Extent 数为零，生产者新增三元组数恰为 $J$，新增原始 Read 及交付位数恰为 $d_{\max}-d_*$。保留仿射服务配置时，新增本地工作及同时数字存储可取

$$
C_{\rm use}=O\left(I_u+(J+Q_u+1)(W^2+c)+B_{{\rm out},u}\right),
\qquad S_{{\rm use},\rm peak}=O(P+W).
\tag{98}
$$

证明。逐步使用定理18.2、18.3及19.3的相同实现；(81) 没有引入额外历史计算。全部 Seek 内部 Step 与预算内 Tick 计入 $J$，正余量的无读步骤不抵消零余量的新读；强制零仍计入深度差。静态服务配置中的 $b_q+b_b$ 即使不再使用也计入同时存储，取得阶段的旧读数与精度搜索字段可丢弃。请求、拒绝、结果与输出仍完整付费。全运行直到 $d_{\max}$ 的后端成本是其实际 $\iota_x+\gamma_x(d_{\max})$ 与 $\sigma_x(d_{\max})$，而非只计取得时的前 $d_*$ 位；驱动者、绑定、物理安装与外部档案同样保留原收费范围。这里不对无限命令序列给一次有限总费用。证毕。

## 26. 四种意义、精确箭头与供应边界

**定义 26.1（本仿射合同中的四种意义）。** 空间是实际当前无限位置配置 $T^{r+i}x$，有限空间任务是其真正当前 $q_L$ 与 (1) 的有限 DATA。时间是实际 Emit、Advance、Return 的先后；接收者只取得交接后的后缀及本地计数，不取得原初始化以来的完整事件史。边界是生产者实际已付费原始前沿的当前兼容区与两墙拥有的具体 lift，初始空前沿为整圈；它不是任意物质边界。记忆是实际保留的有限控制、缓存、(81)、显式预算以及持续绑定／权利；未读尾、丢弃事件和数学上存在的过去不算接收者已保留的记忆。这四种意义没有各自复制全历史。

本合同供应的取得箭头与继续箭头准确为

$$
\begin{aligned}
&\bigl(\text{同源仿射有限回复，实际本地事件，独占 Step 权}\bigr)
\longrightarrow
\bigl(\partial_m,\mathfrak a_{\rm aff}\bigr),\\
&\bigl(\mathfrak a_{\rm aff},\text{同源下一实际事件}\bigr)
\longrightarrow
\bigl(\text{更新后的真实当前边界及活记录}\bigr),\\
&\bigl(\mathfrak a_{\rm aff},D(L,H)\le\delta(d,s)\bigr)
\longrightarrow \text{该当前切面的有限 DATA 及合法预算内使用},\\
&\bigl(\mathfrak a_{\rm aff},L,H,\text{持续权}\bigr)
\xrightarrow{\text{付费 Seek}}
\text{真正达到的充分切面及其有限空间答案}.
\end{aligned}
\tag{99}
$$

第一箭头通过定理23.3、24.1取得达到边界；它没有入口边界输出。后续箭头由推论24.2承担，均消费真实事件、guard 或实际推进。边界本身不产生权利、不选定未知尾或下一续块，也不输出完整无限空间；记录的当前坐标可以重建相同边界，却不是完整原生产者字段或原历史的逆。单一静止仿射值不是有序双墙输入。这里未声称空间、时间、边界和记忆四个完整 view 的核相等或相互可逆。

**定义 26.2（精确供应与综合推导的归属）。** 第22–26节是这个指定来源与控制器上的 `repo-derived` 理论综合；承重增量是未知加性零点下的全回复首次可靠下降、由该下降校准紧邻完整寿命、再结合实际 Emit 的达到恢复及同源继续使用。差分抵消、有限误差三角不等式、整数算术和 Fibonacci 时钟各为中间工具，不宣称它们是新的一般原理。本节不是物理定理、普适最小性结果或 Lean 认证，也不作全球原创性或文献穷尽声明。

| 精确供应 | 本节实际消费与界限 |
| --- | --- |
| 本卷 §§1–8，尤其定义1.2、2.2及定理3.1、3.2、4.1、8.2 | 原固定初始化、真实顺序输入、强制零、每次有限 Next、实际 $T$、准确未读尾续接、DATA guard 与顺序带位费用；不供应免费的无限来源或调用权生成器。 |
| 本卷 §12，定理12.2、12.3及 (38)–(48) | 达到坐标唯一性、闭端点与侧点所有权、出生／死亡转移及历史纤维。恢复当前坐标不选择纤维中的实际历史。 |
| 本卷 §§16–17，尤其定义16.1及 (68) | 独占持续交接、暂停语义、两次相邻真实续块间 $G_{D-1}$ 的完整寿命。未知零点使旧三比分类不再直接适用；不转移定理17.3的入口结论或四个新位界。 |
| 本卷 §§18–21，尤其定理18.2、18.3、19.2、19.3 | 当前记录的实际 Emit 分支识别、零余量继续、有限 Seek／Peek、数字服务与完整资源边界；(81) 只省略其不被活使用消费的静态入口字段。 |
| [Exact Current Boundary Provenance §§1–9][AFF-PROV] | §§1–3 的同一实际尾续行与具体墙点，§§4–5 的合法命令投影及精确 DATA 域，§6 的全点尾双射与每点历史纤维，§§7–9 的真实分支 Emit、付费有限尾逆及其事件专用比较范围。这里用其区分当前点、边界、历史与实际尾的结论，不将其已知边界前提下的有限尾解码当成未知入口边界取得。 |
| [Boundary Dynamics §§36.1–36.6][BD-ACTIVE] | 实际像、共同核、输出／合法性／后继相容及反向恢复的额外条件。具体 (99) 不等于满足全部共同核条件，更没有由正向达到恢复推出反向入口恢复。 |
| 本卷定义13.2、19.1；RRO20.2、20.6、24.2、35.1；[固定版有限 Zeckendorf 算术][MATHLIB] | 二次整数符号计算、有限 Low、原分割与时钟、标准有限规范展开及唯一性，均在原范围内复用。没有把位置删除换成本卷 successor，或把上游声明的引用算成本次编译。 |

**定义 26.3（保留的原任务与实现义务）。** 原 fixed-$G_{\rm gc}$、original-$Q$、parked-consumer、unchanged-initialization、完整原响应、任意 interior-cut 及完整独立四-view 恢复义务全部保持各自原假设和未决范围。特别是新增仿射读口和持续 Step 权是明确接口前提，不是原事件专用端口、旧停放消费者或不许修改初始化的服务自动具有的能力。入口问题严格保持定义24.3的量词与 open 状态，达到恢复不结算它。

固定 $q,b$、已知误差界、同一当前区域、有限未饱和回复、无未观察推进及持续独占权共同承担证明。若 $b$ 改变，(82) 多出零点差；若 $q$ 改变，(84) 不成立；未观察的 Advance 或并发调用使 $w$ 不再是这一个前沿的完整寿命。本节不从这些证明失效推出一切其他合同均不可能。任意物理传感器的安装、仿射读数确实对应这个付费区域、参考单位／误差保证与实际持续权限仍需独立实现桥。任意实数传感器、撤权、并发、源外变动、无限任务的一次有限完成、任意源的统一有限 provisioning、统一常数存储和与 $q,d_0$ 无关的最坏取得费用均未由本合同供应。

[AFF-PROV]: RECURSIVE_RELATIONAL_OBSERVATION_EXACT_CURRENT_BOUNDARY_PROVENANCE.md

## 追加锚（本行以下为增补区）

## 27. 入口恢复的完整观察与精确量词

**定义 27.1（入口接收者及其完整观察）。** 本节至第30节使用定义22.1、24.3的同一原初始化、原始源、交接与独占持续调用轮。接收者的源操作是已返回切面上的 Extent$(n)$，其中任意有限整数 $n\ge1$ 均可自适应选择，以及真正执行原 Next 的 Step。允许重复查询、有限暂停、任意有限本地计算、实际持有权利的检查、合法释放和停止。释放只有既定的轮次控制效果，不赠送新读口、重新接入或不可见的驱动者推进；释放本身也不是正确入口答案。

完整观察保留每个请求及其精度、完整非负回复整数及既定自定界帧、服务完成、固定交接确认、每次真正 Emit 的位值及 Emit／Advance／Return 次序、本地已完成请求数和 Step 数，以及声明的模式、持有权利与轮次控制结果。接收者只有该合同给出的共同公共约定和初态；私有配置不增加初态建议或确认字段。接收者可保存这些观察的任意有限记录并据此决策，不要求使用定义23.2的算法。仅把事件数目相同而位值不同的两条轨迹判同，不满足本定义。

原始 Read 响应与次数、原始游标和未读端点、私有 $p,r,d,N,M,k$、交接前的绝对历史与计数、来源身份建议、计算／存储费用和物理延迟不是观察。通道和权利描述符采用相同源无关安装与字面值，权利的实际有效性仍须各自在本世界成立。Wall、初始切面重读、rewind、私有状态导出、认证绝对计数与额外空间查询均不由这个交接安装；不把一个未安装命令解释成新的信息性拒绝。第18节的取得后接口若作为接收者已经合法取得的记录上的后续程序使用，仍须满足其原取得与 guard 前提，而不是免费初始查询。

目标始终是交接时的 $\partial_0$，含区域、墙角色和实际拥有的 lift；可用定理12.2的唯一坐标描述。它不会在 Step 后重置为当前边界。逐实例有限指在每个允许世界上经过有限次实际操作与本地计算给出这个精确答案，不是给某个预设精度或 Step 上界。所有操作、回复和输出仍按第8、25节付费。

**定义 27.2（全误差要求与固定 floor 子合同）。** 对世界 $W=(x,r;q,b)$，令 $\mathcal E_{\mathcal D}(W)$ 为沿因果接收者 $\mathcal D$ 的实际请求、实际当前深度逐次满足 (80) 的完整允许回复迹。定义24.3所问的确定性存在命题是

$$
\exists\mathcal D\ \forall x\in K\ \forall r\in\mathbb N
\quad\forall(q,b)\in\mathbb Q_{>0}\times\mathbb Q_{\ge0}
\forall\eta\in\mathcal E_{\mathcal D}(x,r;q,b):
\quad\mathcal D\text{ 有限停止且输出 }\partial_0.
\tag{100}
$$

这里 $r$ 是原初始化后的实际返回；定理3.1保证每个这样的有限运行真实存在。各世界在初始化时私有地固定自己的有理配置，不能随误差或动作改变。

另定义一个指定实现的较弱正确性要求：只要求对定义25.1的同一个确定数字服务

$$
F_{q,b}(d,n)=\left\lfloor2^n(b+q\alpha^d)\right\rfloor
\tag{101}
$$

有限且正确，而非要求对全部 $\eta$ 正确。其完整帧和服务完成方式固定、没有建议性附加字段；其有限二次算术、无原始 Read、无 Advance 性质仍按定义25.1。式 (101) 对所有有限 $n\ge1$ 可调用，不设精度上限。以下将直接否定这个较弱的全配置要求，从而否定 (100)。不会由数值误差界推断任意指定选择器都给相同回复；误差允许集合内的舍入选择本身可能携带额外信息。

## 28. 两个实际 proper 入口的一步汇合

**引理 28.1（不同付费入口的共同孩子与共同尾）。** 对任意 $t\in K$，分别从原空前沿初始化以下两个实际原始源，并在表中返回交接：

$$
\begin{array}{c|c|c|c|c|c|c|c}
 &x&p&r&d&N_p&s&\text{实际未读尾}\\\hline
W_A&010t&0&1&1&0&1&10t\\
W_B&000t&00&3&2&0&3&0t
\end{array}
\tag{102}
$$

两者均为真正达到的 proper 死亡返回，入口边界不同，分别为 $\partial(1,1)$、$\partial(2,3)$。在两者上执行第一个交接后 Step，其真实 Emit 都为零，随后都 Advance、Return；返回字段为

$$
\begin{array}{c|c|c|c|c|c|c|c}
 &p'&n&d'&N_{p'}&k_{p'}&s'&\text{实际未读尾}\\\hline
W_A&010&2&3&2&4&4&t\\
W_B&000&4&3&0&6&4&t.
\end{array}
\tag{103}
$$

它们在这个真实返回有相同的完整当前点和边界 $\partial(3,4)$。从此所有有限真实续行的深度、松弛、未读尾、实际 Emit 位及 Advance／Return 顺序相同；原私有历史字段仍可不同。

证明。所列源均由完整块 $0,10$ 接成，故对每个 $t\in K$ 合法。$W_A$ 的初始化后第一调用真正读取首零，发出 $\operatorname{Low}(0)=0$ 并返回。此时 $p=0$，$b_0=k_0=1$，恰在死亡返回；它未预读后面的 $10$。$W_B$ 的首调用同样取得 $0$。第二调用从这个死亡返回真正再读一个零，取得 $00$，发出 $\operatorname{Low}(1)=1$ 并返回于二。此时 $k_{00}=G_3-2=3$，第三调用不读，发出 $\operatorname{Low}(2)=0$，返回于三。实际已读字仍为 $00$，恰在其死亡返回。故 (102) 是原初始化的有限执行，不是只满足缓存等式的符号状态。

由 (38)–(40)，$\partial(1,1)$ 的初始墙是 $e_1$ 上的 $x_1^+$，终止墙是 $e_0$ 上的 $Z(0)$；$\partial(2,3)$ 的初始墙是 $e_{-1}$ 上的 $Z(1)$，终止墙也是 $e_0$ 上的 $Z(0)$。区域的正向长度分别为 $\alpha$、$\alpha^2$，所以它们确为不同带所有权边界。所有死亡等号均保留。

交接后第一调用中，$W_A$ 真正读一，再真正读其强制零，追加 $10$；$W_B$ 真正读一个零，追加 $0$。两者发射前的有限整数均为三：前者为 $G_1+1=3$，后者为 $0+3=3$。所以实际 Emit 都是 $\operatorname{Low}(3)=0$，不是只比较事件标签。各自 Advance 一次并清空 scratch 后得到 (103)。它们的新增 Read 数分别为二、一，不被混作公开观察；到这个返回的总已读长度却都为三。式 (48) 的两条不同父分支在此得到同一个出生坐标 $(3,G_3-1)=(3,4)$，出生松弛为 $G_2-1=2$。其初始墙为 $e_1$ 上的 $x_1^+$，终止墙为 $e_{-1}$ 上的 $Z(1)$，两世界均拥有这些具体点。

在 (103) 应用 [Exact Current Boundary Provenance][AFF-PROV] 定义1.1、定理2.1–2.2，取共同深度三、松弛二、前缀 $010,000$ 及共同实际尾 $t$。它们的 $N$ 差为二，返回时间反向相差二，满足该定理的实际切口条件。因此完整当前点确实相等，包含所有具体侧点。下面也把实际后继不变量写出，以明确其对标量服务的用途。

在任意匹配的后继返回，存在共同实际取得的完整字 $w$，使

$$
\begin{aligned}
p_A&=010w,&p_B&=000w,&d_A&=d_B=3+|w|,\\
N_A&=N_B+2,&n_B&=n_A+2,&k_B&=k_A+2,\\
N_A+n_A&=N_B+n_B,&k_A-n_A&=k_B-n_B,\\
\text{未读尾}_A&=\text{未读尾}_B=\operatorname{tail}_{|w|}(t).
\end{aligned}
\tag{104}
$$

正松弛时两者都不 Read，以同一个 $N+n$ 发射，再各 Advance 一次；零松弛时两者从同一实际尾、同一绝对原始位置读相同的 $0$ 或 $10$，包括强制零，两份 $N$ 增量相同，发射前整数仍相同。子时钟递推保存所有偏移，返回清空待发字段。归纳证明 (104) 和全部实际事件相同。每个有限调用均由定理3.1、3.2生产性完成，不能以无限尾的可计算性代替这些真实读取。证毕。

**引理 28.2（汇合后的完整仿射观察）。** 给引理28.1的两个世界安装同一个固定有理配置 $q>0,b\ge0$、同一个 floor 程序 (101)、相同源无关通道／权限安排。在第一个交接后 Step 返回以后，若接收者控制状态和已有观察相同，则对任意后续自适应精度、任意有限交互及整个无限允许续行，其完整允许观察都相同。这里没有限制未来精度，也没有要求未来尺度继续落在某个粗网格格子内。

证明。(104) 给每个匹配返回的真实深度相等，所以每个共同请求 $n$ 的整个整数 $F_{q,b}(d,n)$ 相等，进而完整帧、服务完成及本地请求计数相等。它们在同一固定 $q,b$ 下计算，不是每次重新选择一个允许误差。Step 的位值和逐事件次序由引理28.1给出，本地 Step 数同时增加。固定确认、持有权利的检查、描述符字面值、合法模式和轮次控制具有相同已安装规则及相同结果；两者都实际持有原来的持续权利。暂停不推进，本地计算只有相同输入，释放只作相同控制变动。原始端点与私有绝对时间没有被判同，也没有导出它们。

因此对完整命令／事件前缀归纳，下一命令、精度、保留记录、停止决定及输出相同，全部原字段的允许观察都保留。归纳也覆盖 Step 内已交付的 Emit、Advance、Return 前缀。若调用第23–24节的接收程序，其查询和每个内部 Step 就是这些实际操作；它们在相同观察上得到相同的可靠检测及达到记录。其后第18节真正取得记录上的 LiveStep、Peek、Seek、Arm／Tick 也相同：当前 $(d,s)$ 相同，DATA guard、有限代表、预算、拒绝和本地计数相同，每个内部 Step 由 (104) 配对。没有初始安装这些服务之外的新 getter，也不把一个任选见证历史当成原历史。

每个无限观察序列的坐标均属于一个有限前缀，故坐标逐项相同。此句不声称无限交互可在有限时间完成。公开帧没有时延、后台工作或 padding 建议字段；若加入这些额外通道，须另证相等。证毕。

## 29. 任意自适应精度下的入口非恢复定理

**定理 29.1（同一配置的实际反例与全域确定性非恢复）。** 对每个定义27.1的确定性因果接收者，如果它在所有 proper 死亡返回、所有原始源和所有固定有理 $q>0,b\ge0$ 的 floor 子合同 (101) 上都有限停止，则存在一个固定有理配置 $(q_*,b_*)$，以及引理28.1的两个真正达到的 proper 入口，使它在两世界上获得相同完整观察、在相同的本地观察位置有限停止并给出相同输出，而入口边界分别为 $\partial(1,1)$、$\partial(2,3)$。若只在 Return 决策，该位置就是同一本地返回。两世界使用一个相同的固定仪器程序与配置，源无关地安装在各自原初始化中。

因此即使只承诺 proper 死亡入口、即使指定后端就是 (92) 的确定 floor 服务、即使允许任意无界自适应精度，也不存在逐实例有限且全域正确的入口恢复器。定义24.3的全允许误差存在命题 (100) 尤其为假。

证明。固定这样一个接收者 $\mathcal D$。先取一个真实参考实例：原始源 $0^\infty$，从原空初始化完成一次 Next，在实际返回 $(0,1)$ 交接；仪器私有配置为 $q=1,b=0$，使用同一个 floor 程序。在尚未执行交接后 Step 时，它的真实标量始终为 $\alpha$，所以每次请求的实际整数为 $\lfloor2^n\alpha\rfloor$。这是 proper 死亡返回的一个全域有限性实例，不是标量零、深度无穷或 $q=0$ 的极限环境。

沿这个实际实例，只看到第一次 Step 发起以前，或者此前已完成的有限停止，以先出现者为准。这个前缀必有限：若二者都不在有限操作后出现，则只有静止查询、暂停或本地计算持续进行，接收者不会在该实际实例有限停止，违反假设。只在此真实前缀内取 Extent 精度的最大值，并为零次查询定义

$$
N=\max\bigl(\{1\}\cup\{n:\text{该前缀实际请求过 Extent}(n)\}\bigr),
\quad h=2^{-N},\quad L=h\lfloor2^N\alpha\rfloor.
\tag{105}
$$

置

$$
b_*=L+\tfrac12h,\qquad q_*=\tfrac14h.
\tag{106}
$$

它们是固定有限有理配置，$q_*>0,b_*>0$。对 $j=1,2$，由 $0<\alpha^j<1$ 有

$$
L<b_*+q_*\alpha^j<L+h.
\tag{107}
$$

真实参考值 $\alpha$ 也在半开网格格 $[L,L+h)$。一个精度 $N$ 的 dyadic 格子包含在每个较粗精度 $1\le n\le N$ 的某个格子内，故

$$
\left\lfloor2^n(b_*+q_*\alpha)\right\rfloor
=\left\lfloor2^n\alpha\right\rfloor
=\left\lfloor2^n(b_*+q_*\alpha^2)\right\rfloor
\quad(1\le n\le N).
\tag{108}
$$

这证明指定 floor 服务的实际字面相等，而不只是 (80) 允许选择相同近似值；(107) 还严格避开最终两值的格子边界。

现在先安装同一组 (106) 与同一个服务／控制协议，再取任意共同 $t\in K$，运行引理28.1的两个源至其指定交接。参数只依 $\mathcal D$ 的有限参考前缀，不依这个 $t$ 或其任何位；两个最终世界不沿运行改换参数。可特别取 $t=0^\infty$，得到两个最终为零的实际源。参考世界的参数只用来确定有限前缀，不被当作最终比较对中的另一台仪器。

在最终两世界的第一次 Step 以前，深度分别固定为一、二，真实标量正是 (107) 的两值。初始接收状态、固定确认、已装权利、全部控制字段与参考前缀相同；(108) 配对其中每次完整请求和回复。逐操作因果归纳迫使它请求相同的下一个精度，并作同样的暂停、计算、检查或决定。这同时保证有限前缀的自适应最大精度就是所取 $N$ 所覆盖的精度，不是预先把无限运行截在某个任意上界。

若参考前缀以无 Step 的有限停止结束，最终两世界也在相同前缀输出同一个答案。它不可能同时等于两个不同入口边界。这包括立即决定、没有初始查询和任意有限静止精化后决定。

否则它们都发起第一个真实 Step。引理28.1给相同的实际 Emit$(0)$、Advance、Return，并在其真实返回得到 (103)。因此接收者状态仍相同；若允许在已交付的事务事件上提前作决定，其观察前缀也相同，已不能在两个入口上同时正确。对继续到返回的情形，引理28.2保证此后无论请求多高精度、推进多少步、运行何种合法后续程序，完整允许观察永远相同。两个最终世界本身都是原假设的实际有限性实例，所以接收者在它们上有限停止，且停止位置与输出相同；同一个输出仍不能等于两个不同的 $\partial_0$。

最后，(101) 的回复对每次实际请求均满足 (80)，每个服务与实际 Read 均有限。若 (100) 的接收者存在，它特别会在这些确定 floor 实例上全域有限且正确，刚证矛盾。故全误差结论不需要假设误差独立、嵌套、无偏或有利舍入，也没有将某个任意固定误差机制替换成 floor。证毕。

这里的配置量词是“每个拟议全配置接收者，都有一个配置及同配置实际反例对”。不是声称每个事先指定的配置都产生这个反例，更不是在同一运行中选取不同仪器。参考前缀所需的总性只在实际 proper 实例上使用；不从一个不可达到的恒定极限回复推导有限首次移动。

## 30. 达到恢复、反向箭头与来源界限

**推论 30.1（可取得当前边界不提供通用入口逆）。** 在定义22.1的准确合同下，全允许误差的达到恢复及同源继续使用成立，而全允许误差的逐实例有限确定性入口恢复不成立。具体地，定理24.1和推论24.2的正向箭头保持 (99) 的全部条件；不能增加如下通用反向箭头：

$$
\bigl(\text{实际取得的当前边界、保留的全部有限允许观察、持续权利}\bigr)
\longrightarrow\partial_0.
\tag{109}
$$

证明。正向结论直接复用定理24.1及推论24.2。若 (109) 是对全部实际接入及全部允许回复有限可用的逆，将它接在该有限达到程序之后，就得到 (100) 的接收者，与定理29.1矛盾。更具体地，在定理29.1的移动情形，最终反例对从第一次 Step 后就共享 (104) 的当前边界、完整当前点和后续观察；合法运行达到程序得到的记录与持续使用也相同，原入口仍不同。反例不是撤销调用权，也没有阻止合法有限 DATA、跨更新 LiveStep 或真正移动的 Seek。

因此此合同中的“边界”表达实际付费前沿，“时间”表达交接后的实际事件，“记忆”表达已保留的有限数据与真实权利，“空间”表达实际当前点；这些独立意义仍按定义26.1。付费向前动作可以消去一个未保留的入口区别，同时使新的当前边界可取得。它没有把四个完整 view 的核变成相同，也没有恢复交接前的绝对史、完整私有字段、整个无限源或初始当前点的回滚服务。证毕。

**约定 30.2（精确供应、承重增量与证据范围）。** 定理29.1是本指定原生产者与仿射合同中的 `repo-derived` 普通数学综合。承重增量是两个真正达到的不同深度入口的一步同孩子／同尾汇合，结合实际总性实例的有限 floor 前缀，得到无精度上限的入口障碍。既有 Fibonacci 时钟、二次算术、floor 取整、一般同回复归纳与差分消去均不是新的数学原则。

| 来源 | 准确消费与迁移界限 |
| --- | --- |
| 本卷定义1.2、2.2、16.1、22.1，定理3.1、3.2、12.2、12.3及 (38)–(48) | 同一空前沿初始化、实际有限 Read／Next、寿命等号、坐标及具体墙所有权、独占交接和原始尾续接。式 (102)–(103) 逐步验证跨深度父切口确实执行；既有同深度历史碰撞本身不承担这一步。 |
| [Exact Current Boundary Provenance][AFF-PROV] 定义1.1、定理2.1–2.2、4.2、6.2及 §§11–17 | 同深度、同松弛、同实际尾的执行与完整点对应在 (103) 后使用；其原投影命令定理的观察类不能直接覆盖新标量读口。引理28.2另用真实深度相等核对完整 Extent、帧和控制观察。原事件专用跨边界障碍不被冒充为仿射障碍。 |
| 本卷 §§22–26，尤其定义24.3、25.1及 (92) | 原始入口问题、全误差合同及实际 floor 子实现；定理29.1否定定义24.3的入口恢复命题，定理24.1的达到恢复和推论24.2的后续使用保持各自原条件。 |
| [直接目标取得 §§5–9][ENT-DIRECT]；[有限精度永久盲性 §§2–7][ENT-CAP]；[有限发射容量 §§1–2][ENT-CAPACITY] | 分别供给纯乘法目标取得的全误差／指定后端量词和 Return／早 Emit 区别、有固定精度上限的确定 floor 障碍、已知边界的有限发射纤维。它们的目标、校准或精度条件不同；这里既无固定精度上限，也不以初始尾目标或已知边界替换入口目标。 |
| NativeAcquiredPrefixCylinder 及其 [owning Scribe][NAPCB]，包括私有 `next_native_spec`、`prefix_cons`、`raw_tail_add`；[SignedSeriesFibres][SSF] 及 [owning Scribe][SSFB] | 实际流执行／重启及具体 seam 纤维是正面既有供应。前者的 seed/payload/Stop 控制器不同，后者的相位双点不是本证明中两台生产者状态的相等。 |
| [InterfaceKernelCriterion][IKC] 及 [owning Scribe][IKCB]，Boundary Dynamics §§36.1–36.6 | 实际像因子化和输出／合法性／后继条件是既有判据。入口常值性的失败由具体同源初始化的反例给出。 |
| van den Bos–Vaandrager，[*State Identification for Labeled Transition Systems with Inputs and Outputs*][ENT-IDENT] §§1–3；Brattka–Gherardi–Pauly，[*Weihrauch Complexity in Computable Analysis*][WCA] 定义4–9 | `literature-attested`：初态识别与动作后的兼容性、有限观察名字及 Cauchy 表示的背景。前者的有限状态／有限标签框架不自动处理本节无界精度与配置，后者不供给实际 Step 汇合；均非本节模型定理的外部证明。 |
| [钉版 mathlib Zeckendorf][MATHLIB] | 有限规范展开与唯一性供应 Low 的有限算术背景；本证明使用本卷时钟公式。 |

所列文献与仓内供应按表中给定的假设和结论使用；(79)–(80) 的全精度入口非恢复结论由引理28.1–28.2与定理29.1的构造及证明承担，不作全球新颖性或文献穷尽声明。其证据是普通条件证明，不含 Lean/kernel 认证、程序执行的数学验证、数值模拟或物理传感器实现结论。

第26.3所列原 fixed-$G_{\rm gc}$、original-$Q$、parked-consumer、unchanged-initialization、完整原响应和任意 interior-cut 义务保持原范围。定理29.1不论任意其他仪器、已知配置、真实旧记录、额外认证通道、随机误差保证、撤权、并发或非 Advance 源变动。它不声称各个固定后端都不能通过额外的舍入规律传送建议，也不把更多物理测量的缺席当成宇宙不可能性。本定理不提供一般空间／时间／边界／记忆双向恢复或独立物理对应。

[ENT-DIRECT]: https://github.com/the-omega-institute/trureturing/blob/a0436a550dc6c32b66a14243eebf638d0698664a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNCALIBRATED_TARGET_ACQUISITION.md
[ENT-CAP]: https://github.com/the-omega-institute/trureturing/blob/a0436a550dc6c32b66a14243eebf638d0698664a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_CAPPED_PRECISION_PERMANENT_BLINDNESS.md
[ENT-CAPACITY]: https://github.com/the-omega-institute/trureturing/blob/a0436a550dc6c32b66a14243eebf638d0698664a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FINITE_EMISSION_CAPACITY.md
[ENT-IDENT]: https://arxiv.org/html/1907.11034v2

## 追加锚（本行以下为增补区）

## 31. Owned intersections at one acquired entrance depth

Keep the exact source, arithmetic successor, initialization and original three-event interface of Sections 1–3. An entrance is an actual returned history $a=(x,r)$ of that producer, not a state assembled from compatible registers. Write $d(a)=|p(a)|$ and $y(a)=T^rx$. For $d\ge1$ put

$$
a_d=G_d-1,\qquad b_d=G_{d+1}-2,\qquad
U_{d,s}=T^{s-N_p}C_p\quad(p\in P_d, N_p\in[0,G_{d-1}-1]),
\qquad s\in J_d=[a_d,b_d]\cap\mathbb Z.
\tag{110}
$$

Here $P_d$ denotes the complete block words of digit length $d$. The full-image statement of Theorem 7.2 and the coordinates of Theorem 12.2 make $U_{d,s}$ independent of $p$: it is the complete current-point set of $\partial(d,s)$, including both lifts at every internal split phase and precisely its owned lift at each wall. Equivalently, [Exact Current Boundary Provenance][AFF-PROV], Theorem 6.2, gives $U_{d,s}=Q_{d,b_d-s}[K]$. These are equalities of subsets of $K$, not definitions using only projected arcs. At depth zero set $U_{\rm init}=K$ and let $\partial_{\rm init}$ have no proper walls. The only depth-zero return is initialization; at depth one $J_1=\{1\}$.

**Theorem 31.1 (The complete owned intersection matching).** For every $d\ge2$ set $k_d=G_{d-2}$. If $s<t$ belong to $J_d$, then

$$
U_{d,s}\cap U_{d,t}=
\begin{cases}
\{Z(s-G_{d-1})\},&t=s+k_d,\\
\varnothing,&t\ne s+k_d.
\end{cases}
\tag{111}
$$

Thus the distinct-boundary intersection graph consists exactly of the disjoint pairs

$$
\{s,s+k_d\},\qquad a_d\le s\le b_d-k_d,
\tag{112}
$$

and its remaining vertices are isolated. Every displayed pair and singleton intersection is attained by actual initialized histories. If $d$ is even, the common wall is the initial wall of $s$ and terminal wall of $s+k_d$; if $d$ is odd, these roles reverse. In both cases its integer label is $m=G_{d-1}-s\le0$, and both sides own the same point $Z(-m)$. No positive-label double fibre or excluded endpoint supplies an additional intersection.

Proof. Use one common absolute return $r=a_d$. For every $0\le N<G_{d-1}$, Theorem 12.2 gives an attained state $(p_d(N),a_d)$ with $s=a_d+N$. Consequently

$$
H[U_{d,a_d+N}]=R^{a_d}H[C_{p_d(N)}].
\tag{113}
$$

The full depth-$d$ positional partition has disjoint arc interiors by RRO Theorem 20.2, including its cylinder and side-limit proof. The selected cylinders here are exactly those ending in zero. Their rotated arc interiors remain disjoint. Hence any intersection of two of their projected closed arcs must occur at common walls. Theorem 12.2 lists those walls as $e_{A_d-s},e_{B_d-s}$, with $A_d,B_d$ as in (39). Irrationality of $\phi$ makes different integer labels different phases. Equal initial walls or equal terminal walls force $s=t$; the cross equalities for $s<t$ give exactly

$$
t-s=|A_d-B_d|=G_d-G_{d-1}=k_d.
$$

For even $d$, $A_d-s=B_d-(s+k_d)=G_{d-1}-s$; for odd $d$, $B_d-s=A_d-(s+k_d)$ has that same value. Since $s\ge G_d-1$,

$$
m=G_{d-1}-s\le1-k_d\le0.
$$

By (38)–(40), its full phase fibre is the single point $Z(-m)$ and that point belongs to both complete sets. Their disjoint interiors and unequal other walls exclude every other point. This proves (111) with ownership, rather than just a contact of phases. It also handles $m=0$: the common point is $Z(0)$, not an invented split point at label zero.

The width of $J_d$ is $G_{d-1}-1<2k_d$. For $d=2$ this reads $1<2$; for $d\ge3$ it follows from $G_{d-1}=G_{d-2}+G_{d-3}\le2G_{d-2}$. No vertex can therefore be both a lower and an upper member of (112), proving the matching assertion. The pair range is nonempty: $G_{d-1}-1\ge k_d$ for $d\ge2$ (equality at $d=2,3$).

Finally (113) comes from the actual cylinder image $T^{a_d}C_{p_d(N)}=U_{d,a_d+N}$. Every point of each displayed intersection has a preimage in each corresponding cylinder; Theorem 3.1 actually reaches that prefix at return $a_d$. These are two genuine histories with the same complete current point. Explicitly, one may take $p_d(s-a_d)(10)^\infty$ and $p_d(s+k_d-a_d)(01)^\infty$ at that common return. The alternating-tail wall calculation in Provenance Proposition 3.1 assigns the first to the $G_{d-1}-s$ wall and the second to the same wall of $s+k_d$; both have collapsed to the stated $Z(s-G_{d-1})$. The cylinder-image argument already proves attainment without recognizing an infinite alternating source during execution. Birth and death equalities are retained throughout. $\square$

## 32. Genuine-origin preparation and the conditional binary residue

For $d\ge2$ fix the explicit boundary label

$$
\varepsilon_d(s)=\mathbf1_{\{s\ge a_d+k_d\}},\qquad s\in J_d.
\tag{114}
$$

Give depths zero and one the single value $\varepsilon=0$. In every pair (112), the lower member is below $a_d+k_d$, because $b_d-a_d<2k_d$, and the upper member is at least this threshold. Thus (114) separates the two members of every owned intersection. In particular at depth two its values distinguish $s=2$ and $s=3$ without any future event.

**Assumption 32.1 (Installed preparation, completed record and complete cut).** A fixed source-independent monitor is installed at the genuine initialization acknowledgement of this actual producer. It receives every subsequent actual Emit/Advance/Return, once and in order, through a faithfully associated paid channel. There are no omitted or autonomous Advances. The chosen finite handoff is marked at a genuine Return. The monitor has supplied finite computation, a protected authentic record writer, and authority to complete and retain its write. The receiver has a supplied completed read of that record and an authentic association to the same source, initialization epoch and handoff. These are installed capabilities, not conclusions inferred from a coordinate or bit string.

At handoff the source stays quiescent until the receiver's next original Next. The receiver retains the exclusive continuing right on this same producer; no fresh producer, raw endpoint or right is synthesized. Its new source observations are precisely the original Emit/Advance/Return events of its actual Next calls. It receives neither Wall nor Extent, private raw responses or read counts, old absolute time, old trace, $p,N_p$, internal clocks, nor a spatial query. Programs and public context are common. Physical latency, preparation duration, workspace size and source-dependent service timing are not observation ports.

The completed preparation cut leaves the authentic data $(d,\lambda)$, where $d$ is actually computed, encoded, supplied and charged, and $\lambda$ is the supplemental record being compared. Every other receiver-accessible source- or history-dependent preparation distinction factors through $(d,\lambda)$ and common public inputs, or has actually been erased or made inaccessible by a supplied isolation operation. This includes caches, old outputs, archives, references, identities, epoch numerals, counters, lengths, PC, flags, table indices and termination-time information. The old producer fields continue privately to implement Next; the cut does not erase the running producer or expose its state. The monitor's other state is isolated or destroyed and provides no subsequent advice.

Authentication and possession may assure that the record and endpoint belong together without disclosing a further distinguishing identity. If readable association fields, descriptors or their checks distinguish candidate histories beyond $(d,\lambda)$, those distinctions belong in the retained data and the stated conditional alphabet comparison no longer applies. Descriptor installation, use, protection, retention lifetime, completed write/read, acknowledgement and isolation are separately supplied and paid. Equal accessible data give equal receiver initial states, apart from any independent source-independent randomness. This is a complete receiver-accessible cut, not a claim that the entire producer has only two states.

**Proposition 32.2 (The label is acquired on its own run).** Under Assumption 32.1 one common finite preparation program writes exactly $(d(a),\varepsilon_{d(a)}(s(a)))$ at every finite actual handoff $a$ with $d(a)\ge1$, and $(0,0)$ at initialization. It needs no raw read in addition to those of the original producer and no full event archive. It does need the genuine-origin channel and the completed protected write/read of the assumption.

Proof. Run the already supplied temporal observer of Definition 2.3 from its empty prefix and zero counter at the genuine acknowledgement. Theorem 3.1 proves by induction on these actual events that its retained $\widehat p,n$ equal the actual acquired $p,r$ at each Return. Therefore it computes $d=|\widehat p|$ and $s=N_{\widehat p}+n$, and Theorem 12.2 identifies these with the actual boundary coordinates, including both lifetime endpoints. Compute (114), write the framed depth and supplemental value, and finish the authenticated write before the complete cut. The supplied completed read then delivers those same data on the associated run. At initialization the observer is still empty and writes $(0,0)$. Events can be discarded after the finite observer update; no copied chronology is needed. The induction has no initial value if this monitor is first installed at an already blind midstream receiver. Authentication, reliable retention and isolation remain explicit premises of the construction. $\square$

**Theorem 32.3 (Sharp supplemental alphabet conditional on acquired depth).** In Assumption 32.1, require one common decoder to recover the entrance boundary of every actual history, using the acquired depth, a prepared supplemental value and subsequent original events only. For each fixed depth the smallest possible supplemental alphabet has size

$$
M_d=\begin{cases}1,&d=0,1,\\2,&d\ge2.\end{cases}
\tag{115}
$$

The upper bound is attained by the same-run preparation (114) and the finite common decoder of Section 33. The lower bound at every $d\ge2$ still holds if the complete infinite future event sequence is supplied mathematically, with no finite stopping or computational restriction. Supplemental records in this lower-bound class may depend on the entire actual preparation history, rather than only on its boundary. This is an alphabet minimum under the complete cut and original-event menu; it is not a least sufficient partition or a minimum over enlarged measurement menus.

Proof. At depths zero and one the boundary is respectively $\partial_{\rm init}$ and $\partial(1,1)$, so one value and zero recovery calls suffice; a nonempty actual domain cannot use an empty alphabet. At $d\ge2$, choose any pair (112) and the two actual histories of Theorem 31.1. Their current points coincide. Producer correctness gives the same entire future Emit word $\Phi(y)$; Advance and Return have the same fixed order, so the entire permitted future agrees. A one-value supplemental record, equal acquired depths and the complete cut leave identical mathematical inputs to any decoder, yet the two entrance boundaries differ. This excludes one value even with an infinite future. Computation, storage or waiting on that future cannot separate those two inputs.

Conversely (114) makes the sets $U_{d,s}$ with any one label pairwise disjoint by (111). The full future identifies $y$ by RRO20.6–20.7, so within that label it identifies at most one $s$, and the actual entrance supplies one. This first proves semantic sufficiency. Lemma 33.1 and Theorem 33.3 give its effective finite version and same-run realization, completing the upper bound in the asserted finite-decoder class. No assertion that all sufficient labels refine (114) is used: different matching components can be labelled independently, and a general history-dependent label need not factor through the boundary. $\square$

## 33. A finite inverse using actual future events

**Lemma 33.1 (Finite positional separation within either label).** For every $d\ge2$, every $s,t\in J_d$ and every $y\in U_{d,s}$, $z\in U_{d,t}$,

$$
\varepsilon_d(s)=\varepsilon_d(t),\qquad
q_{d+2}(y)=q_{d+2}(z)
\quad\Longrightarrow\quad s=t.
\tag{116}
$$

Proof. Suppose $s\ne t$. Theorem 31.1 and (114) make their projected closed arcs disjoint: all projected contacts in (113) were exactly the matching pairs and have different labels. Both arcs are cells in the same rotated depth-$d$ phase partition (113). Every cell of the full partition has length either $\alpha^d$ or $\alpha^{d+1}$ by RRO20.2. Since the two selected closed cells do not even touch, each circular gap between them contains at least one whole intervening cell. Thus each gap has length at least $\alpha^{d+1}$. This includes a gap crossing the chosen phase seam; it is a statement about oriented circle arcs, not about the order of representatives in $[0,1)$.

A depth-$(d+2)$ positional cylinder has a connected phase arc of length at most $\alpha^{d+2}<\alpha^{d+1}$. It cannot meet both selected arcs: a connecting subarc would have to cross one of those two gaps. Equal prefixes would place $y,z$ in exactly such a cylinder. This contradiction proves (116). Endpoint membership can only reduce a projected intersection and cannot invalidate the strict length inequality. $\square$

**Definition 33.2 (The common event decoder).** Read the completed record of Proposition 32.2 while the source is paused. At $d=0,1$, output the unique entrance and current boundary without calling Next. At $d=2$, (114) directly gives $s=2+\varepsilon$; again output the entrance and current boundary without a recovery call. For $d\ge3$ set

$$
L=d+2,\qquad H_d=G_{d+2}-1.
\tag{117}
$$

Make exactly $H_d$ actual Next calls on the retained original producer, checking Emit/Advance/Return order and counting completed calls locally. In parallel, apply Definition 2.3 as a local event calculation with an initially empty auxiliary prefix and auxiliary time zero. Its input is the received suffix of actual Emit bits. It observes no producer private field. At call $H_d$ take the first $L$ digits of the auxiliary prefix, denoted $u$.

Enumerate $s\in J_d$ with the received label. Test whether

$$
C_u\cap U_{d,s}\ne\varnothing.
\tag{118}
$$

This is a finite exact test. Use the depth-$L$ cylinder formula of RRO20.2 and the ordered arc and ownership formulas (38)–(40). All phase endpoints have representatives in $\mathbb Q(\sqrt5)$. Reduce modulo one, splitting an arc at zero when necessary, and compare endpoints exactly. A positive-length common arc has a point in the interiors of both arcs, whose fibre belongs to both complete sets. If the common projection is only an endpoint, test its included lifts: a positional-cylinder wall is a positive-label $e_j$ with its specified side, and a current wall is given by $\chi_+$ or $\chi_-$ in (38). Coincident positive labels in this case can only be $j=1$; opposite sides there are distinct points. A nonpositive current wall is a singleton and cannot coincide with a positive positional-wall label. A wall lying inside the other arc has its full required fibre there. These rules decide every contact, including the seam. Equality and order in the fixed quadratic field are decidable by integer arithmetic and sign comparisons, with zero tested before squaring; no approximate phase oracle or test on an arbitrary real is required.

Return the unique successful $s$ and its entrance boundary with the ordered owned walls (40). To obtain the genuine attained boundary without retaining the whole recovery word, compute

$$
N_u=\sum_{j<L}G_ju_j,\qquad
\widetilde b_j=\operatorname{Low}(N_u+j)\quad(0\le j<H_d).
\tag{119}
$$

Starting with the decoded entrance $(d,s)$, apply the live coordinate update of Theorem 18.2 to these bits in order, using only local computation. Retain its final coordinates $(D,S)$, local count $H_d$ and the actual continuing right. The bits in (119) regenerate previously received values; they are not additional source events, advances or read receipts.

**Theorem 33.3 (Finite acquired inverse, owned output and live resumption).** Under Assumption 32.1, Definition 33.2 terminates on every actual history and returns exactly its entrance boundary, including its owned lifts, and exactly the boundary at its genuine stopping return. At $d\le2$ it makes no recovery call. For every $d\ge2$ a sufficient uniform observation bound is $G_{d+2}-1$ completed original triples, with the just-stated zero-call shortcut at depth two. On every such recovery segment there are at most four additional actual raw reads, including every forced zero. The source ends at $T^{r+m}x$, where $m$ is the number of recovery calls, not at the entrance point unless $m=0$.

The returned attained coordinates and the retained right support every subsequent finite lawful LiveStep, guarded Peek/Arm/Tick and moving Seek of Section 18, on the same producer and its exact unread tail. This statement supplies the missing acquired boundary precondition for those routines; it does not newly prove their already supplied live-use theorems or authenticate a historical member.

Proof. The small depths follow from (115), $J_1=\{1\}$ and $J_2=\{2,3\}$. At $d\ge3$ let $y=T^rx$ be the actual entrance point. The actual received word is $v_{H_d}(y)$ by Theorem 3.1. The event calculation of Definition 2.3, started at time zero, is correct on this word because the same word is the output of the original initialized producer on mathematical input $y\in K$. Only its observer calculation is used; no second producer is executed and no raw getter for $y$ is installed.

Let $\widetilde p$ be its auxiliary prefix at $H_d$ and $e=|\widetilde p|$. Theorem 3.1 for that mathematical input says its event fibre is $C_{\widetilde p}$. RRO20.6 says the same fibre fixes $q_L(y)$, since $H_d=G_L-1$. A complete block prefix of length $e<L$ permits two tails differing before $L$, so cannot fix that positional prefix. Hence $e\ge L$, and the extracted $u$ is exactly $q_L(y)$. To bound auxiliary storage, for every $e\ge2$ the birth identity gives

$$
b_{\widetilde p}=G_e-1-N_{\widetilde p}\ge G_e-G_{e-1}=G_{e-2}.
\tag{120}
$$

The auxiliary clock actually has $b_{\widetilde p}\le H_d=G_L-1$, so $e\ge L+2$ is impossible. Thus $L\le e\le L+1$. This also shows why a potentially long event word need not be archived.

The actual entrance lies in $U_{d,s(a)}$, so it passes (118). If two candidates passed, their witnessing points in $C_u$ would have the same depth-$L$ prefix and label, contradicting Lemma 33.1. The finite enumeration and exact test therefore return precisely $s(a)$. Formula (40) gives the actual owned lifts. In particular the proof uses the complete sets in (118); replacing them by unrestricted projected wall contact would not prove the statement.

The finite representative $Z(N_u)$ has the same $q_L$ as $y$. RRO20.6 therefore gives $v_{H_d}(Z(N_u))=v_{H_d}(y)$, and finite-core succession identifies these bits with (119). Starting from the now correct entrance coordinates, Theorem 18.2 updates on each actual observed bit to the genuine next coordinates. Local regeneration uses those same bit values in the same order, so induction gives exactly the actual stopping $(D,S)$, despite the absence of a stored event archive. It does not replace the producer's actual prefix or tail by those of $Z(N_u)$. Computation while paused adds no Advance.

For the raw-read bound put $\delta=b_d-s(a)$. The first actual renewal is call $t_1=\delta+1$. If the successive actually read block lengths are $g_1,g_2\in\{1,2\}$, the next two renewal calls, when continued, are

$$
t_2=t_1+G_{d+g_1-1},\qquad
t_3=t_2+G_{d+g_1+g_2-1}.
\tag{121}
$$

These are the birth-to-renewal lifetimes (68), including the final renewing call. In particular

$$
t_3\ge1+G_d+G_{d+1}=G_{d+2}+1>H_d.
\tag{122}
$$

At most two blocks are physically acquired during the recovery horizon; their total length is at most four. All other calls are read-free. Each reached read and each finite arithmetic operation terminates by the source contract and Section 2, so all $H_d$ calls and the subsequent finite calculations finish. The zero-call cases have zero new raw reads.

Finally the actual producer has remained at its own raw cursor, advanced exactly $m$ times, and retained its original binding and right. Theorem 3.2 gives exact continuation there. At positive depth the just-proved attained coordinates satisfy precisely the data-and-right precondition of Theorem 18.2, so its LiveStep updates and Theorem 18.3's finite Seek, with the stated guards for stationary use, apply to this same run. At depth zero the first later Next must instead use the actual initialized rule: its first Emit is zero for the physically read block $0$ and one for $10$, giving births $(1,1)$ and $(2,2)$ respectively. This follows directly from Definition 2.2 with $p=\varnothing,n=0$; no proper-wall formula with a negative Fibonacci index is used. Thereafter the positive-depth live rule applies. $\square$

## 34. Payload, working storage and the same-run resource comparison

**Proposition 34.1 (Separate actual resource coordinates).** Consider the preparation, completed cut, recovery and any subsequent finite use on the one run of Theorem 33.3. Let $r,d$ describe the actual handoff, $m$ its recovery calls, and $e$ its new raw bits during recovery. In the order

$$
(\operatorname{Read},\text{raw delivered bits},\operatorname{Next},
\operatorname{Emit},\operatorname{Advance},\text{postinitial Return}),
$$

the preparation and recovery coordinates are exactly

$$
(d,d,r,r,r,r),\qquad(e,e,m,m,m,m).
\tag{123}
$$

For $d\le2$, $m=e=0$. For $d\ge3$, $m=H_d$, and there are exactly two actual renewal blocks during recovery, with

$$
e=g_1+g_2\in\{2,3,4\},\qquad D=d+e.
\tag{124}
$$

The retained and transferred record can have data payload

$$
b_{\rm rec}\le2\ell(d)+1+\mathbf1_{\{d\ge2\}}=O(\log(d+2)),
\tag{125}
$$

before fixed framing and association/rights descriptors. Its supplemental field has no variable bit at $d=0,1$ and one bit at $d\ge2$. The preparation monitor, producer and decoder have implementations using $O(d+1)$ working or decoded-coordinate bits during this finite segment. A streaming implementation uses $O(P+c+d+1)$ simultaneous local digital storage for all of them, where $P,c$ have the installed-program and descriptor meanings of Definition 8.1. It stores no $H_d$-bit event archive or candidate table. Retained external outputs, source backend storage and the preparation/isolation/association services have their own actual storage and costs.

Proof. Original Next performs exactly one Emit/Advance/Return and acquires each raw bit once, including a forced zero. This proves (123). Theorem 33.3 gives $m=e=0$ in the small cases and excludes a third renewal at $H_d$ otherwise. The second renewal does occur by that horizon: $t_1\le G_{d-1}$ and $g_1\le2$ imply

$$
t_2\le G_{d-1}+G_{d+1}
=G_{d+2}-G_{d-2}\le G_{d+2}-1=H_d.
\tag{126}
$$

Hence exactly the two physical blocks are read, proving (124). The producer's stopping raw cursor is precisely $D$ and its unread tail is $\operatorname{tail}_D x$; no local regeneration changes either.

Use Definition 8.1's self-delimited binary depth and then one label bit only when $d\ge2$. This proves (125). There is one completed framed record write and one completed framed record read; their actual bit traffic, copies, protection and access are paid separately. Any simultaneously retained sender copy and receiver copy both count. The depth field is part of this payload, not free context acquired by a decoder from the future. The alphabet minimum (115) is conditional on it.

During preparation the maximum actual depth is $d$, $r\le G_{d+1}-2$ for $d>0$, and the monitor of Proposition 32.2 holds its $d$-digit prefix, count and constant-number caches. All these integers have $O(d+1)$ bits. Its digital preparation work may be bounded, using Section 8's arithmetic, by $O(P+c+(r+1)((d+1)^2+c))$, in addition to actual input/output and the supplied record/cut services. The monitor processes $r$ real triples (six bits each in that code); any separate channel copies are actual additional traffic. Its source-correlated workspace is then cleared or isolated as stipulated, rather than secretly left readable.

During recovery the actual depth is at most $d+4$, and the auxiliary prefix length is at most $d+3$ by (120). The call counter, $H_d$, $N_u$, each candidate $s$, the decoded entrance and attained coordinates, signed wall labels and finite Zeckendorf descriptions all use $O(d+1)$ bits. An included natural wall may be printed as the finite description $Z(B)$ with its $O(d+1)$-bit integer, or as its literal finite digit word; the exceptional $x_1^\pm$ have fixed finite symbolic descriptions. This does not print an infinite spatial point. Powers and weights are generated from consecutive values, candidates are tested one at a time, and arithmetic scratch is reused. This proves the simultaneous storage bound, including coexisting producer and receiver fields; it is not the smaller payload bound (125).

For explicit finite decoding work, the auxiliary event calculation uses $m$ observer updates, the scan (118) examines at most $G_{d-1}$ candidates, and regeneration (119) uses $m$ finite Low evaluations and live-coordinate updates. The actual producer separately performs its $m$ emission computations. Every quadratic endpoint coefficient has $O(d+1)$ bits. As in Definition 13.2, exact integer parts can be found by $O(d+1)$ sign comparisons on integers of that width, each using grade-school multiplication and reusable linear scratch. Thus a conservative bound for the decoding calculation alone is

$$
O\bigl((m+G_{d-1}+1)(d+1)^4+B_{\rm decoded}\bigr)
\qquad(d\ge3),
\tag{127}
$$

where $B_{\rm decoded}$ is the literal result-output length. The power four allows all coefficient generation, scans, copying, clearing and return positioning; it is an upper bound, not an asserted fastest algorithm. Producer arithmetic, descriptor checks, actual event reception/output, framing, and completed record services remain separate paid coordinates. In particular the recovery emits exactly $6m$ producer-event bits in the fixed code, before extra frames and copies. The decoder need not retain those $6m$ bits. $\square$

Record retention is a lifetime obligation in addition to payload size: keeping $b_{\rm rec}$ bits for the actual waiting period, protecting them, invoking the reader and transferring the continuing turn all need their supplied services. The complete cut may physically erase a workspace or isolate it; an isolated but still present workspace remains part of actual storage. Backend provisioning $\iota_x$, generation/delivery $\gamma_x(d+e)$ and retained source storage $\sigma_x(d+e)$ of Definition 8.1 are not zero. Preparation driver input, program and origin synchronization, real endpoint binding, record authentication, acknowledgements, output destinations and any external archive are also counted at their actual costs. No finite generator or finite physical installation for every unknown $x\in K$ follows from the sequential-source promise.

For later finite use let $J$ be all further actual Next calls, including calls inside Seek or bounded Tick, and let $d_{\max}$ be the final and hence largest actual raw depth in that segment. Its additional vector is exactly

$$
(d_{\max}-D,d_{\max}-D,J,J,J,J).
\tag{128}
$$

Indeed each later raw bit extends the same actual prefix once, and the source resumes exactly as in Theorem 3.2. Requests, refusals, parameter parsing, local arithmetic, outputs, budgets, descriptor uses and retained archives are separately charged as in Sections 8 and 19.3. The four-read recovery bound does not recur for free and does not bound arbitrarily long later use. Both the literal producer prefix and its counters can grow without bound under continuing Next. A fixed finite program does not imply bounded memory.

There is a simpler comparison using exactly the same genuine-origin preparation. The monitor already computes $s=N_p+r$. It may complete an authentic record containing the exact $(d,s)$ instead of (114), and the same kind of complete cut may retain only those coordinates and the actual right. At depth zero use the initialized tag. At proper depths the larger payload is $O(d+1)$ bits, with a $\Theta(d+1)$-bit ordinary binary $s$ field since $G_d-1\le s\le G_{d+1}-2$. That direct export gives the boundary immediately with no recovery Advance or new raw read. It is not a newly acquired geometric measurement or a new mathematical achievement: it exports already acquired coordinates. The small record saves transferred/retained preparation payload under its declared cut, while introducing later event acquisition, arithmetic and source movement. Preparation working storage, final decoded storage and output still have linear depth scale; $H_d$ can be exponential in $d$. Neither construction dominates the other in all resource coordinates. No optimal horizon, total-resource dominance, global bit-cost optimum or physical provisioning theorem is claimed.

## 35. The recovery arrow and its precise suppliers

Keep the independent meanings of Definition 7.1. Space is the complete current positional point; time is the actual chronological producer events; boundary is the oriented compatible paid-frontier region with its included current lifts; memory is actually acquired retained information together with its live binding/right. The installed monitor and complete cut add a specific memory channel to that same process. The proved finite arrow is

$$
\bigl(\text{actually prepared }d,\varepsilon;
\ \text{actual future triples through }m;
\ \text{retained same-run right}\bigr)
\longmapsto
\bigl(\partial_{\rm entrance},\partial_{\rm attained};
\ \text{lawful continuing use}\bigr).
\tag{129}
$$

The finite positional prefix used internally by the decoder belongs to the genuine entrance point; RRO20.6 is the exact correspondence between that positional information and the observed temporal word. Lemma 33.1 then identifies the boundary, and Theorem 18.2 transports the decoded record along the very events that actually occurred. Thus the two routes to the attained boundary agree on the common run. Lawful action uses the original right and the attained guard; it is not created by printing coordinates. Source movement during recovery is real, and the entrance output is a retrospective boundary answer, not a restored entrance configuration.

The substantive mathematical addition is the concrete owned intersection formula (111), its sharp depth-conditioned binary residue (115), and the effective finite event inverse (116)–(122). General zero-error colouring and factorization are reused. [DefectGraphMinimumColoring][EB-COLOR], including its private `repair_label_feasible_exists` and [owning Scribe][EB-COLOR-B], treats a finite state carrier and fixed record/target maps; here the finite graph is instead computed explicitly on the boundary set $J_d$, while actual source histories remain infinite in number. Its generic theorem supplies neither (111) nor this event horizon. [InterfaceKernelCriterion][IKC] and its [owning Scribe][IKCB] supply actual-image factorization criteria, not finite acquisition; Theorem 33.3 gives the latter in this source-specific contract. No application of these Lean declarations was compiled for these ordinary proofs.

The geometric and execution hypotheses are exactly RRO20.1–20.7 (no11 carrier, arithmetic $T$, complete cylinder fibres, endpoint sides and the temporal/positional partition identity), RRO35's block lifetimes, and this volume's Theorems 3.1–3.2, 7.2 and 12.2–12.3. Their precise use in (113) is one common attainable absolute return, not a comparison of independently optimized arcs. [SignedSeriesFibres][SSF] and its [owning Scribe][SSFB], including private `prependBlock` and the internal seam classification proof, are existing positive supply for full phase fibres. [Pinned mathlib's Zeckendorf source][MATHLIB] supplies `Nat.zeckendorfEquiv`, `Nat.sum_zeckendorf_fib`, `Nat.zeckendorf_sum_fib` and the terminating finite construction, including private `zeckendorf_aux`; its Fibonacci indices are $j+2$ for our digit weight $G_j$. It supplies finite Low arithmetic, not the operational recovery theorem. [NativeAcquiredPrefixCylinder and its owning Scribe][NAPCB], including private `next_native_spec`, `prefix_cons`, `raw_tail_add` and the imported reconstruction proofs, concern the different seed/payload/Stop controller on arbitrary binary raw streams. Its acquired-state and exact-tail restart results remain credited prior supply, not an identification of that controller with this one.

[Exact Current Boundary Provenance][AFF-PROV] Theorems 2.1–2.2, 6.1–6.4 and Sections 8–9 already give same-tail execution, the complete owned-set tail bijection, finite historical fibres and an event inverse once the full $(d,\delta)$ is supplied. Its Section 15 gives a necessary record-range criterion without finite acquisition. [Finite Emission Capacity][EB-CAPACITY] Sections 2 and 7 likewise fix the complete known initial boundary before identifying finite observation fibres. Here only $d$ and (114) survive preparation; deriving $s$, including actual point ownership, is precisely the missing input bridge. Once that bridge is proved, the continuing live routines of Sections 18–19 are direct reuse, not additional novel results.

The installed-origin and complete-cut disciplines are also reuse. [Atomic Generation Acquisition][EB-ATOMIC] Section 9 supplies faithful origin monitoring and protected same-source field preparation, while Proposition 12.6 distinguishes that field from an installed complete read service. [Joint Moment Fibers][EB-JOINT] Section 39 requires an actually acquired authentic entry and a complete receiver-accessible residue, counting identity, PC, cache, timing and access distinctions. [Acquired Intrinsic Depth Calibration][EB-INTRINSIC] Sections 4–6 supplies actual preparation, complete retention, authentic later entry and a finite consumer on its original right-spine interface. [Atomic Boundary Trichotomy][EB-TRICHOTOMY] Section 9 already has concrete paired historical fibres and binary source/parity supplements. Their objects are finite ordered trees, substitutions and their specified readouts; none provides this paid Zeckendorf matching or its finite unknown-$s$ decoder. Proposition 32.2 explicitly instantiates the already supplied monitoring method with this producer's temporal observer. It does not install that instrument at an already blind affine receiver. The unchanged no-record affine entrance obstruction of Sections 27–30 therefore remains in its original scope.

[Bounded Unit Drift Identifiability][EB-DRIFT] treats a different contract: moving multiplicative units, supplied drift bounds, scale replies and initial raw-tail targets. Neither a unit-drift promise nor a scale reply is a premise of (129). Its subcritical acquisition and critical hidden-configuration obstruction are not retargeted to this event-only problem. Likewise the [FibonacciFactorCompletion coordinate bridge][EB-FACTOR] and its [owning Scribe][EB-FACTOR-B] use grouped three-digit labels, guards and bounded affine coordinates; its private endpoint helpers in the [endpoint-budget source][EB-FACTOR-END] concern closed expanded colour constraints on fixed actual tails. Those do not identify the paid frontier or supply its preparation record. These positive suppliers retain their original hypotheses.

The cited repository texts and pinned upstream source are the primary mathematical sources for the exact correspondences just stated. The additional claims are repository-derived ordinary conditional proofs; no inaccessible literature text is used as a verified theorem supplier, no global priority or exhaustive-literature claim is made, and no new Lean certification or executed mathematical validation is asserted.

Even with the new record, the result does not identify the whole infinite spatial point, the old event chronology, or the actual member of (42). For a recovered entrance of depth $d\ge1$, even a complete entrance point leaves its $G_{d-1}$ possible original histories; (114) agrees on all of them, and the decoder chooses none as actual. The whole-event future has the current-point kernel, whereas the prepared label plus a finite future recovers the boundary on the stated depth fibre; these are different observation maps. The four full kernels are not asserted equal. Original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization, arbitrary interior-cut, full original-response and alpha/beta cross-model acquisition/action obligations remain at their original domains. General mutual recovery of independently meaningful space, time, boundary and memory, and their independent physical interpretation, remains unresolved. This conditional finite arrow does not complete that sustained objective.

[EB-COLOR]: ../../../D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring.lean
[EB-COLOR-B]: ../../../Blueprint/D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring.scribe.cs
[EB-CAPACITY]: RECURSIVE_RELATIONAL_OBSERVATION_FINITE_EMISSION_CAPACITY.md
[EB-ATOMIC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md
[EB-JOINT]: RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[EB-INTRINSIC]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_INTRINSIC_DEPTH_CALIBRATION.md
[EB-TRICHOTOMY]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md
[EB-DRIFT]: RECURSIVE_RELATIONAL_OBSERVATION_BOUNDED_UNIT_DRIFT_IDENTIFIABILITY.md
[EB-FACTOR]: ../../../D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.lean
[EB-FACTOR-B]: ../../../Blueprint/D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.scribe.cs
[EB-FACTOR-END]: ../../../D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EndpointNecessity.lean

## 追加锚（本行以下为增补区）

## 36. Same-offset Reference extension and the original entrance

**Definition 36.1 (The additional same-offset port).** Set

$$
\alpha=(\sqrt5-1)/2,\qquad G_0=1,\quad G_1=2,\quad
G_{j+2}=G_{j+1}+G_j.
$$

The source, initialization, handoff, exclusive persistent calling rights, and actual operations are those of Definitions 1.2, 2.2, 16.1, 22.1, and 27.1 of this volume. A source is one fixed
$x\in\{0,1\}^{\mathbb N}$ with no adjacent ones. It is initialized at the empty acquired prefix and driven through a finite number of actual Next calls before handoff. Step invokes this same producer's Next; it delivers the actual Emit bit, Advance, and Return in their actual order. Passing the zero after a one requires an actual raw Read. No operation other than an actual Advance changes source time. The handoff and public installation carry no private-history information.

A world has one fixed rational configuration

$$
q>0,\qquad b\ge0.
$$

This configuration is fixed before the initialized source run, independently of its raw bits, and remains the same across handoff and every later operation. Its value, bounds and description length are not given to the receiver as advice.

At a returned cut of actual acquired depth $d$, Extent$(n)$, for any finite integer $n\ge1$, returns a nonnegative integer $a$ with

$$
\left|a2^{-n}-(b+q\alpha^d)\right|\le2^{-n}.
\tag{130}
$$

The extension considered here additionally supplies Reference$(n)$, returning a nonnegative integer $c$ with

$$
\left|c2^{-n}-b\right|\le2^{-n}.
\tag{131}
$$

Reference reads this same fixed $b$. It performs no raw Read or Advance and supplies no other private information. Both ports return complete unsaturated finite integer frames with fixed source-independent framing and acknowledgement. Calls and their finite precisions are paid; there is no unit-cost real-number or infinite-name reply. All errors across both ports may be correlated and adaptive, subject only to (130), (131), and the common fixed configuration. This is an explicit additional observation interface. Its relation to the interface of Theorem 29.1 is specified in Definition 41.3.

**Definition 36.2 (Original entrance and inherited coordinate rules).** The exact target is the original handoff boundary $\partial_0$, including its oriented wall roles and owned lifts. At return zero it is the empty boundary, with whole-circle compatible region, represented by $(d_0,s_0)=(0,0)$. Every proper attained boundary has unique coordinates

$$
d\ge1,\qquad s\in J_d=\{G_d-1,\ldots,G_{d+1}-2\}.
$$

Its positively oriented arc has length $\alpha^d$, initial wall $e_{A_d-s}$, terminal wall $e_{B_d-s}$, and respective owned lifts

$$
\chi_+(A_d-s),\qquad\chi_-(B_d-s),
\tag{132}
$$

where

$$
(A_d,B_d)=
\begin{cases}(G_{d-1},G_d),&d\text{ even},\\
(G_d,G_{d-1}),&d\text{ odd},\end{cases}
$$

$e_m=[-m\phi]$, $\phi=(1+\sqrt5)/2$,
$\chi_\pm(1)=x_1^\pm$, and $\chi_\pm(m)=Z(-m)$ for $m\le0$. Attainment ensures that the indices used in (132) are at most one. Thus recovering $(d_0,s_0)$ recovers precisely the requested boundary and ownership, without selecting a private historical representative.

The following results of this volume are used with their original endpoint conventions; the displayed coordinate and clock rules are citations of those results.

1. Theorems 3.1–3.2 give actual initialized execution, finite completion of each reached Read and Next, and exact continuation on the actual unread tail.
2. Theorems 12.2–12.3 give (132), uniqueness of the coordinates, and the actual clock transitions. Put
   $$
   \delta(d,s)=G_{d+1}-2-s.
   $$
   A positive-slack Step reads no raw bit and moves $(d,s)$ to $(d,s+1)$. A zero-slack Step reads the next complete actual block, of length $g\in\{1,2\}$, and returns at the birth coordinates $(d+g,G_{d+g}-1)$. Return zero reads its first block on its first Step. From a birth at depth $D\ge1$, the next actual block-reading Step occurs exactly $G_{D-1}$ Steps later, including that final Step.
3. Lemma 17.1 supplies the closed-error three-ratio test for $\{1,\alpha,\alpha^2\}$. The clock inversion and resource computation in Theorem 17.3 identify the original boundary from the first two correctly classified block updates.
4. Lemma 28.1 supplies two actual differently deep proper death entries with identical first Step events and a common complete current point, depth, and unread tail afterward. Its whole-future execution invariant is used below. Lemma 28.2 supplies the matching original controls and frames after that merger; the new Reference observation is checked separately below.

**Definition 36.3 (Sequential receivers and the primitive Reference resource).** Receiver operations are the causal operations of the source contract. A source query is made at a returned cut and has a finite reply transaction. Early termination while receiving an allowed transaction prefix is permitted in the lower bound. This does not install cancellation, overlapping calls, or a new interleaving source operation. In particular no new Reference can be started inside an unfinished source reply transaction. Equal whole frames imply equal observable prefixes for any such early decision. A next request is initiated only after the current transaction completes; there is no cancellation operation or restart that creates a second outstanding request. Public checks, pauses, releases, endpoint descriptors and acknowledgements have the source-independent rules of Definition 27.1. No release supplies an unobserved advance or a fresh handoff.

The acquired-current-record programs of Definition 18.1 and Corollary 24.2 are available only after the receiver has legitimately acquired their required current record, and each spatial request retains its original DATA guard and budget conditions. These are programs on an earned record, not an initial private-state query. In particular no getter of $p,r,N_p$, raw-Read count, source identity or authenticated absolute time is added.

For a receiver $\mathcal D$, world $W$, and allowed error trace $\eta$, define

$$
B_{\mathcal D}(W,\eta)
=\#\{\text{completed primitive Reference replies before the first actual Step}\}.
\tag{133}
$$

If it stops without a Step, count the completed replies before stopping. Every primitive completion counts even if its value is discarded, or if a program packages several calls in a macro. All Reference calls after the first Step are unrestricted. Since source queries are made only at returned cuts, using Step initiation, its Advance, or its completion as the first-Step cutoff does not insert another Reference completion inside that Step. Early stopping within that Step is treated explicitly below.

## 37. Finite entrance recovery with no later Reference calls

**Theorem 37.1 (Universally finite original-entrance recovery).** Under (130)–(131), a single causal deterministic receiver recovers the original $\partial_0$, with the ownership in (132), after finitely many operations on every allowed initialized world and every allowed joint error trace. It also obtains a genuine reached boundary and retains its original calling rights. All of its Reference replies complete before its first Step, and it uses no later Reference calls. The exact primitive counts and per-instance bounds are (142)–(143) below. No upper bound on the initial depth or on the configuration description is required.

**Proof.** At the original paused cut, for $n=1,2,\ldots$, request one Extent$(n)$ and one Reference$(n)$. Write their decoded values as $U_n,V_n$, and set $W_n=U_n-V_n$. Stop this search at the first index $n_*$ satisfying

$$
W_n>2048\,2^{-n}.
\tag{134}
$$

For integer replies this is simply $a-c>2048$. Put

$$
\varepsilon=2^{-n_*},\qquad e=2\varepsilon,\qquad V_*=V_{n_*},
$$

and retain $W_0:=W_{n_*}$. The subscript zero here denotes the cut before any receiver Step. Discarding earlier data does not remove its calls from (133).

Let $z_0=q\alpha^{d_0}>0$. On every search round,

$$
|W_n-z_0|\le2\,2^{-n}.
$$

Consequently every round with $z_0>2050\,2^{-n}$ satisfies (134), independently of the errors. The search is finite, and

$$
n_*\le\min\{n\ge1:2^nz_0>2050\}.
\tag{135}
$$

At the selected round, (134) implies $z_0>2046\varepsilon=1023e$.

Now perform actual Steps one at a time. After each returned Step, request only Extent$(n_*)$, with decoded value $U_i$, and set

$$
W_i=U_i-V_*.
$$

At every reached cut, with true multiplicative component $z_i=q\alpha^{d_i}$,

$$
|W_i-z_i|
\le|U_i-(b+z_i)|+|V_*-b|
\le2\varepsilon=e.
\tag{136}
$$

The same fixed $b$ in both ports is exactly what licenses (136). Correlation, adaptation, and reusing one reference error do not affect this pointwise inequality.

For each Step, retain precisely the candidates $c\in\{1,\alpha,\alpha^2\}$ satisfying

$$
|W_i-cW_{i-1}|\le(1+c)e.
\tag{137}
$$

The actual candidate always satisfies (137). By the actual source transitions, depth increases by at most four before and through the second actual block update. The elementary bounds used in Lemma 17.1 give $\alpha^4>1/8$. Thus, throughout that interval,

$$
z_i>1023e/8,\qquad
W_i>(1023/8-1)e>64e.
\tag{138}
$$

Lemma 17.1, with error parameter $e$, therefore makes (137) unique and correct at each of these Steps. This is an induction on actual Steps up to the second actual block update: no earlier Step can be falsely classified as an update, and neither actual update can be missed. Inequality (138) refers to the real source run independently of the algorithm's tentative labels. It is not an assumption about the correctness of those labels.

All comparisons in (137) are exact comparisons of finite elements of $\mathbb Q(\sqrt5)$, as in Definition 17.2. The finite arithmetic does not require $q$ or $b$. The initial difference may have either sign during the search; after (134), all differences used for (137) are positive by (138).

Record the local Step numbers $t_1,t_2$ of the first two nonunit classifications and their true length increments $g_1,g_2\in\{1,2\}$. Each actual Step is finite. The clock transitions ensure that both updates occur after finitely many Steps. More precisely,

$$
t_1=\delta_0+1,\qquad
t_2-t_1=G_{D-1},\qquad D=d_0+g_1\ge1,
\tag{139}
$$

where $\delta_0=0$ at return zero and otherwise $\delta_0=G_{d_0+1}-2-s_0$.

Generate the strictly increasing Fibonacci weights until the unique $D$ satisfying (139) is found. Output

$$
d_0=D-g_1,\qquad
s_0=G_{d_0+1}-1-t_1.
\tag{140}
$$

For $d_0\ge1$, (139) proves that these are the real original coordinates. For $d_0=0$, the first Step reads a block, so $t_1=1$, and (140) gives $s_0=G_1-2=0$; output the empty boundary in this case. For a proper entry, use (132) for its exact oriented boundary and owned lifts. This is the original-entry inversion of Theorem 17.3, applied after the error transport (136), rather than substituting an attained boundary for the entry.

Stop at the actual Return of the second update. Its real reached coordinates are

$$
d_*=d_0+g_1+g_2,\qquad s_*=G_{d_*}-1.
\tag{141}
$$

All Steps used the handed-off endpoint and its real unread tail. No history was replaced or source rewound. Keep the genuine original calling right together with (141) and the local Step count. For the operation counts, put $m=t_2$. The protocol completes exactly

$$
\begin{array}{c|c}
\text{primitive resource}&\text{number}\\\hline
\text{Reference before first Step}&n_*\\
\text{Reference in the entire recovery}&n_*\\
\text{Extent}&n_*+m\\
\text{actual Step / producer event triples}&m\\
\text{new actual raw Reads}&g_1+g_2\in\{2,3,4\}.
\end{array}
\tag{142}
$$

Moreover

$$
m=\delta_0+1+G_{d_0+g_1-1}\le2G_{d_0+1},\qquad d_*\le d_0+4.
\tag{143}
$$

These are Theorem 17.3's actual clock counts: all forced zeros in the two new blocks are read and charged. Every request precision, complete reply bit, integer computation, stored field, and output remains paid. Equations (135), (142), and (143) are per-instance bounds and exact call counts. The pre-handoff driver still pays its actual $r$ Next calls, $d_0$ raw Reads and finite configuration; those costs do not disappear from the same run. Reference adds its own paid requests and complete replies, and its finite service arithmetic is paid as well. No uniform bit-cost or latency bound is asserted. $\square$

## 38. Proper death entries with constant affine signal

**Definition 38.1 (Two deterministic floor ports).** The specified subclass of allowed errors at both ports is

$$
F_{q,b}(d,n)=\lfloor2^n(b+q\alpha^d)\rfloor,
\qquad R_b(n)=\lfloor2^nb\rfloor.
\tag{144}
$$

Both replies satisfy their closed error contracts. They are deterministic finite integer services. The Extent floor is the one in Definition 25.1 and (101); the Reference floor of the rational $b=C/F$ is the integer quotient $\lfloor 2^nC/F\rfloor$. Framing, service completion, and acknowledgement contain no side information.

**Lemma 38.2 (An odd-depth constant-alpha family).** There is a sequence of actual proper death-handoff worlds, each with fixed positive rational $q$ and nonnegative rational $b$, whose initial Extent true value is exactly $\alpha$. For every finite set of precisions, the Reference floor replies in sufficiently late members equal $\lfloor2^n\alpha\rfloor$ at all those precisions.

**Proof.** Let $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$ be ordinary Fibonacci numbers, so $G_j=F_{j+2}$. The identity

$$
\alpha^d=(-1)^{d-1}(F_d\alpha-F_{d-1}),\qquad d\ge1,
\tag{145}
$$

follows by induction from $\alpha^2=1-\alpha$: multiplication of the right-hand side by $\alpha$ changes it to
$(-1)^d(F_{d+1}\alpha-F_d)$.

For each odd $d\ge1$, install

$$
q_d=1/F_d,\qquad b_d=F_{d-1}/F_d.
\tag{146}
$$

Choose the actual source $x=0^\infty$ and hand off after

$$
r_d=G_{d+1}-2
\tag{147}
$$

actual initialized Next calls. This is the actual history $p=0^d$, $N_p=0$, $s=r_d$ in Theorem 12.2, with $s\in J_d$. Theorem 3.1 realizes it on the source $0^\infty$ from the prescribed empty initialization. It is proper and has $\delta(d,s)=0$, including $d=1,r_1=1$. No extra read or symbolic-state initialization is used.

For odd $d$, (145) gives

$$
b_d+q_d\alpha^d=\alpha,\qquad
\alpha-b_d=\alpha^d/F_d>0.
\tag{148}
$$

Thus every static Extent request has exactly the first reply in (144) with true signal $\alpha$, at arbitrary precision. Also $b_d\to\alpha$ from below through rational values. For each fixed finite $n$, irrationality of $\alpha$ gives

$$
\ell_n=2^{-n}\lfloor2^n\alpha\rfloor<\alpha<\ell_n+2^{-n}.
$$

For a finite precision set $P$, choose odd $d$ so large that
$\alpha-b_d<\min_{n\in P}(\alpha-\ell_n)$, with no restriction needed if $P$ is empty. Then

$$
\lfloor2^nb_d\rfloor=\lfloor2^n\alpha\rfloor\quad(n\in P).
\tag{149}
$$

Each choice (146) is fixed before that world's initialized run; it never changes during that run. The source is the same $0^\infty$ throughout this family, so this construction needs no configuration inferred from private source bits. $\square$

## 39. Bounded primitive Reference use forces a finite static prefix

**Lemma 39.1 (One-world realization of the whole static path).** Fix a finite integer $K\ge0$. Suppose a causal deterministic receiver $\mathcal D$ stops in finitely many operations on every proper death-handoff world with the two floor services (144), and satisfies $B_{\mathcal D}\le K$ on all those worlds. Correctness is not needed for this lemma. Consider its formal static interaction in which every Extent$(n)$ and Reference$(n)$ is answered with

$$
A(n)=\lfloor2^n\alpha\rfloor,
\tag{150}
$$

with the stipulated full framing and source-independent public controls. Then a first Step initiation or a prior stopping decision occurs after a finite prefix.

**Proof.** We first use only finite-prefix realizability. Before any Step, a finite prefix of this formal interaction mentions finitely many Reference precisions. Lemma 38.2 supplies one actual proper death world matching all those Reference replies. Its Extent true signal is exactly $\alpha$, so it matches all the Extent replies in that prefix as well. Identical controls and deterministic finite-prefix causality realize the entire prefix on that world, including each requested precision, literal reply frame, and local computation. If the prefix ends inside a reply frame, choose the same precision and match the entire frame; this also matches the observed partial frame.

If the formal static interaction completed $K+1$ primitive Reference calls before Step or stop, its finite prefix through the last such completion would therefore occur on an actual proper death world. This would violate the assumed budget there. Consequently the formal static interaction has at most $K$ such completed Reference calls.

Suppose nevertheless it never initiated a Step or stopped. In this entire hypothetical static interaction, the set $P$ of Reference request precisions is finite. Indeed at most $K$ Reference transactions complete, and the sequential interface can have at most one further in-progress Reference transaction. A finite service frame does not create infinitely many new requests; a receiver that diverges during local work or an unfinished receipt has no new completed request to use. Include the finite precision of that pending transaction in $P$ if present.

Now choose **one** odd $d$ in Lemma 38.2 satisfying (149) for this entire finite set $P$. Keep its fixed rational $(q_d,b_d)$ and its one actual proper death entry for the rest of the argument. Every Reference frame occurring anywhere on the hypothetical infinite static path matches in this same world. Every Extent frame, even at an unbounded sequence of future precisions, matches because the true static Extent signal in this world is exactly $\alpha$. All public controls match as well. Determinism therefore gives the same complete infinite static interaction, or the same local-computation divergence, on this one actual world. This contradicts finite stopping on that world.

The argument's two realizations have different roles: finite-prefix realizability excludes a $(K+1)$-st Reference completion, whereas the resulting finiteness of $P$ permits one-world realization of the alleged whole infinite static path. No totality assumption was applied to (150) as if it were a world with $q=0$ or irrational private $b$. The conclusion follows. $\square$

## 40. Same-configuration two-port entrance obstruction at every fixed budget

**Theorem 40.1 (Proper-death two-floor lower bound).** For every finite integer $K\ge0$, no causal deterministic receiver can simultaneously have the following three properties, even when its promised inputs are restricted to proper death entries and both ports use the fixed floor services (144):

1. it stops after finitely many operations on every such initialized world;
2. it outputs that world's exact original entry boundary, with its oriented wall roles and owned lifts;
3. on every such world its completed primitive Reference replies before the first actual Step, or before stopping without a Step, number at most $K$.

There is no restriction here on finite adaptive precision, total Extent calls, local computation, Steps, or Reference calls after the first Step. The final configuration (152) may depend on the receiver and its finite prefix. It is the same fixed configuration in the two final worlds, chosen independently of the common tail and installed before either initialized run. The theorem does not assert failure at every configuration specified in advance.

**Proof.** Assume a receiver has all three properties. Apply Lemma 39.1 and let $P_0$ be its finite formal static prefix through first Step initiation or prior stopping. If a decision is made within a query transaction, include that request precision. Define

$$
N=\max\bigl(\{1\}\cup
\{n:\text{either port was requested at precision }n\text{ in }P_0\}\bigr),
\quad h=2^{-N},\quad L=h\lfloor2^N\alpha\rfloor.
\tag{151}
$$

Choose the single rational configuration

$$
b_*=L+h/2,\qquad q_*=h/4.
\tag{152}
$$

It is fixed, with $b_*>0$ and $q_*>0$. The three quantities

$$
b_*,\qquad b_*+q_*\alpha,\qquad b_*+q_*\alpha^2
\tag{153}
$$

all lie strictly between $L$ and $L+h$. The irrational number $\alpha$ is also strictly in that dyadic cell. A precision-$N$ dyadic cell is contained in a single cell at every precision $1\le n\le N$. It follows that

$$
\begin{aligned}
\lfloor2^nb_*\rfloor
&=A(n),\\
\lfloor2^n(b_*+q_*\alpha)\rfloor
&=A(n)
=\lfloor2^n(b_*+q_*\alpha^2)\rfloor,
\qquad 1\le n\le N.
\end{aligned}
\tag{154}
$$

Install (152), the same two floor programs, and the same public endpoint and control conventions in each of the following two worlds supplied by Lemma 28.1. One may take the common tail $t=0^\infty$.

$$
\begin{array}{c|c|c|c|c|c|c|c}
&x&p&r&d&N_p&s&\text{actual unread tail}\\\hline
W_A&010t&0&1&1&0&1&10t\\
W_B&000t&00&3&2&0&3&0t
\end{array}
\tag{155}
$$

These are actual initialized runs, with different proper death entries $\partial(1,1)$ and $\partial(2,3)$. In particular, the first has initial owned wall point $x_1^+$ at $e_1$ and terminal owned point $Z(0)$ at $e_0$; the second has initial owned point $Z(1)$ at $e_{-1}$ and terminal owned point $Z(0)$ at $e_0$. Their arc lengths are $\alpha$ and $\alpha^2$.

The actual-history content of the supplier is important: $W_A$ has performed one genuine Next, reading its initial zero; $W_B$ has performed three, reading zero on each of its first two calls and no raw bit on the third. Their initialized emitted words are respectively $0$ and $010$. Only the fixed handoff acknowledgement, not those driver histories, is available after handoff. No forced zero in the next $10$ block has been pre-read in $W_A$.

Before the first receiver Step the two true affine signals are the last two values of (153), and the Reference true signal is $b_*$ in both worlds. Equation (154) matches their whole port frames to $P_0$. Induction on causal observations, including partial-frame decisions when allowed, therefore makes both worlds follow precisely this same finite prefix with the same next requests and precisions. There is no a priori cap on what precision the receiver might request: $N$ was taken from the already finite prefix furnished by Lemma 39.1.

If it stops there without a Step, it gives one identical answer to the two different original boundaries, contradicting correctness.

Otherwise it initiates the first actual Step in both worlds. The supplied actual transition is

$$
\begin{array}{c|c|c|c|c|c|c|c}
&p'&n&d'&N_{p'}&k_{p'}&s'&\text{actual unread tail}\\\hline
W_A&010&2&3&2&4&4&t\\
W_B&000&4&3&0&6&4&t.
\end{array}
\tag{156}
$$

The first call actually reads one and its forced zero, and the second actually reads one zero. Both emit the actual bit $\operatorname{Low}(3)=0$, then Advance and Return. In particular the entire publicly visible event sequence, with bit values, is identical. If the receiver terminates on an intermediate transaction event, its observations and answer are already identical, giving the same contradiction. Hidden Read counts are not public advice.

If it continues through Return, both worlds have the same complete current point and boundary $\partial(3,4)$, the same depth three, the same slack two, and the same actual unread tail. We use the actual whole-future invariant of Lemma 28.1, not merely equality of current lengths. After any further matched finite source continuation there is a common acquired block word $w$ with

$$
\begin{gathered}
p_A=010w,\quad p_B=000w,\quad d_A=d_B=3+|w|,\\
N_A=N_B+2,\quad n_B=n_A+2,\quad k_B=k_A+2,\\
N_A+n_A=N_B+n_B,\quad k_A-n_A=k_B-n_B,\\
\text{unread tail}_A=\text{unread tail}_B
=\operatorname{tail}_{|w|}(t).
\end{gathered}
\tag{157}
$$

Thus nonreading Steps have equal emissions and clock progress; reading Steps consume the same actual next block, including a forced zero, and have equal actual emitted bit values. These are productive executions of the original endpoints.

At every matched returned cut after (156), Extent replies coincide at **every** finite precision by equal depths and the common fixed $(q_*,b_*)$. Reference replies coincide at **every** finite precision because

$$
R_{b_*}(n)=\lfloor2^nb_*\rfloor
$$

is the same in both worlds independently of depth. No use of $n\le N$ is made after the first Step. Whole integer frames, service completions, fixed acknowledgements, valid rights, endpoint descriptor literals, local counts, and legal control outcomes coincide. Checks, pauses, and releases have the same source-independent rules. Source time does not advance during any of them.

Induction on complete command/event prefixes now couples every adaptive future query and Step and every allowed transaction-prefix decision. An arbitrary infinite continuation is coupled coordinate by coordinate because each coordinate lies in a finite prefix. This does not claim an infinite continuation is finitely completed. In particular, no number of later Reference calls or larger precisions can distinguish the original entries. If the receiver has legitimately completed an acquisition that earns a current record, the current $(d,s,i;\kappa)$ parts agree. The programs of Definition 18.1 then have identical DATA guards, budgets, finite representatives, refusals and rights, and every internal Step is covered by (157). This statement retains that acquisition premise; neither an initial current-record oracle nor an export of the unequal private producer histories is supplied.

Both final worlds satisfy the receiver's proper-death finite-stopping hypothesis. Hence it eventually stops at the same observable position and returns the same answer in both. Their original boundaries in (155) remain different, so at least one answer is wrong. The contradiction proves the theorem. $\square$


## 41. Exact Reference-resource relation and its scope

**Corollary 41.1 (Finite per-instance use and unbounded pre-Step Reference resource).** In the extended same-$b$ all-error model, there exists an original-entry receiver that is finite on every world and error trace, while for every such successful receiver

$$
\forall K\in\mathbb N\quad
\exists W,\eta:\quad B_{\mathcal D}(W,\eta)>K.
\tag{158}
$$

The witnesses in (158) can already be chosen among actual proper death entries with both ports using (144).

**Proof.** Existence is Theorem 37.1, including return zero and all allowed errors. If some successful receiver had a fixed finite bound in (158), it would in particular have that bound and finite correctness on the proper-death two-floor subclass. This contradicts Theorem 40.1. The same argument shows that its budget cannot be bounded even on that subclass. Each budget on that subclass is individually finite by totality. $\square$

**Definition 41.2 (Supplier correspondence and the source-specific synthesis).** The mathematical increment of §§36–41 is the resource relation of Corollary 41.1 for primitive same-offset Reference completions before the first actual Step. Its lower-bound ingredients are the proper odd-depth family, one-world realization of an alleged infinite static path under a finite completion budget, and simultaneous coupling of both floor ports to one common configuration. This is a `repo-derived` synthesis for the source and observation interface of Definition 36.1.

The positive proof uses subtraction only as an intermediate error transport, then applies the existing ratio and clock results. The lower bound reuses the actual initialized merger instead of declaring equality of symbolic states or scalar values sufficient. The precise inherited correspondence is:

| Supplier | Use under its original conditions |
| --- | --- |
| Definitions 1.2, 2.2, 16.1, 22.1 and Theorems 3.1–3.2 | Empty-frontier initialization, actual no11 source, finite sequential Read/Next, physically read forced zeros, retained exclusive rights, genuine events and exact actual-tail continuation. The additional Reference operation does not advance or read this source. |
| Theorems 12.2–12.3, (38)–(48) | Unique entrance coordinates, positively oriented walls and their particular owned lifts, proper lifetime endpoints and birth/death clock rules. Definition 36.2 recalls these results rather than supplying new coordinate theorems. |
| Lemma 17.1, Definition 17.2 and Theorem 17.3 | Three-ratio classification with closed absolute error, finite quadratic comparisons, inversion from the first two actual updates and the complete intervening lifetime, and the genuine operation/Read counts. Theorem 37.1 first establishes its transported error bound (136); the old multiplicative hypothesis is not applied directly to affine Extent replies. |
| Definitions 25.1, 27.1–27.2 and Lemmas 28.1–28.2 | Finite unsaturated floor replies, the full public observation class, source-independent controls and the initialized pair (102)–(104). Theorem 40.1 separately checks the new Reference frames, both before the merger and at every later precision. |
| Definition 18.1 and Corollary 24.2 | Legitimately acquired current records and their guarded finite use. These results supply no initial getter, absolute counter or private-history export. |
| [Exact Current Boundary Provenance][AFF-PROV], Definition 1.1 and Theorems 2.1–2.2 | The full current-point and actual-tail correspondence already used in Lemma 28.1. Its different original projection interface alone does not establish equality of the two new port observations. |
| van den Bos–Vaandrager, [*State Identification for Labeled Transition Systems with Inputs and Outputs*][ENT-IDENT], §§1–3; Brattka–Gherardi–Pauly, [*Weihrauch Complexity in Computable Analysis*][WCA], Definitions 4–9 | The `literature-attested` background correspondence of Convention 30.2: initial-state identification, compatibility after actions and finite approximate names. Those general frameworks do not supply the proper odd-depth family or this two-port primitive-call bound. |
| [Pinned finite Zeckendorf arithmetic][MATHLIB] and Definitions 13.2, 19.1 | Finite canonical arithmetic and exact quadratic sign comparisons within the foregoing proofs. Fibonacci identities, triangle inequalities, floor cells and equal-observation induction are intermediate ingredients, not additional general principles. |

The cited literature is used only for this bounded correspondence. No global novelty or exhaustive literature classification is assigned to the synthesis.

**Definition 41.3 (Interface and recovery scope).** Theorem 29.1 and Corollary 30.1 concern the original interface without Reference. Definition 36.1 explicitly enlarges that interface; Theorem 37.1 neither changes nor refutes the earlier no-Reference entrance obstruction. Theorem 40.1 concerns the enlarged class with a fixed finite primitive Reference bound, and its receiver-dependent configuration quantifier remains the one stated there. It is not a theorem of failure for every individually predesignated configuration. The all-error positive theorem covers jointly adaptive closed errors; the negative witnesses use the two particular deterministic floors of Definition 38.1.

The recovered original boundary is its oriented region with its actual owned lifts, including the empty entrance. It is not the actual private producer history $(p,r)$, the individual $N_p$, exact instrument parameters $q,b$, an authenticated initialization-time counter, the unread infinite source or a rollback of the reached source. The attained record and any subsequent finite use retain the acquisition, persistent-right, DATA-guard and budget premises of §§18 and 24. A locally computed witness of a boundary is not asserted to be the actual producer prefix.

The original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization, full-original-response and arbitrary interior-cut obligations of Definitions 9.2 and 26.3 keep their original scopes. The exact FIB $p_J$/all-response problem and original global 8-versus-9 problem are different targets; no bridge to them is asserted by Corollary 41.1. Neither an unrestricted space/time/boundary/memory inverse nor an equivalence with a physical realization follows from this additional observation contract.

## 追加锚（本行以下为增补区）

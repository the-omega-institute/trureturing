# Overlapping spatial records and retained chronology

## 1. The finite source and selected-past contract

**Definition 1.1 (source and interpretation).** This is a `repo-derived`, ordinary finite classical construction using [Boundary Dynamics](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md) §§100–105 and 114.1. Its mathematical claims have no Lean verification; broader recovery claims remain open. Fix $m=2$, $d=1$, $\ell=2$, $n=4$ and $\mathbb F_2=\{0,1\}$. The same actual hidden depth $K=k\ge1$, or one fixed common prior $\mu$, governs seed acquisition and all payload Reads. Given $k$, restored fresh Reads are independent with $\Pr(\alpha)=r_k=F_{k+1}/F_{k+3}>0$ and $\Pr(\beta)=1-r_k>0$.

The paid seed prelude interprets $\alpha\beta$ as 0 and $\beta\alpha$ as 1, discarding equal pairs with paid retries. It retains the actual seed $R$. Payload segments use the original parser

$$
w_{j,0}=(\beta\alpha)^j\alpha,
\qquad w_{j,1}=(\beta\alpha)^j\beta\beta.
$$

Only completed markers count toward $n$. The public initialized passive selector $\pi$ bookmarks exactly after the third completed marker on every four-marker word, including rejected words. It then continues the actual payload to the original $\mathrm{Stop}_{w_4}$; there is no Read after Stop. Retries, return cycles, incomplete parsing and noncompletion are retained in the source contract.

For the actual seed $\rho=1$, the repeated coefficients are $v_1=v_2=v_3=v_4=1$ and $C_1=1+1=0$ in $\mathbb F_2$. For a marker prefix $u$ of length $t$, the original fields are $\beta(u)=|u|$ (integer weight) and $h(u)=|u|\bmod2$. Here $\beta(u)$ is a field name, distinct from the raw Read symbol $\beta$.

**Definition 1.2 (one positive selected cell).** Use the original fingerprint acceptance event

$$
E_1=\{R=1,\ Q_4=(0,2),\ \widetilde A=1\},
\qquad H=\{w\text{ in }E_1:|w_1w_2w_3|=1\}.
$$

The zero in $Q_4$ requires zero payload return cycles. The retained bare snapshot, actual suffix and actual Stop on $H$ are respectively

$$
B_0=(\rho,\ell,t,\beta,h)=(1,2,3,1,1),
\qquad Y=1,\qquad s_{\rm stop}=1.
$$

The selected-past consumer is $T(w)=w_1w_2w_3$. The original decoder $\mathscr D_\pi$ of §§105–106 and 114.1 takes the zero-based colex rank in the entire selected dictionary, not an ordinary lexicographic rank. In this cell its dictionary is $[100,010,001]$: reverse the three coordinates and compare with $0<1$.

**Proposition 1.3 (actual accepted witnesses).** The complete marker words in $H$ are exactly $1001,0101,0011$. Each has positive joint source mass

$$
\lambda=\frac12\sum_{k\ge1}\mu(k)r_k^2(1-r_k)^4>0,
$$

or the corresponding single-depth term. These are three members of the six-word accepted support of $E_1$, rather than the whole accepted support.

Proof. At seed 1 the fingerprint is the parity of the complete weight, so every weight-two zero-return word passes it. Exactly one of the first three positions is 1 precisely for the three displayed words, whose last marker is then 1. Their literal payloads follow $0\mapsto\alpha$, $1\mapsto\beta\beta$; each uses two $\alpha$ and four $\beta$ Reads. The seed and payload law of §§100.2 and 102.2 gives the displayed positive mass. Acceptance here means $\widetilde A=1$, not the stronger true pairing condition $A=1$: $0101$ passes the fingerprint but fails true pairing. The restriction to $H$ is retrospective; no conditional source sampler or advance acceptance input is supplied. $\square$

## 2. Spatial scopes and the chronology they lose

**Definition 2.1 (event identity and retained local records).** Within the selected prefix on $H$, let $a$ be its first zero event, $b$ its first one event, and $c$ its second zero event. Identity includes the ordinal within its marker kind, but no global position or timestamp. Thus $a$ precedes $c$. Supply two labelled discrete spatial scopes

$$
S_1=\{a,c\},\qquad S_2=\{b,c\},\qquad S_1\cap S_2=\{c\}.
$$

The two occurrences of $c$ in the records refer to the same actual event. A chronological event word $\omega$ is one of $abc,bac,acb$, corresponding respectively to selected marker words $010,100,001$. Define $r_i(\omega)$ by deleting events outside $S_i$ while preserving the order of retained events, and let $q(\omega)=(r_1(\omega),r_2(\omega))$.

The records are actually acquired: initialize each to the empty word, append a completed event to every scope containing it, and hold both after the third-marker bookmark. The original completed-marker count $t$ and weight $\beta$ identify a first zero by old $t-\beta=0$, a second zero by old $t-\beta=1$, and a first one by old $\beta=0$. This gives finite causal record updates even on prefixes outside $H$, where absent identities need not appear. The receiver gets the two frozen ordered records, with their shared-event identity, and no merged delivery log, global indices, clock, or replay archive.

**Proposition 2.2 (the missing cross-scope relation).** With inverse images restricted to $\Omega=\{abc,bac,acb\}$,

$$
q^{-1}(ac,bc)=\{abc,bac\},
\qquad q^{-1}(ac,cb)=\{acb\}.
$$

Agreement on the shared event does not determine whether $a$ or $b$ occurred first.

Proof. The first record is always $ac$. For $abc$ and $bac$ the second record is $bc$, while for $acb$ it is $cb$. In the first case the local relations are only $a\prec c$ and $b\prec c$; both orders between $a,b$ are actual accepted possibilities by Proposition 1.3. In the second case the records give $a\prec c\prec b$. $\square$

## 3. The precedence bit is acquired and held

**Definition 3.1 (retained chronology register).** Supply one persistent register $z\in\{0,1\}$, initialized to 0 before seed acquisition. At the actual first completed payload marker, write that marker's value to $z$. Every other raw event holds it, including seed retries, return cycles, partial parsing, later markers, the bookmark and Stop. The same register is retained through decoding; there is no additional frozen output copy. The original parser's old completed count $t=0$ identifies this write, so the register needs no private first-marker flag.

**Hypothesis 3.2 (same-source event contract).** The selector has the same fixed initialization on the same actual source history as the parser and local record writers. All completed-marker events, old/new fields, acquired seed, bookmark, retained records, register and subsequently delivered suffix and Stop belong to that execution. Record updates and the first-marker write complete before their transaction is retained; the third-marker record updates complete before the bookmark latch. Selection does not depend on $z$. No event from another history, event issued before marker completion, speculative decision, earlier latch or new replay port is admitted.

**Proposition 3.3 (retained relation invariant).** Under Hypothesis 3.2, at the bookmark and every later event on $H$,

$$
z=w_1=\mathbf1\{b\prec a\}.
$$

Proof. Before the first completed payload marker the register is 0 and all non-marker events hold it. Its unique write stores $w_1$, and every later event holds that value. On $H$ both $a$ and $b$ exist: the first marker is 1 exactly when the first one $b$ precedes the first zero $a$. The actual bookmark therefore retains a relation from the observed history. Decoding never receives an independently chosen chronology bit. $\square$

## 4. Restoring the original chronological consumer

**Definition 4.1 (finite adapter to the supplied decoder).** On the realized record/register pairs, define

$$
j(ac,bc,z)=1-z,\qquad j(ac,cb,0)=2.
$$

The adapter supplies this integer to the unchanged original $\mathscr D_\pi$ together with $B_0,Y,s_{\rm stop}$. It does not replace that decoder's full nonnegative-integer domain, its dictionary, interface checks or original defaults. No result about other adapter addresses is asserted.

| Accepted full marker word | Chronological selected events | Retained local records $q$ | Retained $z$ | Selected-past colex rank $j$ | Restored selected past |
| --- | --- | --- | ---: | ---: | --- |
| $1001$ | $bac$ | $(ac,bc)$ | 1 | 0 | $100$ |
| $0101$ | $abc$ | $(ac,bc)$ | 0 | 1 | $010$ |
| $0011$ | $acb$ | $(ac,cb)$ | 0 | 2 | $001$ |

**Proposition 4.2 (failure, restoration and fixed-interface sharpness).** Under the same-source contract on $H$, $q$ alone cannot factor $T$, even with the common $B_0,Y,s_{\rm stop}$. The actually retained pair $(q,z)$ does factor $T$ through the adapter and original decoder. Exactly two supplementary label values, hence one fixed-width bit, are necessary and sufficient relative to this fixed $q$ and selected-past consumer.

Proof. The first two rows have the same supplied local records, bare snapshot, suffix and Stop, but different required selected pasts. Any decoder of those identical inputs must give one answer, so cannot restore both. Their acquired $z$ values differ; the adapter returns ranks 0 and 1. The third row returns rank 2. The original colex dictionary then gives precisely the last column. Any supplementary label needs at least two values on the two-element ambiguous fiber, and Definition 3.1 achieves two values with a causal write and holding rule. This lower bound is conditional on retaining $q$; with only the bare snapshot and suffix the selected dictionary has three members, as in §§104–105. The transient rank $j\in\{0,1,2\}$ is computed from $q,z$, not stored in the one-bit register. $\square$

## 5. Four expressions, supplies and limits

**Definition 5.1 (the exact four-expression interpretation).** All expressions refer to the same selected history and fixed public contract.

| Expression | Mathematical content | Recovery scope |
| --- | --- | --- |
| Space | The labelled incidence scopes $S_1,S_2$ and their common event $c$ | Supplied discrete locality; no metric distance |
| Time | The chronological word $\omega$ and its precedence relation | Order of completed selected markers; no absolute time or duration |
| Boundary | Frozen $(q,\text{bookmark }3)$ with the supplied source snapshot $B_0$ | Local retained orders; the unaugmented boundary merges $abc,bac$ |
| Memory | The actually acquired and held relation $z=\mathbf1\{b\prec a\}$ | The missing cross-scope precedence, interpreted with the boundary |

**Proposition 5.2 (mutual recovery at the stated scope).** With the labelled scopes, source cell and bookmark supplied, the augmented boundary $(q,z)$ and chronological selected word $\omega$ determine one another on $\Omega$. Their common retained information is sufficient for $T$; neither the bare scopes, $q$ alone, nor $z$ alone has that property.

Proof. Reading a chronological word gives both restrictions and its $b\prec a$ bit. Conversely $(ac,bc,0)$, $(ac,bc,1)$ and $(ac,cb,0)$ reconstruct respectively $abc,bac,acb$, including every precedence relation between $a,b,c$. Replacing $a,c$ by 0 and $b$ by 1 gives $T$, and the table gives the inverse within this cell. The scopes are fixed across all three histories; $q$ merges the first two; $z=0$ merges $abc,acb$. Thus the joint recovery does not make all four bare expressions independently sufficient. $\square$

**Definition 5.3 (supplies and cost coordinates).** The additional final chronology register has two values throughout initialization, acquisition and retention. The final local records contain four event-label occurrences, including two references to the same $c$, and have two realized joint values on $H$. A compressed joint record alphabet and two physically retained local lists are different resource contracts. The original source, paid seed Reads/retries and retained seed, parser, counters, completed-event routing, selector initialization and bookmark latch, spatial incidence/identity convention, local record storage and writes, frozen snapshot, actual suffix/Stop delivery, adapter arithmetic, original decoder/dictionary and output storage all remain separately supplied and charged. No label count here prices their total or peak space, time, energy, or raw Read cost. Marker length four does not bound seed retries on unrestricted executions.

**Definition 5.4 (relation to the existing theory).** Boundary Dynamics §§25–27 supplies the distinction between joint target recovery and each representation being sufficient; §§36–39 supplies the distinction between task-relative common information, dynamic operation and completion. Section 40 distinguishes local compatibility from global recovery. Here the shared identity $c$ and its local order agree, yet the accepted pair $abc,bac$ supplies a concrete missing precedence edge. This is a source-realized local-record obstruction and a retained-edge construction, rather than a new generic quotient or gluing theorem.

Boundary Dynamics §§97 and 100–103 supplies the actual marker/parser source, paid seed, positive accepted support and colex convention; §§104–108 supplies passive selection, the original selected-past consumer and completed-event/retention contract. Sections 109–114 preserve factorization direction, common realizations, canonical outputs and separate resource coordinates. The standalone [§115 continuation](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS_CONTINUATION.md) supplies a different event-aware response-index gap and its synchronization boundary; its numerical gap is not used or extended here. These are repository-source attributions. The new content is the explicit overlapping-scope record map on this source and its causally retained precedence repair, with no external originality claim.

**Definition 5.5 (unresolved limits).** This finite task-relative witness does not recover metric distance, absolute time, return-cycle histories, seed-acquisition transcripts, hidden depth, arbitrary protocols, or a global spacetime completion. It does not establish autonomous operation from the frozen boundary after removing supplied parser/selector state, general optimal memory, or minimal total acquisition resources. Other source cells, seeds, scope families, event schedules and consumers require their own compatible-history and acquisition analyses. Broader conditions for four independently sufficient expressions, unbounded local-to-global chronology recovery and physical interpretations remain open.

## 追加锚（本行以下为增补区）

## 6. All positive third-latch histories and their finite marker records

**Definition 6.1 (source, cut and acquired information).** Keep Definition 1.1's $m=2,d=1,\ell=2,n=4$, paid seed extractor, original parser, common hidden $K$, and unique original Stop. Install one fixed finite or countable depth prior $\mu$ before the first Read; a fixed depth is its point-mass case. Given $K=k$, every legal Read uses the same $r_k=F_{k+1}/F_{k+3}$ and is conditionally fresh. Let $\mathcal H_3(\mu)$ be the positive finite histories at the third-marker latch, before any fourth-segment Read. Conditioning uses only the actually acquired filtration of [Future Response Sufficiency](RECURSIVE_RELATIONAL_OBSERVATION_FUTURE_RESPONSE_SUFFICIENCY.md) §§9,15. It does not include $E_1$, a fourth marker or an undelivered Stop. The paid Read index $N(h)$ is an analysis variable, not a clock port. Infinite retry/return paths have no completed third-latch record.

Use the finite marker-record supplier [Full E1 Scope Extension](RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md) §2:

$$
S_1^+=\{a,c,d\},\qquad S_2^+=\{b,c\},
$$

where $a,c$ are the first two zeros and $b,d$ the first two ones. Third occurrences of one kind have no identity in these scopes. The records $Q^+=(r_1^+,r_2^+)$ are written only at completed markers with old $t<3$, and $Z$ holds the first marker. Both seed values use the same writer. The original bare weight field at the latch is denoted $w=\beta(b_1b_2b_3)$; the raw-letter count $B$ below is a different object.

This supplier is not silently identified with Definition 2.1's old $Q$. If only the old scopes are installed, add and pay for the actual incidence $d\in S_1^+$ with that supplier's writer. The first retained local alphabet changes from $\varnothing,a,ac$ to $\varnothing,a,ac,d,ad,da$; the second remains $\varnothing,b,c,bc,cb$. The added occurrence has ordinal identity supplied by old $(t,\beta)$, with no timestamp. This explicitly retained finite incidence, its routing and its writes are part of the recovery contract.

**Theorem 6.2 (finite records supply every marker coordinate).** On all of $\mathcal H_3(\mu)$, the supplied $(w,Q^+,Z)$ determines the complete marker triple, for both actual seeds and every retry/return history. Conversely the marker triple determines these finite records. Their complete actual table is

| Marker triple | $w$ | $r_1^+$ | $r_2^+$ | $Z$ |
| --- | ---: | --- | --- | ---: |
| $000$ | 0 | $ac$ | $c$ | 0 |
| $001$ | 1 | $ac$ | $cb$ | 0 |
| $010$ | 1 | $ac$ | $bc$ | 0 |
| $011$ | 2 | $ad$ | $b$ | 0 |
| $100$ | 1 | $ac$ | $bc$ | 1 |
| $101$ | 2 | $ad$ | $b$ | 1 |
| $110$ | 2 | $da$ | $b$ | 1 |
| $111$ | 3 | $d$ | $b$ | 1 |

Proof. At each marker completion the old zero count $t-\beta$ and one count $\beta$ identify the appropriate first or second occurrence, exactly as in the supplier's four routing rules. A third occurrence is unmatched and leaves the local records unchanged. Reading the eight triples through these rules gives the table. Its eight addresses are distinct. All non-marker events hold these fields; seed acquisition chooses coefficients in the bare syndrome but does not change routing. Hence the table applies to both seeds with arbitrary intervening retries and returns. It uses no future acceptance information. With the old $Q$ instead, $110$ and $101$ still share $(w,Q,Z)$; the added incidence is a necessary supply for this particular table. $\square$

**Theorem 6.3 (source normal-form bijection).** Put $X=\alpha\alpha$, $Y=\beta\beta$, $s_0=\alpha\beta$, $s_1=\beta\alpha$, $c_0=\alpha$, $c_1=\beta\beta$. The map

$$
(\rho,b,u,\mathbf j)\longmapsto
h=u\,s_\rho\mid
\prod_{i=1}^{3}(\beta\alpha)^{j_i}c_{b_i},
\qquad
\rho\in\{0,1\},\quad b\in\{0,1\}^3,\quad
u\in\{X,Y\}^{*},\quad \mathbf j\in\mathbb N^3
\tag{SC.1}
$$

is a bijection onto $\mathcal H_3(\mu)$. The displayed delimiter and segment boundaries are determined by the original parser; they are not inputs from another execution. If $p=|u|_X$, $q=|u|_Y$, $s=j_1+j_2+j_3$, and $w=b_1+b_2+b_3$, its from-zero raw counts are

$$
A=4-w+2p+s,\qquad B=1+2w+2q+s,\qquad
N=A+B=5+w+2(p+q+s).
\tag{SC.2}
$$

Proof. In the seed control, each equal pair is rejected and every first unequal pair accepts exactly its displayed seed. Thus the prelude uniquely yields $u,s_\rho$. In segment $i$, each $\beta\alpha$ returns to its initial phase, while $\alpha$ there completes zero and $\beta\beta$ completes one. Reading until each of the first three completions uniquely yields $j_i,b_i$; no earlier delimiter or replay is needed. Conversely every tuple follows these exact transitions and first reaches the third completion at the final letter of (SC.1). Every letter has positive probability at every supported depth, so every tuple has positive common-prior mass. Parsing and concatenating are inverse, not just mutually compatible descriptions. The accepted seed contributes one letter of each kind, each reject contributes two of its kind, each return contributes one of each, and the three completion suffixes contribute $3-w$ alphas and $2w$ betas. This proves (SC.2). $\square$

## 7. Acquiring, holding and interpreting the raw chronological relation

**Hypothesis 7.1 (priced same-history supplementary record).** Extend the observer by an empty rejection-word record $U$ over $\{X,Y\}$ and three initialized nonnegative counters $J_1,J_2,J_3$. During the paid prelude, append $X$ or $Y$ to $U$ when that actual equal pair is rejected. The original seed-second-letter phase distinguishes rejection from acceptance and supplies the pair's kind. No earlier rejected pair is queried later. During payload, increment $J_{t+1}$ precisely on an actual $\alpha$ return from old $q_{\beta,t+1}$ with $t<3$. The original phase and acquired letter identify this transition; no loop-duration measurement is used. All other events hold these fields.

The original third-marker event writes $Q^+$ and any prescribed original fields before the latch. At that latch, the same $U,\mathbf J,Q^+,Z,R$ are held; no second frozen output copy is required. All fourth-segment events and Stop hold the selected-past fields. The controller still performs the original fourth segment and original Stop, including arbitrarily many returns; after Stop it has no Read permission. The original paid finite control, seed, bare snapshot, local records and their read/write access remain charged.

A local recovery query at the third latch may use these held fields. A receiver obtains them only if this entire augmented record is explicitly delivered there, with transmission and output storage charged. The old single bare-snapshot recipient does not automatically get $U,\mathbf J,Q^+,Z$, control copies or another snapshot. No subsequent source query, new Stop, reset, copy of the source, prior resampling or post-Stop source access is granted. The original selected-marker decoder $\mathscr D_\pi$ is unchanged; raw-history reconstruction is a separately declared local target.

**Theorem 7.2 (causal raw recovery and holding).** Under Hypothesis 7.1, for every $h\in\mathcal H_3(\mu)$ the actually held record

$$
\mathsf M(h)=(R,w,Q^+,Z,U,J_1,J_2,J_3)
\tag{SC.3}
$$

determines the complete raw past $h$, including every seed retry and all three segments' returns. Conversely $h$ determines $\mathsf M(h)$. This inverse uses only already acquired data and remains valid for the held selected record along the continuing original execution.

Proof. Before the first Read, $U$ is empty and $\mathbf J=0$. Induction through the seed control shows that $U$ contains exactly the completed rejected pairs in their actual order; partial pairs and the accepting pair do not append. Induction through the payload control shows that $J_i$ counts exactly the completed returns in segment $i$; a pending first $\beta$ has not yet incremented it. Thus at the third completion $U=u$ and $\mathbf J=\mathbf j$ from (SC.1). The original seed supplies $\rho$ and Theorem 6.2 supplies all three $b_i$. Concatenation in (SC.1) therefore reconstructs precisely the actual raw word, and deterministic parsing/writing provides the converse.

All these invariants are adapted to the acquired filtration: each write uses an actual returned letter and its old original phase. The latch follows the third record write, including the all-equal triples' unmatched event. At that instant every required value is already present. The phase $p_4$ and later original phases prohibit further selected-record writes, so the same reconstruction continues to name the past at the latch while the fourth segment advances. This is holding of one acquired record, not retrospective recovery from future observations. $\square$

**Definition 7.3 (precedence and incidence expression).** Give the $X$ retries identities $X_1,\ldots,X_p$ and the $Y$ retries identities $Y_1,\ldots,Y_q$, ordinal within kind. Let $x_j$ be the number of $X$ retries preceding $Y_j$. The acquired retry relation consists of

$$
0\le x_1\le\cdots\le x_q\le p,\qquad
X_i\prec Y_j\ \Longleftrightarrow\ i\le x_j,
\tag{SC.4}
$$

with the intrinsic orders on each kind. Empty lists and zero counts are allowed. Give the returns in segment $i$ identities $L_{i,1},\ldots,L_{i,J_i}$, all incident to that same original segment and ordered by their occurrence. Every retry precedes the accepted seed pair, which precedes all payload segments; each segment's returns precede its completing marker, and segments have the original parser order. Each retry expands to its two equal letters, the actual seed to $s_R$, each return to $\beta\alpha$, and each marker to $c_{b_i}$.

These are relations between actual acquired events. Ordinals, segment membership and the terminal latch have computational/storage costs; they are not global time coordinates. The vector in (SC.4) is a derived reading of held $U$, not another free archive. If stored directly instead, each $Y$ rejection appends the current completed $X$-retry count, which must itself be acquired, stored and charged. An unpacked vector and a binary rejection word have different bit costs.

**Theorem 7.4 (relational reconstruction in both directions).** With the same source grammar and finite marker supplies, the precedence/incidence expression of Definition 7.3, the held record (SC.3), and the raw history at the third latch determine one another on their actual images.

Proof. The generic prefix-count inverse is already supplied by [Joint Moment Fibers](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md), Proposition 3.1: here its letters are the retry types $X,Y$. Specifically (SC.4) and $p$ recover

$$
u=X^{x_1}Y\,X^{x_2-x_1}Y\cdots
X^{x_q-x_{q-1}}Y\,X^{p-x_q}.
\tag{SC.5}
$$

For $q=0$, this means $u=X^p$. Each pair $X_i,Y_j$ has exactly one orientation by (SC.4), so the relation is the unique retry order of (SC.5). The return incidences give the three $J_i$ without confusing occurrences in different segments. The actual seed and the table in Theorem 6.2 then complete (SC.1). Conversely parsing $h$ supplies each retry identity, its cross-kind precedence, every return incidence, seed and marker record; (SC.5) returns exactly the same $u$. Thus the inverse includes the marker-local records rather than treating their shared identities as a source of raw-event order.

The prefix inverse itself is reused, not a new generic theorem. The source-specific step is that its arguments are produced by the original paid seed parser, and that the separately acquired return incidences restore the raw events that the finite marker records held away. $\square$

## 8. Complete raw fibers and their fixed-letter degree-two refinement

**Definition 8.1 (the quantitative slice).** For the remainder of §§8–10 fix the acquired seed $R=1$ and marker triple $100$, at the third latch before any fourth Read. This is a retrospective analysis of positive acquired histories under the one fixed prior of Definition 6.1, not the event $E_1$ and not a conditional source sampler. Write $\mathcal F_{A,B}$ for the raw histories on this slice with from-zero counts $(A,B)$. This symbol denotes a finite fiber, not the acquired filtration.

For $a=A-3$, $b=B-3$, put

$$
\mathcal S_{A,B}
=\{s\in\mathbb N:s\le\min(a,b),\
a-s\in2\mathbb N,\ b-s\in2\mathbb N\},
\quad p_s=(a-s)/2,\quad q_s=(b-s)/2.
\tag{SC.6}
$$

Negative $a$ or $b$ makes this set empty. Distinguish raw $\beta$ count $B$, marker weight $w=1$, the original bare snapshot, and the following ordered-pair count:

$$
C(h)=\#\{i<j:h_i=\alpha,\ h_j=\beta\}.
\tag{SC.7}
$$

**Theorem 8.2 (complete count fiber).** The fiber $\mathcal F_{A,B}$ is exactly the disjoint union, over $s\in\mathcal S_{A,B}$, of all retry words with $p_s$ copies of $X$ and $q_s$ copies of $Y$, and all triples $\mathbf j$ with sum $s$, inserted in (SC.1) with $\rho=1,b=100$. Consequently

$$
F(A,B):=|\mathcal F_{A,B}|
=\sum_{s\in\mathcal S_{A,B}}
\binom{p_s+q_s}{p_s}\binom{s+2}{2}.
\tag{SC.8}
$$

It is nonempty exactly when $A,B\ge3$ and $A-3,B-3$ have the same parity.

Proof. At this triple (SC.2) is $A=3+2p+s$, $B=3+2q+s$. Solving these integer equations gives precisely (SC.6), with no omitted retry kind or return placement. Normal-form uniqueness makes the union disjoint. For each $s$, retry order has $\binom{p_s+q_s}{p_s}$ possibilities and three nonnegative return counts have $\binom{s+2}{2}$ possibilities. If the excess counts have equal parity, choose $s=0$ when both are even and $s=1$ when both are odd. Conversely the equations force the stated parity and nonnegative excess. $\square$

**Theorem 8.3 (complete degree-two classification).** Let $I(u)$ count scattered $XY$ pairs in the retry word and let $s=\sum_i j_i$, $p=|u|_X$, $q=|u|_Y$. On the specified slice,

$$
C(h)=4I(u)+c_s+2j_1+j_3,\qquad
c_s=2p(s+3)+\binom{s+1}{2}+2.
\tag{SC.9}
$$

Define

$$
\begin{aligned}
P_{p,q}(t)
&=\#\{0\le x_1\le\cdots\le x_q\le p:
                 \textstyle\sum_jx_j=t\},\\
g_s(d)
&=\max\{0,\min(s,\lfloor d/2\rfloor)-\max(0,d-s)+1\}.
\end{aligned}
\tag{SC.10}
$$

For $q=0$, $P_{p,0}(0)=1$ and its other values are zero. Then the complete refined fiber size is

$$
F(A,B,C)=
\sum_{s\in\mathcal S_{A,B}}
\ \sum_{t=0}^{p_sq_s}
P_{p_s,q_s}(t)\,
g_s(C-c_s-4t).
\tag{SC.11}
$$

Equality of $(A,B,C)$ is equality of the complete degree-two signature of raw letters represented by the two fixed basis vectors over $\mathbb Z$. It implies equality in every fixed-letter represented step-two carrier. An observation that labels individual occurrences or includes parser context is an additional observation, not this fixed-letter degree-two datum.

Proof. Reuse the ordered-pair concatenation identity in [SignatureOrderedMoment](../../../D5/S3/Observer/Chronology/SignatureOrderedMoment.lean), ordered_pair_moment_append: $C(vv')=C(v)+A(v)B(v')+C(v')$. Within $u$, each $XY$ contributes four raw $\alpha\beta$ pairs; hence $C(u)=4I(u)$. Its cross contribution to the accepted seed and payload is $2p(s+3)$. The accepted $\beta\alpha$ has no internal $\alpha\beta$ pair and its alpha contributes $s+2$ pairs to the payload.

Within the three payload segments, internal return pairs and intersegment return pairs total $\binom{s}{2}$. The first marker's $\beta\beta$ adds $2j_1$ and the second marker's $\alpha$ adds $j_3$ before third-segment betas; the third marker's alpha adds none. Thus the total is $4I(u)+2p(s+3)+(s+2)+\binom{s}{2}+2j_1+j_3$, which is (SC.9). The prefix-count supplier identifies retry words of area $t$ with the vectors counted by $P_{p,q}(t)$. Fixing $d=2j_1+j_3$ gives $j_3=d-2j_1$, $j_2=s+j_1-d$. Nonnegativity is exactly

$$
\max(0,d-s)\le j_1\le\min(s,\lfloor d/2\rfloor).
$$

Its integer count is $g_s(d)$, including $d<0$ or $d>2s$, when it vanishes. Combining these independent choices within each normal-form summand proves (SC.11).

The reused [TruncatedTensorSignature](../../../D5/S3/Observer/Chronology/TruncatedTensorSignature.lean) chronological_tensor_signature_append and SignatureOrderedMoment's diagonal/ordered-pair identity give, for fixed raw basis $e_\alpha,e_\beta$, degree one $(A,B)$ and doubled degree-two coordinates

$$
T_{\alpha\alpha}=A^2,\quad T_{\beta\beta}=B^2,\quad
T_{\alpha\beta}=2C,\quad T_{\beta\alpha}=2(AB-C).
\tag{SC.12}
$$

Hence the complete integral tensor datum and $(A,B,C)$ recover one another. Applying a fixed-letter representation to these coordinates gives its shadow; it cannot distinguish histories already equal in (SC.12). [BinaryParikhStepTwoBridge](../../../D5/S3/Observer/GoldenChronology/BinaryParikhStepTwoBridge.lean), binary_parikh_matrix_entries and binary_doubled_magnus_center, supplies the equivalent Parikh/centered coordinate $(A,B,2C-AB)$, with true assigned to $\alpha$. None of these generic identities asserts injectivity on this stopped-source language; (SC.11) supplies its actual residual fibers. $\square$

**Theorem 8.4 (exact small fibers and return-placement collision).** The count cells $(3,3),(5,5),(7,7)$ have respectively $1,8,33$ histories. Their nonempty degree-two fibers are

| $(A,B)$ | $C:\ F(A,B,C)$ |
| --- | --- |
| $(3,3)$ | $2:1$ |
| $(5,5)$ | $5:1,\ 6:1,\ 7:2,\ 8:2,\ 9:1,\ 12:1$ |
| $(7,7)$ | $12:1,\ 13:1,\ 14:3,\ 15:3,\ 16:4,\ 17:4,\ 18:4,\ 19:3,\ 20:2,\ 21:2,\ 22:3,\ 23:1,\ 26:1,\ 30:1$ |

In particular these two actual positive histories have the same raw counts and complete fixed-letter degree-two data:

$$
\begin{aligned}
h_L&=\beta\alpha\mid
(\beta\alpha)\beta\beta\,(\beta\alpha)\alpha\,\alpha,
&\mathbf j_L&=(1,1,0),\\
h_R&=\beta\alpha\mid
\beta\beta\,\alpha\,(\beta\alpha)^2\alpha,
&\mathbf j_R&=(0,0,2).
\end{aligned}
\tag{SC.13}
$$

Both have $(A,B,C)=(5,5,7)$ but different acquired return incidences. They require no seed retries, future acceptance, replay or new source action.

Proof. At $(3,3)$ only $s=0,p=q=0$ occurs. At $(5,5)$ the summands are $(s,p,q)=(0,1,1),(2,0,0)$, of sizes $2$ and $6$. Their $C$ distributions are respectively $\{8:1,12:1\}$ and $\{5:1,6:1,7:2,8:1,9:1\}$. At $(7,7)$ the summands are $(0,2,2),(2,1,1),(4,0,0)$, of sizes $6,12,15$. For the first, $P_{2,2}(t)$ at $t=0,\ldots,4$ is $1,1,2,1,1$ and $c_0=14$; for the second $P_{1,1}(0)=P_{1,1}(1)=1$ and $c_2=15$; for the third $c_4=12$ and $g_4(d)$ at $d=0,\ldots,8$ is $1,1,2,2,3,2,2,1,1$. Substitution in (SC.11) gives the table.

For (SC.13), $p=q=0$, $s=2$ and $2j_1+j_3=2$ in both cases, so (SC.9) gives $C=7$ and (SC.2) gives $(5,5)$. The original parser assigns the displayed different return vectors, so normal-form injectivity proves $h_L\ne h_R$. This is a collision caused by legal return placement between completing markers, not a renamed selected-three-marker example or an arbitrary free-word collision. $\square$

## 9. Equal history masses, legal future independence and static supplement sizes

**Definition 9.1 (full original future and local reconstruction target).** On the slice of Definition 8.1 let $V$ be the entire legal future from the common $p_4$ phase: raw fourth-segment Reads, their deterministic phase/return/completed-marker events, the actual suffix $Y=b_4$, and its original $\mathrm{Stop}_{b_4}$ and delivery. All finite initial parts are included as projections of this stopped transcript. This is the full original future of Future Response Sufficiency §§10,21; held past records are not extra future deliveries. In particular a new report of the past return sum, a final $Q_4$ readout, a fingerprint report or an $E_1$ oracle is not included in the original recipient interface. Conditioning on $E_1$ would remove all histories with past returns and is a different problem.

The raw-history target is $H_3=h$. A static supplementary label below is a deterministic function of this acquired past, interpreted with the declared count or degree-two boundary and any original future $V$. Static labels are mathematical code assignments on finite fibers. Their alphabet size by itself supplies neither an online updater nor a free query of $h$.

**Theorem 9.2 (uniform actual fibers and independence from all legal future).** For every nonempty $\mathcal F_{A,B}$ and every fixed $\mu$ of Definition 6.1, each member has the identical positive joint mass

$$
Z_{A,B}=\sum_{k\ge1}\mu(k)r_k^A(1-r_k)^B>0.
\tag{SC.14}
$$

Conditional on this actual fiber, $H_3$ is uniform and independent of $V$. The same statement holds conditional on any nonempty refined fiber with given $C$. No arbitrary posterior mixture is used.

Proof. The deterministic parser and latch contribute no additional factor to a particular raw cylinder. A literal history includes its particular rejected pairs and particular accepted seed pair, so its mass is (SC.14); there is no seed factor $1/2$ here. That factor belongs only to summing over the entire accepted-seed prelude. Distinct third-latch words are a prefix antichain, because a proper extension has already crossed the third latch, so these cylinders are disjoint. The fiber event has mass $F(A,B)Z_{A,B}$.

For a complete legal future raw word $v=(\beta\alpha)^j c_e$ followed by the required Stop, put $a_v=\#\alpha(v)$, $b_v=\#\beta(v)$. Fixed-$k$ stopping-layer freshness from Boundary Dynamics §97 gives

$$
\Pr_\mu(H_3=h,V=v\mathrm{Stop}_e)
=Z_{A+a_v,B+b_v},\qquad
\Pr_\mu(V=v\mathrm{Stop}_e\mid H_3=h)
=\frac{Z_{A+a_v,B+b_v}}{Z_{A,B}}.
\tag{SC.15}
$$

This depends only on $(A,B)$, with the common $p_4$ control, not on retry order, the split between retries and returns, or return placement. The same ratio holds for every legal unfinished future cylinder using its acquired letter counts. The posterior used to mix the future is exactly

$$
\nu_{A,B}(k)=\mu(k)r_k^A(1-r_k)^B/Z_{A,B},
$$

which arises from each of these actual histories under this same prior. Future noncompletion has probability zero: at every supported $k$ a complete return has probability $r_k(1-r_k)\le1/4$, and mixing preserves vanishing tails. Thus the countably many complete stopped words, together with their deterministic events, determine the full future law. For any future event $E$, (SC.15) gives

$$
\Pr_\mu(H_3=h,V\in E\mid\mathcal F_{A,B})
=\frac1{F(A,B)}\Pr_{\nu_{A,B},p_4}(V\in E).
\tag{SC.16}
$$

Restricting the finite past side to a nonempty $C$ class replaces $F(A,B)$ by $F(A,B,C)$ and leaves the same future row. This proves both assertions. $\square$

**Theorem 9.3 (static exact labels and success with future side information).** On any fixed nonempty count fiber let $F=F(A,B)$, let $f$ be a deterministic past label with at most $D\ge1$ values, and allow a decoder independent local randomization and the full original $V$. Its best conditional exact reconstruction success is

$$
\sup_{\mathrm{decoder}}\Pr(\widehat H_3=H_3\mid\mathcal F_{A,B})
=\frac{|f[\mathcal F_{A,B}]|}{F}.
\tag{SC.17}
$$

Optimizing the static assignment as well gives $\min(D,F)/F$. Every positive compatible past/future pair is recoverable exactly if and only if $f$ is injective on the fiber. Thus the least static supplementary alphabet has $F$ values and $\lceil\log_2 F\rceil$ fixed-width data bits.

When $(A,B,C)$ is already supplied, the corresponding fixed-class statements replace $F$ by $F(A,B,C)$. One alphabet serving every $C$ class at these fixed counts needs exactly $\max_C F(A,B,C)$ values. Its optimal conditional average success, averaged over the actual $C$ distribution at those counts, is

$$
\frac1{F(A,B)}\sum_{C:F(A,B,C)>0}\min\{D,F(A,B,C)\}.
\tag{SC.18}
$$

In particular the count-only exact alphabets on the three cells of Theorem 8.4 have sizes $1,8,33$, whereas after supplying $C$ they have sizes $1,2,4$.

Proof. Theorem 9.2 makes the past uniform within each nonempty label class and independent of the entire future, even after the label is given. For a class $A_z$ and any future, the sum of a randomized decoder's probabilities of its different possible pasts is at most one; its success there is at most $1/|A_z|$. Selecting one representative attains this value. The class probability is $|A_z|/F$, so each nonempty class contributes $1/F$, proving (SC.17). At most $\min(D,F)$ classes are possible, and an assignment with that many classes attains the bound.

Every complete legal future is positive for every history in the fiber. Hence two distinct pasts with the same label cannot both be recovered on a shared positive future input. An injective finite label can be inverted, proving the zero-error equivalence. These are the finite-label and actual-image principles already supplied by Boundary Dynamics §102.2 and [LosslessEncodingCriterion](../../../D5/S3/ConceptDynamics/Coding/LosslessEncodingCriterion.lean), lossless_iff_injective_on_image. Finite enumerative coding supplies an index and inverse for each finite dictionary; it does not acquire the missing past. For given $C$, apply the same argument within that class, reuse labels across disjoint known $C$ classes, and weight by $F(A,B,C)/F(A,B)$ to obtain (SC.18). The exact sizes follow from the complete table. $\square$

## 10. Linear retained chronology and growing degree-two loss

**Theorem 10.1 (worst-case retained chronology versus predictive counts).** For every integer $m\ge0$, the positive $100$ slice contains a count fiber at

$$
A=B=2m+3,\qquad N=4m+6,
$$

with at least $\binom{2m}{m}$ histories. A record that permits exact raw-history recovery for every member, even with the count boundary and all original future, needs at least

$$
\left\lceil\log_2 F(2m+3,2m+3)\right\rceil
\ \ge\ 2m-\log_2(2m+1)
\tag{SC.19}
$$

bits of distinguishable supplementary retained configurations. Conversely Hypothesis 7.1 recovers every positive third-latch history with $O(N+1)$ retained bits. Thus worst-case retained raw chronology grows linearly with paid past length, while the acquired predictive count fields $(A,B)$ need only $O(\log(N+2))$ retained bits. No uniformly finite retained record reconstructs every positive third-latch past.

Proof. In (SC.8), take $s=0,p=q=m$: every ordering of $m$ rejected $X$ pairs and $m$ rejected $Y$ pairs is a distinct actual positive history of length $4m+6$. The central binomial coefficient is the maximum among the $2m+1$ coefficients whose sum is $2^{2m}$, so $\binom{2m}{m}\ge2^{2m}/(2m+1)$. Theorem 9.3 gives the required configuration lower bound; future observations cannot relieve it. A bounded-bit retained device has only finitely many distinguishable configurations, contradicting this sequence for sufficiently large $m$.

For the upper bound, encode $U$ as one bit per rejected pair and retain its length/occupancy metadata in $O(\log(N+2))$ bits. The three exact return counters each use $O(\log(N+2))$ bits. The original seed, marker records, selector and fixed four-segment control have bounded alphabets. The same representation works during acquisition; no prefix has more completed retry pairs or returns than the reads it has actually consumed. Since $|U|=p+q\le N/2$, its held footprint is

$$
|U|+O(\log(N+2))\le N/2+O(\log(N+2)).
\tag{SC.20}
$$

Initialization, occupancy and counter encodings are included, not hidden persistent modes. For an analysis bound $N\le L$, fixed buffers/counter widths therefore give a finite $O(L+1)$ retention bound on that domain. This is not permission to truncate the original source at $L$; paths outside it continue and need growing storage for universal exact recovery.

The predictive counts are actually acquired from zero as in Future Response Sufficiency §§9,15, and with the supplied finite control determine the legal continuation law. Retaining the two integers costs logarithmic space. This does not bound probability materialization: exact rational numerators/denominators, model installation, arithmetic workspace and output may require more space; an arbitrary real or countable prior needs its own effective representation obligations. The comparison is between held chronological information and held count fields, not between optimal total machines. $\square$

**Theorem 10.2 (degree two leaves linear worst-case residual information).** For every $m\ge0$ there is a nonempty degree-two class at counts $A=B=2m+3$ whose supplementary zero-error alphabet has at least

$$
\frac{\binom{2m}{m}}{(2m+3)^2+1}
\tag{SC.21}
$$

values. In particular its necessary supplementary bits are at least

$$
2m-\log_2(2m+1)-\log_2((2m+3)^2+1),
\tag{SC.22}
$$

so even the full fixed-letter degree-two boundary leaves growing linear worst-case loss. There is also an explicit positive same-degree-two source family: for each $m$, choose independently one of the retry blocks $XYYX$ and $YXXY$ in each of $m$ consecutive blocks, then append the actual seed $\beta\alpha$ and zero-return marker prefix $\beta\beta\alpha\alpha$. The $2^m$ resulting histories all have

$$
A=B=4m+3,\qquad N=8m+6,\qquad C=8m^2+12m+2.
\tag{SC.23}
$$

They remain indistinguishable by the full original future. This is a fixed actual $C$ family, not an existence claim about arbitrary mixtures.

Proof. At fixed counts, $C$ is an integer between $0$ and $AB$, so there are at most $AB+1$ degree-two classes. Distribute the complete count fiber among them and apply Theorem 10.1; a largest class has at least (SC.21) members. Theorem 9.3 then gives (SC.22). A possibly negative small-$m$ lower bound is simply weaker than the nonnegative bit bound; the linear asymptotic conclusion uses large $m$.

For the explicit family, each displayed block consists entirely of four legal rejected equal pairs. Both raw expansions have four alphas, four betas and $C=8$. This is the reused two-letter $ABBA/BAAB$ step-two collision from [PrimeGoldenThirdOrderChronologyEscape](../../../D5/S3/Observer/Chronology/PrimeGoldenThirdOrderChronologyEscape.lean), step_two_signature_abba_eq_baab, applied to retry types, with Chen composition. Across $m$ blocks the alpha-before-beta count is $8m+16\binom m2=8m^2$. The final actual seed and marker prefix have counts $(3,3)$ and $C=2$, adding the cross contribution $12m$. This proves (SC.23). Fixed-length block boundaries and their distinct words make all $2^m$ choices different; normal-form parsing makes them positive histories of the same original source. Theorem 9.2 supplies their identical future rows. The generic collision is not new content: its legal prelude realization, common-prior equality and unbounded retained-loss consequence are the connection here. Together with (SC.13), it separates retry-order loss from the independent return-placement loss. $\square$

## 11. Recovery directions, resource contracts and suppliers

**Theorem 11.1 (four expressions on the enlarged actual domain).** With Hypothesis 7.1's actual acquisitions and specified delivery, the following expressions carry the same selected raw past on all of $\mathcal H_3(\mu)$: its raw chronological word; its parser-labelled incidence/precedence relation of Definition 7.3; and its augmented held boundary (SC.3). In this interpretation, spatial records mean the declared local marker scopes together with actual retry/return incidence records, time means precedence of raw events, and memory means their acquired and held representation. The count/law boundary is a projection of this augmented boundary, and this projection is noninjective even after its fixed-letter degree-two refinement and the entire original future are supplied.

Proof. Theorems 6.2–7.4 give each direction on actual images, including both seeds, all marker triples, empty preludes, either single retry kind, and any finite return vector. Reconstructing $h$ and counting its letters gives $(A,B)$ and the original control at the latch, hence the fixed-prior continuation law by the cited predictive supplier. Conversely the two raw words in (SC.13) have the same finite marker records, acquired seed, counts, fixed-letter degree-two data and continuation law but different return incidences; Definition 7.3 separates them. Theorem 10.2 gives growing residual classes as well. Thus bare scopes, their marker records alone, predictive counts, semantic length/window laws and fixed-letter degree two cannot reconstruct the raw chronology. None of these directions turns a semantic law into an observation port or recovers the full generated source tree, hidden actual $K$, metric distance, physical time or a global spacetime. $\square$

**Definition 11.2 (separate retention, precision and total costs).** Theorem 9.3's cardinalities are static supplementary data-alphabet minima on explicitly fixed positive fibers. Theorems 7.2 and 10.1 supply a causal acquisition and retention upper bound, not an online minimum attaining those static ranks. All readable state, metadata, marker identities, record alphabets, counters and their widths are counted. A variable exact integer is not one constant-size register; storing (SC.4) unpacked may require $q\,O(\log(p+2))$ bits rather than the bit word in (SC.20).

Every original Read, including both letters of every rejected pair, each return and all fourth-segment Reads, is still paid. Stop, local writes, routing/control, initialization, program/model installation, counter arithmetic, buffer growth, temporary workspace, output and the explicitly added third-latch delivery are separate costs. Holding uses the same record; any materialized relational graph or duplicate output is separately charged. Raw reconstruction can stream (SC.1) from held data with finite control/counters, or materialize its $N$-letter output and pay $O(N)$ output space. Neither choice proves a minimum in time, peak workspace, installation, energy or total resources.

Exact discrete relation recovery requires correctly stored pair types, integers and marker identities. Replacing these by finite-precision real moments is a different observation: no universal inverse tolerance follows here. A finite length bound supports a finite exact record as in (SC.20); unrestricted positive histories do not have a uniformly finite exact chronology record. Semantic recovery of continuation/length/window laws under the support conditions in Future Response Sufficiency §§21–26, finite-precision stability of those inversions, actual online acquisition of counts and raw-past reconstruction are four separate claims. The latter is proved here without assuming that counts can be recovered from the law for every prior. Physical durations are absent from the original paid-call interface.

**Definition 11.3 (reuse and mathematical attribution).** The source-specific normal-form/acquisition, raw-fiber, future-independence and retention conclusions are repo-derived ordinary deductions. Generic prefix inversion, ordered-pair composition, finite coding and signature identities inside their proofs are reused intermediate statements. Boundary Dynamics §§97,100,102,105,114 supplies the paid stopping grammar, actual common seed/depth law, finite-label side-information distinction and original recipient contract. Future Response Sufficiency §§9,12,15,21–26 supplies from-zero counts, actual-prior posterior rows, the full legal future and the distinction between semantic law recovery and lost raw order. Full E1 Scope Extension §2 and [Source Coherence Continuation](RECURSIVE_RELATIONAL_OBSERVATION_SOURCE_COHERENCE_CONTINUATION.md) supplies completed-marker routing, write-before-latch and holding; Theorem 6.2 checks the finite supplier on the entire marker-triple image used here.

The generic ordered-pair, Chen and Parikh identities are reused from the named chronology modules. [PrimeGoldenChronologyFiberSeparation](../../../D5/S3/Observer/Chronology/PrimeGoldenChronologyFiberSeparation.lean), prime_golden_chronology_fiber_separation, supplies a two-event oriented separation when, in the target ring, the commutator of the first and second observed event values differs from the commutator in the reverse order; that hypothesis does not assert separation of the source fibers (SC.11). ConceptDynamics' [FiniteIdentificationOutputCapacity](../../../D5/S3/ConceptDynamics/ExperimentBoundary/FiniteIdentificationOutputCapacity.lean), finite_identification_output_capacity, and LosslessEncodingCriterion supply finite output and actual-image coding principles. FiberBinaryIdentification's arbitrary-question construction requires arbitrary questions; that permission is not imported into the paid Read/Stop source.

The applicable mature intermediate statements have these attributions: Cover, *Enumerative Source Encoding*, [doi:10.1109/TIT.1973.1054929](https://doi.org/10.1109/TIT.1973.1054929), [original §I, Proposition 1 and inverse algorithm](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf), supplies finite dictionary indexing; Mateescu, A. Salomaa, K. Salomaa and Yu, *A sharpening of the Parikh mapping*, [doi:10.1051/ita:2001131](https://doi.org/10.1051/ita:2001131), [Theorem 2.1](https://www.numdam.org/item/ITA_2001__35_6_551_0/), supplies the binary count/scattered-pair entries; Richomme, *On some 2-binomial coefficients of binary words: geometrical interpretation, partitions of integers, and fair words*, [arXiv:2510.07159v1, §4.2, Lemma 4.12](https://arxiv.org/html/2510.07159v1#S4.SS2), supplies the bounded-partition/cut-vector fiber. In (SC.10) its partition is the reverse of $(x_1,\ldots,x_q)$, with $p$ copies of $X$, $q$ of $Y$ and scattered-pair count $t$. These are literature-attested intermediate tools, not new generic coding or signature mechanisms.

The new connection is the complete stopped-source fiber and degree-two classification, its actually acquired relational inverse and common-prior future independence, and the consequent chronology retention separation. Source reads and ordinary proofs do not constitute new Lean compilation, kernel certification, ingestion or coverage. No external priority claim, tensor hierarchy, physical interpretation, persistent-goal completion or optimum over total acquisition resources follows.

## 追加锚（本行以下为增补区）

## 12. The whole graded ordered-letter readout on the actual source

**Definition 12.1 (domain, interface and readout).** Keep the source, fixed finite or countable prior $\mu$, acquired filtration and third latch of Definition 6.1. Every statement in §§12–17 concerns the same $\mathcal H_3(\mu)$, including both actual seeds, all eight marker triples, every finite paid seed retry and every finite return placement, unless a slice is explicitly named. The parameters remain $m=2,d=1,\ell=2,n=4$; the symbol $k$ below denotes a readout cutoff, not the hidden depth $K$. All original Read/Stop permissions remain those of Future Response Sufficiency §9. In particular no reset, source copy, address query, prior resampling, clock, test oracle or post-Stop Read is supplied.

For a raw word $h=h_1\cdots h_N$ and a fixed-letter pattern $v=v_1\cdots v_j$, define

$$
c_v(h)=\#\{1\le i_1<\cdots<i_j\le N:h_{i_1}\cdots h_{i_j}=v\},\qquad
c_{\varepsilon}(h)=1,\qquad
G_k(h)=(c_v(h):|v|\le k),\quad
G_{\infty}(h)=(c_v(h):v\in\{\alpha,\beta\}^{*}).
\tag{SC.24}
$$

Every binary pattern is included, not only chosen moments or the degree-$k$ part. Positions are distinct and strictly increasing, but need not be contiguous. These are multiplicity-bearing scattered-subword counts: neither contiguous-factor counts, presence-only subword data, parser-context labels nor relations on individually indexed occurrences. Degree counts aggregated tuples of raw letters; it is not a lower bound on relational arity. Definition 7.3 already gives a sufficient binary precedence relation with paid occurrence identities and growing storage.

Use the existing Magnus polynomial in the free associative integer algebra:

$$
\mathcal P(h)=\prod_{i=1}^{N}(1+x_{h_i}),\qquad
[x_v]\mathcal P(h)=c_v(h),\qquad
\mathcal P(hh')=\mathcal P(h)\mathcal P(h').
\tag{SC.25}
$$

The product/coefficient identification is the reused `magnusPolynomial_coeff_scatteredCount` of [MagnusWordCoefficients](../../../D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients.lean); concatenation follows in the same source order. The coefficients are exact integers. For a finite $h$, degrees above $N$ vanish, although there is no uniform degree or finite configuration bound over the actual domain.

**Definition 12.2 (signature conventions and their precise correspondence).** At degree two the coefficients are $c_{\alpha\alpha}=\binom A2$, $c_{\beta\beta}=\binom B2$, $c_{\alpha\beta}=C$, $c_{\beta\alpha}=AB-C$. They are not the doubled Chen coordinates (SC.12): that convention has diagonals $A^2,B^2$ and mixed entries $2C,2(AB-C)$. Counts plus either convention determine the other, by the reused diagonal/ordered-pair identity of SignatureOrderedMoment.

If a whole exponential convention is desired, explicitly choose the formal rational series $\mathcal E(h)=\prod_i\exp(x_{h_i})$. In the degree filtration, substitution $x_a\mapsto\exp(x_a)-1$ carries $\mathcal P(h)$ to $\mathcal E(h)$, and substitution $x_a\mapsto\log(1+x_a)$ is its inverse. Both have identity linear part, so they descend to inverse maps at every finite cutoff. Equivalently, the coefficient of a pattern $v$ in $\mathcal E(h)$ is the sum over decompositions of $v$ into nonempty constant-letter blocks, with contribution $c_{a_1\cdots a_s}(h)/(\ell_1!\cdots\ell_s!)$ for block letters $a_i$ and lengths $\ell_i$. The all-singleton decomposition contributes $c_v(h)$; all others use shorter patterns. This triangular conversion proves equality of the complete cutoff fibers for these two explicitly chosen characteristic-zero conventions. It does not equate their coordinates or supply finite-precision conditioning for the conversion.

Only the degree-two tensor implementation is attributed to the existing chronology modules; their source does not supply a completed all-order tensor construction. An arbitrary scalar, ring or matrix representation can collapse the free coefficients, even at all orders. No injectivity of such a shadow, full physical path signature or analytic convergence claim is used here. The exact single-degree deck of ExactDeckCore is equivalent to $G_k$ at a supplied common length $N\ge k$; when $k>N$ that degree alone is zero and cannot replace (SC.24).

## 13. An order-faithful embedding through paid seed retries

**Theorem 13.1 (all binary orders embed in one legal third-latch slice).** For every fixed $\mu$ of Definition 6.1, define $\delta(0)=\alpha\alpha$, $\delta(1)=\beta\beta$ and

$$
\iota(u)=\delta(u)\,\tau,\qquad
\tau=\beta\alpha\mid\beta\beta\alpha\alpha,
\qquad u\in\{0,1\}^{*}.
\tag{SC.26}
$$

This is an injection into the actual $R=1$, marker-$100$, zero-return slice, with the same $w=1,Q^+=(ac,bc),Z=1$ and original bare/control fields. For every $k\ge1$ and all $u,v$,

$$
G_k(\iota(u))=G_k(\iota(v))
\quad\Longleftrightarrow\quad G_k(u)=G_k(v),
\tag{SC.27}
$$

where the right side uses the same scattered-count convention on letters $0,1$. For distinct $u,v$, their first separating degree is also preserved. The from-zero raw counts are

$$
A(\iota(u))=2|u|_0+3,\qquad
B(\iota(u))=2|u|_1+3,\qquad N(\iota(u))=2|u|+6.
\tag{SC.28}
$$

Proof. Every doubled input letter is an equal pair rejected by the actual seed extractor. The next pair $\beta\alpha$ first accepts seed 1; $\beta\beta$, $\alpha$, $\alpha$ then complete exactly the three markers $100$, without returns. Theorem 6.3 therefore supplies positivity, unique parsing and injection, for every such prior, rather than an instruction to force an execution. Its count formula gives (SC.28). The vertical stroke in (SC.26) is a parser-derived delimiter, not an added source event.

The Magnus polynomial of $\delta(u)$ is obtained by substitution $x_0\mapsto2x_\alpha+x_\alpha^2$, $x_1\mapsto2x_\beta+x_\beta^2$. If $\mathcal P(u)-\mathcal P(v)$ first has a nonzero homogeneous component in degree $r$, the corresponding substituted component is $2^r$ times that component with renamed letters. It remains nonzero over $\mathbb Z$, and all lower components remain zero. Multiplication on the right by $\mathcal P(\tau)$ leaves this first component unchanged because its constant term is 1. A first separating degree exists for distinct finite words: different lengths are separated in degree one, and at a common length the top word coefficient separates them. These reused coefficient facts prove both directions of (SC.27) and the stronger first-degree assertion. This ordinary calculation is the general literal-doubling mechanism also present in LiteralPowerSubstitution's private coefficient supplier; its public endpoint for `positivePairWords` has a narrower telescope and is not invoked as a theorem about an unrelated recursion. $\square$

**Theorem 13.2 (actual-prior future transfer and refined-fiber coding).** Any nonempty subset $\mathcal A$ of a fixed $\mathcal F_{A,B}$ has uniform conditional past and is independent of the entire original $V$ of Definition 9.1. In particular this applies to every $G_k$ class in that complete fiber and to every same-count family in the image of $\iota$. Each literal member has mass $Z_{A,B}>0$ from (SC.14); every legal unfinished cylinder or complete future $v\mathrm{Stop}_e$ has conditional mass $Z_{A+a_v,B+b_v}/Z_{A,B}$ from (SC.15), with the original deterministic events and no added past report.

For $F=|\mathcal A|$ and any deterministic supplementary past label $f$ with at most $D\ge1$ values, the best conditional exact success using that label, any supplied past fields constant on $\mathcal A$, all $V$ and independent decoder randomization is $|f[\mathcal A]|/F$. Optimizing the static assignment gives $\min(D,F)/F$. Zero-error recovery on every positive compatible past/future pair requires and suffices for an injective label; its least static alphabet is $F$ and its fixed-width data requirement is $\lceil\log_2 F\rceil$ bits.

Proof. Restrict (SC.16) to the finite past event $\mathcal A$ and normalize by $|\mathcal A|Z_{A,B}$. The future row remains the actual posterior $\nu_{A,B}$ under the same installed $\mu$, not a selected mixture. The argument of Theorem 9.3 then applies unchanged to this finite conditional dictionary. Every complete legal future is positive for every member; it cannot distinguish two equal labels. A representative per label class attains the success bound, and finite dictionary indexing attains the static injective alphabet. No online acquisition of that index is asserted. These are source restrictions of the existing future-independence and finite-coding suppliers, not new generic coding theorems. $\square$

## 14. Strict escape at every cutoff and residual retained chronology

**Theorem 14.1 (every order fails and its successor genuinely refines it).** Let $\theta(0)=01$, $\theta(1)=10$. For every fixed $\mu$ and every $k\ge1$, set $u_k=\theta^k(0)$, $v_k=\theta^k(1)$ and $h_k^+=\iota(u_k)$, $h_k^-=\iota(v_k)$. These are distinct positive same-source third-latch histories with the common records of Theorem 13.1, identical $G_k$ and full original future law, but

$$
\begin{aligned}
A(h_k^{\pm})=B(h_k^{\pm})&=2^k+3,\qquad N(h_k^{\pm})=2^{k+1}+6,\\
c_{\alpha\beta^k}(h_k^+)-c_{\alpha\beta^k}(h_k^-)
&=2^{\,2+k(k-1)/2}>0.
\end{aligned}
\tag{SC.29}
$$

For every $t\ge1$, independently choosing $u_k$ or $v_k$ in $t$ consecutive blocks and applying $\iota$ gives $2^t$ distinct histories in one $G_k$ class, with

$$
A=B=t2^k+3,\qquad N=t2^{k+1}+6,
\tag{SC.30}
$$

the same seed/marker/count boundary and full future law. Relative to those supplied data this family needs at least $t$ supplementary bits for zero error, and the optimized static $D$-label success is $\min(D,2^t)/2^t$ even with all $V$.

Proof. Reuse Ochsenschläger's word theorem as given with its coefficient proof in Lejeune–Leroy–Rigo, *Computing the $k$-binomial complexity of the Thue–Morse word*, [arXiv:1812.07330v1, Lemma 30](https://arxiv.org/pdf/1812.07330v1): $u_k,v_k$ agree through $k$, first differ at $k+1$, and their $01^k$ count difference is $2^{(k-1)(k-2)/2}$. Theorem 13.1 multiplies this leading coefficient by $2^{k+1}$ and leaves it unchanged under the common suffix, yielding (SC.29). Both input words have $2^{k-1}$ copies of each letter. Thus (SC.28) gives the stated counts, and Theorem 13.2 gives their actual future law.

Truncated multiplication in (SC.25), equivalently the literature's concatenation congruence, makes all block choices equal through $k$. Their fixed block length $2^k$ and $u_k\ne v_k$ make all choices distinct; the embedding preserves them. The same counts give (SC.30), and Theorem 13.2 supplies the label bound. This uses the Thue–Morse recursion $(u,v)\mapsto(uv,vu)$, not the indexed positive-pair recursion $(u,v,a)\mapsto(uav,vau)$. The existing degree-two family is its $k=2$ case; the retained conclusion here is the all-cutoff transfer and strict next-order escape on the original acquisition domain. $\square$

For example, $u_3=01101001$, $v_3=10010110$. Their actual images have $(A,B,N)=(11,11,22)$, agree through degree three, and differ at $\alpha\beta^3$ by 32. This description names eight paid equal-pair retries in each history; it grants no word-writing action to the source.

**Theorem 14.2 (linear residual on complete actual fibers, including a growing-order regime).** For every $m\ge0$, $k\ge1$ and every fixed $\mu$, put $N=4m+6$, $A=B=2m+3$, and define

$$
\begin{aligned}
Q_k(N)&=\prod_{j=2}^{\min(k,N)}
       \left(1+\binom Nj\right)^{2^j-2},\\
C_k&=\sum_{j=2}^{k}j(2^j-2)
     =(k-1)2^{k+1}-k(k+1)+2.
\end{aligned}
\tag{SC.31}
$$

An empty product is 1. Some complete $G_k$ class within $\mathcal F_{A,B}$ has size at least $\lceil\binom{2m}{m}/Q_k(N)\rceil$. Its necessary supplementary zero-error bits, even with all $V$, are at least

$$
\max\left\{0,\left\lceil
\log_2\binom{2m}{m}-\log_2 Q_k(N)
\right\rceil\right\}
\ge
\max\left\{0,\left\lceil
2m-\log_2(2m+1)-C_k\log_2(N+1)
\right\rceil\right\}.
\tag{SC.32}
$$

For each fixed $k$ this is $N/2-O_k(\log(N+2))$. More generally, along $N=4m+6\to\infty$, every integer schedule $k(N)\ge1$ satisfying

$$
k(N)2^{k(N)}\log(N+1)=o(N)
\tag{SC.33}
$$

still leaves $(1/2-o(1))N$ supplementary bits on some actual class. An unbounded cutoff alone is therefore not a sufficiency condition. These are worst-case conditional distinguishable-configuration bounds, not per-history description lengths or minima of total observer resources.

Proof. Theorem 10.1 supplies at least $\binom{2m}{m}$ actual zero-return retry orders in this count fiber. At fixed counts, degree one and the two pure-letter coordinates in every degree are fixed. Each other degree-$j$ coefficient is an integer between 0 and $\binom Nj$, so there are at most $Q_k(N)$ possible profiles. This is a product upper bound; it assumes neither independent coordinates nor joint attainability of their separate maxima. Pigeonhole on the complete actual fiber gives the displayed class, and Theorem 13.2 supplies its static supplement requirement.

The central-binomial inequality of Theorem 10.1 gives $\log_2\binom{2m}{m}\ge2m-\log_2(2m+1)$. Also $1+\binom Nj\le(N+1)^j$, hence $\log_2Q_k(N)\le C_k\log_2(N+1)$. The finite sum in (SC.31) gives $C_k\le(k-1)2^{k+1}\le2k2^k$, which proves both the fixed-order and (SC.33) conclusions. Hypothesis 7.1 still supplies the held chronology representation (SC.20); a fixed small coefficient table has logarithmic held size but leaves this linear residual. The polynomial profile-counting mechanism is already literature-attested in Lejeune–Rigo–Rosenfeld, [*On the binomial equivalence classes of finite words*, arXiv:2001.11732v1, §4 Proposition 12](https://arxiv.org/pdf/2001.11732v1); only its explicit actual-fiber retention consequence is used here. $\square$

## 15. Complete recovery, finite length and threshold transfer

**Theorem 15.1 (actual-image completeness and finite-length sufficiency).** For every fixed $\mu$ and all $h,g\in\mathcal H_3(\mu)$, $G_\infty(h)=G_\infty(g)$ if and only if $h=g$. Under Hypothesis 7.1's acquisition and specified delivery, the full readout, raw selected word, held record (SC.3), and parser-labelled precedence/incidence expression of Definition 7.3 determine one another on their actual images. Counts and the fixed-prior continuation law are projections; their reverse chronological recovery fails even after any one fixed $G_k$ and the full original $V$ are added.

For each individual $h$, the cutoff $\min(A(h),B(h))+1$ identifies its word among all compatible actual histories. For every public integer length bound $L\ge5$, one sufficient cutoff for the entire actual domain $N\le L$ is

$$
q(L)=\min\left\{
\lfloor L/2\rfloor+1,
\left\lfloor\frac{16}{7}\sqrt L\right\rfloor+5
\right\}.
\tag{SC.34}
$$

This is a semantic sufficient order, not a sharp threshold or an online resource optimum. The cap $L$ is a recovery promise, not a new stopping rule.

Proof. Reuse the generic finite-word coefficient inverse: degree one gives $N=A+B$, and degree $N$ has the unique nonzero word coefficient $c_h(h)=1$. Thus the whole readout recovers $h$; evaluation of (SC.25) gives the converse. Theorems 6.3, 7.2 and 7.4 supply the actual parser, held-record and relational inverses. Counts and the original control give the future law under the installed prior. Theorem 14.1 supplies actual noninjective fibers for every fixed cutoff, with identical future rows; no semantic law port is needed for this obstruction.

The smaller elementary inverse is the right-bounded-block reconstruction supplier of Fleischmann–Lejeune–Manea–Nowotka–Rigo, [*Reconstructing Words from Right-Bounded-Block Words*, arXiv:2001.11218v2, §3 equation (2), Theorems 19 and 21](https://arxiv.org/pdf/2001.11218v2). To specify its arguments here, choose the minority raw letter $a$, let $b$ be the other letter, and let $p=|h|_a$. Write $h=b^{g_0}a b^{g_1}a\cdots a b^{g_p}$. Its supplied counts satisfy

$$
t_i:=c_{a^i b}(h)=\sum_{j=i}^{p}\binom ji g_j,
\qquad
g_p=t_p,\quad
g_i=t_i-\sum_{j=i+1}^{p}\binom ji g_j
\quad(0\le i<p).
\tag{SC.35}
$$

Every used pattern has degree at most $p+1$; degree-one counts select $a$ and $p$. This known triangular inverse reconstructs the runs, including $p=0$ and empty runs. The two-sided alternative $c_{a^i b a^{p-i}}=g_i$ uses the same order because it selects all $p$ occurrences of $a$. These are explicit supplier substitutions, not new generic word-reconstruction theorems. Applying the inverse to the actual raw word and then the original parser yields all records without extra source access. It gives the first bound in (SC.34).

For the stronger large-length cutoff, use the Krasikov–Roditty scattered-multiset reconstruction bound $\lfloor16\sqrt n/7\rfloor+5$, as stated in the introduction and §3 of that reconstruction supplier, with original attribution [*On a Reconstruction Problem for Sequences*, JCTA 77, 344–348, doi:10.1006/jcta.1997.2732](https://doi.org/10.1006/jcta.1997.2732). Its convention is multiplicities of scattered subwords at a common known length, not contiguous factors or presence alone. If this bound exceeds $n$, the full degree-$n$ word already suffices. Otherwise ExactDeckCore's `exactKDeck_eq_iff_cutoffMagnus_eq_of_common_length`, with its hypothesis $k\le n$, transports the supplied exact-deck uniqueness to the whole cutoff. Degree one fixes $n$, so the bound at $L$ serves all smaller $n$ as well. Taking the smaller of these two sufficient orders proves (SC.34). The square-root theorem is a literature supplier, not newly proved or Lean-verified content here. $\square$

**Theorem 15.2 (source/generic threshold relation and necessary growth).** Let $b(n)$ be the least integer cutoff at least 1 separating all binary words of length at most $n$ under (SC.24). Let $r_\mu(L)$ be the least cutoff at least 1 separating the actual histories of length at most $L$ when the already acquired tuple $(R,w,Q^+,Z,A,B)$ is also supplied. For every $L\ge8$,

$$
b\!\left(\left\lfloor\frac{L-6}{2}\right\rfloor\right)
\le r_\mu(L)\le b(L)\le q(L).
\tag{SC.36}
$$

Neither the full legal future nor its semantic law lowers $r_\mu(L)$ for zero error on all positive compatible histories. In particular, for $L\ge10$,

$$
\lfloor\log_2(L-6)\rfloor\le r_\mu(L),
\tag{SC.37}
$$

and every integer schedule sufficient on every bounded actual domain must tend to infinity with $L$. The least-order growth and sharp source threshold remain open here; (SC.37) is an explicit obstruction, not an optimal generic lower bound.

Proof. The complete cutoff suffices, so both minima exist; Theorem 15.1 gives $b(L)\le q(L)$. Restricting the generic inverse to actual words gives $r_\mu(L)\le b(L)$. For $n=\lfloor(L-6)/2\rfloor$, all $\iota(u)$ with $|u|\le n$ lie in the actual length-$L$ domain. If two such input words have equal $G_k$, they have equal counts because $k\ge1$; their images therefore have equal supplied tuples and, by Theorem 13.1, equal $G_k$. Any cutoff sufficient on the source separates them and hence separates the entire generic length-$n$ domain. This proves the lower transfer in (SC.36).

For any collision of the supplied tuple and $G_k$ on the larger actual domain, the same raw-count likelihood calculation as Theorem 9.2 gives the same actual posterior and future row at the common $p_4$ phase, irrespective of which common seed/marker tuple it has. Every complete future is positive for both; a realized future or its common law cannot repair their collision. Conversely an injective past tuple needs no future. This proves the threshold statement with future supplied. For (SC.37), put $s=\lfloor\log_2(L-6)\rfloor\ge2$ and $k=s-1$ in Theorem 14.1: its length $2^s+6$ is at most $L$, so an order-$k$ decoder fails and the minimum is at least $s$. This also proves divergence, while (SC.33) identifies a regime in which growing order still leaves linear residual. No claim of cutoff independence from the prior is needed for these inequalities. $\square$

## 16. From-zero acquisition, same-record holding and precision

**Hypothesis 16.1 (the supplementary writer and receiver contract).** A coefficient observer, if used, is installed and initialized before the first paid seed Read: $c_\varepsilon=1$ and every other installed coefficient is zero. On an actual returned letter $a$ before the selected latch, it performs

$$
c_v(ha)=c_v(h)+\mathbf1\{\operatorname{last}(v)=a\}\,c_{v^-}(h),
\qquad 1\le |v|\le k,
\tag{SC.38}
$$

where $v^-$ deletes the last letter and every right side is an old value. Descending-degree updates implement this rule without treating the current Read as multiple positions. The writer includes every rejected/accepted seed letter, return, partial parse and completing letter. The third-marker completing Read updates this table and all prescribed marker fields before the latch. Afterwards every fourth-segment event and the unique original Stop hold this same selected-past record. Counts used for its reconstruction refer to that same past, not to later active totals.

The owner is the actual raw-letter recipient with access to the original phase/control. Installation, addressing, local storage, writes, counter arithmetic, growth, holding and workspace are explicitly supplied and paid. A receiver receives the augmented table or another sufficient record only under an explicit delivery contract, with transmission and output storage charged, as in Hypothesis 7.1. The old bare-snapshot recipient gains no new fields or archive access. The original selected-marker decoder remains unchanged; raw-past reconstruction is the separate local target already declared in §9.

**Theorem 16.2 (finite promise and unrestricted finite completion).** Under Hypothesis 16.1, (SC.38) acquires the correct installed cutoff on every finite prefix up to the third latch while the required exact widths are supplied and no overflow occurs, and holds it thereafter. For a public promise $N\le L$, installing $k=q(L)$ from zero suffices for exact reconstruction on that domain. A sufficient dense coefficient data allocation is

$$
B_{\rm dense}(L,k)=\sum_{j=1}^{\min(k,L)}
2^j\left\lceil\log_2\!\left(1+\binom Lj\right)\right\rceil
\tag{SC.39}
$$

bits, plus charged control, length/overflow metadata, coordinate addressing, installation, arithmetic workspace and output. Identically zero higher levels may be omitted. For fixed $k$ the data allocation is $O_k(\log(L+2))$; it has the fixed-order recovery failure of Theorem 14.1. With $k=q(L)$ it is finite and at most $(L+1)(2^{k+1}-2)$. Installing every degree through $L$ is another sufficient choice of $O((L+1)2^L)$ data bits, not a necessary observer design.

A finite length monitor may enter an explicit overflow state on the first Read beyond $L$, then hold invalid selected-past data while the original execution continues. It must detect exceeding the promise before a counter's out-of-range write; saturation or wraparound cannot be advertised as exact. This introduces no earlier Stop or truncation permission. Recovery is guaranteed only on nonoverflow histories in the declared domain. Universal service on all finite completions instead needs unbounded possible retained configurations, while each completed finite history can use finite storage.

Proof. The reused scattered-subword recurrence splits occurrences into those avoiding the new last position and those using it exactly once. Induction from the initialized empty prefix gives (SC.38); write-before-latch and subsequent holding give the selected-past invariant. On $N\le L$, each degree-$j$ counter stays in $[0,\binom Lj]$, yielding (SC.39); $\binom Lj\le2^L$ yields the displayed envelope. Theorem 15.1 supplies the inverse, rather than interpreting finite memory as an extra measurement port. The length monitor has only the required finite initialized count/overflow states and changes the observer's validity claim, not the source menu.

For unrestricted finite prefixes one can maintain a paid from-zero length counter and all degrees through its current acquired length $n$. Before the next update, degree $n+1$ has old value zero, so installing that level and then using all retained old lower levels preserves the invariant. All counter growth and allocation are charged; the number and widths of coordinates grow, with no uniform finite bound. More economically, reuse Hypothesis 7.1's from-zero $U,J_1,J_2,J_3$ and finite seed/marker fields. Its $|U|+O(\log(N+2))\le N/2+O(\log(N+2))$ held data reconstruct $h$ and permit local computation of any requested finite cutoff, or a streamed factored representation of its polynomial. That computation uses the already held same-history data, not a new source/archive query; materializing a coefficient table or a raw output pays its own space and work. Theorem 10.1 forbids a uniformly finite exact chronology record over all positive completions. Infinite noncompletion paths have no finite third-latch target in this claim. $\square$

**Proposition 16.3 (late installation cannot recover erased prefix data).** Fix $k\ge1$. If the complete retained observer state after a prelude factors only through $G_k$ and the common original finite control, raising its cutoff later does not recover every omitted earlier higher coefficient or the raw past. This applies even when all subsequent original input and $V$ are supplied. It does not apply to a state that has also held a sufficient $U/J$ record or other lossless earlier information.

Proof. Use the two rejected-pair prefixes $\delta(u_k)$ and $\delta(v_k)$ from Theorem 14.1, before either has accepted a seed. They share $G_k$, counts and the actual seed-waiting control; no marker has been completed. Yet their degree-$(k+1)$ coefficients differ. The stipulated observer states coincide there. Give both the same positive legal suffix $\tau$ and then any common positive complete fourth-segment future. Deterministic updates from identical states on identical later inputs stay identical, but the required earlier coefficient and selected raw history remain different by Theorem 13.1. Independent later randomization likewise cannot produce zero-error recovery of both. Thus an upgrade needs higher prefix contributions already represented, for example by a sufficient held record, or a from-zero scheme maintaining all needed levels. No replay source is present to supply them retrospectively. $\square$

**Definition 16.4 (precision, prediction and cost boundaries).** The default contract is exact discrete coefficients with nonoverflowing integer widths. On a specified finite domain, correctly ranged coordinate estimates with absolute error strictly below $1/2$ can be rounded to these integer counts; the same supplied coordinate set, exact metadata and delivery are still required. The growing dynamic range and number of counters cost bits. Perfect precision does not repair a fixed-cutoff collision. No uniform normalized-moment tolerance, bounded-width real-register implementation or stability of arbitrary represented/exponential conversions follows.

Semantic recovery of a continuation law, actual online acquisition of its count/control boundary, numerical stability of law inversion, exact past recovery, and prediction of a future realization are different targets. Future Response Sufficiency §§21–26 retains its own prior/support and effective-representation conditions for the first three; the present inverse neither requires counts to be recovered from every prior's law nor identifies the actual hidden $K$. All original Reads, including retries, returns and the entire fourth segment, remain paid. Original Stop, initialization, program/model installation, routing/control, coefficient writes, buffer growth, holding, arithmetic, temporary workspace, decoding, output and any added receiver delivery are separate costs. A factored polynomial, variable integer or locally reconstructed output is not a constant-size register. None of these held-data bounds proves an optimum in time, energy, peak workspace, online updating or total resources.

## 17. Supplier scope and the remaining recovery boundary

**Definition 17.1 (reuse and actual-source contribution).** The ordinary `repo-derived` contribution is the order-faithful embedding into the actual paid third-latch language, its every-cutoff strict escape and common-prior full-future transfer, the complete refined-fiber retained-loss bounds and the actual-image finite-length/acquisition bridge. Generic scattered coefficients, Thue–Morse collisions, polynomial profile counting, finite coding and word reconstruction remain reused intermediate tools. These source reads and ordinary proofs are not new Lean applications, builds, kernel/axiom certification, ingestion or coverage, and make no external originality claim.

The actual source and acquired-record suppliers are §§6–11, Boundary Dynamics §§97,100,102,105,114, Future Response Sufficiency §§9,15,21–26, Full E1 Scope Extension §2 and Source Coherence Continuation. They fix the common depth, original stopping grammar, parser-produced identities, from-zero counts, actual posterior, write-before-latch and specified holding/delivery. The normal form, rather than a shared letter name or a generic word theorem alone, is what admits the witness histories.

The generic formal suppliers are MagnusWordCoefficients's coefficient identity, PositivePairFiltration's indexed recursion/cutoff cancellation, LiteralPowerSubstitution's first-degree scaling, ExactDeckCore's common-length $k\le N$ bridge, and FullLyndonRecovery's existing reconstruction of all shorter coefficients from Lyndon coordinates. PositivePairExactDeckAsymptotics already supplies fixed-order generic deck-image growth; its constants and global image exponents are not assumed uniform in a growing cutoff or attained on a specified source fiber. The explicit range product (SC.31) avoids that extra assumption. Joint Moment Fibers §§3,5 already supplies prefix-count and positive-pair mechanisms. The degree-two convention comes from SignatureOrderedMoment/TruncatedTensorSignature, while PrimeGoldenChronologyFiberSeparation needs a nonzero represented commutator and does not supply a universal inverse. The primary word suppliers used with precise statements are Lejeune–Leroy–Rigo Lemma 30, Lejeune–Rigo–Rosenfeld Proposition 12, and Fleischmann–Lejeune–Manea–Nowotka–Rigo's bounded-block inverse and explicit report of the Krasikov–Roditty bound cited above. The original Krasikov–Roditty publication is attributed via its DOI; its square-root statement is used as reported in the cited reconstruction paper.

**Definition 17.2 (pyramid, golden-language and original alphabet boundaries).** [Atom-Pyramid Boundary Calculus](AURIC_FIB_ATOM_PYRAMID_BOUNDARY_CALCULUS.md) §§12.1–12.3 permits task-relative response-kernel replacement only under an actual strict-seam source bijection, correct factor-once accounting and the declared external menu. Equal kernels need not recover internal sources. Here the analogous useful distinction is already explicit: equal original future rows do not restore a discarded actual past. No new seam theorem, tree source or Fibonacci capacity formula is transferred to this stochastic history domain.

That supplier's native $\alpha,\beta$ are ordered-tree leaves, with $\rho(\alpha)=\beta$, $\rho(\beta)=\langle\beta,\alpha\rangle$; its five window modes and no11 paths are not the original fresh raw Read replies. [ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean), `readout`, allows finite-address queries with alpha/beta/branch/absent answers and charges its own distinct-address menu. It supplies no such action here. Its tree bracketing and substitution depth, the pyramid's window-read order, acquired length and physical duration have the separate domains of §12.5. The witness morphism $\theta$ and expansion $\delta$ describe attainable words; they are not operations offered to the running source.

GoldenFactorParikhMagnusBridge's degree-two recovery concerns consecutive factors of the declared golden word, with the original language restriction. The unrestricted paid retry grammar contains every binary retry word and arbitrarily long equal-letter runs, so that restricted rigidity does not invalidate Theorem 14.1 or apply as a source inverse here. AURIC History Records Time Arrow §§185,190 already studies finite area/address-moment blindness; those moments are not the entire fixed-letter scattered-count readout. Its generic recursion and loss principles are reused background, not a duplicate assertion of the present same-paid-history transfer.

**Definition 17.3 (mutual recovery and open extensions).** On the declared actual images, complete chronology, the acquired augmented record and its parser-labelled incidence/precedence expression recover one another; the complete graded fixed-letter readout is another expression of that same information. Finite truncations are projections with actual residual fibers. Increasing aggregate order is necessary within this particular readout architecture across unbounded histories; it is not necessary to raise the arity of occurrence-aware relations, and it does not make a dense hierarchy mandatory memory. The count/law boundary can remain predictively sufficient while chronologically incomplete. Supplied locality and order mean the discrete scopes and precedence of §11.1, without a physical metric or clock.

Sharp source/generic thresholds, the best online acquisition of static supplementary labels, stability for other signature conventions, optimal total resources, wider mutual-recovery conditions and physical space/time reconstruction remain open here. No finite appendix completes the persistent minimal-relational-structure goal.

## 追加锚（本行以下为增补区）

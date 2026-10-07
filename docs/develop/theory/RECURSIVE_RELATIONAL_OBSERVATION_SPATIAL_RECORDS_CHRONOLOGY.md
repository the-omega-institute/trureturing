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

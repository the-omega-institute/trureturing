# Recursive Relational Observation: Native Leaf Boundary Acquisition II

This same-theme continuation of [Native Leaf Boundary Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md), abbreviated NLBA, continues its numbering after §16. Its source is a different active installation: the initial terminal roster has arbitrary raw labels, and acquisition advances the actual source. The ordered stationary installation and all its conclusions retain their stated domains. The numbered arguments below are ordinary mathematics; additions belong after the final append anchor.

## 17. A raw terminal installation with persistent labels and fresh zeros

**Definition 17.1 (the concealed entry and its two address systems).** Use the birth-typed local source of [Atomic Generation Acquisition, Definitions 17.1 and 17.3](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md), abbreviated AA. Thus

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle,
\qquad
P_p:\alpha\longmapsto\beta,
\qquad
S_p:\beta\longmapsto\langle\beta,\alpha\rangle.
\tag{NLBAII.1}
$$

Logical navigation follows children only through branches. A finite logical address below either kind of logical leaf is absent. The material tree $C(t)$ represents an $\alpha$ by one terminal vertex, a $\beta$ by a vertex with one terminal left marker, and a branch by a vertex with two ordered logical child subtrees. A marker is material and has a material address, but is not a logical child or growth target. Material addresses are root-based words over $L,R$ in this presentation. Write $V(u)$ for its material-address set and $\partial C(u)$ for its terminal-address set.

An actual legal old word from the allocated $\alpha$ seed has produced an unknown $t\in\mathcal D$, where $\mathcal D$ is the finite terms with no $\alpha$ at an $L$-ending logical leaf. Let $a,c$ be its numbers of $\alpha,\beta$ leaves and let $L=a+c\ge3$. The old word, $t$, its original internal root reference, its internal addresses and its material order are not observer inputs. The addressed dispatcher is nevertheless authentically bound to that original root. AA Theorem 17.2 supplies both this reachable class and the meaning of its labelled causal order.

At attachment there is a framed authentic complete raw terminal roster $1,\ldots,L$. Its installed binding is a bijection

$$
\lambda_0:\{1,\ldots,L\}\longrightarrow\partial C(t).
\tag{NLBAII.2}
$$

The mathematical codomain in (NLBAII.2) specifies what the real dispatcher binds; the observer is not given the map. Initial raw labels may be arbitrarily permuted relative to the original left-to-right order. They are neither material addresses nor a promise of allocation order. The initial roster is installed at attachment; the persistence law below governs subsequent edits. It is not a restriction asserting that this arbitrary roster was generated from a one-label seed by that law during the concealed old word.

**Assumption 17.2 (one actual field, complete calls and their backing).** Every actual material vertex has a rational field cell. The old preparation initialized each cell to zero and used no field input, so the field at attachment is zero. Its known law is symmetric unit adjacency with zero diagonal. At a current logical term $u$, write $A_u$ for that adjacency matrix, with the actual vertices indexed by their material addresses for mathematical description only. The raw menu is

| Request | Actual effect at a settled cut | Complete reply |
| --- | --- | --- |
| Reset | Set every current field cell to zero; retain the tree and roster | fixed acknowledgement |
| Add$(j,q)$, $1\le j\le n$, $q\in\mathbb Q$ | Add $q$ at the terminal currently bound to raw label $j$ | fixed acknowledgement |
| Tick | Replace $x$ by $A_u x$ | fixed acknowledgement |
| Read$(j)$, $1\le j\le n$ | Retain the tree and field | the literal rational at that terminal |
| Hold | Retain the tree and field; prevent unrequested evolution | fixed acknowledgement |
| $P_p$ | Execute the original guarded promotion at logical address $p$ | original Growth$(P,p)$ or original tagged refusal |
| $S_p$ | Execute the original guarded split at logical address $p$ | original Growth$(S,p)$ or original tagged refusal |

Here $n$ is the current raw roster length. Absent address, branch target and wrong leaf type have distinct refusal reasons; every such refusal leaves tree, field and roster unchanged. Add or Read with an integer outside $1,\ldots,n$ returns RangeRefusal and changes nothing. Complete malformed frames return BadFrame without change. A proper incomplete frame waits with its actual pending input and has no completed reply. Missing current rights disable a call; they are not a refusal reason. There are no Tag, internal Read, internal actuator, FetchGrowth, Next, old-journal, unknown-size or response-law ports.

Use AA Definition 20.2's three-bit tags and address payload $A(p)=1^{|p|}0p$ for the addressed calls, with the stated distinct refusal reasons and Growth payloads. Field calls occupy a disjoint tagged channel. For a definite finite encoding, let $\operatorname{bin}(m)$ be the shortest binary word for $m\ge0$, including $\operatorname{bin}(0)=0$, and encode a nonnegative integer by $1^{|\operatorname{bin}(m)|}0\operatorname{bin}(m)$. A signed integer has an additional sign bit, with negative zero invalid; a reduced rational uses a signed numerator and a positive denominator in these encodings. Fixed operation tags specify the payload types. Invalid complete packets return BadFrame. Thus an acquisition label has $O(\log(n+1))$ bits and zero/one operands have constant length. The channel, parser and encoding are fixed independently of $t$ and $\lambda_0$. Every complete reply, its framing, finite transmission, acknowledgement and return is supplied and charged. There is no timing, work, capacity or allocation metadata in replies.

Calls and completed observer updates are serialized on this one actual source. A requested Tick is the only field evolution. Hold admits finite local work without any additional Tick. No other writer, revocation, crash or unfinished interleaved edit is admitted. Authentic reference and source binding, exact full-field Reset, exact rational arithmetic and serialization, complete roster binding, original current growth authority, finite work backing and sufficient finite fresh material are installed premises. Every newly bound terminal has the actual grants needed by this same service. Allocation exhaustion is not an exposed branch of these finite executions. Enlarging the task by an observable capacity or supply state requires retaining that state as well.

**Definition 17.3 (persistent material and raw-label growth).** The material and field templates are exactly NLBA Assumption 10.2. At an enabled $P_p$, retain the old terminal at $p$, attach a fresh marker at $pL$, and set its field to zero. At an enabled $S_p$, retain the old root at $p$ as a branch, reuse its old marker at $pL$ as the left logical $\beta$ root, and attach fresh vertices at $pLL$ and $pR$, both initialized to zero. Every old material address and every old field value persist. Thus, for the actual inclusion $i$ of old vertices,

$$
x'_{i(v)}=x_v\quad(v\text{ old}),
\qquad x'_z=0\quad(z\text{ fresh}).
\tag{NLBAII.3}
$$

The raw binding has the following additional installed lifecycle. If the acted terminal carried raw label $j$, then

$$
\begin{array}{c|c|c}
\text{edit}&\text{inherited label}&\text{other new label}\\ \hline
P_p&\lambda'(j)=pL&\text{none}\\
S_p&\lambda'(j)=pLL&\lambda'(n+1)=pR.
\end{array}
\tag{NLBAII.4}
$$

All other old raw bindings remain unchanged; a split increases the length from $n$ to $n+1$. The original Growth reply supplies no new raw-label payload. The appended label is known from this installed rule and the maintained length, not inferred from an allocation name. Binding, dispatch and grants in (NLBAII.4) are substantive premises. They are not conclusions of numeric field inversion. This installation replaces initial ordered-roster advice by a particular persistent raw-label contract and permits active acquisition; it is not a strict weakening of the whole NLBA ordered installation.

## 18. Terminal marking earns both entry and current correspondence

**Definition 18.1 (an armed cut and one edit assay).** A settled cut is armed when every current terminal has field value one. No condition on internal cells is included in this definition. To arm the entry, actually Reset, perform Add$(j,1)$ for every initial raw label, and Hold. Between this arming and the final zeroing, the acquisition uses no Tick.

An edit assay starts armed with raw length $n$. Perform exactly one enabled original $P_p$ or $S_p$, consume its whole Growth reply, Hold, and Read every old raw label $1,\ldots,n$, in increasing order. Complete the entire scan even if a zero has already been found. The new split label $n+1$ is excluded from this scan. Rearm by Add$(j,1)$ at the unique old zero label, and, after a split, also Add$(n+1,1)$. No other Add is made in this assay.

**Theorem 18.2 (the fresh-zero inverse for one original edit).** For every current source of §17 at an armed cut, and every enabled edit at a logical leaf whose terminal has unknown old raw label $j$, the assay of Definition 18.1 returns

$$
\operatorname{Read}_{\rm after}(k)=
\begin{cases}0,&k=j,\\1,&1\le k\le n,\ k\ne j.
\end{cases}
\tag{NLBAII.5}
$$

Consequently the actual acted old label is acquired by a finite scan, independently of terminal order, topology, internal field values or a source-dependent selector. The rearming calls make every current terminal one again, with all field values still in $\{0,1\}$ if that was true before the edit.

Proof. At $P_p$, the old terminal at $p$ becomes internal and keeps its value one. Its new marker at $pL$ is fresh zero and inherits exactly its label $j$. No other old terminal or binding changes. Thus every scanned terminal except $j$ remains one, while $j$ reads zero.

At $S_p$, the old marker at $pL$ becomes an internal logical root and retains its value one. The fresh marker at $pLL$ is zero and inherits $j$. The fresh right terminal at $pR$ is also zero but carries the appended label $n+1$, which is not scanned. Every other old label still binds its previous one-valued terminal. This again proves (NLBAII.5). Hold and the absence of Ticks prevent any propagation of internal values into these readings.

Add$(j,1)$ changes a zero terminal to one; after a split the additional Add does the same to the only other new terminal. All unchanged terminals were one already. Old values persist and fresh values were zero, so no cell has left $\{0,1\}$ when the incoming full field was binary. The scan and its zero test use only actual finite replies and the known old roster length. $\square$

**Definition 18.3 (a source-independent entry traversal).** Starting with the armed entry, maintain a finite stack of logical addresses, initially just $\varepsilon$. At each visit to an address $p$, issue the real $P_p$ and consume its complete reply.

1. A branch refusal records a branch and schedules $pL,pR$ in left-first order.
2. Growth$(P,p)$ records an entry $\alpha$ leaf and completes its edit assay.
3. A wrong-type refusal records an entry $\beta$ leaf; issue the real $S_p$, consume Growth$(S,p)$, and complete its edit assay.

Neither leaf case schedules descendants. An absent-address refusal is an off-premise failure for this procedure, not an alternative successful reconstruction. The procedure's control uses the acquired replies, addresses and stack, never an unknown subtree as a runtime argument. It maintains the raw length, increasing it after each successful split. A successful assay at $p$ with decoded old label $j$ records the entry and current bindings

$$
\begin{array}{c|c|c}
\text{entry leaf}&\text{entry binding}&\text{current binding after its assay}\\ \hline
\alpha&j\mapsto p&j\mapsto pL\\
\beta&j\mapsto pL&j\mapsto pLL,\quad n+1\mapsto pR.
\end{array}
\tag{NLBAII.6}
$$

Previously obtained bindings are retained. When the stack is empty, actually Reset and Hold. Retain an entry report $(t,\lambda_0)$ separately from the mutable current code and binding table. This report records the acquired entry, not the unobserved old successful word.

**Theorem 18.4 (actual acquisition of entry and advanced current maps).** Under §17, one fixed finite instruction program carrying out Definition 18.3 terminates for every finite promised $t$ and every arbitrary initial bijection $\lambda_0$. It acquires the exact entry report $(t,\lambda_0)$ and the exact current term and raw correspondence. Its actual final source is

$$
u_f=\rho(t),
\qquad
\rho\alpha=\beta,
\quad \rho\beta=\langle\beta,\alpha\rangle,
\quad \rho\langle v,w\rangle=\langle\rho v,\rho w\rangle,
\tag{NLBAII.7}
$$

with field zero on every actual material vertex. Here $\rho$ is the already defined old-frontier replacement, not a new source opcode. The initial and current tables are earned numerical descriptions of the real binding; neither is an internal-reference cast. No upper bound on source size, depth, preparation length or raw permutation is used for stopping.

Proof. Regard the finite entry term as a proof parameter, not as an input to the program. Its distinct logical leaf addresses are prefix-incomparable. At a branch, a refused $P$ makes no change and schedules precisely its two entry subtrees. An edit made at a leaf in an earlier entry subtree preserves every not-yet-visited entry node, its logical address, its constructor and its original terminal binding. In particular promotions add no logical child, and a split's fresh children are never scheduled by a leaf case.

Structural induction on the entry term therefore proves that the visits are exactly its logical nodes in preorder. The response at each branch is its branch refusal. At an entry $\alpha$, $P_p$ succeeds. At an entry $\beta$, $P_p$ has the wrong-type refusal and the following $S_p$ succeeds. No scheduled visit is absent. There is exactly one successful edit per entry leaf. Each complete inner call is finite under Assumption 17.2; each assay scans a known finite current list. The finite stack consequently empties without source-size advice. Its recorded constructors reconstruct precisely $t$.

The arming invariant is established by the initial Reset and terminal Adds. Branch and wrong-type refusals preserve it; Theorem 18.2 reestablishes it after each edit assay. Thus every decoded $j$ is the actual old raw label at that addressed entry leaf. An unprocessed entry leaf has never moved or been relabelled. Its label is still its initial label in $1,\ldots,L$. The decoded old labels are therefore distinct initial labels, exhausting that set after all $L$ leaves. This proves the entry map in (NLBAII.6), including the distinction between an $\alpha$ vertex and a $\beta$ marker.

For the current map, an entry $\alpha$ contributes exactly the terminal at $pL$. An entry $\beta$ contributes exactly $pLL,pR$, with the old and appended labels specified in (NLBAII.6). Distinct entry leaves have disjoint descendant regions. Later entry edits do not modify earlier contributions; all split labels are appended once with distinct new integers. These assignments are disjoint and exhaust the actual final terminals, so they are precisely the current bijection, rather than a partial association.

The source endpoint is the established old-frontier macro of [LAB Arithmetic Growth, Definition 9.3 and Theorem 9.4](RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md) and NLBA Proposition 12.3: each entry $\alpha$ was promoted once, each entry $\beta$ split once, and old branches persisted. These already proved semantics give (NLBAII.7); the additional result here is the acquired raw/address correspondence without a supplied frontier or ordered roster. Rearming also occurred after the last assay. The final actual Reset sets every cell, including internal old and fresh cells, to zero; the final Hold preserves that cut during the retained-code construction. $\square$

## 19. Retained raw prediction and an actually callable ordered service

**Definition 19.1 (the synchronized retained state).** After Theorem 18.4 retain the mutable recursive current term $u$, its finite material graph, a field vector $\widehat x$ in persistent material-address coordinates, and the acquired raw table $\widehat\lambda$. Retain the actual service reference, current rights, finite instruction program, pending-call workspace and their backing. The entry report is an additional immutable archive, with separate storage.

The mathematical invariant has a root-preserving material isomorphism $\iota$ to the actual current source satisfying

$$
\widehat x_v=x_{\iota(v)}\quad(v\in V(u)),
\qquad
\text{raw label }j\text{ actually binds }\iota(\widehat\lambda(j)).
\tag{NLBAII.8}
$$

The original logical constructors and addresses also coincide. Initially $u=\rho(t)$ and $\widehat x=0$. The isomorphism is a proved correspondence; evaluating it does not provide a callable internal actuator or a new object reference.

**Theorem 19.2 (full raw-menu prediction on the advanced source).** From the acquired cut there is a retained finite transition procedure, requiring no further correspondence-learning assay, with these properties for every finite common adaptive continuation of the whole raw menu of Assumption 17.2. It predicts the entire reply of every next request, computes its corresponding complete successor, and maintains (NLBAII.8) at every settled cut after actual use. All finite addresses, integer labels and rational operands are admitted with their stated refusal or success semantics. Hypothetical calculation alone issues no real command and makes no actual source change.

Proof. Theorem 18.4 establishes the invariant at the actual final zero cut. Navigate logical $u$ to decide the original guard at $p$. This is exactly the finite constructor navigation of NLBA Theorem 12.1 and the existing Native code-navigation results, not an acquired Tag port. An absent, branch or wrong-type refusal is predicted with its exact reason and identity successor.

For a successful $P_p$, the current table contains exactly one $j$ with $\widehat\lambda(j)=p$. Retain all old field coordinates, add coordinate $pL$ with value zero, replace the logical $\alpha$ by $\beta$, and replace just that table entry by $pL$. The source does exactly this by (NLBAII.3)–(NLBAII.4). For a successful $S_p$, find the unique $j$ with $\widehat\lambda(j)=pL$. Retain coordinates $p,pL$ and their old values, add $pLL,pR$ with zero values, make the branch with its left $\beta$ and right $\alpha$, and set $\widehat\lambda(j)=pLL$, $\widehat\lambda(n+1)=pR$. All other entries persist. Extend $\iota$ by the actual fresh vertices. Both success replies are the original complete kind/address words. Fresh grants come from Assumption 17.2, not from this finite calculation.

Reset zeros the whole retained vector. Add$(j,q)$ uses the earned table to add $q$ at exactly the actual bound terminal. Read returns its retained rational. The adjacency step satisfies the already established persistent-field calculation

$$
(A_{\rm actual}x)_{\iota(v)}
=\sum_{w\sim v}x_{\iota(w)}
=\sum_{w\sim v}\widehat x_w
=(A_u\widehat x)_v.
\tag{NLBAII.9}
$$

Hold changes no coordinate. These are NLBA Theorem 12.1's field correspondences with the newly earned raw table in place of a supplied ordered table. Out-of-range labels are determined by the same current $n$ and have their exact RangeRefusal and identity successor. Complete malformed frames produce the same BadFrame. Proper incomplete frames retain the finite pending input and wait on both descriptions, with no completed output or source edit. The fixed framing rule introduces no source-dependent extra reply.

For actual use, forward the real call, consume its entire reply and return, and complete the retained update before exposing another settled cut. Exclusive serialization makes the source and its record coincide there. For hypothetical use, perform the same finite computation on a separately charged copy, without forwarding. Induct on the number of complete requests: equal preceding complete replies make a common adaptive policy choose the same next request, operand and stop decision; the verified one-step correspondence then supplies equal full replies and related successors. Fixing a common random tape gives the same argument for each finite realized continuation. No inverse of $A_u$, bounded lifetime store or finite response oracle is used. $\square$

**Definition 19.3 (the earned canonical dispatcher).** Enumerate the current logical leaves in left-to-right order using the retained finite $u$. For each leaf, its material terminal is the leaf itself for $\alpha$, and its marker for $\beta$. Let $\tau_u(k)$ be the resulting $k$th material terminal address. For $1\le k\le n$, scan the earned raw table to find the unique label

$$
\pi_u(k)=\widehat\lambda^{-1}(\tau_u(k)).
\tag{NLBAII.10}
$$

The callable ordered entry translates Add$(k,q)$ and Read$(k)$ to actual raw calls with label $\pi_u(k)$, forwards their entire responses, and commits the matching retained updates. It forwards the other valid operations, including original addressed $P/S$, unchanged. An out-of-range ordinal is forwarded unchanged and is out of raw range as well. The same source-independent grammar is used for field ordinals and raw labels; malformed complete frames remain malformed and are forwarded to that branch. Proper incomplete frames are held pending without a completed inner or outer operation. Buffering, parsing, scanning, rewriting, forwarding, output and return are finite paid work of this dispatcher, not a selector primitive.

**Theorem 19.4 (realization of the ordered contract by the earned map).** On the same actual $C(\rho(t))$ and its subsequent actual successors, Definition 19.3 realizes exactly NLBA Definition 10.1 and Assumption 10.2's ordered field-and-original-growth service. In particular its terminal order, guards, full replies, persistent field lifts and settled successors agree for every finite common adaptive canonical continuation. Its retained entry is callable on the actual source under the existing current grants.

Proof. By Theorem 18.4, the current raw table is a bijection onto the actual terminals and $u$ is the original current ordered syntax. Therefore (NLBAII.10) sends the canonical ordinal to that very terminal. This proves the ordered Add and Read meanings without assuming an ordered initial roster.

After $P_p$, the same position in canonical order contains its fresh marker. After $S_p$, that one position is replaced by the consecutive left marker and right $\alpha$. Every other terminal retains its relative order. The raw-label updates in Theorem 19.2 bind precisely these vertices, so recomputing (NLBAII.10) gives exactly NLBA's ordered-roster replacement rule. The source graph and field are the actual graph and field throughout; neither a replayed specimen nor a separately optimized source has been substituted. All other operations and all negative replies have the common literal meanings checked in Theorem 19.2. The same finite adaptive induction applies. The callable reference and rights were retained throughout, with backing for the finite scans and calls, so this is an installed translation and not merely an extensional relabelling formula. $\square$

## 20. The canonical zero-cut kernel and the richer private task

**Definition 20.1 (independent canonical expressions and common context).** Fix the actual canonical entry of Definition 19.3, the field law, serialization, binding and authority roles of §17. The canonical continuation task permits exactly the ordered menu realized in Theorem 19.4, with all its full output and successor semantics. It exposes no direct raw-label call, private table inspection, entry-archive inspection, cost meter or allocation-name port.

Let $\mathcal Z_{\rm can}$ be the settled acquired-or-later cuts with $u\in\mathcal D$, at least three current logical leaves, no pending frame or edit, completed matching retained update, and zero on every actual material field cell. Define the following data by their source meanings, using NLBA Definition 13.1's observations.

| Expression | Independent content on $\mathcal Z_{\rm can}$ |
| --- | --- |
| Space | The unrooted unit material tree, its complete canonical linear terminal order, and its present zero field, modulo terminal-order-preserving isomorphism |
| Time | The labelled causal birth/lifecycle order of all successful original $P/S$ events from the actual seed to the current source |
| Boundary | The canonical terminal-to-terminal first-nonzero impulse-onset table of the actual unit-adjacency law, with diagonal zero, together with the present terminal zero restriction |
| Memory | The retained current recursive constructor code, zero field vector and canonical ordinal-to-material-terminal table, interpreted at the fixed actually callable canonical entry |

Time has AA's original $(P,p),(S,p)$ labels and its actual lifecycle/creation precedences, not an arbitrary chosen serialization. It includes the successful acquisition growth as well as earlier source growth. It omits Reset, Add, field Ticks, Holds and elapsed duration. Boundary is independently defined by what a unit impulse and successive actual adjacency Ticks would do at the canonical terminals. Marking does not literally sample this onset table: the table is computable after acquisition from the earned graph. Producing that finite derived table incurs its calculation, output and storage costs; literal onset sampling would require further actual assays.

Memory's canonical ordinal table is determined by the constructor record; it contains no raw labels. The raw implementation table, entry report, parser backing, grant records and actual reference are separately retained parts of the installation. The common context fixes binding and authority for the data-recovery assertions; no recovery direction creates these resources or determines their private bytes. Memory is a finite transition representation at the current cut, not an unrestricted copy of the generation or field-control history.

**Proposition 20.2 (application of the existing zero-cut inverse to the acquired dispatcher).** On the actual joint image of $\mathcal Z_{\rm can}$, each of the four data expressions in Definition 20.1 recovers the other three. All recovery routes agree. Each has exactly the kernel of the canonical continuation task. These data recoveries commute with every admitted finite operation or composite whose starting and ending cuts lie in $\mathcal Z_{\rm can}$. The raw predictor remains valid also at the intervening nonzero cuts.

Proof. The new hypothesis correspondence is Theorem 19.4: this acquired actual dispatcher, graph, original root interpretation, field lift and ordered roster satisfy precisely NLBA §§10–13, and the final Reset of Theorem 18.4 supplies a genuine zero entrance. Thus NLBA Theorem 13.2 and Proposition 13.3 apply to this service, with the following data maps and no change of their hypotheses.

The boundary table is the complete canonical leaf metric by NLBA Lemma 2.1. NLBA Lemma 2.3 recovers its full unit subdivision tree, and NLBA Theorem 11.1 recovers its original root and ordered $u$. Space uses that same root inverse. AA Theorem 17.2 recovers $u$ from its actual labelled causal order and computes that order from $u$. Memory already decodes $u$. At the declared cuts the whole field is known to be zero, so these are exactly the four existing observations, not definitions of the missing inverses. Every recovery factors through the same original current $u$; composing back gives the identity on each actual image. This also gives route agreement.

Equal $u$ gives identical entire canonical continuations by Theorems 19.2–19.4. Different roster lengths already give different exposed legal ranges. At equal lengths, different $u$ have different canonical onset tables by the cited full-tree and original-root inverses; an actual finite Reset/Add/Tick/Read experiment distinguishes them. Hence every one of the four data kernels is precisely the canonical task kernel.

The persistent field correspondence and actual canonical roster updates have already been verified in §19. Successful $P/S$ preserve a globally zero field and update the causal order by their actual new events. Tick, Read, Hold, Reset, Add$(k,0)$ and the negative replies have the existing zero-domain meanings. Nonzero Add can leave the domain; Theorem 19.2 still transports the full intermediate field, including through later growth. If a finite composite returns to zero, its ending views are again the four observations of that same ending $u$, so it gives the same result along every recovery route. This is the existing four-view theorem instantiated at an earned ordered entry, not a new generic four-view principle. $\square$

**Proposition 20.3 (the whole-field zero condition cannot be replaced by terminal zeros).** On the acquired source, Time and the structural onset table do not determine arbitrary current fields. Even supplementing them by the present terminal zero readings does not recover the full field on the unrestricted continuation domain.

Proof. At any acquired current $u$ choose a canonical terminal $\ell$ and its neighbour $v$. Since the material tree has at least three leaves, $v$ is nonterminal. One actual continuation is Reset. Another is Reset, Add$(\ell,1)$, Tick, where the Add uses the earned canonical ordinal. Unit adjacency and the fact that $\ell$ has degree one give $A_u e_\ell=e_v$. The resulting fields are respectively zero and $e_v$. Their Time and structural onset tables coincide, and every current terminal reads zero in both. A further Tick followed by Read at $\ell$ returns respectively zero and one. Thus they have different full fields and different canonical future behavior. A paid actual Reset restores $\mathcal Z_{\rm can}$ in either case. Theorem 19.2 also detects membership there from its synchronized full vector. This supplies the exact zero-cut restriction used above; it does not assert that no other, differently restricted nonzero recovery domain exists. $\square$

**Proposition 20.4 (raw maps and entry reports are additional information).** The canonical four expressions do not recover the private raw correspondence, the entry archive or authority. In particular their exact task-kernel assertion does not extend to the richer direct-raw-label task.

Proof. Fix one entry $t$ and vary its arbitrary initial raw bijection. Theorem 18.4 produces the same $\rho(t)$ and final zero field for all choices, but different inherited raw correspondences. The canonical current four data expressions are identical. Choose a current logical leaf at which two resulting raw tables assign different old labels $j,j'$. In both raw services Reset and Add one at every current raw terminal. Then perform the enabled original growth at that same logical address and Read$(j)$. Theorem 18.2 gives zero in the installation where $j$ was acted on and one in the other. Thus a common finite direct-raw continuation distinguishes these two states, although their canonical ordered continuations agree. The retained raw map supplies an indispensable distinction for this richer prediction task. The construction makes no minimum-size or total-cost assertion about its representation.

For the entry report, take

$$
t_0=\langle\beta,\langle\beta,\alpha\rangle\rangle,
\qquad
t_1=\langle\beta,\langle\beta,\beta\rangle\rangle.
\tag{NLBAII.11}
$$

Both are reachable with three logical leaves. After their respective acquisitions, one actual $S_{RR}$ from $\rho(t_0)$ gives exactly $\rho(t_1)$; it is enabled because that subtree in $\rho(t_0)$ is $\beta$. The second acquisition is already at that same term. All these cuts have globally zero fields. Their current canonical four data agree, while their retained entry reports contain different terms. This concerns general acquired-or-later cuts; it does not deny the invertibility of $\rho$ on an appropriately promised immediate endpoint. An entry archive is therefore kept as a separate historical report, not hidden in causal Time or the current canonical kernel.

Finally data equality never supplies an actual reference or grant. The same finite data can be present without an authorized entry; then the corresponding source call is disabled. The common-binding and current-rights premises are necessary for the callable claim and are held fixed in Proposition 20.2. No data inverse to private authority has been asserted. $\square$

## 21. One attained preparation, acquisition and continued-use account

**Definition 21.1 (charged run and representations).** All counts refer to one actual old preparation, this acquisition, its retained records and any subsequent use. Charge integer and rational operations at their actual finite operand widths; charge each located source or dispatcher assignment, allocation and grant, request, complete reply, frame, acknowledgement, return, copied bit and local scan. Actual references have their actual encoded lengths. No arbitrary integer, source-specific selector, raw-to-address decoder or object reference has unit-size backing by convention.

For the entry let $a+c=L$, $N_0=|V(t)|$, and let $w_0$ be the actual old successful word, with $D_0$ the sum of its address depths. The word and $D_0$ are resource-analysis parameters, not observer advice. In the actual left-first order of the entry leaves, number their assays $r=1,\ldots,L$, let $B\subseteq\{1,\ldots,L\}$ be the positions of entry $\beta$ leaves, and let $n_s$ be the actual roster length after $s$ such assays. Put

$$
n_s=L+|B\cap\{1,\ldots,s\}|,
\qquad
R_{\rm mark}=\sum_{s=0}^{L-1}n_s
=L^2+\sum_{r\in B}(L-r).
\tag{NLBAII.12}
$$

These are the sizes and reads on this particular run, not optima taken from separate runs. The maintained current length and empty-stack test supply all loops; none of these a posteriori parameters is a stopping bound.

**Theorem 21.2 (attained acquisition operations and source work).** The acquisition of Definitions 18.1 and 18.3 has the following exact counts:

$$
\begin{aligned}
N_0&=2L+c-1, & n_f&=L+c, & N_f&=3L+2c-1,\\
\text{successful promotions}&=a,&\text{successful splits}&=c,
&\text{fresh material vertices}&=a+2c.
\end{aligned}
\tag{NLBAII.13}
$$

There are $2L-1$ addressed $P$ calls and $c$ addressed $S$ calls, a total $M=2L+c-1$. Exactly $L$ succeed; the $L-1+c$ remaining calls are the stated branch and wrong-type refusals. Including initial arming, rearming after every assay including the last, and final zeroing, its field calls are

$$
\begin{array}{c|c}
\text{operation}&\text{actual count}\\ \hline
\mathrm{Reset}&2\\
\mathrm{Add}(j,1)&2L+c\\
\mathrm{Tick}&0\\
\mathrm{Read}(j)&R_{\rm mark}\\
\mathrm{Hold}&L+2.
\end{array}
\tag{NLBAII.14}
$$

Thus there are $3L+c+4$ fixed field acknowledgements, separately from $R_{\rm mark}$ scalar replies and $M$ full addressed replies. Every acquisition field value and scalar reading lies in $\{0,1\}$. Source field work is exactly $2L+c$ unit additions, $N_0+N_f$ Reset cell writes and $a+2c$ fresh active-field zero initializations, with no acquisition adjacency arithmetic or Tick-buffer clearing. The located source parent/left/right growth assignments are $4a+8c$ in AA's templates. Maintaining an indexed raw binding table uses one changed binding per promotion and two per split, hence $a+2c$ binding assignments, besides length updates, navigation, material allocation, grants, framing and return.

Proof. A logical full binary tree with $L$ leaves has $2L-1$ logical nodes; each $\beta$ adds its one marker. This gives $N_0$. Theorem 18.4 visits each logical node with $P$ and visits each entry $\beta$ once more with $S$. The leaf edits are precisely $a$ promotions and $c$ splits; they add $a+2c$ vertices and $c$ leaves. This gives every count in (NLBAII.13) and the addressed success/refusal counts, without using a source-size announcement.

Arming makes one Reset and $L$ Adds. Each of the $L$ assays scans exactly its old roster of size $n_s$, uses one Hold, and rearms one inherited terminal. Each split rearms one additional appended terminal. Final zeroing adds one Reset and one Hold. This proves (NLBAII.12) and (NLBAII.14). Reset, Add and Hold each return one fixed acknowledgement, giving $2+(2L+c)+(L+2)=3L+c+4$. The binary-field assertion follows from the zero start, the absence of Ticks and Theorem 18.2.

Each Add makes exactly one unit addition. The two Resets act on the actual sizes $N_0,N_f$. Fresh active cells are initialized once per allocation by (NLBAII.3). AA Proposition 22.1's promotion and split templates have respectively four and eight located structural assignments. Formula (NLBAII.4) has respectively one and two changed binding entries. These counts concern the named structures and exclude neither the actual dispatcher work nor the allocation, grant and bit-level costs specified separately. $\square$

**Proposition 21.3 (literal traffic and old preparation on that same run).** Let

$$
J_{\rm all}=\sum_{p\text{ entry logical node}}|p|
+\sum_{p\text{ entry }\beta\text{ leaf}}|p|,
\qquad
J_{\rm leaf}=\sum_{p\text{ entry logical leaf}}|p|.
\tag{NLBAII.15}
$$

The addressed request payload is exactly $2J_{\rm all}+4M$ bits and its reply payload is exactly $2J_{\rm leaf}+5M$ bits in Assumption 17.2's AA framing. Each of the $M$ replies also has its actual completion, local acknowledgement and return. Add all literal field command/index/rational frames, the initial roster frame, pending latches, transmission and cleanup. The old preparation has exactly $c$ promotions and $L-1$ splits, $3+4c+8(L-1)$ located source structural assignments, and $N_0$ initial active-field zero writes. Its actual old address traffic, $D_0$ navigation, original root installation, roster attachment, allocations, grants, source and observer backing are additional parts of the same bill. Any old journal actually retained by that preparation is additional material, not an input earned by this acquisition.

Proof. An addressed request has three tag bits and $2|p|+1$ address bits. The calls consist of one at every old logical node and the extra one at every old $\beta$ leaf, giving the stated request length. A success reply has its three-bit tag, kind bit and address word, hence $2|p|+5$ bits. A refusal has its three-bit tag and two-bit reason, hence five bits. There is exactly one success at every old leaf, giving the reply expression. Scalar readings here are literal zero or one, but their request labels and framing still have their own finite lengths.

AA Proposition 22.1, applied to the actual word ending at entry counts $(a,c)$, gives $P_0=c$, $S_0=L-1$ and the displayed source construction count. The zero field was initialized on those actual allocated cells. The arbitrary terminal bijection installed at attachment has $L$ actual bindings and their actual references and grants. Neither concealing their address interpretation from the observer nor lacking the old serial word makes any of this source work free. $\square$

**Proposition 21.4 (a simultaneous finite layout and continued prices).** There is an attained acquisition layout with $R_{\rm mark}\le L(L+c)$ scalar scans, $O(R_{\rm mark}+N_f^2)$ additional local comparisons, indexed record operations and logical-address symbol copies, and the following coexisting stores. This operation count is in addition to field-frame encoding, parsing and transmission. Integer comparisons, indexing and copying have their actual widths; it is not a unit-bit complexity bound.

| Store | Attained size or separate charge |
| --- | --- |
| Actual material tree and installed field/Tick backing | $N_f$ vertices, $N_f-1$ links, binary active field during acquisition, actual references, dispatcher and any reserved output buffer |
| Mutable current code and graph, raw terminal table and current field vector | $O(N_f\log(N_f+1))$ numerical bits in an indexed layout at the binary-field acquisition cuts |
| Entry code and initial raw/address report | $O(N_0\log(N_f+1))$ numerical bits in a separately retained indexed layout |
| Logical traversal stack and explicit address work | $O(N_f^2)$ bits for copied binary address words and pending finite frames |
| Scan counters, identified labels, current length and parser control | finite words of their actual lengths; numerical counters have $O(\log(N_f+1))$ bits |
| Program, actual bound entry, current grants, I/O and work backing | their actual simultaneous sizes |

Replies may be consumed and cleared as each assay records its unique old zero label; no scalar archive or complete onset matrix is retained by this layout. If exported, a full current canonical onset table can be computed in $O(n|V(u)|)$ indexed graph visits by separate unit-tree traversals and has $n^2$ entries of $O(\log(|V(u)|+1))$ bits. Its export and any retained copy are additional. Later operations pay their actual growing source, retained-record, arithmetic, scanning and output costs.

Proof. Equation (NLBAII.12) bounds each of its $L$ summands by $L+c$. The scan compares each received bit-valued rational with zero, retaining the identified label and enough state to check uniqueness. Copied addresses have length at most $N_f-1$, and at most $O(N_f)$ frames and node records coexist. Maintaining current and entry tree records by finite scans, locating their indexed nodes and copying their address work can conservatively be done in $O(N_f^2)$ local operations and symbols, in addition to the $R_{\rm mark}$ readings and their parsing. These steps use exactly the retained codes and replies of the proved traversal. They invoke no unknown permutation decoder. Encoding each indexed node, child and table entry needs $O(\log(N_f+1))$ numerical bits, which proves the indexed-store rows; the separate copied-address bound is not hidden inside them. The actual reference encodings and authority backing are further charges.

Once installed, code navigation decides a $P/S$ guard in at most a scan of its finite address and current code. A canonical terminal lookup and a raw-table inverse lookup can both be performed by finite scans of at most $O(|V(u)|)$ entries; no constant-price selector is assumed. A successful $P/S$ extends the retained full vector by one or two zero cells and changes the stated bindings. Reset writes every current source cell and every retained vector coordinate. An actual Tick may use a zeroed source output buffer and the $2(|V(u)|-1)$ directed unit-edge additions; matching prediction uses its separately charged retained vector and the same adjacency calculation. Add makes its actual rational addition, Read transmits its actual scalar width, and every operation pays framing, full output and return. Hypothetical multi-step predictions use their actual copies and local work without source commands.

A tree traversal from each canonical terminal computes its distances to all the others in $O(n|V(u)|)$ indexed visits; NLBA Lemma 2.1 identifies these computed values with onset times. A complete distance word and causal-event label word must be constructed and transmitted at their actual sizes when requested. Later rational operands and nonzero adjacency iterations can have arbitrarily large widths, and later growth can have arbitrarily many vertices. The finite instruction program supplies pointwise finite use, not bounded lifetime memory or a uniform total bill. $\square$

**Proposition 21.5 (one concrete attained marked run).** Take the entry

$$
t=\langle\beta,\langle\beta,\alpha\rangle\rangle,
\qquad
\lambda_0(1)=RR,\quad\lambda_0(2)=LL,\quad\lambda_0(3)=RLL.
\tag{NLBAII.16}
$$

There is an actual run of §18 with $a=1,c=2,L=3$, $N_0=7$, $N_f=12$ and final roster length five. Its acquired canonical-to-raw terminal permutation is $(2,4,3,5,1)$. Acquisition uses seven addressed calls, two Resets, eight Adds, twelve scalar Reads, five Holds and no Tick. Its addressed payloads are 46 request bits and 45 reply bits, before channel completion and return. These counts occur together on this same run.

Proof. The legal old word $P_\varepsilon S_\varepsilon P_RS_R$ constructs this $t$, with zero field throughout the old preparation. Its structural preparation has 27 located assignments and seven active-field initializations as in Proposition 21.3. Install precisely the arbitrary raw bijection (NLBAII.16), then actually arm its three terminals.

The traversal's leaf assays are at $L,RL,RR$. At $L$, $P$ returns wrong-type and $S$ succeeds; the three old raw readings are $(1,0,1)$. Label two now binds $LLL$, and the appended four binds $LR$; rearm both. At $RL$, another wrong-type $P$ and successful $S$ give the four old raw readings $(1,1,0,1)$. Label three now binds $RLLL$, and appended five binds $RLR$; rearm both. At $RR$, $P$ succeeds and the five readings are $(0,1,1,1,1)$. Label one now binds $RRL$ and is rearmed. The root and $R$ visits are the two branch refusals, so there are five $P$ calls and two $S$ calls. The final Reset/Hold leaves the actual $\rho(t)$ with globally zero field.

The final raw table is consequently $1\mapsto RRL$, $2\mapsto LLL$, $3\mapsto RLLL$, $4\mapsto LR$, $5\mapsto RLR$. The canonical terminal order is $LLL,LR,RLLL,RLR,RRL$, giving the displayed permutation. The old scan lengths are $3,4,5$, summing to twelve. Initial arming uses three Adds and rearming uses $2+2+1$ more. Including the initial and final Holds gives five Holds. Finally $J_{\rm all}=9$, $J_{\rm leaf}=5$ and $M=7$ in Proposition 21.3, giving 46 and 45 bits. All named scalar readings, growth replies and updates have been specified on this actual sequence, rather than collected from separate minimizers. $\square$

## 22. Sufficient alternatives and exact boundaries of the acquisition

**Proposition 22.1 (a sufficient propagation alternative and its resource distinction).** On exactly the installation of §17, repeated first-arrival assays from one persistent raw anchor also suffice to acquire the acted label after each single successful edit. This alternative uses adjacency propagation; the marking acquisition above does not need it. Neither construction is asserted to minimize the whole resource vector.

Proof. Fix raw anchor $h=1$ at a settled current source. Reset, Add$(h,1)$, and Hold. At each positive Tick, Hold and Read just the still-pending other raw terminals until each has first returned nonzero, removing a terminal from the pending list when it arrives. NLBA Lemma 2.1 says that its first epoch is exactly $d(\lambda(h),\lambda(k))$ and its first value is one. Finite connectivity proves termination without a size bound. This is the existing first-arrival fact, applied to raw-labelled terminals without using their original order.

Let $d,d'$ be the distances before and after one successful edit whose inherited old label is $j$. Every old edge persists and the terminal carrying $j$ moves one edge farther outward, for either growth template. Thus for distinct old labels $r,k$,

$$
d'(r,k)-d(r,k)={\bf1}_{r=j}+{\bf1}_{k=j}.
\tag{NLBAII.17}
$$

When $j\ne h$, the anchor-row change on old $k\ne h$ is a single one at $j$. When $j=h$, all those entries increase by one. Since the old roster has at least three terminals, these signatures are distinct. Comparing consecutive earned rows identifies $j$, and the fixed append rule identifies a split's new label. The same old-frontier traversal therefore earns the two maps. One may omit the last new row: after the first $L-1$ distinct initial labels have been identified, the last original leaf has the sole unused initial label. This elimination uses actual recorded labels, not a supplied correspondence.

For example, an alternative that measures the initial row and the rows after the first $L-1$ leaf edits has $L$ unit trials on actual intermediate sources $u_s$, $s=0,\ldots,L-1$. Write $N_s=|V(u_s)|$, let $D_s$ be the current anchor eccentricity and set

$$
K=\sum_{s=0}^{L-1}D_s,
\qquad
R_{\rm row}=\sum_{s=0}^{L-1}\sum_{k\ne h}d_s(h,k).
\tag{NLBAII.18}
$$

Including final Reset/Hold, that specified schedule uses Reset $L+1$, Add $L$, Tick $K$, Read $R_{\rm row}$ and Hold $K+L+1$. Its direct source field additions are $2\sum_s D_s(N_s-1)+L$, before its additional actual dispatch, decoding and retention work. These are counts on that alternative's own one run. Marking instead has the counts of Theorem 21.2, more unit Adds and no propagation; no sum of different alternatives' separately best coordinates is claimed attained.

Reacquiring the complete raw leaf metric after every edit is another sufficient choice, using one pulse at every current terminal rather than one anchor trial at that stage; (NLBAII.17) still identifies the inherited label. The old NLBA ordered-roster installation is a sufficient stationary alternative when authentic initial order is already supplied, and preserves the entry source. Guard-only constructor traversal can suffice for source syntax with appropriate destructive updates, but syntax by itself contains no arbitrary raw bijection, as Proposition 20.4 proves. The final rearming of the marking schedule is also dispensable if followed immediately by final Reset; omitting its one or two Adds changes its attained counts, not its correspondence theorem. These are sufficient operational comparisons, not a whole-resource optimum. $\square$

**Proposition 22.2 (load-bearing initialization and lifecycle premises).** The marking proof requires the fresh-zero field lift, held execution and persistent-label rule. Removing any of these from the installation invalidates the corresponding inference in its transcript. This statement is about this protocol, not impossibility of all identification procedures on larger alternative models.

Proof. If the fresh marker instead starts at one, while all old terminals are one, a promotion leaves every scanned terminal one. The zero signature (NLBAII.5) is absent. If unrequested adjacency Ticks are allowed, start from the initial arming field, which is one at all terminals and zero internally. One such Tick makes every terminal zero, because every terminal's neighbour is internal. A subsequent successful edit with fresh zeros now has all its other old terminals zero as well. The scan does not have a unique old zero label. These are concrete failures of the inference even though the source remains a finite tree.

If arbitrary post-edit relabelling is allowed, a promotion followed by swapping the acted label with an untouched label makes the unique zero appear under that other label. The scan then identifies its post-swap label rather than the old label in the entry correspondence. The preserved-table induction and the entry assignment in (NLBAII.6) are invalid without (NLBAII.4). Additional observations or a different lifecycle could support a different theorem, but are not supplied by this proof. Likewise the controlled source-root binding, complete roster, full-field Reset, current rights and exact call/return are assumptions of the actual experiment, not facts certified by a zero/one transcript. $\square$

**Proposition 22.3 (irreversible advance and unrecovered chronology).** The acquisition returns an advanced source rather than an unchanged specimen. Its current canonical data, raw correspondence and acquired entry report do not determine the old total successful generation word on the unrestricted old-history domain of §17.

Proof. It adds $a+2c>0$ material vertices using only the two positive growth templates. Reset changes fields only, and the menu has no deletion or source reset. Hence the actual endpoint cannot be the entry material tree. This is the particular acquisition endpoint claim, not a statement about all possible stronger source interfaces.

For chronology use NLBA Theorem 14.3 and AA §§18–19's already proved old-word fibres. Explicitly, the legal words

$$
P_\varepsilon S_\varepsilon S_LP_R,
\qquad
P_\varepsilon S_\varepsilon P_RS_L
\tag{NLBAII.19}
$$

end at the same $\langle\langle\beta,\alpha\rangle,\beta\rangle$ and have the same split word, but different third events. Their old field stays zero. Attach the same raw bijection at their common term. Every attachment datum and every current raw menu meaning in §17 is then identical. All actual marking calls, replies, acquired entry and current maps, and future full raw predictions agree by the proved invariant. They cannot determine which old word occurred. Time in Definition 20.1 is instead their common labelled causal order. An actual old FetchGrowth/Next service or old total journal would require the separately retained historical material and ports of AA, which are absent here. $\square$

## 23. Supplier subtraction and retained mathematical scope

**Definition 23.1 (exact attribution and scope).** The raw-label fresh-zero inverse, its entry/current acquisition join and its actually retained ordered dispatcher are `repo-derived` source-specific deductions. The following supplied mathematics is used with its original conditions, rather than asserted as new content.

| Supplier | Exact correspondence and limit |
| --- | --- |
| [NLBA §§10–16](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md) | Its $C(t)$, original guards, persistent field inclusion, zero initialization, full-menu invariant, ordered root rigidity and zero-cut four-view theorem are retained. Initial authentic terminal order is replaced here by §17's raw binding and label lifecycle; §§18–19 earn the missing association. No new root-rigidity, general wave inverse or four-view theorem is claimed. |
| [NLBA Lemma 2.1 and Lemma 2.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md) | First arrivals give unit leaf distances and the full subdivision tree has the stated distance-vector inverse. They are used for the propagation comparison and canonical boundary interpretation, not as unpaid measurements in terminal marking. |
| [AA §§17–23](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md) | The reachable birth-typed class, unary-marker source, actual original edits, causal reconstruction, complete addressed framing and located structural counts are unchanged suppliers. The routing records and FetchGrowth/Next ports of its larger history service are not present here. |
| [LAB Arithmetic Growth §§9–10](RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md) and NLBA Proposition 12.3 | The old-frontier macro is exactly $\rho$ with $a$ promotions and $c$ splits. It is reused after unknown-frontier traversal; its endpoint and counts are not claimed as new. |
| [NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs) | `sourceControl`, `initialControl`, `native_source_producer` and private `traverse`, `production_reads`, `stationary` supply acquired-stack finite traversal on an unchanged source with literal Native constructor reads. Those stronger reads do not supply this raw-port relation. The fixed-stack method itself is credited, not reinvented. |
| [NativeUniformTree](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.scribe.cs) | `term_at_prim`, `readout_prim`, `substitution_prim` and private `treeView`, `child`, `walkStep`, `walk_exact`, `rootReply`, `readout_walk` supply finite navigation and substitution on supplied codes. They give no reference cast, fresh grant or identification of an unknown raw binding. |
| Pinned mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, [Algebra/Free](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Free.lean), [SimpleGraph/Metric](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/Metric.lean) | `FreeMagma.of`, `mul`, `lift`, `hom_ext` and graph distance are existing syntax and metric tools. They do not provide this source's raw lifecycle or an acquired correspondence. |
| [NCR §§1–2,8](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md), [PVC §§1–2](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md), [Structural Atlas 13.7](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md), [PR57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#57-a-complete-paid-ideal-realization-of-the-original-ordered-tree-interface) and [Process Geometry §40](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) | Acquired source codes, actual retained/callable records, task-relative complete behavior, separately earned command-order complements and paid view conversion are existing results under their own Native, fixed-$H$, atomic-patch, lane, meter and original-output premises. None installs the raw/addressed association of (NLBAII.2). The additional result is that concrete source-dependent association and its service use, rather than a new generic converter or history wrapper. |
| [Atomic Global Port Orientation §§22–26](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md) | Its hidden local wiring, global-$\rho$/presence menu and exact fibres have different operation meanings. Original addressed growth, raw terminal Add/Read and the fresh-zero lifecycle here are not ports or inferred structure of that model. Its original obstructions remain in their original scopes. |

The relevant literature boundary is also explicit. Ilmavirta, Lassas, Lu, Oksanen and Ylinen, [*Quantum computing algorithms for inverse problems on graphs and an NP-complete inverse problem*, arXiv:2306.05253v2, Theorem 1 and §5.1](https://arxiv.org/html/2306.05253v2), supply boundary rigidity against all connected simple graphs of a fixed order and credit the classical tree-metric result when both competitors are trees. These are `literature-attested` suppliers for metric interpretation, not an active correspondence acquisition under (NLBAII.3)–(NLBAII.4). Frohme, [*Active Automata Learning with Adaptive Distinguishing Sequences*](https://arxiv.org/abs/1902.01139), supplies the established general setting of active adaptive discrimination; no automaton-learning complexity, unknown-state reset or selector result is imported into this source. Neither citation supplies the specific zero-marker assay or the newly earned joint raw/addressed service. The attribution is source-relative and makes no worldwide priority claim.

**Definition 23.2 (the asserted recovery domain).** The conclusions quantify the ideal digital installations of §17 and their supplied finite material. They do not establish physical realization, noisy calibration, source authenticity, grants from numerical data, recovery of an unretained old total word, all-cut inversion during unfinished calls, bounded lifetime memory or global resource optimality. Recovery from unknown nonzero fields requires further independently justified restrictions or observations, as Proposition 20.3 demonstrates. A general minimal relation structure for all possible internal-observer processes, or universal sufficiency and minimality of the two generators, is not a conclusion of this construction. Original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization and final-no-Ready obligations retain their exact original scopes. The attained gain is a paid initial/current correspondence and callable canonical four-expression service on an explicitly changed active installation, within the stated zero-cut recovery domain.

## 追加锚（本行以下为增补区）

## 24. Earned normalization and a fixed binary batch experiment

**Definition 24.1 (the source, the reports and the paid normalization).** Keep exactly Definitions 17.1–17.3, including their arbitrary authentic attachment bijection, complete raw roster, original root-bound growth dispatcher, unit-adjacency field, full-field Reset, current rights, serialization and backing. In particular an old generation word does not prescribe the attachment permutation. Quantify over every finite reachable entry $t$, every legal old word ending at it, and every attachment bijection $\lambda_0$. Write $a+c=L\ge3$ for its entry leaf counts, and $n=2L-1$ for its number of logical nodes. The required reports are the exact entry $(t,\lambda_0)$ and the exact actual advanced term, full field and current raw binding. An unchanged endpoint is not required.

First actually perform the all-$P$ traversal of [Atomic Generation Acquisition II, Definition 54.1 and Theorem 54.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md), abbreviated AAII. A branch refusal schedules its original left and right children; a promotion or wrong-type leaf reply finishes that visit. This uses only the original growth channel, so its proof applies to the restriction of the present richer service to that channel. It earns $t$ and the actual $\nu(t)$, where every original logical leaf has become $\beta$, without learning $\lambda_0$. There are $n$ real $P$ calls, $a$ successes, and no $S$ calls. The field remains zero by the persistent lift (NLBAII.3).

Enumerate the earned original logical leaves in left-to-right order as $p_1,\ldots,p_L$, retaining their original types $\eta_i\in\{\alpha,\beta\}$. The initial label belonging to leaf $i$ was bound to

$$
e_i=\begin{cases}p_i,&\eta_i=\alpha,\\p_iL,&\eta_i=\beta,\end{cases}
\qquad\text{and is now bound to }p_iL.
\tag{NLBAII.20}
$$

The last assertion follows from the actual promotion inheritance rule, not from a known permutation. Let $j_i=\lambda_0^{-1}(e_i)$ denote the still unknown initial label; this is a proof parameter, not a controller operand. Retain the entry code separately from its mutable current code. The traversal stack, the codes and their construction have their actual costs.

**Definition 24.2 (fixed masks and the complete batch schedule).** Choose a finite $q\times L$ binary table $B=(b_{ri})$, $q\ge1$, independently of the unknown permutation. It may be generated by a fixed finite rule from the earned term and known roster, or supplied as a finite public table whose construction and storage are charged. It supplies no raw-to-address map. Put

$$
h_i(r)=\sum_{s=1}^{r}b_{si},\quad h_i(0)=0,
\qquad k_i=h_i(q),\qquad K=\sum_{i=1}^{L}k_i.
\tag{NLBAII.21}
$$

After Definition 24.1 execute Reset, Add$(j,1)$ for every original label $1\le j\le L$, and Hold. For each $r=1,\ldots,q$ do the following finite operations, in the displayed order.

1. For each $i$ with $b_{ri}=1$, in increasing $i$ order, actually split at the logical address $p_iL^{h_i(r-1)}$. Consume the entire Growth reply and record the appended raw label, namely the maintained previous length plus one, with its new right-terminal address. Increase the maintained length.
2. Execute Hold and then Read$(j)$ for every original label $j=1,\ldots,L$, in increasing order. Retain $z_{rj}=1-\operatorname{Read}(j)$.
3. For precisely those original labels whose reading was zero, execute Add$(j,1)$, including in the last round.

No appended label is scanned or armed; no Tick occurs. After the rounds decode the finite observations as in Theorem 25.1, then actually Reset and Hold. All growth targets and all loops use the earned addresses, the public table, actual replies and maintained finite counters. The procedure neither schedules the new right $\alpha$ children nor asks an unknown subtree which operation to perform. Negative, partial and disabled calls retain §17's meanings; the promised acquisition uses only complete enabled calls.

## 25. Exact binding separation on the original fresh-zero lifecycle

**Theorem 25.1 (the fixed-mask iff, both maps and the actual endpoint).** For each fixed $t$ and $B$ of §24, the batch schedule admits a decoder returning the required exact entry and current raw maps for every attachment permutation if and only if the $L$ columns of $B$ are pairwise distinct. When they are distinct, one finite table-comparison decoder suffices, and the complete acquisition terminates for every promised entry. Its actual endpoint is $u_B$ with full field zero, where the original branches are retained and original leaf $i$ is replaced by

$$
B_{k_i},\qquad B_0=\beta,\qquad B_{s+1}=\langle B_s,\alpha\rangle.
\tag{NLBAII.22}
$$

For the decoded initial label $j_i$, the reports are exactly

$$
\lambda_0(j_i)=e_i,
\qquad \lambda_B(j_i)=p_iL^{k_i+1}.
\tag{NLBAII.23}
$$

If the $s$th split in cone $i$ occurs at $(r,i)$, its appended label is

$$
\ell(r,i)=L+\sum_{v<r}\sum_{m=1}^{L}b_{vm}+\sum_{m\le i}b_{rm},
\qquad \lambda_B(\ell(r,i))=p_iL^{s-1}R.
\tag{NLBAII.24}
$$

These inherited and appended assignments exhaust the actual current roster. The iff is restricted to the fixed schedule of Definition 24.2 and all its permitted transcript decoders, including use of its entry code and known appended records. It is not an impossibility theorem for other raw-port experiments.

Proof. At the start of a round the initial label $j_i$ is bound to the marker of the leftmost $\beta$ in its original leaf cone, at $p_iL^{h_i(r-1)+1}$, with value one. That cone is disjoint from every other original leaf cone. When selected, its target $p_iL^{h_i(r-1)}$ is therefore an enabled logical $\beta$, even after repeated earlier selections. The split retains its root and old marker as internal vertices, preserving their fields, and moves $j_i$ to the fresh zero marker one edge farther left. Its new right terminal receives the new label and zero field. With no Tick, growth in another cone and Add at another labelled terminal cannot change these values. Consequently the round's actual readings satisfy

$$
\operatorname{Read}_r(j_i)=1-b_{ri},\qquad z_{rj_i}=b_{ri}.
\tag{NLBAII.25}
$$

There is one zero original-label reading for each selected cone. Adding one at precisely these zeros restores all original-label terminals to one. Appended terminals stay zero. Starting with the actual initial arming proves this invariant by induction for all rounds; every source cell remains binary, including old cells that have become internal. This establishes the joint response law on the actual specimen, without an internal field read or a supplied decoder.

For distinct columns, compare the observed finite column $(z_{rj})_{r=1}^{q}$ with the $L$ public columns. There is exactly one match, and (NLBAII.25) says that it is the actual original leaf carrying $j$. This finite comparison earns (NLBAII.23), including the entry distinction between an $\alpha$ vertex and a $\beta$ marker. The old-label marker moves once per selection. On its $s$th selection the new right terminal is $p_iL^{s-1}R$; later selected targets lie strictly in its left cone and never act on this appended terminal. The fixed order of successful splits gives exactly the preceding-count formula (NLBAII.24). Distinct original leaf cones do not intersect, all appended indices are different, and $B_{k_i}$ has exactly one inherited terminal and $k_i$ appended terminals. Thus these formulas form a bijection onto all $L+K$ current terminals. Induction on the same splits gives (NLBAII.22). Final Reset zeros every internal and terminal cell, and Hold preserves this actual endpoint while its retained records are constructed.

For necessity suppose columns $i$ and $i'$ coincide. Attach two different original labels to these two original terminals and swap only those labels in a second permitted installation of the same $t$. Normalization has the same guard transcript in both. Every round selects these cones together or leaves both alone. Equation (NLBAII.25) therefore gives the same literal reading at each original label in both installations, and the resulting rearming commands are identical. All addressed operations, Growth words, roster lengths, appended-label records, acknowledgements and final Reset/Hold outputs are also identical. This is an induction on exposed outputs and round boundaries; it does not assert that unobserved fields between individual rearming Adds have identical material coordinates. The decoder receives the same whole transcript, but the required entry maps and inherited current maps differ. No such decoder can be correct for both.

The hidden distinction also affects the complete raw continuation task. From either final zero cut arm the original labels $1,\ldots,L$, split the final leftmost $\beta$ in cone $i$, and Read one of the swapped labels. The fresh-zero rule makes that reading zero in the installation where this label belongs to $i$ and one in the other. Thus duplicate columns merge different required raw behaviors, rather than merely different private encodings. Sufficiency and necessity follow. All loops are finite, all called addresses are earned and enabled, and finite backing supplies the complete calls; no size cap is used for stopping. $\square$

## 26. Binary incidence and a same-run acquisition account

**Theorem 26.1 (attained binary profile).** For a separating table $B$, count the normalization and every operation of Definition 24.2, including its last rearming. Let $\mathcal L(t)$ be all entry logical positions, including branches, and set

$$
D=\sum_{p\in\mathcal L(t)}|p|,\qquad
D_\alpha=\sum_{i:\eta_i=\alpha}|p_i|,\qquad
W_B=\sum_{i=1}^{L}\left(k_i|p_i|+\frac{k_i(k_i-1)}2\right),
\qquad M=n+K.
\tag{NLBAII.26}
$$

On this single run the source and menu counts are

$$
\begin{aligned}
N_0&=2L+c-1,&N_{\nu}&=3L-1,&N_B&=3L+2K-1,\\
P\text{ calls}&=n,&P\text{ successes}&=a,&S\text{ calls/successes}&=K,\\
\text{refusals}&=L-1+c,&\text{fresh vertices}&=a+2K,&\text{final terminals}&=L+K,\\
\mathrm{Reset}&=2,&\mathrm{Add}&=L+K,&\mathrm{Read}&=Lq,\\
\mathrm{Tick}&=0,&\mathrm{Hold}&=q+2.&
\end{aligned}
\tag{NLBAII.27}
$$

All acquisition Add scalars and scalar field replies are zero or one. Raw labels, addresses and counters retain their actual widths. Addressed request and reply payloads, in §17's framing, are respectively

$$
2(D+W_B)+4M,\qquad 2(D_\alpha+W_B)+5M.
\tag{NLBAII.28}
$$

There are $L+K+q+4$ fixed field acknowledgements, $Lq$ scalar replies and $M$ complete addressed replies. Each call additionally incurs its actual framing, transmission, End, acknowledgement where required, return and cleanup. Direct source structural assignments are $4a+8K$; fresh active-field zero writes and changed raw-binding assignments are each $a+2K$, with $K$ roster-length increments. The two source Reset sweeps write $N_{\nu}+N_B$ cells. These coordinates do not include the separately paid receiver copies and record construction.

Proof. Normalization retains $L$ logical leaves, all $\beta$, so its material order is $n+L=3L-1$. Each later split adds two material vertices and one terminal. It is successful by Theorem 25.1; normalization has $L-1$ branch and $c$ wrong-type refusals. Initial arming uses $L$ Adds, and the $K$ selected incidences give exactly $K$ scanned zeros and hence $K$ rearming Adds. There is one initial Hold, one per round, and one final Hold. Reset, Add and Hold give $2+(L+K)+(q+2)$ fixed acknowledgements. No scalar return from a Tick has been charged: this installation's Tick returns a fixed acknowledgement, and no acquisition Tick is issued.

The $s$th split of cone $i$ has depth $|p_i|+s-1$. Summing gives $W_B$. Each request has $2|p|+4$ bits, each success reply $2|p|+5$, and each refusal five. Successful promotions have depth sum $D_\alpha$, proving (NLBAII.28). The four/eight structural assignments, one/two fresh field cells and one/two changed bindings per promotion/split are the original templates of §§17 and 21. Since the first Reset occurs after normalization, its size is $N_{\nu}$, not $N_0$. This proves every displayed coordinate together. $\square$

**Theorem 26.2 (the class-scoped Read/incidence frontier).** Among Definition 24.2's separating $q$-round tables, such tables exist precisely when $2^q\ge L$. For each feasible $q$, let $h$ be least with $\sum_{j=0}^{h}\binom qj\ge L$, and put $C_{<h}=\sum_{j=0}^{h-1}\binom qj$, with empty sums zero. The exact least attainable split count in this class is

$$
K_{\min}(q,L)=\sum_{j=0}^{h-1}j\binom qj+h(L-C_{<h}).
\tag{NLBAII.29}
$$

Thus the least Read count in this fixed full-original-roster binary class is $L\lceil\log_2 L\rceil$. At a fixed feasible $q$, (NLBAII.27) with $K=K_{\min}(q,L)$ simultaneously attains that class's least split count, fresh-source count and final material order for those $q$ scans. This does not optimize address depths, retained masks, total traffic or acquisition over other experiment classes.

Proof. By Theorem 25.1, this source's binding problem in this class is exactly selection of $L$ different binary columns. For the classical separating-system context see Katona, [*On separating systems of a finite set*, Journal of Combinatorial Theory 1, 174–194](https://doi.org/10.1016/S0021-9800(66)80024-8). The elementary counting and weight-selection arguments below are not claimed as new combinatorial results or as a quotation of a particular theorem of that paper. There are $2^q$ words, so injectivity requires and permits $L\le2^q$. To minimize the sum of their weights, exchange any chosen heavier word with an omitted lighter one. The replacement preserves distinctness and strictly reduces the integer sum. Repeating these finite exchanges leaves every weight layer below $h$ present and exactly $L-C_{<h}$ words of weight $h$. Their weight is (NLBAII.29). Conversely selecting exactly those words attains it. Ties can be resolved lexicographically; finite weight-and-word enumeration constructs the table using only $q,L$, with its enumeration work charged.

For a simple uniform construction take $q=\lceil\log_2 L\rceil$ and the padded binary words for $0,\ldots,L-1$. Its $K=\sum_{i=0}^{L-1}\operatorname{popcount}(i)\le Lq$ is an attained account, and need not minimize incidence at this $q$. To attain (NLBAII.29), use the lightest-word construction instead. Theorem 26.1 turns these known code facts into actual split, Add, field-width and material costs on this installation. Since the class scans all $L$ original labels each round, minimizing $q$ gives its stated Read minimum. No lower bound for a controller that changes this schedule, signal alphabet, scan pattern or field experiment has been used. $\square$

**Definition 26.3 (local work, retained material and preparation).** The account includes the actual old preparation and subsequent retained use, with the encoding and charge convention of Definition 21.1. The old source word has $c$ promotions and $L-1$ splits, $3+4c+8(L-1)$ located structural assignments, and $N_0$ active-field initializations. Its actual address traffic, navigation, allocated root, original roster attachment, references, grants, field/Tick backing, producer control and any retained journal are additional charges. No old journal is supplied to this acquisition.

An attained receiver layout stores the explicit $qL$ mask bits and $qL$ observed bits, the entry and current constructor records, the immutable entry table, the full current raw table, the current material graph and full zero vector, finite counters, traversal/address workspace, and its actual program, parser, I/O, reference, grants and backing. Two-bit constructor payloads for the entry and current terms have together $4n+4K$ bits; their links, indices and ownership material are extra. Indexed graph and table records take $O(N_B\log(N_B+1))$ numerical bits, and literal copied-address workspace can conservatively take $O(N_B^2)$ bits. Counters also pay their actual widths, including $\log(q+1)$ when empty mask rows make $q$ large. Arbitrary reference encodings are not bounded by these numerical estimates.

After mask construction, direct comparison of each observed column with each public column uses at most $O(qL^2)$ bit comparisons. Reading mask rows and scheduling the rounds uses $O(qL)$ further indexed operations. Finite graph/table scans, copied addresses and current-tree construction can conservatively use a further $O(N_B^2)$ indexed record operations and address-symbol copies. Thus $O(qL^2+N_B^2)$ suffices for these local operations together. These are attained operation counts, in addition to the chosen mask generator's work, literal frame coding/transport and all actual operand widths. Initial raw labels have $O(\log(L+1))$ packet width; appended-label counters and stored indices pay their own lengths. The finite generating rule, decoder and scans are computations paid by the observer, not source primitives. Exporting an onset table or causal record adds its computation, output and retained-copy costs; no wave observations occur in this no-Tick experiment.

## 27. A paid integer-age experiment with one final original-roster scan

**Definition 27.1 (unit-input age schedule).** Use the same actual normalization of Definition 24.1, then Reset, Add$(j,1)$ for every original label $j\le L$, and Hold. For $i=1,\ldots,L-1$, split once at the earned logical address $p_i$, then Add$(j,1)$ for all original $j\le L$, and Hold. Do not act on $p_L$, scan between stages, arm appended labels, or issue Tick. After all stages Read each original label once, decode as below, then Reset and Hold. All unit inputs and the larger integer values are actual field operations and literal replies, not an unobserved clock.

**Theorem 27.2 (age binding, endpoint and simultaneous resources).** The schedule terminates and earns the exact entry map and complete current raw map for every §17 attachment. At its sole scan,

$$
\operatorname{Read}(j_i)=\begin{cases}L-i,&i<L,\\L,&i=L.\end{cases}
\tag{NLBAII.30}
$$

Its endpoint replaces original leaves $1,\ldots,L-1$ by $B_1$ and the last by $B_0$. The inherited labels bind $p_iLL$ for $i<L$ and $p_LL$ for $i=L$; appended label $L+i$ binds $p_iR$. Here $p_LL$ means the address $p_L$ followed by one letter $L$. The final whole field is zero. On this same acquisition,

$$
\begin{aligned}
P\text{ calls}&=2L-1,&S\text{ calls/successes}&=L-1,\\
\mathrm{Reset}&=2,&\mathrm{Add}&=L^2,&\mathrm{Read}&=L,\\
\mathrm{Tick}&=0,&\mathrm{Hold}&=L+1,\\
\text{fresh vertices}&=a+2(L-1),&\text{final terminals}&=2L-1,&N_{\rm age}&=5L-3.
\end{aligned}
\tag{NLBAII.31}
$$

Every acquisition field cell is an integer between zero and $L$. Scalar replies therefore pay $O(\log(L+1))$ bits. There are $L^2+L+3$ fixed field acknowledgements and $L$ scalar replies, besides the $3L-2$ complete addressed replies and all call completion costs. Formula (NLBAII.28) applies with $k_i=1$ for $i<L$, $k_L=0$, and $M=3L-2$. Structural, fresh-zero, binding and Reset-write counts are those of Theorem 26.1 with $K=L-1$, while field additions are the $L^2$ actual units here.

Proof. Before its split at stage $i$, the original label in cone $i$ has received its initial unit and the $i-1$ earlier stage units. Its split moves this label to fresh zero. From that stage through stage $L-1$ it receives exactly $L-i$ further units, including stage $i$ itself. The last label is never moved and receives the initial unit and all $L-1$ stage units. This proves (NLBAII.30); its $L$ values are distinct. A finite comparison with this known list decodes $i$ and hence the entry address $e_i$ of (NLBAII.20). Distinct cones are each split at most once, so the inheritance and append formulas follow directly from (NLBAII.4) and exhaust the $2L-1$ current terminals.

There are $L$ initial Adds and $L(L-1)$ stage Adds, one final scan, $L-1$ successful splits, and the displayed Holds and Resets. No Add targets an internal or appended cell. An old cell keeps the finite value it had when it became internal; an inherited terminal has at most the number of remaining stage inputs, and the last terminal has $L$. Thus the entire field has the stated integer bound before final Reset, not just the scanned terminals. Counting source vertices, framing and acknowledgements as in Theorem 26.1 proves the remaining assertions. Column decoding is replaced here by finite integer comparisons; its work, growing numerical widths, entry archive, current records, references and retained use remain paid. $\square$

## 28. Earned entrance to complete continuation and the existing view inverse

**Theorem 28.1 (raw and canonical continuation at either acquired endpoint).** At the actual endpoint of Theorem 25.1 or Theorem 27.2, retain the earned current term $u$, its material graph, its whole zero field vector, the complete current raw bijection and length, the separate entry report, and the actual bound service reference, current grants and backing. These establish invariant (NLBAII.8) at this actual $u$. Therefore the finite procedures of Theorems 19.2–19.4 give the complete raw and canonical menus and successors for every finite common adaptive continuation, at arbitrary subsequent rational fields. This conclusion uses the new endpoint initialization, without assuming $u=\rho(t)$ or an initially known raw decoder.

Proof. Theorem 25.1 or 27.2 gives the actual original-root constructor code and an exhaustive bijection to actual material terminals. Its address realization extends to every vertex by the definition of $C(u)$, preserving each edge. Actual final Reset gives equality of every field coordinate with the retained zero vector. Hence the graph/field/binding invariant of Definition 19.1 holds. The proof of Theorem 19.2 requires precisely this invariant; its one-step argument does not require the special initialization $\rho(t)$ used in its earlier acquisition.

For clarity the complete successor correspondence at this earned entrance is as follows. At a $P$ or $S$ request the retained logical code gives the actual absent, branch, wrong-type or success case. A successful $P_p$ keeps old coordinates, appends zero at $pL$, replaces the $\alpha$ code by $\beta$, and transfers the unique binding at $p$ to $pL$. A successful $S_p$ retains $p,pL$, appends zero coordinates $pLL,pR$, replaces $\beta$ by its actual branch, transfers the unique binding at $pL$ to $pLL$, and binds the new last label to $pR$. The actual installation supplies the corresponding fresh grants. Every refusal has its exact reason and identity successor. Reset zeros every coordinate, Add$(j,r)$ changes the coordinate selected by the earned table by $r$, Read$(j)$ returns that literal coordinate, and Hold preserves the state. The edge-preserving realization intertwines adjacency, so Tick updates the whole vector by $A_u$ and has this installation's fixed acknowledgement. This includes all internal cells, even when the old fields are nonzero.

Out-of-range integers return RangeRefusal without change; malformed complete frames return BadFrame without change. Proper incomplete frames remain pending with their finite retained input and no completed reply. Actual use forwards the call, consumes the whole reply and return, then commits the matching record update before the next settled cut. The same binding, rights and serialized parser assumptions give the stated enabledness. Induction on complete requests proves every finite common adaptive continuation; finite extensions of pending prefixes follow the same fixed grammar. This does not claim an inverse for arbitrary busy states.

For canonical use enumerate the current ordered material terminals $\tau_u(k)$ from $u$ and scan the earned raw table to compute $\pi_u(k)=\lambda_u^{-1}(\tau_u(k))$. Forward ordinal Add/Read to that actual label and forward their complete replies; update the table after every growth. A promotion replaces its one canonical terminal by the new marker; a split replaces it by its consecutive left marker and right terminal. Thus the maintained adapter has exactly the original ordered replacement rule. Negative and incomplete cases have the same handling as Definition 19.3. This proves the hypotheses and full conclusion of the existing canonical service on this same advanced specimen. The finite lookups, rewrites, calls, copied records and future growth/arithmetic are charged as used; code equality produces no reference or authority. $\square$

**Theorem 28.2 (application on the exact canonical whole-zero image).** Fix this actual canonical binding and current rights. At settled synchronized cuts reached from either acquisition, restrict to reachable $u$ with at least three logical leaves and zero on every material field cell. On this domain use exactly Definition 20.1's independent data meanings:

| Expression | Content |
| --- | --- |
| Space | Actual unrooted unit material tree, complete canonical terminal order and present zero field, modulo order-preserving isomorphism |
| Time | Actual labelled causal birth/lifecycle order $E(u)$ of successful original $P/S$ events |
| Boundary | Canonical terminal impulse-onset table of the actual unit-adjacency law and present terminal zero readings |
| Memory | Retained recursive current code, full zero vector and canonical terminal table at the fixed callable entry |

Each data expression recovers the same $(u,0)$ and hence the other three on their actual joint image. All routes agree and have the canonical continuation kernel. Their recovered dynamics agree for every admitted operation or finite composite whose initial and final cuts are in this domain. The full raw/canonical predictor of Theorem 28.1 also covers the intervening nonzero fields.

Proof. This is Proposition 20.2 with its entrance earned by Theorem 28.1. Its metric, root and causal inverses remain suppliers: NLBA Lemma 2.1 identifies first nonzero impulse arrival with unit distance; NLBA Lemma 2.3 recovers all material subdivision vertices from the complete leaf metric; NLBA Theorem 11.1 recovers the original root and ordered term. The same original-domain root and coordinate rigidity is supplied by `NativeMaterialRootRecognition.original_rigidity`, and finite recognition by its `effective_inverse`, under exactly no-left-$\alpha$ birth typing, complete linear terminal order and at least three leaves. Those results start with a finite graph presentation and order; they do not acquire a raw binding. Here the graph, original address meaning and order are earned by Theorem 28.1.

AA Theorem 17.2 gives the mutual correspondence of $u$ with its actual labelled causal event order: current branches supply the $S_p$ events, and positions born $\alpha$ that are no longer $\alpha$ supply their $P_p$ events, with their local and creation precedences. Memory parses that same $u$. The whole field is zero by the domain, so no hidden field component remains to be decoded. Conversely $u$ computes these finite data. All supplier maps therefore factor through the same $(u,0)$, proving the inverse identities and route agreement. Equal terms and zero fields give identical full canonical continuation by Theorem 28.1. Unequal terms give either different exposed roster lengths or different canonical leaf metrics by the supplied inverse, distinguished by a finite actual Reset/Add/Tick/Read experiment. Thus the task kernels agree.

Every final view after an actual returning-to-zero composite is the supplier observation of its same ending term and zero field, by the maintained full vector and growth correspondence. This proves dynamics compatibility even when intermediate fields leave the image. An onset table can be computed from the earned graph, but this batch or age acquisition has not sampled it by waves: calculation/export and actual observed provenance are different claims and costs. Time is causal order, not a retained serialization of successful or field-control commands. The initial raw permutation, entry report, actual grants and private record bytes remain additional retained material outside these canonical data inverses, exactly as in Proposition 20.4. $\square$

## 29. Comparison, supplier correspondence and exact remaining boundaries

**Definition 29.1 (alternative runs on the same attachment).** The following profiles include the actual acquisition calls and final zeroing on the original installation. Each row uses its own actual trajectory and endpoint; $a,c,L$ always refer to the common entry. The one-edit row is precisely Definitions 18.1–18.3, including last rearming. The propagation row is exactly Proposition 22.1's initial trial and trials after the first $L-1$ edits, with $u_s,N_s,D_s$ its own intermediate terms, material sizes and anchor eccentricities. Put

$$
R_{\rm mark}=L^2+\sum_{r:\eta_r=\beta}(L-r),\quad
K_{\rm prop}=\sum_{s=0}^{L-1}D_s,\quad
R_{\rm prop}=\sum_{s=0}^{L-1}\sum_{j\ne1}d_s(1,j).
\tag{NLBAII.32}
$$

| Acquisition | Successful $P,S$ | Reset, Add, Read, Tick, Hold | Final material order and endpoint |
| --- | --- | --- | --- |
| Published one-edit scan | $a,c$ | $2,\ 2L+c,\ R_{\rm mark},\ 0,\ L+2$ | $3L+2c-1$, $\rho(t)$ |
| Fixed binary batch | $a,K$ | $2,\ L+K,\ Lq,\ 0,\ q+2$ | $3L+2K-1$, $u_B$ |
| Integer-age schedule | $a,L-1$ | $2,\ L^2,\ L,\ 0,\ L+1$ | $5L-3$, the endpoint of Theorem 27.2 |
| Published anchor propagation | $a,c$ | $L+1,\ L,\ R_{\rm prop},\ K_{\rm prop},\ K_{\rm prop}+L+1$ | $3L+2c-1$, $\rho(t)$ |

All rows have $2L-1$ attempted $P$ calls. Their attempted $S$ calls are their displayed successful split counts. Common old preparation and attachment costs remain additional, and every row pays its own later calls, source work, masks/decoding or wave processing, widths and retained records. Propagation's direct field additions are $2\sum_s D_s(N_s-1)+L$; its field values are actual walk counts. Binary batch and one-edit marking have binary fields; age uses the integers of Theorem 27.2. The wave row's small Add count does not remove its Ticks or adjacency arithmetic.

**Theorem 29.2 (the precise resource gain and its limits).** The minimal-row binary batch has $L\lceil\log_2 L\rceil<L^2\le R_{\rm mark}$ Reads for every $L\ge3$. The age schedule has $L$ Reads and $L^2$ actual unit Adds. These are actual binding acquisitions on the supplied lifecycle, with the full continuations of §28. Their statements supply no universal Read optimum, fixed-$\rho(t)$ endpoint optimum or total-resource ranking of the alternatives.

Proof. The binary count follows from Theorems 26.1–26.2. The elementary inequality $2^{L-1}\ge L$ for $L\ge3$ gives $\lceil\log_2 L\rceil\le L-1<L$. The published scan count is at least $L^2$. Theorem 27.2 proves the age count and its paid wider signals. The endpoints and other coordinates are those of Definition 29.1, not independent choices to be combined. In particular the binary row's $q$ bound applies to its full-roster binary schedule; the age row attains a smaller Read count by a different signal and Add budget. Split incidences affect source size and address depths through (NLBAII.26)–(NLBAII.28), and different endpoints need not meet a caller's fixed-endpoint requirement. The proved coordinate comparisons consequently do not imply the asserted larger optimizations. Keeping the existing one-edit or propagation procedure is sufficient when its own endpoint and prices meet the task. $\square$

**Definition 29.3 (mathematical suppliers and residual domain).** The source-relative `repo-derived` additions are the actual batched and integer-age entrances to the unknown raw binding, their exact maps/endpoints and their same-run tradeoffs. Classical pair separation, binary counting and lightest-word selection are consumed within Theorem 26.2; they are not new abstract coding results. The original raw lifecycle, full predictive invariant, canonical adapter and whole-zero view inverse are precisely §§17, 19–20. The normalization, framing and source assignments are AAII §§53–54 and AA §§20–22. The actual causal reconstruction is AA §17. The material and leaf-distance inverses are NLBA §§2, 11–13, with the original-root recognition supplier and its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.scribe.cs) giving the same original-domain graph/root conditions. `NativeFullSourceProducer` supplies a source-blind finite stack traversal with stronger literal Native reads; `NativeUniformTree` supplies navigation and substitution on given codes. Their private traversal/navigation proofs and owning Scribes do not supply unknown raw-label association or new grants. Pinned mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, `Algebra/Free.lean`, supplies the ordered free-magma syntax and its lift, without an acquisition port.

The prepared nonzero passive image already treated by [NLBA §§19–21](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md) and consumed by [Quantum Principles, Application 33.1](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md) has an actual unit-source preparation, passive Tick age and consecutive samples at the fixed first terminal. It remains a different valid inverse domain; no nonzero-field impossibility is inferred here. The [private-randomization quadratic-clock source](FIB_UNCALIBRATED_QUADRATIC_CLOCK_PRIVATE_RANDOMIZATION.md) has fixed complete real report worlds, independent seeds and three chronological reports, as specified in its Definitions 1.1–1.2 and Theorems 7.2, 7.4–7.5. It provides neither this raw lifecycle nor an unknown-binding decoder. The published AAII §60 history-content floor concerns the original initialized seven-request history task, and [Unknown Field Native Startup §§24–26](RECURSIVE_RELATIONAL_OBSERVATION_UNKNOWN_FIELD_NATIVE_STARTUP.md) concern arbitrary small signed entries on native Jacobi paths without an order cap. Their original scopes and proofs are not replaced by these deterministic tree-field experiments. No unproved operation/output/resource correspondence from those distinct sources is used.

Attribution of these specific operational deductions is relative to these suppliers; no worldwide priority or new general inverse principle is asserted. Fresh-zero inheritance, complete roster and authentic source binding, exact field operations, held serialization, current authority and sufficient finite backing are model hypotheses. The experiment earns the unknown numerical association conditional on them; its transcript does not certify those premises or manufacture callable access. At the acquired cuts the full retained vector comes from actual full-field Reset. Terminal zeros alone do not establish this domain: Proposition 20.3's zero field and internal-neighbour unit field have the same terminal zeros and different next Tick/Read behavior. Full raw continuation at arbitrary fields in Theorem 28.1 does not extend the canonical inverse of Theorem 28.2 to arbitrary fields or journals.

The separately paid entry archive is not silently included in every current view. Old total successful serialization, erased field-control records, private raw permutations in canonical views, arbitrary busy-state inversion, noisy calibration, bounded lifetime memory, physical realization and a universal minimal common relation structure remain outside the conclusions. Original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization and final-no-Ready obligations retain their exact scopes. These acquisitions do not settle them by changing an endpoint, port or initialization.

## 追加锚（本行以下为增补区）

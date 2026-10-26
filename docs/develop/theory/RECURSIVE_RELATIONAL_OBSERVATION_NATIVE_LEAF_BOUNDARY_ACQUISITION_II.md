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

## 30. A binary word in the native branching field

**Definition 30.1 (the binary origin and its actual image).** Fix one actually earned current original term $u\in\mathcal D$, its unit material tree $C(u)$, its complete canonical terminal order, and its complete actual raw correspondence. Write $N=|V(u)|$, let $b\ge4$ be its number of material leaves, and put $I=N-b$. The law is exactly the native symmetric zero-diagonal unit adjacency matrix $A$, not a rescaled contraction. Retain the authentic bound reference, current rights, serialization and sufficient finite backing of §17. Whole-field zero must have been established by actual operations on this specimen. Actually Add one at the first canonical terminal $e$, using its earned raw label, and Hold. This is the new origin, with actual field $x_\varnothing=e$.

For $d\in\{0,1\}$, the binary operation $\operatorname{Next}(d)$ performs, in order, actual Tick, Add$(e,d)$, Hold, Read$(e)$. Add$(e,0)$ is an actual call. Its output is the complete ordered tuple of the three acknowledgements and the literal Read reply. A malformed complete wrapper packet returns BadFrame without an inner call; a proper incomplete packet remains pending without a completed operation. Valid wrapper calls are serialized through their completed retained updates. Define, for the actual successive binary inputs $w=d_0\cdots d_{m-1}$,

$$
x_w=A^m e+\sum_{i=0}^{m-1}d_iA^{m-1-i}e,
\qquad x_{wd}=Ax_w+de.
\tag{NLBAII.33}
$$

The inverse image in this section consists of these fields, on this fixed earned graph and new origin. Between the origin and such a cut there is no growth, Reset, other rational Add or unrequested Tick. Reads and Holds preserve the field. The old source generation and old erased field history are not part of $w$.

**Theorem 30.2 (native full-field binary inverse, including length).** For every source and origin of Definition 30.1, the map

$$
\{0,1\}^{*}\longrightarrow\mathbb Z^{V(u)},\qquad w\longmapsto x_w
\tag{NLBAII.34}
$$

is injective. Given the earned finite graph and the full present field promised to lie in this image, a finite procedure recovers the unique word and its length. It needs no retained copy of the old binary word or its length. This is an inverse on the promised image, with no asserted efficient or total off-image recognizer.

Proof. The material tree has maximum degree three and exactly $b$ graph leaves. If $n_j$ counts degree-$j$ vertices, the tree identity gives $n_3=b-2\ge2$. Choose distinct degree-three vertices and their joining path. Give every path vertex weight two, each of the four off-path neighbours at its endpoints weight one, and every other vertex weight zero; call this integral vector $g$. The four neighbours are distinct and outside the path: a failure of either property gives a cycle. At each path vertex the sum of neighbouring weights is at least four, and at each chosen off-path neighbour it is at least two. Thus $Ag\ge2g$ coordinatewise, including the zero coordinates.

Set $h=(\operatorname{Id}+A)^{N-1}g$. Every vertex has a path of length at most $N-1$ to a positive coordinate of $g$; the identity terms pad that path. Consequently $h$ is integral and strictly positive. Commutation and nonnegative coefficients give $Ah\ge2h$. For $s_j=h^{\mathsf T}A^je$, symmetry and positivity imply

$$
s_0>0,\qquad s_{j+1}\ge2s_j,\qquad
s_D>\sum_{j=0}^{D-1}s_j\quad(D\ge1).
\tag{NLBAII.35}
$$

For the last inequality, $s_j\le2^{-(D-j)}s_D$, whose finite geometric sum is strictly smaller than $s_D$. Hence if $P(z)=\sum_{j=0}^D a_jz^j$ is nonzero with all $a_j\in\{-1,0,1\}$ and $a_D\ne0$, the absolute value of the leading contribution to $h^{\mathsf T}P(A)e$ exceeds the sum of the absolute values of all the others. For $D=0$ positivity gives the same nonvanishing. Therefore $P(A)e\ne0$.

The field of a word is the value at $A$ and $e$ of the monic polynomial $z^m+\sum_{i<m}d_i z^{m-1-i}$. Distinct words, including words of different lengths and the empty word, give distinct such polynomials; their difference has coefficients in $\{-1,0,1\}$. Nonvanishing proves (NLBAII.34). Enumerate finite binary words by increasing length and then lexicographically, calculate each finite field exactly, and compare coordinates. On the promised image the unique match is reached after finitely many comparisons and gives both outputs. This procedure uses neither a scalar port for $h^{\mathsf T}x$ nor knowledge of the previous word. The weights are a proof and computation device on the earned graph. $\square$

The source-specific content is the applicability of leading-term separation to this actual native material adjacency, for every $b\ge4$, without changing its edge weights or Tick. Positional leading-term separation itself is not a new general numeration principle. Four leaves are a sufficient condition here, not a necessity or a minimality claim.

## 31. Literal boundary sampling with a genuinely advanced endpoint

**Definition 31.1 (the earned leaf reconstruction coefficients).** Enumerate the $b$ material leaves in canonical order and let $J:\mathbb Q^b\to\mathbb Q^N$ be their coordinate injection. Use the all-leaf forcing of [NLBA, Lemma 3.2](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md): mark all leaves; a marked vertex with exactly one unmarked neighbour forces that neighbour. This colours the whole tree in precisely $I$ individual forces. Indeed, if a nonempty unmarked set $U$ remained at a stalled cut, the forest consisting of $U$, its marked neighbours, and the edges with at least one endpoint in $U$ would have minimum degree at least two. An unmarked vertex was not an initial leaf and has degree at least two; a marked neighbour has at least two neighbours in $U$ by stalling. A nonempty finite forest cannot have that minimum degree.

Attach to the initial leaf $\ell_j$ the constant vector polynomial $p_{\ell_j}(z)=e_j$ in $\mathbb Z[z]^b$. At a force $v\to w$, all other neighbours of $v$ are marked; define

$$
p_w(z)=z p_v(z)-\sum_{v'\sim v,\ v'\ne w}p_{v'}(z).
\tag{NLBAII.36}
$$

For every vertex, write $p_v(z)=\sum_{r=0}^I z^rp_{v,r}$, filling unused degrees with zeros. Induction on the force order, using $Ae_v=\sum_{v'\sim v}e_{v'}$, proves

$$
\sum_{r=0}^I A^rJp_{v,r}=e_v.
\tag{NLBAII.37}
$$

Degree is at most the number of forces so far, hence at most $I$. With block ordering by $r$, let $C$ be the $b(I+1)$ by $N$ matrix whose $v$th column is the stack of $p_{v,r}$, and put

$$
K=[J,AJ,\ldots,A^IJ].\qquad KC=\operatorname{Id}_N.
\tag{NLBAII.38}
$$

This is the known leaf-forcing argument specialized to the already earned unit graph; it is not an additional identification theorem for unknown edge laws. The infection mechanism also occurs in Burgarth and Maruyama, *Indirect Hamiltonian identification through a small gateway*, New J. Phys. 11 (2009) 103019, [arXiv:0903.0612v1, §II](https://arxiv.org/abs/0903.0612v1), where a known graph and a gateway infecting its vertices supply different quantum-identification hypotheses. Only the combinatorial forcing mechanism is used here; no quantum experiment or its permissions are imported.

**Definition 31.2 (actual Sample).** At a binary-image cut with actual field $x_w$, Hold and Read every canonical leaf in order, obtaining $y_0$. For $r=1,\ldots,I$, actually Tick, Add$(e,0)$, Hold, and Read every canonical leaf, obtaining $y_r$. Return the literal ordered window, every complete inner reply, and the decoded pre-sampling word and length. Inner replies may be streamed; any retained or returned copies are paid storage. The decoding calculation uses (NLBAII.38) and Theorem 30.2. It does not replace any of these actual calls. The procedure is admitted under the binary-origin promise; it is not a total inverse for arbitrary fields.

**Theorem 31.3 (observation, inverse and actual successor).** Sample terminates on every promised binary-image cut and has the following simultaneous properties:

$$
y_r=J^{\mathsf T}A^rx_w\quad(0\le r\le I),\qquad
x_w=C^{\mathsf T}\begin{pmatrix}y_0\\ \vdots\\y_I\end{pmatrix},
\qquad x_{\rm end}=A^Ix_w=x_{w0^I}.
\tag{NLBAII.39}
$$

It installs $x_{w0^I}$, rather than $x_w$, as the retained current predictive vector. Its exact inner counts are $I$ Ticks, $I$ Adds, $I+1$ Holds and $b(I+1)$ Reads. All Add operands are zero. It recovers the pre-sampling binary word even when a previous predictive vector and binary word have been discarded, provided the earned graph, raw map, callable reference, rights and origin promise persist.

Proof. Induct on the actual Tick calls: the zero Adds, Holds and Reads do not change the field, so the $r$th sampled field is exactly $A^rx_w$. Symmetry of $A$ gives $K^{\mathsf T}x_w=(y_0,\ldots,y_I)^{\mathsf T}$. Transposing $KC=\operatorname{Id}$ proves the reconstruction formula. Theorem 30.2 then recovers precisely $w$. Each intervening Tick followed by an actual zero Add is a binary zero step, so the final field is $x_{w0^I}$. Multiplying the reconstructed vector by $A$ exactly $I$ times installs this actual endpoint. Counting the specified finite calls gives the bill. No inverse of $A$ is used: $A$ may be singular. On this special word image, $A^Ix_w=A^Ix_{w'}$ would imply $w0^I=w'0^I$ by Theorem 30.2, and therefore $w=w'$, but this restricted injectivity is not an inverse on arbitrary fields. $\square$

## 32. Independently defined sampled Space, Time, Boundary and Memory

**Definition 32.1 (sampled domain and common callable context).** Fix the origin and retained earned context of Definition 30.1. Consider completed Sample cuts, with all retained updates finished and no pending frame. Write $v=w0^I$ for the actual binary chain at such a cut, including the zero steps actually executed inside that last Sample. Define four numerical expressions by their different source meanings:

| Expression | Content at this sampled cut |
| --- | --- |
| Space | The unrooted unit material tree, complete canonical linear leaf order, and actual present field $x_v$, modulo order-preserving graph isomorphism |
| Time | The actual labelled successful original-$P/S$ causal birth/lifecycle order $E(u)$ and the actual binary input chain $v$ since the new origin |
| Boundary | The canonical terminal impulse-onset table of the actual unit law, with diagonal zero, and the literal trailing window $(y_0,\ldots,y_I)$ received by the last Sample |
| Memory | The retained current recursive original term, full current predictive vector $x_v$, and canonical ordinal-to-material-terminal table |

The onset table has its independent counterfactual response-law meaning from NLBA §§2 and 13: a unit impulse is first nonzero at graph distance. It is computable from the earned graph and is not represented as a literally performed impulse experiment. The appended window, in contrast, consists of actual replies on this very specimen. Computing, exporting or storing either part is paid. Space carries the actual present field, not a pre-sampling copy. Time includes sampling zeros but excludes Reads, Holds, refusals, elapsed duration, old total serializations and erased old field-control records. Its generation component is the actual causal order with AA's original event labels, not a selected replay. Memory contains neither a binary journal nor private raw labels.

The actual reference, rights, complete private raw map, parser, backing and optional entry archive are separately retained common context. The inverse statements below do not reconstruct their bytes or create authority. They concern the joint image of these four specified expressions at the same sampled cuts, not every possible nonzero field or every operation log.

**Theorem 32.2 (four actual-image inverses and agreement).** On this sampled domain each expression effectively recovers the other three. Every route agrees. Each expression determines the complete current native canonical predictor and its entire settled successors under every finite common adaptive continuation. These recoveries remain valid after any admitted binary operation followed by an actual Sample, using its advanced endpoint.

Proof. Space first recovers $u$ by [NLBA, Theorem 11.1](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md), whose hypotheses are precisely this reachable birth-typed material tree, at least three leaves and its complete canonical linear leaf order. Thus its original root and ordered syntax are recovered; an arbitrary untyped tree or unordered boundary would not meet those hypotheses. Its present vector then gives $v$ by Theorem 30.2.

Time recovers $u$ by [AA, Theorem 17.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md): this is the actual original labelled causal birth/lifecycle order on $\mathcal D$. The same supplier computes that canonical causal order from $u$. Time already contains $v$, so (NLBAII.33) calculates the actual present vector. Memory has $u$ and the present vector, hence also recovers $v$ by Theorem 30.2.

Boundary's onset table is the complete leaf metric by NLBA Lemma 2.1. Its full unit subdivision tree, including degree-two vertices, is recovered by NLBA Lemma 2.3, and its original root and syntax by Theorem 11.1. The recovered graph supplies the same $I,J,C$. Equation (NLBAII.39), applied to the literal window, recovers $x_w$ and then $w$. Appending its $I$ actual sampling zeros gives $v$ and the actual present vector. This uses no fictitious simultaneous readings from several cuts.

Conversely, from any recovered pair $(u,v)$ in this sampled image, compute $I$ from $u$ and remove its known final $I$ zeros to obtain $w$. Equation (NLBAII.33) gives $x_w$ and $x_v$, and hence the entire literal numerical window, onset table and canonical Memory. AA's causal reconstruction gives exactly $E(u)$. This reconstructs each original expression, rather than choosing an arbitrary representative history. All routes therefore factor through the same pair $(u,v)$ and return the same values.

The complete graph, present vector and earned context establish invariant (NLBAII.8). The proof of Theorems 19.2–19.4 consequently predicts every full canonical reply and updates its graph, vector and bindings after actual calls. For binary Next the pair changes to $(u,vd)$; for Sample it changes to $(u,v0^I)$. A Next followed by Sample ends at $(u,vd0^I)$ with the actual new trailing window, so the proved recoveries apply again there. No claim that an unsampled intermediate cut already contains the last-Sample observation of a different cut is needed. $\square$

Different vectors at the same $u$ are distinguishable by a finite actual all-leaf window: (NLBAII.38) annihilates no nonzero difference. Different ordered terms are distinguishable even in the six-operation menu used below: at the first logical address where their constructors differ, $P$ has different branch/wrong-type/success meanings. If their exposed roster lengths differ, a range test already distinguishes them. Thus removal of Reset does not destroy these separating continuations. These statements do not make the canonical data sufficient for a task exposing the private raw map or archive; Proposition 20.4's distinction persists.

## 33. Complete binary continuation, the original entrance and its bill

**Definition 33.1 (retained binary use and exit from its image).** At synchronized binary cuts, Recall and Length actually Hold and compute the word or length from the retained full vector by Theorem 30.2, returning the Hold acknowledgement and the requested answer. Neither stores the old input word as a premise. The separately available full raw and canonical menus retain all §17 semantics. An actual arbitrary rational Add, growth or Reset updates the full predictive invariant but need not stay in the binary image. No binary inverse is promised after such an exit unless a fresh qualifying origin is actually prepared. Prediction on a paid copy does not execute any source operation.

**Theorem 33.2 (complete current use).** Starting at any synchronized binary or sampled cut, the retained graph, original code, current vector and earned raw map predict each complete native reply and its whole successor and remain correct after every finite actual common adaptive continuation of the installed menu. This includes addressed success and all distinct original refusals, scalar replies, acknowledgements, out-of-range labels, malformed complete frames and proper incomplete frames. Under its binary-phase restriction, Next returns the literal scalar $e^{\mathsf T}x_{vd}$, Sample returns (NLBAII.39), and Recall/Length leave the field unchanged.

Proof. Initialize (NLBAII.8) by the actually established origin or the reconstructed Sample endpoint. At $P_p$, the old $p$ value persists, the fresh $pL$ value is zero, the acted raw label moves to $pL$, and every other raw binding persists. At $S_p$, $p,pL$ persist, fresh $pLL,pR$ are zero, the acted label moves to $pLL$, and the appended label binds $pR$. Update the actual graph and original constructor code accordingly. The original guards, including absent, branch and wrong-type distinctions, are read from that code. A refusal has the identity successor.

Read and Add use the earned actual raw table; Tick is the neighbour sum on the full current vector; Hold is identity; Reset, when installed, zeros every current coordinate. Labels outside the current length and complete malformed frames have their stated identity successors. Incomplete frames retain their actual pending bytes with no completed reply or source edit. Missing rights disable the call and are outside the successful-use promise. These are exactly §19's one-step correspondences, independent of the way the initial invariant was established. Forward each actual call, consume its entire reply and finish its retained update before another settled cut. Induction on complete common adaptive requests proves the full claim; after fixing a common random tape the same induction applies to each finite randomized realization. Canonical forwarding uses the actual inverse raw table, never a numerical inverse promoted to a reference. The binary formulas follow from the actual calls already proved. $\square$

**Proposition 33.3 (the credited integer-age/Reset entrance).** The original seven-operation installation of §17 and the actual schedule of Theorem 27.2 give a complete independent entrance to Theorems 30.2–33.2. For an entry with $L_0\ge3$ logical leaves, execute that all-$P$ normalization and integer-age binding schedule, including both actual Resets and its final Hold. Its actual endpoint has

$$
b=2L_0-1\ge5,\qquad N=5L_0-3,\qquad I=3L_0-2,
\tag{NLBAII.40}
$$

whole-field zero, earned syntax, complete entry and current raw maps, and the retained same-source callable service. Add one at its first earned canonical terminal and Hold to establish Definition 30.1. This entrance is retained as an alternative in its own right; the arbitrary-field six-operation entrance below is a different actual installation.

Proof. Theorem 27.2 supplies the displayed actual graph and maps and proves global zero by its last Reset, including internal cells. Its complete-call and retention correspondence is Theorem 28.1. The terminal count is at least four and the final extra Add and Hold give exactly $e$. All other hypotheses of Definition 30.1 are those supplied and retained by §§17 and 27. No no-Reset experiment or later scalar-origin construction is used in this implication. $\square$

**Theorem 33.4 (one binary run's resource vector).** After any qualifying origin let $K_1$ be the number of Next calls, $R_1$ the number of Sample calls, and $Q_1$ the total number of Recall and Length calls in one finite binary continuation. Set $m=K_1+R_1I$, its actual binary length. Excluding the entrance and origin, the exact primitive counts are

$$
\begin{aligned}
\mathrm{Tick}&=m,&\mathrm{Add}&=m,\\
\mathrm{Read}&=K_1+R_1b(I+1),&
\mathrm{Hold}&=K_1+R_1(I+1)+Q_1.
\end{aligned}
\tag{NLBAII.41}
$$

For the actual entrance in Proposition 33.3, including the origin, the same specimen's totals are

$$
\begin{aligned}
P&=2L_0-1,&S&=L_0-1,&\mathrm{Reset}&=2,\\
\mathrm{Add}&=L_0^2+1+m,&\mathrm{Tick}&=m,\\
\mathrm{Read}&=L_0+K_1+R_1b(I+1),\\
\mathrm{Hold}&=L_0+2+K_1+R_1(I+1)+Q_1.
\end{aligned}
\tag{NLBAII.42}
$$

Every primitive request, entire response, framing, return and retained update, both sides of the dispatcher, is paid at its actual finite bit width. These counts do not include unrelated additional raw calls; such calls incur their actual counts and work and can leave the binary image.

Proof and size bounds. Count the definitions, including every zero Add inside Sample and its initial Hold and all-leaf read. Add the already attained Theorem 27.2 counts and the actual origin. No coordinate of this vector is chosen from another run.

For explicit finite representations, the maximum field entry after $j$ binary steps satisfies $M_0=1$ and $M_{j+1}\le3M_j+1$, hence $M_j<3^{j+1}$. Thus each integer field entry has $O(j+1)$ bits. The actual source vector and retained predictive vector are separate simultaneous stores, each with $O(N(m+1))$ field bits, in addition to addresses, graph and code. Exact repeated neighbour summation uses a separate $N$-entry result buffer, at most $2(N-1)$ directed additions and $N$ initializations per actual Tick; source and predictor work are both charged. A literal window has $b(I+1)$ entries at their actual widths. Returned words, windows and complete replies also occupy actual output backing; caller-retained copies are not free.

One may compute $h$ using $N-1$ applications of $\operatorname{Id}+A$, with entries at most $2\cdot4^{N-1}$. In (NLBAII.36), a force uses a shift and at most two subtractions. Induction bounds the sum of the absolute coefficient values of each $p_v$ by $3^I$. Storing $C$ as a dense array takes at most $Nb(I+1)$ integer slots of $O(I+1)$ bits; computation, copies, reconstruction and their scratch are paid. Exhaustive decoding a length-$m$ word examines at most $2^{m+1}-1$ candidates. Constructing their fields by sparse steps costs $O(N(m+1)2^m)$ scalar arithmetic operations with actual operand widths, besides comparisons and output; this is an attained finite bound, not an efficiency optimum. A sequential implementation can discard each failed candidate but must pay for the current candidate, reconstructed vector and live scratch alongside all retained source state.

The separate entry archive, complete private raw table, canonical table, parser and partial packets, instruction code, traversal/address records, actual reference and grants, live decoded outputs, allocation and clearing costs all coexist when used and are charged. Old preparation of the specimen also remains charged; (NLBAII.42) does not erase it. The $2^m$ different length-$m$ words require at least $m$ bits of distinguishing capacity in any exact finite representation of their distinct fields. There is no bounded-lifetime-memory, constant-precision or inexpensive-decoder conclusion. $\square$

## 34. Arbitrary-field acquisition in the six-operation installation

**Assumption 34.1 (different attachment, same original growth).** The installed source has all §17's original term, raw roster, exact rational field, actual binding, persistent growth, fresh-zero, reference, authority, finite completion and held-serialization hypotheses, with these explicit differences. At attachment its entire field is arbitrary and unknown in $\mathbb Q^{V(t)}$, including internal cells. There is no Reset operation. The exact installed menu is $P,S,\mathrm{Add},\mathrm{Tick},\mathrm{Read},\mathrm{Hold}$. A complete former Reset tag is BadFrame with identity successor. The other full framing, success, refusal, range and incomplete-frame semantics are unchanged. Fresh allocation still initializes just its new cells to zero. The unknown entry is $t\in\mathcal D$ with $a$ alpha leaves, $c$ beta leaves, $L=a+c\ge3$ and arbitrary initial raw bijection $\lambda_0$. Its complete finite raw roster length is exposed as in §17; neither $t$, an old field, a history, a size bound nor an address decoder is input advice.

**Definition 34.2 (arming without clearing).** Initially Hold. For each initial raw label $j=1,\ldots,L$, Read its actual value $z_j$ and actually Add$(j,1-z_j)$. Then Hold. There is no Tick, so the different label calls address different unchanged terminals; every terminal is now one. No conclusion about any internal field follows.

Perform Definition 18.3's actual preorder traversal and Definition 18.1's single-edit assay, omitting both Resets: a branch refusal schedules its entry children; a promotion success records entry alpha; a wrong-type refusal is followed by an actual split and records entry beta. After each success Hold and read every old raw label, excluding an appended split label, identify its unique zero, and rearm the inherited and any appended zero by Add one. Neither leaf case schedules its newly created children. Retain the exact entry code and acquired entry map separately from the current code and map. When the stack empties, Hold. Call the actual resulting whole field $x_{\rm mark}$; it is not declared zero.

**Theorem 34.3 (earned correspondence at an arbitrary nonzero endpoint).** Under Assumption 34.1, the one procedure of Definition 34.2 terminates for every finite promised attachment. It earns the exact $(t,\lambda_0)$ and exact current $(u,\lambda)$ on the original callable source, where

$$
u=\rho(t),\qquad b=L+c,\qquad N=3L+2c-1,\qquad I=N-b=2L+c-1.
\tag{NLBAII.43}
$$

The map $\lambda$ exhausts the actual current terminals, not merely those scanned. The full current graph is known. The field $x_{\rm mark}$ can still have arbitrary internal values, so the theorem has not yet established a synchronized full-field predictor or a zero entrance.

Proof. Initial Read/Add arming sets every terminal to one, independently of its old rational value. Because no Tick occurs throughout marking, arbitrary internal values cannot propagate to the scanned terminals. Under the actual persistent fresh-zero growth rule, a promotion moves its one acted old raw label to a fresh zero marker; a split moves its one acted old label to a fresh zero marker and appends a separate fresh zero right terminal. Every other scanned old label remains at a one-valued terminal. Hence the literal old-label scan has exactly the single zero (NLBAII.5), even with arbitrary internal values. The actual rearming restores all current terminals to one.

For termination and entry reconstruction, use structural induction on the finite entry subtree at each scheduled address, with an arbitrary pending continuation outside that subtree. Earlier edited entry leaves are in disjoint cones and preserve every unvisited entry constructor and binding. A branch refusal schedules exactly its two actual entry subtrees. At alpha the actual promotion finishes that leaf; at beta the actual wrong-type refusal and split finish that leaf. No new child is visited, no scheduled address is absent, and every recursive visit is to a proper entry subtree. Thus the finite stack empties with the exact entry code, without advice about its height or size.

The unvisited entry labels have not moved. Each unique scanned zero is therefore the actual initial label of this addressed entry leaf. Across all leaves these distinct labels exhaust $1,\ldots,L$. At alpha, record $j\mapsto p$ for the entry and $j\mapsto pL$ currently. At beta, record $j\mapsto pL$ for the entry, and $j\mapsto pLL$, $n+1\mapsto pR$ currently. Disjoint cones and distinct append indices show that these assignments exhaust the final roster. The actual successful edits are precisely one old-frontier replacement at every entry leaf, giving $u=\rho(t)$, as in Theorem 18.4; its proof of code and map did not use internal zero. Counting that same actual material gives (NLBAII.43). All original values persist when their vertices become internal, and their old values were not measured there. This proves precisely why the endpoint is $x_{\rm mark}$, without inferring full zero from arming. $\square$

## 35. Actual leaf observation and executed whole-field nulling

**Definition 35.1 (observing the marked specimen).** On the actual earned $u$, construct $J,K,C$ by Definition 31.1. Here $J$ may be in raw order using the earned bijection, or in canonical order through its actual forwarding; use the same order consistently in $K,C$ and the calls. Starting from the final held cut of Definition 34.2, Read all $b$ terminals. For $r=1,\ldots,I$, actually Tick, Hold and Read all $b$ terminals. There is no Add during this observation. Stack the literal replies as $y$ and calculate

$$
x_{\rm mark}=C^{\mathsf T}y,\qquad x_d=A^Ix_{\rm mark}.
\tag{NLBAII.44}
$$

Install $x_d$, the actually advanced field, as the synchronized predictive vector. This recovers the field at the start of this observation, not the arbitrary field at attachment before marking and growth.

**Definition 35.2 (the reversed boundary control).** Put $r_*=I+1$ and compute, using exact rational arithmetic on the earned graph and recovered vector,

$$
g=-C A^{r_*}x_d=\begin{pmatrix}g_0\\\vdots\\g_I\end{pmatrix},
\qquad g_j\in\mathbb Q^b.
\tag{NLBAII.45}
$$

For $s=0,\ldots,I$ actually Tick, Add at each terminal $j$ the operand $(g_{I-s})_j$, in increasing label order, and Hold. All $b(I+1)$ Adds are executed, including zero operands. A control block is not applied before its preceding Tick. The field stays held while a block is calculated or transmitted, and retained updates follow actual operations. This is a finite use of the six installed operations, with no Reset tag, internal actuator or inverse Tick.

**Theorem 35.3 (whole-field zero earned by these actual operations).** The observation in Definition 35.1 returns the exact stated $x_{\rm mark}$ and synchronizes at the actual endpoint $x_d$. The control in Definition 35.2 ends with zero on every actual material vertex, for every unknown rational field allowed by Assumption 34.1. The graph, full raw correspondence, reference and current rights are retained on the same specimen throughout.

Proof. During the observation, the $r$th literal terminal block is $J^{\mathsf T}A^rx_{\rm mark}$. Thus $y=K^{\mathsf T}x_{\rm mark}$, and symmetry together with $KC=\operatorname{Id}$ proves (NLBAII.44), including the actual advanced endpoint. No known initialization is required for this linear identity.

The actual field after the $I+1$ control rounds is, by induction on the rounds,

$$
A^{I+1}x_d+\sum_{s=0}^I A^{I-s}Jg_{I-s}
=A^{I+1}x_d+Kg
=A^{I+1}x_d-KCA^{I+1}x_d=0.
\tag{NLBAII.46}
$$

Indeed each block is added after its Tick and then undergoes exactly the remaining $I-s$ Ticks. Adds at distinct terminals commute within a block and affect exactly those actual terminals by the earned map. Holds introduce no extra dynamics. Formula (NLBAII.46) therefore describes the actual plant, not just a controllability matrix with unexecuted inputs. It proves zero at all coordinates, including internal cells which arming did not clear. Neither invertibility of $A$, positivity of its spectrum, a scalar clock, nor any known old initial field occurs in the calculation. The actual map and authority were retained, and no growth occurs during these two finite phases. $\square$

## 36. No-Reset continuation and a single attained acquisition account

**Theorem 36.1 (complete native use from the acquired zero).** The final cut of Theorem 35.3 establishes (NLBAII.8), with $u=\rho(t)$, its exhaustive earned raw map and its actual full zero vector, on the six-operation installation. Without another correspondence-learning assay, the retained procedures predict the full next output and full successor for every finite common adaptive raw or canonical continuation of this entire installed menu, including arbitrary rational fields after further use. They execute callable canonical Add/Read by the retained actual reference and earned permutation. At settled whole-zero cuts the four zero-cut expressions of Definition 20.1 again recover each other on their stated canonical task.

Proof. Theorem 34.3 establishes the original syntax, material graph and exact current binding, while Theorem 35.3 establishes equality of every actual coordinate to the retained zero. These are precisely the invariant's premises. Repeat Theorem 33.2's full one-step correspondence for the six installed operations. Its Reset case is replaced by the installed BadFrame identity successor for the former tag. The P/S fresh-coordinate and raw-binding updates are unchanged, as are Add, Read, Tick, Hold, all distinct guarded refusals, range replies, proper incomplete waits and malformed complete replies. Induction on actual completed common adaptive requests proves the claim on every finite continuation. Forwarding retains actual completion, output and current authority, rather than using the finite record as a new source reference.

At whole-zero cuts, Space and Boundary recover the original term by the same complete-leaf metric and original-root correspondence as in Theorem 32.2; Time is AA's actual labelled causal order and Memory is the original code with zero vector. Each factors through that same term. Equal terms give equal entire canonical futures. Unequal terms are separated by exposed range or the first differing addressed constructor's P reply, as proved after Theorem 32.2, without Reset. Thus the six-operation restriction preserves the zero-cut canonical task-kernel statement, and composites whose endpoints return to whole zero commute with those data recoveries. The full predictor is still needed at intermediate nonzero fields. No inverse of structural Time to an arbitrary nonzero field is inferred. $\square$

**Theorem 36.2 (same-run six-operation costs).** Let the entry beta leaves have preorder assay positions $B\subseteq\{1,\ldots,L\}$ and define the actual old-roster scan length sum

$$
R_{\rm mark}=\sum_{s=0}^{L-1}\bigl(L+|B\cap\{1,\ldots,s\}|\bigr)
=L^2+\sum_{q\in B}(L-q)\le L(L+c).
\tag{NLBAII.47}
$$

For exactly Definitions 34.2, 35.1 and 35.2 on this one actual run, including its final whole-zero Hold, the primitive counts are

$$
\begin{aligned}
P&=2L-1,&S&=c,&\mathrm{Reset}&=0,\\
\mathrm{Read}&=L+R_{\rm mark}+b(I+1),\\
\mathrm{Add}&=2L+c+b(I+1),\\
\mathrm{Tick}&=2I+1,&\mathrm{Hold}&=L+2I+4.
\end{aligned}
\tag{NLBAII.48}
$$

There are $a+2c$ fresh material cells, $4a+8c$ structural assignments under §21's convention, and $a+2c$ binding assignments. Fixed field acknowledgements number $3L+c+b(I+1)+4I+5$; scalar Read replies are counted separately. There are also all $2L-1+c$ complete addressed replies and their frames, and every request, return and dispatch cost.

Proof. The traversal calls P once at all $2L-1$ entry logical positions and S once at each of the $c$ beta leaves. Initial arming uses $L$ Reads and $L$ Adds. The $L$ assays read the old roster, giving (NLBAII.47), and rearm by $L+c$ Adds. Their Holds number $L$, besides the initial and post-arming Holds and final marking Hold, giving $L+3$. Observation adds $b(I+1)$ Reads, $I$ Ticks and $I$ Holds. Reversed control adds $I+1$ Ticks, $b(I+1)$ Adds and $I+1$ Holds. Summing gives (NLBAII.48); Adds, Ticks and Holds have the displayed number of fixed acknowledgements. Successful growth and binding writes have exactly the persistent local templates of §§17 and 21. The mathematical reconstruction and control do not call Reset indirectly. $\square$

**Definition 36.3 (actual precision and simultaneous backing).** The rational values in initial arming, observation and control have their actual finite numerator and denominator lengths. Let $W_{\rm run}$ be the maximum such encoded width among all source fields, control operands, intermediate rational computations, replies and simultaneous retained predictor/scratch entries in this finite implementation. It is finite for each admitted finite run; no bound depending only on $N$ is asserted, since the attachment field itself is arbitrary. Each request and reply uses §17's actual finite label, address and rational encoding. Tree traversal also pays the actual visited address lengths, stack operations, parsing, code construction and map scans.

One implementation retains the integer forcing matrix $C$, the literal $b(I+1)$-entry window, reconstructed vectors, the $b(I+1)$-entry control stack and local rational scratch. Source field, current predictive field and separate result buffers are simultaneous allocations, each charged, not interchangeable uses of one cost coordinate. Constructing $C$ has Definition 33.4's coefficient bound. Matrix products in (NLBAII.44)–(NLBAII.45), including $I+1$ sparse applications for $A^{I+1}x_d$, are exact finite rational operations at their actual widths. Each actual Tick uses a new $N$-entry source result buffer and $2(N-1)$ directed neighbour additions; the retained predictor has its own corresponding computation. The $2I+1$ actual Ticks therefore pay both computations, their zero-initializations and all copied bits. Initial $1-z_j$ operands, possibly negative or large, and every signed control operand are paid. Control blocks and observation outputs can be discarded only after their last use, with their actual clearing costs.

The current graph/code, complete raw and canonical maps, separate entry report, addresses, parser and pending packets, actual reference and grants, input/output backing and any caller-retained outputs are charged alongside these arrays. The original source preparation and the arbitrary attachment field's actual storage remain part of the same run's total resources. These are an attained finite account conditional on exact rational operations and adequate backing, not a uniform size-only precision estimate, a minimum-resource theorem, a physical realization theorem or an arbitrary erased-history recovery theorem.

## 37. A separate same-specimen implication from no-Reset acquisition to the binary domain

**Theorem 37.1 (complete hypothesis mapping and actual composition).** For every attachment of Assumption 34.1, execute Definitions 34.2, 35.1 and 35.2. Then actually Add one at the first earned canonical terminal and Hold. On this same six-operation specimen, Theorems 30.2–33.2 apply to every finite subsequent binary continuation, with $u=\rho(t)$ and the $b,N,I$ of (NLBAII.43). This implication leaves Proposition 33.3's original integer-age/Reset entrance intact.

Proof. Since $L\ge3$, the reachable original entry is a branch. Follow left children to its leftmost logical leaf. Its address is nonempty and ends in L; the defining birth-typing of $\mathcal D$ forbids alpha at such a leaf. Hence this leaf is beta, so $c\ge1$. Therefore the actual acquired material tree has $b=L+c\ge4$ and meets Theorem 30.2's branching hypothesis; this is not extra advice to the acquisition.

Theorem 34.3 supplies the actual original $u=\rho(t)$, complete ordered material graph and exhaustive raw bijection, including every appended label. Theorem 35.3 supplies whole-field zero by executed controls. Theorem 36.1 supplies the synchronized full predictor and actual canonical forwarding. The unchanged installed original P/S semantics, fresh zeros, exact unit-adjacency Tick, rational terminal Adds and Reads, held serialization, authentic same reference, current grants and sufficient finite backing are exactly Assumption 34.1's retained premises. The actual extra Add and Hold consequently establish the $e$ origin of Definition 30.1.

Every primitive inside Next, Sample, Recall and Length belongs to this six-operation menu; no Reset or seventh operation is invoked. All literal sample observations and advanced endpoints are therefore those of this very plant. Its full six-operation continuation is covered by Theorem 36.1; Theorem 33.2's optional Reset clause is simply absent. This verifies each hypothesis of the binary theorem on the same specimen and with its actual initialization, rather than taking a zero field, a map or authority from another run. $\square$

**Corollary 37.2 (joint bill, rather than coordinatewise independent optima).** With $K_1,R_1,Q_1$ and $m=K_1+R_1I$ defined after this new origin, the exact combined counts are

$$
\begin{aligned}
P&=2L-1,&S&=c,&\mathrm{Reset}&=0,\\
\mathrm{Read}&=L+R_{\rm mark}+b(I+1)+K_1+R_1b(I+1),\\
\mathrm{Add}&=2L+c+b(I+1)+1+m,\\
\mathrm{Tick}&=2I+1+m,\\
\mathrm{Hold}&=L+2I+5+K_1+R_1(I+1)+Q_1.
\end{aligned}
\tag{NLBAII.49}
$$

Proof. Concatenate the actual schedule of Theorem 36.2, one actual origin Add and Hold, and the actual binary schedule of Theorem 33.4. They act on the same unchanged graph after acquisition, so their $b,N,I$ agree. Resource bytes and work concatenate at their actual widths and overlap only through actually retained objects. During binary use the source field has the new integer bound of Theorem 33.4; arbitrary-width acquisition data still retained as output or scratch must be added to simultaneous memory until actually released. No component of this joint vector is borrowed from the integer-age/Reset entrance or a separately optimized scalar experiment. $\square$

## 38. Supplier correspondences and the exact remaining scope

**Definition 38.1 (attribution and uncovered native content).** The structural source results used above are [AA §17](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md), [AAII §§53–54](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md), [NLBA §§2–3, 5, 10–13, 19–24](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md), and this volume §§17–29. In particular the old-frontier endpoint, causal reconstruction, ordered-root inverse, all-leaf forcing, arbitrary-field leaf-window reconstruction, full-menu invariant and integer-age entrance are credited suppliers. The new conjunction proved in §§30–37 is the binary field separation on the actual branching native adjacency, literal advancing sampling with four independently interpreted sampled expressions and a complete continued-use record; and, separately, an arbitrary-field no-Reset experiment which earns its syntax/raw correspondence and then observes and nulls the actual whole field. The same-specimen implication in §37 follows from the explicit hypothesis mapping, not from an assertion that independently available conclusions automatically compose.

The existing mathematical declarations and their owning Scribes have narrower roles. [NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean) and [NativeUniformTree](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.lean) supply finite constructor navigation and literal source-read procedures under their stated access, rather than an arbitrary raw binding. [NativeMaterialRootRecognition](../../../D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.lean) has the reachable original material tree, at least three leaves and complete ordered-graph premises used for the root inverse. [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) supplies the finite real stacked-observation rank/kernel relation; that relation alone neither binds a source nor executes a nulling control. The explicit rational coefficient identity and actual calls above supply the needed operational correspondence. For walk interpretation the mature finite-graph identity is `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` in mathlib's [AdjMatrix.lean at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean): finite vertices, decidable equality and a semiring give the adjacency-power count of length-$n$ walks. No new claim about a general walk-count identity is made.

[Recovery Geometry II §§59–68](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md) already give scalar-origin signed-length conditions, bounded-digit inverses, lattice/history consumers, actual advanced prediction and resource limits. Their symmetric positive-link operator satisfies $0<T<\operatorname{Id}$ and uses its stated authentic initialized impulse orbit; their scalar or annihilator-lattice conclusions are not hypotheses about this native $A$ with degree-three branching. Here (NLBAII.35) is proved for this $A$; raw correspondence is earned by actual growth assays; whole zero is proved by (NLBAII.46). No scalar numerical inverse is used to obtain a raw map or authority. General bounded-digit inversion and lattice enumeration are therefore supplier-level phenomena, not claimed new by the binary construction.

The newer [same-handle arithmetic continuation](../../../D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.lean), with its owning Scribe, assumes a bound arithmetic `SourceService`, lawful replacement/graft and gcd Read meanings, retained authority and a completion premise on that handle. The current native menu is not that arithmetic service. [Relational Spectra §§35–38](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md) and [its continuation §§39–43](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA_II.md) concern fixed complex CPTP instruments, exact joint effect/probability records, specified terminal tasks and their compatible successor fibres. Their finite record inverses do not supply the native unit-tree field, raw roster or boundary actuators. The [Green-tail continuation §20](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GREEN_TAIL.md) retains the original continuous Heisenberg source, full off-pole and form-domain hypotheses, and complete exterior integration; the [geometry continuation III §§108–109](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md) likewise has its stated continuous differential source and maximal-domain zero-space. The [private-clock continuation](FIB_UNCALIBRATED_QUADRATIC_CLOCK_PRIVATE_RANDOMIZATION.md) has its independent-seed real-report and resource/minimax hypotheses. None of these correspondences identifies their laws or task domains with Assumptions 30.1 or 34.1. Shared terminology about histories, clocks or boundaries is insufficient to transfer a conclusion. The native deductions above are source-specific applications and constructions, with no worldwide priority assertion.

**Proposition 38.2 (retained limits of the conclusions).** The two entrances and the binary image do not recover arbitrary erased histories, establish an efficient off-image recognizer, create reference or grant authority, prove bounded lifetime memory or imply a universal physical foundation. They do not remove the original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization or final-no-Ready obligations.

Proof. The only binary inverse has the new origin and the specific polynomial image (NLBAII.33) as premises. Its Time records the new binary inputs and original causal order, not an old total serialization. Distinct old field-control histories can end at the same origin and hence have identical later binary fields. In the arbitrary-field entrance, initial terminal arming changes the old field, and only the later $x_{\rm mark}$ is reconstructed; that procedure cannot invert an unrecorded earlier alteration. Structural Time and terminal zeros also omit internal field distinctions by Proposition 20.3. Raw-map and authority distinctions are explicitly retained outside the four numerical expressions, as in Proposition 20.4. The attained exact procedures pay their actual growing field widths, enumeration, all simultaneous stores and legal source work; they supply no uniform efficient recognizer or bounded memory. Finally neither theorem has a hypothesis correspondence identifying its new origin, enlarged active experiment or acquired callable dispatcher with an unchanged original initialization, fixed observation task or the named parked/final endpoints. Those bridges would require their own constructions preserving those exact hypotheses and endpoints. No such bridge is asserted here. $\square$

## 追加锚（本行以下为增补区）

## 39. A known appended anchor and distinct inherited-terminal distances

**Definition 39.1 (the original binding-acquisition task).** Use exactly the installation of Definitions 17.1–17.3. The entry is every finite reachable $t\in\mathcal D$ with $a$ alpha leaves, $c$ beta leaves and $L=a+c\ge3$, after every legal old producer word ending there. Its actual whole field is zero. The observer receives the authentic opaque original-root-bound service, the complete raw roster $1,\ldots,L$, current rights, the fixed framing/return connection and source-independent finite instruction code. Its source-dependent work records are initially empty. The original term, old word, raw bijection $\lambda_0$, internal coordinates and response law table are absent from its inputs. The source law is the original symmetric zero-diagonal unit adjacency, and the full menu includes the actual calibrated whole-field Reset.

All later steps use this same specimen and its installed persistent-label/fresh-zero lifecycle. Each successful promotion retains old cells and moves its old terminal label to its fresh marker; each successful split retains old cells, moves the acted label to its fresh left marker and appends the known next raw integer at its fresh right terminal. These new terminals have the actual grants of Assumption 17.2. No numerical calculation creates a reference or a grant. Exact arbitrarily large finite rational packets, sufficient finite allocation and work backing, exclusive serial calls, Hold, complete replies and completed matching observer updates have exactly §17's meanings. There is no timing, work, capacity, allocation-name or private-reference inspection channel. No other writer, autonomous Tick, revocation, interruption or observable exhaustion is admitted.

The required acquired report contains the exact entry $(t,\lambda_0)$ and the exact actual advanced term, whole field and exhaustive current raw binding. The actual callable reference and current rights are retained in addition to these numerical records. Restoring the entry tree is not part of this task. A successful scalar Read means a complete in-range Read with its literal rational reply and return consumed. Refused or malformed requests are not successful scalar Reads. A report at a settled endpoint cannot leave an unfinished scalar reply in flight. The minimum below concerns this exact reporting task on this full installation, with no uniform bound on finite growth, word widths or work; it concerns no other resource coordinate.

**Definition 39.2 (earned syntax and the actual chain word).** First actually Hold and run the all-$P$ traversal of Definition 24.1, namely [AAII Definition 54.1 and Theorem 54.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md). Consume every complete Growth or tagged refusal and return. This earns separate entry and current constructor words for $t$ and $\nu(t)$, without earning the arbitrary raw permutation. It makes $2L-1$ actual $P$ calls, of which $a$ succeed; its other replies are $L-1$ branch refusals and $c$ wrong-type refusals. No $S$, field input or scalar Read occurs in this pass. Every original logical leaf is now beta, the raw length is still $L$, and the actual entire field is still zero.

Index the earned original logical leaves by $i=0,\ldots,L-1$ in their original left-to-right order, at addresses $p_i$, and retain their original types $\eta_i$. Put

$$
q_i=p_iL,\qquad
\delta_i=d_{C(\nu(t))}(q_0,q_i),\qquad
D_0=\max_{0\le i<L}\delta_i,
\tag{NLBAII.50}
$$

where these distances are finite local computations on the earned graph, not observations of an unknown wave response. Define

$$
k_0=1,\qquad
k_i=D_0+i+4-\delta_i\quad(1\le i<L),\qquad
K=\sum_{i=0}^{L-1}k_i,\qquad D=D_0+L+3.
\tag{NLBAII.51}
$$

For $i=0,\ldots,L-1$, in that order, perform the $k_i$ actual splits at

$$
p_i,\ p_iL,\ \ldots,\ p_iL^{k_i-1}.
\tag{NLBAII.52}
$$

Here $L^s$ in an address means $s$ repetitions of the left letter. At split $(i,s)$, $0\le s<k_i$, consume the complete Growth reply and record the appended label and address

$$
\ell(i,s)=L+\sum_{h<i}k_h+s+1,
\qquad \ell(i,s)\longmapsto p_iL^sR.
\tag{NLBAII.53}
$$

The label is obtained from the installed append rule and the maintained actual length, not from the Growth payload or a concealed allocation ordinal. In particular the first split earns the usable raw anchor

$$
r_*=L+1=\ell(0,0),\qquad z=p_0R.
\tag{NLBAII.54}
$$

Never act at any of the appended right leaves. Let $u$ be the resulting actual term, obtained by replacing original leaf $i$ by $B_{k_i}$, where $B_0=\beta$ and $B_{s+1}=\langle B_s,\alpha\rangle$. Its ordered constructor word and material graph are maintained from the actual replies. For proof only, write $j_i$ for the unknown original raw label of cone $i$. Its current terminal is

$$
v_i=p_iL^{k_i+1}.
\tag{NLBAII.55}
$$

The controller uses the earned logical addresses for growth and known raw integers for field calls; no $j_i$ is an operand before acquisition.

**Lemma 39.3 (legality, exhaustive lifecycle and one actual distance code).** Every split in (NLBAII.52) is enabled. The old labels bind exactly the $v_i$, and all other current labels have exactly (NLBAII.53)'s bindings. The anchor remains $z$, and on this one actual final graph

$$
d_{C(u)}(z,v_0)=3,\qquad
d_{C(u)}(z,v_i)=D_0+i+4\quad(1\le i<L).
\tag{NLBAII.56}
$$

These $L$ distances are pairwise distinct and their maximum is $D$. The graph has $L+K$ terminals and $N=3L+2K-1$ material vertices, and every cell is still zero.

Proof. The source correspondence of the all-$P$ supplier applies to the growth-channel restriction of §17: its branch/type replies and old/fresh material templates are identical. Promotions leave all logical branch positions fixed and move only their acted terminal labels. Consequently the saved initial terminal in cone $i$ is $p_i$ for $\eta_i=\alpha$ and $p_iL$ for $\eta_i=\beta$, and after normalization either one carries its old label at $q_i$. This establishes the starting correspondence without identifying $j_i$.

Since $\delta_i\le D_0$, every $k_i$ is positive. At stage $s$ of cone $i$, the target $p_iL^s$ is beta: the previous split, if any, created precisely its left beta. Different original leaf addresses are incomparable, so edits in other cones preserve this target. Each success has the full original kind/address reply and finite return; there is no hidden type test or new source opcode. The persistent-label rule moves the same inherited label one further left and appends (NLBAII.53)'s label at the new right alpha. Later targets lie strictly in the continuing left chain or in other cones, so those right terminals persist. Induction proves (NLBAII.53)–(NLBAII.55). The $L$ inherited and $K$ appended assignments are disjoint and exhaust the current terminals.

For $i>0$, the path from the original $q_0=p_0L$ to $q_i$ first uses its edge to $p_0$. Replacing that first vertex by $z=p_0R$ changes neither the length nor the rest of this external path. Growth in cone zero leaves the external path unchanged. Each of the $k_i$ left-chain splits extends the inherited terminal in cone $i$ by exactly one edge, so its distance from $z$ is $\delta_i+k_i=D_0+i+4$. In cone zero there is just one split, and the path $p_0R,p_0,p_0L,p_0LL$ has length three. This proves (NLBAII.56). The other distances start at $D_0+5>3$, increase with $i$, and end at $D_0+L+3=D$.

The normalized material size is $3L-1$, and each split adds two vertices and one terminal. Thus the stated sizes follow. The attachment was wholly zero, and only old-value-preserving growth with fresh zero cells has occurred, so the whole field remains zero. All loops terminate: normalization terminates by its supplier, and every later count and address is computed from its earned finite output. $\square$

## 40. An executed waveform whose one scalar earns both raw maps

**Definition 40.1 (literal input word and decoding).** Freeze growth during this experiment on the just constructed $C(u)$. Set

$$
H=D+1,\qquad B=4^D=2^{2D},\qquad M=LH.
\tag{NLBAII.57}
$$

For $r=0,\ldots,D$, send, in increasing $j=1,\ldots,L$ order, the actual calls

$$
\operatorname{Add}\bigl(j,B^{H(j-1)+D-r}\bigr).
\tag{NLBAII.58}
$$

Consume every acknowledgement and return. If $r<D$, next actually Tick and Hold, consuming both acknowledgements and returns. No appended label is an input. After the last input batch, actually Read$(r_*)$ once and consume its whole literal reply $y$ and return. The Tick reply is only its fixed acknowledgement; no intermediate scalar has been obtained. Hold and serialization allow the finite decoding work without an additional source Tick.

Decode exactly $M$ padded base-$B$ digits of $y$, retaining zero digits even beyond the highest nonzero digit. In block $j$, let $d_j$ be the first positive digit index among $k=0,\ldots,D$ at exponent $H(j-1)+k$. Set

$$
i(j)=\begin{cases}
0,&d_j=3,\\
d_j-D_0-4,&d_j\ne3.
\end{cases}
\tag{NLBAII.59}
$$

Use the saved entry types to construct

$$
\lambda_0(j)=
\begin{cases}p_{i(j)},&\eta_{i(j)}=\alpha,\\p_{i(j)}L,&\eta_{i(j)}=\beta,\end{cases}
\qquad
\lambda_u(j)=p_{i(j)}L^{k_{i(j)}+1}\quad(1\le j\le L),
\tag{NLBAII.60}
$$

and include every appended binding (NLBAII.53). After decoding, actually Reset and Hold, consume both complete returns, and install the full zero-vector predictor at this actual $u$. Export the finite entry/current reports through their backed complete output/acknowledgement/return connection; retain the actual service and current grants. Temporary waveform, quotient and output scratch is cleared only after its last use, with its actual clearing work. Caller-retained copies and the separate entry archive remain separately charged. A completed acquisition cut has no pending frame, source edit, output or uncommitted observer update. The scalar $y$ describes the pre-Reset experiment, whereas the returned current field is the actual post-Reset zero field.

**Theorem 40.2 (one successful Read suffices for the exhaustive unknown binding).** For every attachment in Definition 39.1, Definitions 39.2 and 40.1 terminate and return exactly $(t,\lambda_0)$ and $(u,0,\lambda_u)$, with an exhaustive current bijection and the same actually callable service. There is exactly one successful scalar Read in the entire acquisition. For each earned $t$, its one observed $y$ is injective in the arbitrary initial raw bijection under this actual experiment. Source authenticity, calibration, rights and the initialization are still premises of this conditional conclusion.

Proof. Let $A$ be the actual unit adjacency on the fixed final graph, and let $w_j$ be the terminal actually carrying old raw label $j$. These are proof parameters, not supplied runtime observations. Put $g_j=B^{H(j-1)}$ and $v=\sum_{j=1}^{L}g_je_{w_j}$. The batch with index $r$ adds exactly $B^{D-r}v$, and it is followed by exactly $D-r$ later Ticks. Additions at a fixed batch commute, and all intermediate source operations have their literal declared linear effects. Starting at the whole zero field, expansion of the executed word therefore gives the genuine pre-Read field and actual reply

$$
\begin{aligned}
x_{\rm wave}&=\sum_{k=0}^{D}B^k A^k v,\\
y&=e_z^{\mathsf T}x_{\rm wave}
 =\sum_{j=1}^{L}\sum_{k=0}^{D}
 B^{H(j-1)+k}(A^k)_{z,w_j}.
\end{aligned}
\tag{NLBAII.61}
$$

This superposition uses neither a response oracle nor a returning-scalar Tick. The anchor is an actually known raw binding by Lemma 39.3, so the single Read in this formula is legal without the unknown old map.

Every material vertex has degree at most three. The finite-graph walk-count identity, in precisely the unit-adjacency specialization of `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` in [pinned mathlib AdjMatrix.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean), yields nonnegative integral coefficients and the elementary bound

$$
0\le (A^k)_{z,w_j}\le3^k\le3^D<4^D=B
\quad(0\le k\le D).
\tag{NLBAII.62}
$$

The bound follows by at most three choices at each step of a walk. The exponents $H(j-1)+k$ are distinct because $0\le k<H$. Hence (NLBAII.61) is a carry-free base-$B$ expansion. More explicitly, the remainder modulo $B$ is its coefficient at exponent zero, and division by $B$ leaves the same expression with that coefficient removed and the remaining exponents decreased by one. Induct for exactly $M$ divisions, including all padded zero positions. Thus the actual digit at $(j,k)$ is $(A^k)_{z,w_j}$; no assumption about a nonzero last digit is needed.

This use of nonoverlapping coefficients is classical Kronecker packing; see Harvey, [*Faster polynomial multiplication via multipoint Kronecker substitution*, §3.1, Proposition 5](https://arxiv.org/html/0712.4046v1#S3.SS1). Only its ordinary packing interpretation is used, not its multiplication complexity theorem. The new operational obligation here is (NLBAII.61), realized by the legal source word and known anchor, with the coefficient bound proved for this actual graph.

By NLBA Lemma 2.1, specialized to these positive unit edges and zero diagonal, the first positive coefficient in block $j$ occurs exactly at $d_{C(u)}(z,w_j)$. A shorter walk cannot reach that vertex; the unique shortest tree path contributes one at that distance. Lemma 39.3 puts each such distance within $0,\ldots,D$ and makes the cone distances distinct. Therefore $d_j$ exists, (NLBAII.59) gives exactly the cone carrying $j$, and $j\mapsto i(j)$ is a permutation of $0,\ldots,L-1$. The saved initial type and the proved lifecycle give exactly (NLBAII.60). The appended assignments are already earned directly from actual growth and exhaust all remaining labels. This proves both bijections, including the distinction between an initial alpha vertex and an initial beta marker.

Two different initial maps on this fixed $t$ assign some old raw label to different original cones. Their digit blocks then have different first positive indices. Thus their scalar outputs differ. Conversely the displayed finite digit procedure reconstructs every owed map, so the conclusion is actual acquisition, not merely uniqueness of an abstract inverse.

All stages use earned finite syntax, the known roster, explicit finite integers and the authentic appended anchor. Computing their distances, powers, frames, divisions, finite tables and reports terminates with the stipulated backing. No unknown size or unearned selector controls stopping. The last actual Reset acts on every current cell, including internal cells never read, and final Hold preserves that zero field during report construction and cleanup. The acquired graph and full map consequently describe the genuine final state. No other phase used Read, and this one used Read exactly once. $\square$

## 41. The complete-original-menu zero-Read lower bound

**Theorem 41.1 (no exact zero-Read report from the full menu).** Fix any admitted entry term $t$ with $L\ge3$. Consider any source-independent observer whose initially supplied records, opaque reference roles and bytes, rights, roster, framing and public parameters are identical across the possible initial raw bijections. Allow arbitrary finite adaptive use of every request of §17, arbitrary finite local computation and retained records, and arbitrary finite actual growth and field widths. No uniformly exact terminating reporter of Definition 39.1's entry/current binding task can finish with zero successful scalar Reads. In particular the lower bound is not restricted to the waveform, to binary signals, to scans, to a fixed endpoint, or to a chosen growth schedule.

Proof. Choose two distinct bijections at this same $t$, keeping every observer input and installed public condition fixed. Such a pair is admitted by the arbitrary attachment-bijection clause in Definition 17.1; no reference-byte or permission channel encodes the attachment. Couple the same observer at settled cuts reached without a successful scalar Read. Induct on its entire acquired record and local choices at those cuts, not on equality of the hidden fields. An in-range Read that has begun its reply must complete, including consumption and return, before another settled acquisition endpoint; the menu has no reply-abandonment or cancellation operation. Hence no completed zero-Read report can follow such a call. Partial scalar-reply prefixes need not agree between the installations and are not used in this coupling.

A common addressed $P$ or $S$ sees the same current logical term and therefore the same absent, branch, wrong-type or success case. All full refusal and Growth kind/address replies agree. A success has the same structural successor and the same roster increment in both runs. Its inherited raw label can differ, and the unobserved field can differ; neither fact is part of that reply. Any newly appended integer is determined by the common old length, and its new right-terminal address is determined by the common addressed edit.

An in-range Add, Tick, Reset or Hold has its fixed complete acknowledgement. Its actual field successor can differ without an observable response difference. An out-of-range Add or Read has the common RangeRefusal because the current lengths agree. A malformed complete frame has the same BadFrame. Proper incomplete request frames have the same pending input and no completed output; extensions follow the same fixed grammar until a complete command is determined. Calls disabled by missing rights are disabled in both matched contexts; a disabled call is not an extra scalar or type reply. Finite source/output work, allocation, held local processing and return reveal no further metadata by Assumption 17.2. An incomplete request cannot itself be a settled endpoint either.

Thus, at every coupled settled cut, the complete observations, generated requests, local records, output choices and stopping decisions coincide. Choosing an in-range Read prevents a later zero-Read settled report; every other completed command preserves the coupling. If the observer terminates with a zero-Read report, it therefore returns the same reported initial map on both runs. The required initial maps differ, so the report cannot be exact on both. Retaining more such observations or using more hidden field operations preserves this equality and does not repair the failure. This proves the full-menu claim. The current-map requirement is also substantive: at every common growth history, the original labels remain distinct inherited labels in disjoint original cones, so their differing assignments are not deleted by growth. Already the mandatory entry map suffices for the contradiction. $\square$

**Corollary 41.2 (uniform zero-error randomization and the exact coordinate minimum).** A randomized observer with a source-independent random tape, almost-sure finite termination and zero error separately for every attachment of the fixed $t$ must use at least one successful scalar Read almost surely. If exactness is required for every tape, the deterministic bound holds tape by tape. Combined with Theorem 40.2, the exact least successful-Read count for Definition 39.1's task on the original full installation is one.

Proof. There are only $L!$ initial bijections for fixed $t$. Use one common tape space for them. Intersect their probability-one correctness and finite-termination events; this finite intersection still has probability one. For a fixed tape, the coupling in Theorem 41.1 makes the event of stopping before a successful Read, together with its reported map, identical for all attachments. At any tape in the intersection that event is impossible: one output cannot be every distinct owed map. Its probability is therefore zero. A tape-wise correctness premise gives the same argument without null sets. The deterministic procedure of Theorem 40.2 attains one on every admitted entry and bijection. Honest abstention, later deferred acquisition, or a task asking only for canonical syntax is not the exact terminating report required here. $\square$

## 42. The actual returned endpoint, retained use and canonical expressions

**Corollary 42.1 (application of the full predictor at this acquired endpoint).** Retain the earned $u$, its material graph, exhaustive $\lambda_u$, whole zero vector, current roster length, separate entry report and the authentic actual service reference, rights and backing after Definition 40.1. These initialize invariant (NLBAII.8) on this very advanced source. The full raw predictor and earned canonical dispatcher of Theorems 19.2–19.4 and 28.1 apply at this endpoint and after every finite common adaptive continuation, including arbitrary subsequent rational fields. No further binding-learning assay is needed.

Proof. Lemma 39.3 and Theorem 40.2 give an original-root material-address realization preserving every edge and terminal binding. Its code is the actual $u$, and the actual last Reset makes every field coordinate equal to the retained zero. These are exactly the graph, field and binding hypotheses of (NLBAII.8). The proof of Theorem 28.1 applies to any such earned endpoint, rather than only $\rho(t)$, and has the following complete one-step meanings here.

| Request at the retained current state | Complete reply and matched successor |
| --- | --- |
| Reset | Fixed acknowledgement; zero every current coordinate, retaining syntax and roster |
| Add$(j,q)$ in range | Fixed acknowledgement; add $q$ at precisely $\lambda_u(j)$ |
| Tick | Fixed acknowledgement; replace the whole vector by the current unit adjacency times that vector |
| Read$(j)$ in range | Literal current coordinate at $\lambda_u(j)$; identity successor |
| Hold | Fixed acknowledgement; identity successor with unrequested evolution prevented |
| $P_p$ at alpha | Complete Growth$(P,p)$; retain old cells, add zero at $pL$, change alpha to beta and move its unique raw label to $pL$ |
| $S_p$ at beta | Complete Growth$(S,p)$; retain old cells, add zero at $pLL,pR$, form the left-beta/right-alpha branch, move its old label from $pL$ to $pLL$ and append the new last label at $pR$ |

For either growth request an absent address, branch or wrong leaf type returns its distinct original refusal and leaves every component unchanged. Out-of-range integer field labels give RangeRefusal and identity successor; complete malformed packets give BadFrame and identity successor. Proper incomplete frames retain their finite pending bytes and wait without a completed reply or edit. Missing rights disable a call. Fresh grants remain the installed source obligation. The finite code navigation and actual graph/field inclusion prove exactly the same cases in the predictor, including the adjacency identity (NLBAII.9).

For actual use, forward the real call, consume its entire reply and return, and commit the matching paid record update before another settled cut. Induction on common adaptive requests then matches every complete reply and current successor. Hypothetical prediction instead uses a separately charged copy and makes no source call. Canonical ordinal Add/Read is forwarded using the computed inverse raw table at the current ordered terminal; after growth the table is updated by the same lifecycle. Negative and pending cases keep Definition 19.3's handling. The real retained reference and current rights make this continuation callable; the finite numeric maps do not supply authority. This is the existing predictor applied at a newly earned entrance, not a new general simulation theorem. $\square$

**Application 42.2 (the independently specified four expressions at whole-zero cuts).** Fix that actual canonical entry and its binding/authority context. Restrict to settled synchronized acquired-or-later cuts with no pending frame or edit, reachable current term in $\mathcal D$ with at least three leaves, and zero at every material cell. Use the original meanings of Definitions 20.1 and Theorem 28.2:

| Expression | Its independent source content |
| --- | --- |
| Space | The actual unrooted unit material tree, complete canonical linear terminal order and present whole zero field, modulo terminal-order-preserving isomorphism |
| Time | The actual labelled causal birth/lifecycle order $E(u)$ of successful original $P/S$ events from the real seed, including acquisition growth |
| Boundary | The canonical complete terminal impulse-onset table of the actual unit-adjacency law, diagonal zero, together with the present terminal zero restriction |
| Memory | The retained current recursive constructor code, full zero vector and canonical ordinal-to-material-terminal table at the fixed callable entry |

Each recovers the same $(u,0)$ and hence the others on this actual joint image, with agreeing routes and the canonical continuation kernel. These are the existing four expressions; none contains an unrestricted command journal. Time omits the waveform, nondestructive calls, Ticks, field inputs and elapsed duration. The complete canonical Boundary table is calculable from the earned graph, with paid computation/export/storage. The single packed anchor reply did not literally sample that complete table. Present terminal zeros here follow from actual whole-field Reset; they are not additional unpaid scalar observations.

Proof. The new hypothesis correspondence is Corollary 42.1 together with its actual final Reset. NLBA Lemmas 2.1 and 2.3 identify the complete onset table with the unit leaf metric and recover the entire subdivision tree. NLBA Theorem 11.1, equivalently the original birth-typed ordered-root rigidity supplied by `NativeMaterialRootRecognition.original_rigidity`, recovers the original ordered $u$ under the complete linear roster, no-left-alpha and at-least-three-leaf hypotheses. Space uses this same root inverse. [AA Theorem 17.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md) recovers $u$ from its actual labelled causal order and computes that order from $u$. Memory parses $u$. The whole field is zero by the declared domain. Conversely $(u,0)$ computes exactly these four independently interpreted data. Their inverses therefore all pass through the same $(u,0)$, proving every round trip and route agreement.

The complete canonical successors agree by Corollary 42.1. Equal $(u,0)$ gives equal common canonical futures; unequal $u$ has either a different exposed roster length or a different canonical leaf metric and the original finite Reset/Add/Tick/Read separator, as in Proposition 20.2. Thus the four data kernels have exactly that canonical continuation meaning. For every permitted operation or finite composite whose initial and final cuts lie in the whole-zero domain, recoveries agree with the actual ending views. Intermediate nonzero fields are transported by the full predictor, with no zero-domain inverse asserted there.

The raw implementation table, retained $y$ if kept, entry archive, actual references, grants and parser/backing are additional paid context outside these four data. For fixed $t$ the growth word, $u$ and zero field are independent of the arbitrary initial raw permutation, so these canonical data coincide while the owed raw reports differ. Proposition 20.4's raw arm/grow/Read separator still applies on this grown source. Hence no canonical-to-raw inverse or authority inverse follows. Terminal zeros without the whole-zero hypothesis also remain insufficient by Proposition 20.3. This application changes no existing recovery domain. $\square$

## 43. One-run calls, literal widths and simultaneous material

**Theorem 43.1 (the attained call and source-work vector).** Use the actual parameters of (NLBAII.50)–(NLBAII.57), not coordinates selected from different experiments. Definitions 39.2 and 40.1 have exactly

$$
\begin{aligned}
P\text{ calls}&=2L-1,&P\text{ successes}&=a,&S\text{ calls/successes}&=K,\\
\mathrm{Add}&=L(D+1),&\mathrm{Tick}&=D,&\mathrm{Read}&=1,\\
\mathrm{Reset}&=1,&\mathrm{Hold}&=D+2,\\
\text{fresh material vertices}&=a+2K,&
\text{final terminals}&=L+K,&N&=3L+2K-1.
\end{aligned}
\tag{NLBAII.63}
$$

There are $L-1+c$ addressed refusals and $2L-1+K$ full addressed replies in total. Field fixed acknowledgements number $L(D+1)+2D+3$, in addition to the single literal scalar $y$. Under §21's attained local templates, growth has $4a+8K$ located structural assignments, $a+2K$ fresh active-field zero writes, $a+2K$ changed raw-binding assignments and $K$ roster-length increments. Final Reset writes $N$ active field cells. The Adds perform $L(D+1)$ actual integer additions. A two-buffer Tick realization performs $2(N-1)$ directed neighbour additions and $N$ result-buffer zero writes per Tick. Material allocation, navigation, grants, source/observer service, coding, transport, returns and clearing are additional actual work.

Proof. The normalization makes exactly the stated $P$ visits, successes and refusals. Every later growth is one of the $K$ enabled splits. There are $D+1$ batches of $L$ Adds and $D$ intervening Ticks, with no other scalar observation. Hold occurs initially, after each of those Ticks, and after final Reset. Thus the displayed counts are on one actual trajectory. Adds, Ticks, Reset and Holds each acknowledge, giving $L(D+1)+D+1+(D+2)$ fixed field replies. Material and binding counts follow the persistent promotion/split templates; graph size follows Lemma 39.3. A tree with $N$ vertices has $N-1$ edges, so a fresh result vector can be formed by zeroing it and adding each old endpoint into its neighbour once in each directed edge orientation. These are attained source arithmetic counts, not a source-independent physical fee. No initial Reset is hidden in the acquisition: its initial zero field is the original preparation premise and zero-preserving growth. $\square$

**Proposition 43.2 (width, traffic and local arithmetic on this word).** Put

$$
W=2DL(D+1)=2DM.
\tag{NLBAII.64}
$$

Every nonnegative integer source coordinate, literal waveform operand and scalar reply in this acquisition is less than $2^W$, including nonnegative partial Tick sums. In particular their numerical magnitudes need at most $W$ binary bits; their signed rational packet frames and copies cost their full actual lengths. The bounds

$$
D_0\le3L-2,\qquad D\le4L+1,\qquad
K\le1+(L-1)D
\tag{NLBAII.65}
$$

give $O(L^2)$ final material and $O(L^3)$ bits per widest numerical word. They assert no constant-width scalar, total bit-time optimum or uniformly bounded lifetime store.

Proof. At any stage, the field at any vertex is a sum of contributions from a subset of the $M$ input occurrences. Occurrence $(r,j)$ has exponent $H(j-1)+D-r$, distinct for all such pairs, and has been propagated at most $D$ times. Its coefficient is the relevant nonnegative walk count and is at most $3^D<B$. All exponent positions lie in $0,\ldots,M-1$. Thus the whole coordinate, and any partial nonnegative sum in computing it, is at most

$$
\sum_{e=0}^{M-1}(B-1)B^e=B^M-1<B^M=2^W.
\tag{NLBAII.66}
$$

The same exponent bound applies to each input. The positive integer in (NLBAII.58) has exponent $E_{rj}=H(j-1)+D-r$ and exactly $2DE_{rj}+1$ numerator bits. The actual $y$ is a positive integer because every old block has a positive distance coefficient. Its numerator also has at most $W$ bits. Zeroing after the last observation cannot enlarge any magnitude.

The normalized graph has $3L-1$ vertices, so every $\delta_i\le3L-2$. For $i>0$, (NLBAII.51) gives $k_i\le D$, and $k_0=1$. This proves (NLBAII.65) and the sufficient asymptotic bounds.

For explicit literal growth traffic let

$$
\begin{aligned}
G&=\sum_{p\text{ entry logical node}}|p|,
& G_\alpha&=\sum_{p\text{ entry alpha leaf}}|p|,\\
J&=\sum_{i=0}^{L-1}\left(k_i|p_i|+\frac{k_i(k_i-1)}2\right),
& M_g&=2L-1+K.
\end{aligned}
\tag{NLBAII.67}
$$

The original addressed request and reply payloads are respectively $2(G+J)+4M_g$ and $2(G_\alpha+J)+5M_g$ bits, by §17's $2|p|+4$ request, $2|p|+5$ success and five-bit refusal meanings. Every payload additionally pays its actual completion, End, acknowledgement and return costs. The field-input integers are denominator-one reduced rationals. For a positive numerator of bit length $b$, §17's signed self-delimiting numerator and denominator-one encoding has $2b+5$ payload bits, besides the operation tag and raw-label frame. Consequently each of the $M$ inputs pays its own $b=2DE_{rj}+1$, and the sole $y$ pays the same literal rational rule at its actual bit length. Original raw labels use their $O(\log(L+1))$ encodings; the anchor, appended counters and stored indices pay their actual lengths as well. This accounts for transmitted words, not just the number of scalar calls.

One finite implementation constructs an input by computing its finite integer exponent, shifting a one by $2DE_{rj}$ positions and emitting the entire reduced rational frame. It reuses one operand workspace only after the preceding Add and return finish. The decoder performs exactly $M$ successive quotient/remainder extractions by $B=2^{2D}$, and one zero comparison per extracted digit, retaining the first positive index of each of the $L$ blocks. It need not retain a full $L$-by-$(D+1)$ response matrix. With ordinary full-word copying, each shift or quotient/remainder costs its actual at-most-$W$ bit work; $O(MW)$ bit reads/writes suffice for these waveform/digit operations, in addition to counter/exponent arithmetic, literal I/O, source work, graph construction and map/report copies. Counters, index products, comparisons, address concatenations, the $L$ locally computed tree distances and their maximum all pay their actual finite arithmetic and traversal costs. A direct repeated breadth-first traversal computes the required distances on the earned normalized graph using finite indexed adjacency lists, with no source call. No algebraic operation at growing width is declared a unit-cost physical primitive. $\square$

**Definition 43.3 (simultaneous backing, archives and later calls).** During waveform propagation an attained implementation has the actual $N$-cell source field and its separately allocated $N$-cell Tick result buffer, each with up to $NW$ numerical bits in the displayed sufficient representation. These are distinct from the observer's graph, constructor words, raw tables and arithmetic. Local input generation has its operand, exponent and encoding workspace; receipt/decoding has the literal $y$, a quotient copy and digit/comparison scratch. Separate input, output and transport buffers, and any retained response copy, coexist at their actual widths. These stores are counted while live even if some have equal contents. The final retained $N$-coordinate zero predictor is an additional allocation, not the source field or a reused accounting coordinate. A hypothetical nonzero continuation or a speculative predictor copy has its own full vector and work buffer.

The entry code and map archive, mutable current code and indexed material graph, complete current raw bijection, canonical terminal table, per-cone parameters, first-positive indices, traversal stack and addresses, finite program and all pending/completed output backing are simultaneous actual observer material. An indexed graph/table/code layout uses $O(N\log(N+1))$ numerical bits; an explicit copied-address workspace can conservatively use $O(N^2)$ bits. These estimates are additional to the $W$-bit numerical buffers and the actual reference, grant and connection encodings, which have no claimed $N$-only size bound. The acquisition transcript need not be retained after its consumed data are installed. If the caller or producer does retain it or other outputs, their entire actual backing is additional; a short handle does not remove its accessible archive. Clearing or releasing temporary contents after their last use pays every actual write and binding operation; retained cleared capacity remains paid material.

For a chosen implementation reusing a bounded number of packet buffers on the fixed channels and retaining no optional transcript, the two source vectors, separate predictor and all numerical operand/reply/decoding buffers together use $O(NW+W)$ bits. Combining them with the indexed records and explicit address workspaces gives an attained simultaneous $O(NW+N^2)$ numerical backing bound, plus the distinct actual reference, grant, connection and additional retained-output backing just described. The final $N,W$ dominate earlier sizes and widths, so this is a bound on their coexistence, not a sum of peaks from different trajectories. It is not a minimum-space claim. After final Reset an unused Tick buffer can still contain earlier numerical values: it is not an active material field coordinate, remains charged while allocated, and is erased or released only by paid implementation work. Reset itself supplies no erasure theorem for that backing or for observer archives.

The same-run account includes the original root allocation, actual old producer, roster attachment and field preparation. That producer has $c$ promotions and $L-1$ splits from the known alpha, with its actual old address traffic/navigation, grants and $N_0=2L+c-1$ zero field cells; its old word need not be available as a record. Original field/Tick backing, observer initialization and every later output copy are real resources. Subsequent actual raw/canonical use pays every source call, full reply, current-size adjacency computation, rational arithmetic at its attained widths, graph/table update, ordinal lookup, frame and return. Future rational inputs and growth have no uniform finite lifetime bound. A finite instruction program supplies pointwise finite executions with sufficient finite backing, rather than a fixed finite amount of memory for all of them.

## 44. The acquired coordinate minimum and its remaining mathematical boundaries

**Proposition 44.1 (comparison and separation of scopes).** The exact successful-Read minimum in Corollary 41.2 is not a total acquisition optimum, an optimum at a prescribed original endpoint, or a one-Read arbitrary-field/no-Reset entrance. It changes none of the earlier fixed-model or erased-history statements.

Proof. This trajectory makes $D>0$ actual Ticks, $K$ splits and the wide integer inputs of Proposition 43.2, and ends at its own $u$ with $N=3L+2K-1$. The existing integer-age acquisition of Theorem 27.2 makes $L$ Reads, zero Ticks, $L-1$ splits and only $O(\log(L+1))$-bit field values, ending at a different $5L-3$-vertex source. Both are sufficient exact binding acquisitions on the original installation. A minimum in successful Reads supplies no inequalities for their other coordinates or for a caller's different endpoint constraint. Their separately favorable coordinates cannot be combined into a single attained run.

The waveform calculation starts from actual whole-field zero; its final callable zero predictor is established by an actual full Reset. Assumption 34.1 instead permits arbitrary attachment fields and omits Reset. Neither its different entrance theorem nor the same-specimen implication of §37 supplies these waveform premises. The conclusions here therefore assert no one-Read no-Reset result and no fused minimum with that separate entrance or with the binary image of §30.

Old total serialization is also not recovered. The two old legal words (NLBAII.19) have the same entry term, zero field and causal order. Attach the same raw bijection at that common term. They give identical inputs, this entire experiment, both binding reports and all later complete raw futures, although their old third events differ. This preserves Proposition 22.3's erased-history boundary. Whole-zero canonical views still omit the raw permutation and entry/private archives by Application 42.2, and terminal zeros still omit hidden internal fields by Proposition 20.3. A changed initialization, source, task or returned cut proves no statement about an original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization or final-no-Ready obligation that forbids that change. $\square$

**Scope 44.2 (attribution and the four-expression programme).** The source-relative `repo-derived` content of §§39–41 is the actual legal anchor/distance construction, executed packed waveform, exhaustive unknown entry/current raw-binding acquisition and full-original-menu zero-Read exclusion. Its whole-zero continued use and canonical four-expression consequences in §42 are applications of the existing supplied predictor and inverse at this new entrance. The all-$P$ acquisition, birth typing, material lifecycle, first arrivals, root rigidity and causal inverse retain their original authors' mathematics and hypotheses. Ordinary integer expansion and Kronecker packing are mature tools credited in their actual use in Theorem 40.2; no new generic digit theorem, replay/quotient framework or four-view principle is asserted.

The independently meaningful guard-only source encoding/represented service in [AAII §§68–74](https://github.com/the-omega-institute/trureturing/blob/1da4ec9203b30624611f5bdff2b7503472050a45/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md#68-a-recoverable-source-encoding-on-the-original-lab-attachment) uses its $J$ image and guard attachment, without this raw field roster. The known-initialization maintained global history service in [AAII §§75–83](https://github.com/the-omega-institute/trureturing/blob/1da4ec9203b30624611f5bdff2b7503472050a45/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md#75-a-root-bound-global-history-supplement-from-known-initialization) retains its actual annotation and complete original history interface. Neither is an erased arbitrary history inverse or this numerical raw-binding experiment. The [RGII §§59–68](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md) result proves later scalar-origin signed-length conditions and computed lattice/residue consumers on its authentically acquired rational positive-link path with $0<T<\operatorname{Id}$, its own origin and complete outputs. Those operators, ports and task domains are not identified with the present unit branching adjacency by a shared name or a digit expansion. These suppliers are credited rather than counted again as new content. The inspected mathematical correspondences support source-relative attribution, not worldwide priority or a full-corpus absence claim.

Existence of the installed source and its old preparation is a hypothesis; legality of the subsequent displayed construction is proved in Lemma 39.3. Identifiability of the map from the one actual scalar is proved by (NLBAII.61)–(NLBAII.62). Acquisition executes that experiment and finite decoder on the same source. Conditional arithmetic verification of a proposed map under the earned law does not certify authentic binding, full roster, old initialization, fresh-zero allocation, exact calibration, rights or physical conformity. Continued use retains those actual resources and the synchronized full predictor. No inverse creates a missing source reference or permission.

A common actual realization joining unrestricted LAB growth, the original rational-path operations and quantum phase/effect/window sources is still missing, as are the corresponding complete initialization, acquisition, action/output, selector, reference/rights and same-run resource bridges. The exact independent meanings and mutual recovery here remain those of the canonical whole-zero image. No arbitrary rational control-journal inverse, all-busy-cut inverse, noisy physical theorem, universal generator minimum, total runtime/space/material optimum or completion of the full four-expression objective follows. All original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization, final-no-Ready and erased-history scopes remain exact.

## 追加锚（本行以下为增补区）

## 45. An earned root-read installation with a cleared rational preparation

**Definition 45.1 (the root-read task).** Keep AA's logical terms, birth types and guarded $P/S$, NLBA's ordered current-terminal Add interface, and the persistent material/fresh-zero law of §17.3. The field law is still zero-diagonal symmetric unit adjacency. Replace the terminal Read menu by just one nondestructive $\operatorname{Read}_0$, authentically bound to the original material root. It returns that cell's literal rational, with identity successor. Tick returns only its fixed acknowledgement; a root scalar after a Tick requires a separate paid $\operatorname{Read}_0$. Reset, Hold and Add retain their original successors and fixed acknowledgements. There is no other field Read, clone, old-input or response-law port. An out-of-range Add has RangeRefusal and identity successor. The original growth guards, distinct refusal reasons, framing, pending-prefix and disabled-call conventions of §17.2 remain in force.

This installation starts from a known allocated zero $\alpha$ and an earned ordered terminal roster maintained during the actual preparation. It is not acquisition of unknown geometry, an unknown raw permutation or a root right from scalar data. The terminal roster replaces an acted terminal by its new marker after $P$, or by its two consecutive left-to-right terminals after $S$, as in NLBA §§10–13. All references, rooted orientation, dispatcher bindings, current/fresh rights and finite backing are actual retained resources. Exact rational arithmetic, exclusive serialized use, no unrequested evolution or other writer, complete outputs/returns and no observable timing, allocation, capacity or work side channel are premises. Neither a numerical inverse nor a finite test of the law establishes these premises.

For $k\ge1$, set

$$
c=\langle\beta,\beta\rangle,\qquad
T_0=\beta,\qquad T_{j+1}=\langle c,T_j\rangle.
$$

Here and below $e_v$ denotes the unit coordinate at actual material address $v$, and $o=\epsilon$ is the original root. For $1\le i\le k$ define

$$
\begin{aligned}
p_i&=R^{i-1}L,&q_i&=p_iL,&q'_i&=p_iR,\\
z_i&=p_iLL,&z'_i&=p_iRL,&d_i&=i+2,\\
w_i&=e_{z_i}-e_{z'_i},&&Z=[w_1\ \cdots\ w_k].
\end{aligned}
$$

The $p_i$ are disjoint cherries in $T_k$. Their two original terminal markers have depth $d_i$.

**Lemma 45.2 (actual producer for every signed rational input).** Starting at that zero seed, the following successful word builds $T_k$. For $i=1,\ldots,k$, put $r=R^{i-1}$ and perform

$$
P_r;\ S_r;\ S_{rL};\ P_{rLR};
$$

then perform $P_{R^k}$. It uses $2k+1$ promotions and $2k$ splits, has $6k+2$ material vertices and $2k+1$ terminals, and earns their ordered correspondence. For every $a=(a_1,\ldots,a_k)\in\mathbb Q^k$, a provider then performs, in increasing $i$,

$$
\operatorname{Add}(2i-1,a_i);\operatorname{Add}(2i,-a_i),
$$

with no Tick. Its actual field is $Za$. Every zero operand is still an actual completed Add.

**Proof.** At each spine position $r$, the first two events make $\langle\beta,\alpha\rangle$. Splitting its left beta and promoting that split's right alpha make the left subtree $c$; the right spine position is still alpha. The final promotion makes the last spine beta. This proves the term and the successful guards inductively. A promotion adds one vertex and a split adds two, giving $1+(2k+1)+4k=6k+2$. Its logical leaves are the $2k$ cherry betas and the final beta. The maintained roster places $z_i,z'_i$ at $2i-1,2i$. Growth and the initial allocation have supplied only zeros; the two actual Adds therefore establish the displayed field, independently for every coordinate, sign and zero. $\square$

**Definition 45.3 (the cleared handoff).** Before the recovering controller begins, remove or isolate from its accessible state every $a$-dependent provider/input record, operand copy, parser/output buffer, cache, callable archive, selector parameter and observable layout/capacity distinction. Retain $k$, the earned fixed tree and roster, source-independent protocol and framing, and actual callable access/rights/backing. The hidden field $Za$ remains on this same source. The receiver receives no $a$ or old dependent transcript as advice. Isolation and clearing, including authority to perform them, are explicit preparation premises; they are not conclusions of $\operatorname{Read}_0$. Provider input, its reception and work, all clearing and every archive retained elsewhere remain charged to this process. Sufficient finite resources may depend on the actual run, but their size or availability is not an extra receiver observation.

The recovery task is deterministic exact recovery of every $a\in\mathbb Q^k$ from this handoff, with a finite completed report on every input. Adaptive local arithmetic, arbitrary legal field controls, guarded growth, refusals and variable stopping are allowed. An algorithm supplied with an $a$-dependent program, candidate list, resource oracle or uncleared operand does not meet this task.

## 46. Asymmetric growth exposes the hidden amplitudes on the same source

**Lemma 46.1 (the original passive blind directions).** On the fixed original tree $T_k$, every root moment of every $w_i$ vanishes. Common adaptive field experiments using that tree, even with terminal Adds and Reset, cannot recover the arbitrary amplitudes from the cleared handoff.

**Proof.** Swapping the two beta arms of cherry $p_i$ fixes $o$, commutes with the old adjacency and sends $w_i$ to $-w_i$. Thus $e_o^{\mathsf T}A^nw_i=0$ for every $n\ge0$. For two inputs differing only in this direction, a common Add cancels in the field difference, Tick applies $A$, Hold and Read preserve it, and Reset kills it. Root replies agree at every stage, so a deterministic adaptive controller chooses the same subsequent controls. This argument concerns field experiments with the original topology; it does not assert blindness after the asymmetric edits below. $\square$

**Definition 46.2 (one acquisition).** Actually split $q_i$, once for each $i$ in increasing order, with no Tick between these $k$ calls. The old marker $z_i$ becomes the left beta root and the split adds fresh zero vertices

$$
e_i=p_iLLL\ \text{adjacent to }z_i,
\qquad f_i=p_iLR\ \text{adjacent to }q_i.
$$

Let $\iota$ be the persistent old-coordinate inclusion and $B$ the final unit adjacency. The actual field is $\iota Za$, the tree has

$$
N=8k+2\quad\text{vertices},\qquad 3k+1\quad\text{terminals}.
$$

Put $h_i=i+4$ and $H=k+4$. Perform exactly $H$ actual Ticks, with one $\operatorname{Read}_0$ just after each epoch $h_i$, and then Hold. Consume each whole Growth reply, Tick acknowledgement, scalar frame and Hold acknowledgement, including its completed return. The literal chronological scalar list and returned actual field are

$$
y_i=e_o^{\mathsf T}B^{h_i}\iota Za,
\qquad x_{\rm now}=B^H\iota Za.
\tag{46.1}
$$

There is no Reset or rollback in this acquisition.

**Theorem 46.3 (triangular actual observation).** Define the integer matrix

$$
M_{ij}=e_o^{\mathsf T}B^{h_i}\iota w_j.
$$

Then $M_{ij}=0$ for $i<j$ and $M_{ii}=2$. Consequently the actual $k$ scalars in (46.1) recover every rational input by

$$
a_i=\frac12\left(y_i-\sum_{j<i}M_{ij}a_j\right),
\qquad 1\le i\le k.
\tag{46.2}
$$

This includes $a_i=0$ and either sign, without positivity, nonvanishing, separation or bounded-digit assumptions.

**Proof.** An entry of $B^n$ counts length-$n$ walks between its coordinates. For fixed $j$, walks from $o$ to $z_j$ or $z'_j$ that avoid the two new edges of this cherry pair by swapping its two old arms. Edits in other disjoint cherries do not obstruct this pairing. A walk that uses one of this cherry's new edges and ends at $z_j$ has length at least $d_j+2$: an excursion to a new pendant vertex and back costs two beyond the original shortest path. At exactly that length there are precisely two such walks. One takes the detour $q_j,f_j,q_j$ and then finishes the shortest path to $z_j$; the other follows the shortest path to $z_j$ and takes $z_j,e_j,z_j$. Tree uniqueness excludes any other shortest walk or additional detour. A walk using either of these new edges and ending at $z'_j$ has length at least $d_j+4$, since it must return through the cherry junction to the opposite arm. Thus the difference of the two walk counts is zero below $d_j+2$ and is exactly two at $d_j+2=h_j$. With $h_i<h_j$ for $i<j$, the triangular assertions follow. Its nonzero diagonal gives (46.2) over $\mathbb Q$. All its rows are the actually executed reads of Definition 46.2, rather than a counterfactual table. $\square$

The recovered input describes the preparation cut, while the retained source is at $x_{\rm now}$ in (46.1). In particular the last Read and Hold do not undo the preceding Ticks. Every intermediate source field in this acquisition is explicitly $B^r\iota Za$, $0\le r\le H$; every acquisition edit before these Ticks is the corresponding zero extension of $Za$. These formulas give all physical successors as well as the literal replies.

## 47. Four sampled expressions and inverses at the advanced endpoint

**Lemma 47.1 (no input loss at the returned cut).** Put

$$
U=B^H\iota Z,\qquad
\mathcal O_N=\begin{pmatrix}e_o^{\mathsf T}\\e_o^{\mathsf T}B\\\vdots\\e_o^{\mathsf T}B^{N-1}\end{pmatrix},
\qquad F=\mathcal O_NU.
$$

Both $U$ and $F$ have column rank $k$. In particular they have rational left inverses

$$
L_U=(U^{\mathsf T}U)^{-1}U^{\mathsf T},
\qquad L_F=(F^{\mathsf T}F)^{-1}F^{\mathsf T}.
\tag{47.1}
$$

**Proof.** For any $b\in\mathbb Q^k$, $(B\iota Zb)_{e_i}=b_i$, since the fresh $e_i$ has just its old neighbor $z_i$. Hence $B\iota Z$ is injective. For a real symmetric matrix, $\ker B^m=\ker B$ for every $m\ge1$. One elementary proof chooses $2^s\ge m$ and repeatedly uses
$\|B^{2^{s-1}}v\|^2=v^{\mathsf T}B^{2^s}v$ to descend from $B^{2^s}v=0$ to $Bv=0$. Thus $Ub=0$ implies $B\iota Zb=0$, proving the first rank assertion.

Suppose $Fb=0$ and write $v=\iota Zb$. Cayley–Hamilton extends the first $N$ zero moments of $B^Hv$ to all later root moments. Let
$K=\operatorname{span}_{\mathbb R}\{B^re_o:r\ge0\}$. Both $K$ and $K^\perp$ are $B$-invariant by symmetry. The component $v_K$ therefore satisfies $B^Hv_K\in K$ and is orthogonal to $K$; it is zero. The kernel-power identity gives $Bv_K=0$. All positive-time root moments of $v$ now vanish: the $K^\perp$ component never contributes and $Bv_K=0$. In particular $Mb=0$ at the positive epochs $h_i$. Theorem 46.3 gives $b=0$, proving the second rank assertion. For a rational full-column-rank matrix its Gram matrix is positive definite over $\mathbb R$, has a nonzero rational determinant and has a rational inverse. This proves (47.1). No invertibility of $B$ on the full field space is used. $\square$

**Definition 47.2 (independent sampled meanings).** Fix $k$, the earned oriented tree, the preparation order, actual installation and cleared handoff, and the acquisition schedule of Definition 46.2. Consider its returned held cuts as $a$ ranges over all $\mathbb Q^k$. Common context includes this fixed geometry/law/schedule and real access, but no old $a$-dependent advice. The numerical expressions have the following independently specified meanings.

| Expression | Content at its specified cut |
| --- | --- |
| Space | The actual final oriented material tree and its complete present field $x_{\rm now}$ |
| Time | The actual chronological list of $2k$ signed terminal preparation pulses, in the specified alternating order |
| Boundary | The actual paid historical list $y$ of the $k$ root scalars at epochs $h_i$ |
| Memory | The current autonomous root-prediction block $m=(e_o^{\mathsf T}B^rx_{\rm now})_{0\le r<N}$, with the earned model and a callable current-state updater |

Time is this restricted pulse list, including zero pulses, rather than an arbitrary input/control journal. Boundary is historical. Memory is present: its numeric block is locally computed as $m=Fa$ after (46.2), not obtained by free future Ticks or unexecuted Reads. Its updater is initialized by reconstructing the full field from this block; that backing is separately charged. The earlier clearing does not make the actually executed Time cease to exist, but it prevents using its old record as decoder advice. Recovering its numerical pulse list does not authenticate an old transcript or restore an erased physical archive.

**Theorem 47.3 (all numerical routes and image tests).** On the joint sampled image, every expression determines all the other numerical expressions and both the preparation and returned fields. All recovery routes agree. Explicit inverses to the parameter are

$$
\begin{array}{c|c}
\text{Time}&a_i=\text{operand of pulse }2i-1\\
\text{Boundary}&a=M^{-1}y\quad\text{by (46.2)}\\
\text{Space}&a=L_Ux_{\rm now}\\
\text{Memory}&a=L_Fm.
\end{array}
\tag{47.2}
$$

From that unique $a$, the forward maps give the pulse list, $Za$, $y=Ma$, $x_{\rm now}=Ua$ and $m=Fa$. A proposed Space field belongs to the numerical image exactly when $UL_Ux=x$; a proposed Memory block exactly when $FL_Fm=m$. Every rational $k$-list is a numerical Boundary value, since $M$ is invertible. A proposed Time is accepted exactly when it has the stated $2k$ pulse positions and each second operand is the negative of its first. These are finite exact rational tests in the fixed earned context, without a provenance or authority test.

**Proof.** The Time pattern is one-to-one with $a$, Theorem 46.3 proves the Boundary inverse, and Lemma 47.1 proves both present inverses. Each inverse returns the same unique input of the actual run. Factoring any route through it proves every pairwise recovery and every cycle identity, including historical-to-current transport. The left-inverse identities give precisely the stated image tests. $\square$

**Proposition 47.4 (the precise dynamics domain).** Equality of any one of these four numerical expressions is exactly equality of the complete current continuation task within this fixed sampled family and common installed context. The routes agree with the actual preparation/acquisition recurrences and with any later primitive continuation whose ending cut again belongs to that sampled image. All-field continued service remains available when the continuation leaves that image; the restricted Time inverse is not asserted there.

**Proof.** Equal inputs give equal current vectors and trees. The one-step service invariant of §48 then gives every complete future output and successor. If inputs differ, $F(a-a')\ne0$. Some root Read after $r\in\{0,\ldots,N-1\}$ actual Ticks therefore distinguishes the current fields. These are paid possible future calls, not additional replies in the acquisition bill. The preparation Adds, zero-extension edits and Tick powers already prove the forward recurrences at every cut. Uniqueness in (47.2) makes any transport ending in the sampled image agree with its inverse. General Reset, Add, growth or a different Tick schedule need not end in that image, and may erase old preparation information. The full field updater, rather than a fictitious history inverse, serves such successors. $\square$

## 48. Retention and complete same-binding service

**Theorem 48.1 (a full current-state consumer).** At the returned cut of §46 retain the earned current logical term, ordered roster and material correspondence, full exact predictor $\widehat x=Ua$, matching parser/context, genuine callable root reference, current authority and work/output backing. Forward each admitted request to that same source. After consuming its whole reply and return, commit the matching record successor before the next settled request. For every sufficiently backed finite common adaptive continuation in Definition 45.1's full menu, this consumer predicts and delivers every declared output and has exactly the corresponding actual successor.

**Proof.** Maintain equality of each predictor coordinate with its actual persistent material cell, together with equality of logical term, ordered roster and parser state. The complete cases are:

| Request/event | Actual and retained successor | Complete output |
| --- | --- | --- |
| $\operatorname{Read}_0$ | identity | literal $\widehat x_o$ |
| Tick | $\widehat x\leftarrow A_u\widehat x$ on the current tree $u$ | fixed Tick acknowledgement |
| valid Add$(j,q)$ | $\widehat x\leftarrow\widehat x+qe_{\lambda(j)}$ | fixed Add acknowledgement |
| Reset | all current coordinates zero | fixed Reset acknowledgement |
| Hold | identity | fixed Hold acknowledgement |
| successful $P_p$ | old cells retained, fresh $pL$ zero; update term/roster | original Growth$(P,p)$ |
| successful $S_p$ | old cells retained, fresh $pLL,pR$ zero; update term/roster | original Growth$(S,p)$ |
| absent/branch/wrong-type growth refusal | identity | its distinct original tagged refusal |
| out-of-range Add | identity | RangeRefusal |
| complete malformed frame | identity of settled source state | BadFrame |
| proper incomplete frame | retain matching pending input/parser state | no complete output; wait |
| absent right or wrong phase | request disabled | no invented refusal |

The earned term computes exactly the original guards. The maintained binding identifies exactly the current actuator cell and the correctly replaced roster entries. The actual persistent templates prove the two growth rows. The other enabled rows are the installed field equations. Thus every one-step successor and complete output agrees. Incomplete frames require real pending storage; they are not completed identity calls. Disabled requests are not converted into actions by arithmetic. Induction at completed cuts, and through the common parser transitions between them, proves the finite adaptive claim. A future selector must be common, including any fixed supplied common random tape; private unequal archives need not select common calls. Current genuine rights and physical forwarding are essential, and are not produced by (47.2). $\square$

The Memory block of §47 is sufficient to initialize this consumer on the sampled image, since it determines $a$ and $Ua$. After general controls the consumer retains the whole current field and updated tree. No claim says that a fixed-length root block remains sufficient for every arbitrary field after arbitrary growth. There is no terminal Read in this root-read installation. The original terminal service used in §§51–53 is a different installation.

## 49. Two selected adaptive lower bounds attained together

**Theorem 49.1 (successful scalar Reads).** Every deterministic exact recovery protocol of Definition 45.3 makes at least $k$ successful $\operatorname{Read}_0$ calls on every terminating input transcript.

**Proof.** Fix a completed transcript at input $a$ and freeze every control, operand, chosen address, parser decision and stopping decision along it. On this frozen path the actual current field is an affine rational function of the original parameter: Add is a fixed translation, Tick linear, growth a fixed zero extension, Reset zero, and all other completed steps identities. Each of its $r$ successful Reads therefore supplies one affine rational equation in $a$. If $r<k$, their common homogeneous kernel contains a nonzero rational $b$. The different input $a+b$ satisfies all those equations. By induction it produces the same Read replies, fixed acknowledgements, topology-dependent guards/refusals and parser behavior, hence the same adaptive choices and the same terminating report. The receiver's cleared source-independent initial state and absence of side channels are used in this induction. The common report cannot equal both distinct inputs. This contradicts exact recovery. A report made before an abandoned scalar frame is completed is not a completed recovery transcript in this task. $\square$

**Theorem 49.2 (successful acquisition splits).** Every such protocol must make at least one successful split inside each original cherry $p_i$ before terminating, and hence at least $k$ successful acquisition splits and $2k$ fresh material vertices after the handoff.

**Proof.** Suppose a terminating transcript leaves one original cherry without a successful internal edit. Compare $Za$ with $Za+tw_i$, that is, replace just $a_i$ by $a_i+t$ for a fixed nonzero rational $t$. On this transcript the original arm swap remains an automorphism of every current tree: all successful edits lie outside this cherry, while unsuccessful internal calls change nothing. It fixes the root. Until a Reset the difference evolves in its antisymmetric subspace under Tick; common Adds cancel. A Reset erases the difference permanently and cannot reveal it. All root replies therefore agree. Guards and all other completed outputs also agree, so the alternative input follows the same transcript and stopping rule. Exact recovery is impossible.

In an original cherry the branch $p_i$ cannot be successfully edited and its markers are not logical growth targets. The two logical leaves $q_i,q'_i$ are beta. The first possible successful internal edit must thus be $S$ at one of them. The $k$ cherries are disjoint; a single such split cannot be first internal edit in two cherries. Each split creates two fresh vertices. This proves both bounds, even if the protocol also uses promotions, other growth, Add or Reset. $\square$

**Corollary 49.3 (one simultaneous attainment).** The actual run of §§45–46 attains these two selected bounds jointly: exactly $k$ successful root Reads and $k$ acquisition splits, with exactly $2k$ acquisition-created vertices.

The quantifiers are those of the cleared arbitrary-$\mathbb Q^k$ task, not a finite candidate promise. These are separate Read and acquisition-split lower bounds attained by one construction. They imply no minimum for Ticks, source preparation, bit work, precision, observer storage, total traffic or total resources. Under the original terminal-Read interface the already known $z_i$ can be read directly in $k$ calls with no acquisition split. No claim of a cheaper original-leaf implementation follows from replacing its interface and preparation conditions.

## 50. The root experiment's simultaneous operation, traffic and storage account

**Proposition 50.1 (one complete run).** Include the actual seed construction, signed preparation, cleared handoff and precisely Definition 46.2's acquisition, with no optional later continuation. The exact source-operation totals are

| Stage | $P$ | $S$ | Add | Tick | $\operatorname{Read}_0$ | Hold | Reset |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Known-zero construction | $2k+1$ | $2k$ | $0$ | $0$ | $0$ | $0$ | $0$ |
| Signed preparation | $0$ | $0$ | $2k$ | $0$ | $0$ | $0$ | $0$ |
| Acquisition and final cut | $0$ | $k$ | $0$ | $k+4$ | $k$ | $1$ | $0$ |
| Total | $2k+1$ | $3k$ | $2k$ | $k+4$ | $k$ | $1$ | $0$ |

There are $5k+1$ successful Growth replies, $3k+5$ fixed field acknowledgements, and exactly $k$ scalar replies $y_1,\ldots,y_k$. Thus $9k+6$ complete source calls/replies/returns occur. Source growth allocates $8k+1$ fresh vertices beyond the seed and leaves $N=8k+2$ live vertices; it leaves no frozen-topology historical copy of that source. The source's $H$ advanced fields and the decoded current predictor refer to this same specimen.

**Proof and addressed costs.** The first row is Lemma 45.2 and the last acquisition row is Definition 46.2. All preparation Adds, including zeros, are counted. At spine stage $i$, the four event-address depths sum to $4i-1$; the tail event has depth $k$. The construction depth sum is $2k(k+1)$. Acquisition depths sum to $k(k+3)/2$. For the complete successful event word put

$$
E_g=5k+1,\qquad D_g=\frac{5k^2+7k}{2}.
$$

Using AA's original three-bit tag and $1^{|p|}0p$ address framing, the growth request payload total is $2D_g+4E_g=5k^2+27k+4$, and the Growth reply payload total is $2D_g+5E_g=5k^2+32k+5$. Each still has its full End/acknowledgement/return lifecycle. Root-based navigation pays $D_g$ descents and $D_g$ ascents in the parent-return implementation. AA's three-reference-field material implementation has $3+4(2k+1)+8(3k)=32k+7$ structural reference assignments including seed initialization. Fresh field initialization, arithmetic, dispatcher/roster changes, grants, allocations and communications are additional actual operations. $\square$

**Definition 50.2 (literal precision and one stored implementation).** For a nonnegative integer $n$, let $b(n)$ be its binary length, with $b(0)=1$. A reduced rational $q=n/d$, $d>0$, has literal payload length

$$
\ell(q)=2b(|n|)+2b(d)+3
\tag{50.1}
$$

in §17.2's encoding. A terminal selector $j$ has $2b(j)+1$ bits. Thus the $2k$ Add operands cost $2\sum_i\ell(a_i)$ bits, and their selectors cost
$\sum_i(2b(2i-1)+2b(2i)+2)$ bits, besides their fixed tags and complete framing/returns. Root Reads use the fixed original-root binding, without a hidden coordinate payload. Their scalar payload total is exactly $\sum_i\ell(y_i)$. All field acknowledgements have their fixed actual frame lengths; packet copying, decoding and cleanup cost actual bit operations. A scalar equal to zero still has a complete literal encoding and reply.

For an explicit finite layout, compute and retain the matrices $B,\iota Z,M,U,\mathcal O_N,F,L_U,L_F$ and the two $k$-Gram matrices and elimination work, together with $y,a,x_{\rm now},m$. Allocate source two-vector backing of $2N$ rational slots, and an observer arena of

$$
C_A=12N^2+12Nk+16k^2+8N+8k+16
\tag{50.2}
$$

numeric slots. These deliberately sufficient capacities accommodate the listed dense matrices, simultaneous old/new matrix/vector work and augmented elimination arrays; reserved slots are actually allocated and initialized, not a claim of used-slot minimality. Fixed source-independent matrices may be constructed from the earned topology while held, without using hidden amplitudes. Store the earned syntax, explicit material/terminal correspondence, mutable addresses, counters, fixed code/framing, actual reference/rights and all live I/O buffers as separate literal records. A simple explicit-address representation has $O(N(k+1))$ address bits here; counters/selectors pay their actual binary widths. Provider input reception and preparation use their own backed operand records. Clear receiver-accessible dependent copies before the handoff; if a provider archive is isolated but retained, its cells/widths coexist in the total bill. Outputting the recovered pulse list, matrices or vector creates additional literal copies whenever actually retained.

**A concrete input/clearing layout.** One compatible provider stores the canonical input list in a private buffer of

$$
C_{\rm in}=2b(k)+1+\sum_{i=1}^k\ell(a_i)
$$

payload bits, besides its complete reception framing. It uses one reusable outgoing Add-frame buffer of capacity $C_{\rm req}$, at least the maximum actual framed Add length in this run, and a fixed-capacity ACK buffer $C_{\rm ack}$. These capacities and the provider are inaccessible to the recovering receiver. The provider reads each operand from the input buffer, serializes its first-listed and negated requests in order, and consumes both complete ACKs. Negation changes the numerator sign with canonical zero handling; it does not ask the source for an input. After each of the $2k$ complete Add returns, overwrite the entire outgoing and ACK buffers, including any unused old suffix. At final handoff overwrite the entire input buffer and its input-dependent control registers. Keep no provider transcript archive. If those registers occupy $C_{\rm ctl}$ bits and the other accessible transport/parser/copy buffers cleared along the whole preparation occupy a total of $C_{\rm chan}$ overwritten bits, this particular implementation performs exactly

$$
C_{\rm clear}=C_{\rm in}+2k(C_{\rm req}+C_{\rm ack})
                 +C_{\rm ctl}+C_{\rm chan}
$$

bit overwrites for that erasure, in addition to input reception, serialization and all ordinary arithmetic/copy work. The channel term counts every actual copy separately and is zero only for genuinely absent copies. Complete request/reply framing is included in the corresponding buffer capacities, not identified with operand payload. Input reception writes at least $C_{\rm in}$ payload bits, preparation sends the exact operand and selector payloads above, and all its packet transmissions and returns remain actual traffic. Erased arenas still physically retained, their capacities, private input reception backing and any external unerasable input storage remain material resources; clearing means no accessible dependent contents or capacity channel, not free memory reclamation. This gives an explicit paid way to meet Definition 45.3 conditional on its isolation/clearing authority. It does not derive that authority from the numerical experiment.

The recovery itself emits the canonical $k$-list $a$ as its completed local report, with $C_{\rm in}$ payload bits in that same list encoding and its own full framing/return. This is additional report traffic beyond the source replies of Proposition 50.1. Its live outgoing/copy buffers and eventual cleanup are charged. Exporting the reconstructed $2k$-pulse Time, full Space or prediction block would be additional literal output, rather than another native source observation.

**Proposition 50.3 (finite work and exact-width scope).** This stored implementation has finite exact rational work and finite simultaneous backing on every input. Let $W_A\ge1$ be the actual largest binary width of any integer numerator, denominator, counter, product, elimination intermediate, parser length or input/output integer in this implementation. A conservative arithmetic bound for its matrix construction, all displayed inverses and vector transport is

$$
O\big((H+N+1)(N+k+1)^3\big)
\quad\text{rational operations},
$$

with conservative school bit work $O((H+N+1)(N+k+1)^3W_A^3)$, plus actual framing, addressing, allocation, clearing and output work. The numerical arena and two source vectors require at most $O((C_A+2N)W_A)$ value bits, with the separately listed structural, provider, code/access and I/O backing added. These are one implementation's upper bounds, not joint optima.

**Proof.** Repeated finite matrix multiplication forms the powers/rows and columns; rational elimination on the proved nonsingular matrices forms (47.1), and forward substitution gives (46.2). The stated conservative operation bound covers those dense products and solves as well as the $H$ source and predictor advances. One sparse source Tick may instead initialize $N$ new coordinates and make $2(N-1)$ directed neighbor additions; executing a separate predictor Tick pays its own work. This does not reduce the matrices or storage already chosen for the displayed stored realization.

For an independent precision envelope, let $D$ be the least common multiple of the positive input denominators and let $K=\max(1,\max_i|Da_i|)$. Every source coordinate during preparation, growth and epoch $r$ has denominator dividing $D$ and an unreduced numerator of absolute value at most $3^rK$, because every current degree is at most three. Thus the literal current source width is bounded using $b(D)$ and $b(K)+\lceil H\log_2 3\rceil+1$. The matrix entries are integers before Gram inversion; walk counts give $|M_{ij}|,|U_{vi}|\le2\cdot3^H$ and $|F_{ri}|\le2\cdot3^{H+N-1}$. Inverse/solver denominators and all intermediate widths remain included in $W_A$, rather than silently identified with source-cell width. All arrays and finite arithmetic terminate under the finite backing premise. There is no bound uniform over arbitrary rational input widths, no fixed-precision/noise claim, and no use of a small scalar dimension as a total-memory bound. $\square$

## 51. One-growth separation through the original first terminal

**Definition 51.1 (the unchanged original installation).** Here return to the original ordered-terminal interface of NLBA §§10–13: Add$(j,q)$ and Read$(j)$ use the current left-to-right terminal roster, Tick applies unit zero-diagonal adjacency and returns a fixed acknowledgement, Reset zeros the field, and Hold is identity. There is no $\operatorname{Read}_0$ replacement. All $P/S$ guards, persistent zero extension, full replies, range/malformed/pending/disabled semantics and actual binding/authority/backing premises remain those of that original installation. Earned ordered geometry and a maintained roster are assumed; arbitrary unknown raw labels have not become free addresses.

Fix any earned $t\in\mathcal D$ with $L\ge3$ terminals. Let $N=|V(C(t))|$, $I=N-L$, $A=A_t$, and let $e$ be its original first terminal. Fix every pair of distinct rational fields $x,y\in\mathbb Q^N$ on this same tree. The selection algorithm below owns both candidate vectors and the earned tree. It is not given an arbitrary unknown field through those candidate records.

For each original terminal $z\ne e$ define the one legal edit $g_z$: if $z$ is an alpha logical leaf, use $P_z$; if $z=vL$ is a beta marker, use $S_v$. Write $B_z$ for the resulting adjacency, $\iota_z$ for the persistent zero lift, and

$$
\kappa_z=\operatorname{dist}_{C(t)}(e,z)+1.
$$

Editing this nonfirst terminal preserves $e$ as the current first terminal. For $0\le j\le I$ define complete experiment words

$$
\begin{aligned}
V_j&=\operatorname{Tick}^{j};\operatorname{Read}(1),\\
W^+_{z,j}&=\operatorname{Tick}^{j};g_z;
                 \operatorname{Tick}^{\kappa_z+1};\operatorname{Read}(1),\\
W^-_{z,j}&=\operatorname{Tick}^{j+1};g_z;
                 \operatorname{Tick}^{\kappa_z};\operatorname{Read}(1).
\end{aligned}
\tag{51.1}
$$

Every Tick and Growth output is consumed; each word has exactly one successful scalar Read, of this original first terminal. These are alternative experiments starting at the same declared cut, not a single physically executed table and not parallel cloned sources.

**Lemma 51.2 (an edit/Tick commutator with a literal first-terminal test).** For every $q\in\mathbb Q^N$,

$$
e_e^{\mathsf T}B_z^{\kappa_z}(B_z\iota_z-\iota_zA)q=q_z.
\tag{51.2}
$$

Consequently the difference of the two alternative scalar functions in (51.1) is

$$
w^+_{z,j}(q)-w^-_{z,j}(q)=(A^jq)_z.
\tag{51.3}
$$

**Proof.** In the promotion case a single fresh vertex $a=zL$ is attached to $z$. In the split case the old marker $z=vL$ persists and fresh vertices $a=zL$ and $b=vR$ are attached to $z$ and $v$, respectively. Old-old edges are unchanged. Directly applying adjacency to an old field with fresh zeros gives

$$
(B_z\iota_z-\iota_zA)q=
\begin{cases}
q_z e_a,&g_z=P_z,\\
q_z e_a+q_v e_b,&g_z=S_v.
\end{cases}
\tag{51.4}
$$

The unique path from $e$ to $a$ has length $\kappa_z$. Hence its length-$\kappa_z$ walk count is exactly one. In the split case $e$ is outside the old beta cone, so
$\operatorname{dist}(e,b)=\operatorname{dist}(e,z)=\kappa_z-1$. A tree is bipartite and its adjacency has zero diagonal; walks to $b$ therefore have the parity of $\kappa_z-1$, not $\kappa_z$. Its length-$\kappa_z$ count is zero. Substitution in (51.4) proves (51.2), including its sign. The two actual scalar functions are

$$
w^+_{z,j}(q)=e_e^{\mathsf T}B_z^{\kappa_z+1}\iota_zA^jq,
\quad
w^-_{z,j}(q)=e_e^{\mathsf T}B_z^{\kappa_z}\iota_zA^{j+1}q.
$$

Subtract them and apply (51.2) to $A^jq$. No source experiment performing that subtraction or undoing an edit is part of the identity. $\square$

**Theorem 51.3 (the explicit finite separating family).** The $(I+1)(2L-1)$ indexed experiments in (51.1) separate every distinct rational pair $x,y$ on the earned original tree. From owned candidates $x,y$, a finite exact selector chooses one experiment whose actual Read(1) values differ. Executing only that choice uses at most one successful growth and at most $2I+3$ Ticks, and reads only the original first terminal.

**Proof.** We use the all-leaf forcing result of §31.1 and NLBA §3.2 as a supplier. In its present coordinates, if $J$ has the terminal unit columns, then

$$
K=[J,AJ,\ldots,A^IJ]\quad\text{has rank }N.
\tag{51.5}
$$

The hypotheses are exactly a finite native material tree, unit nonzero edges and all its terminal leaves. With $L\ge3$ the material root is a branch, so the rooted terminal set is also the set of all degree-one vertices. For clarity, the supplied forcing argument starts with all terminal coordinate rows. A deepest unforced vertex has a forced child whose other neighbors are already forced. Its adjacency row expresses that one remaining neighbor's coordinate as its row multiplied by $A$, minus its other known neighbor rows. At most $I$ internal vertices are added, so all resulting rows belong to the span of terminal rows times $A^j$, $0\le j\le I$. This is precisely (51.5), rather than a new general observability theorem.

If all the experiment scalars agree on $x,y$, the $V_j$ give $(A^j(x-y))_e=0$. Equality of both $W^+_{z,j}$ and $W^-_{z,j}$, combined with (51.3), gives $(A^j(x-y))_z=0$ for every other terminal. Equation (51.5) now gives $x-y=0$, a contradiction. Thus a differing experiment exists. Enumerate the finite list in a fixed order, compute its two exact rational scalar predictions from the owned candidates, and choose the first difference. This finite selector needs neither a hidden-field oracle nor an actually observed alternative table.

The path joining two distinct leaves contains only internal vertices between them, so its length is at most $I+1$. Thus $\kappa_z\le I+2$, and either $W$ has $j+\kappa_z+1\le2I+3$ Ticks and exactly one successful growth. A $V_j$ has $j\le I$ Ticks and no growth. The roster argument in Definition 51.1 makes their only Read exactly Read(1) at the persisting original $e$. $\square$

**Proposition 51.4 (actual selected acquisition under the pair promise).** Suppose the actual starting field is promised to be one of the owned distinct candidates $x,y$. Execute the selected word of Theorem 51.3 on that one actual source. Its single literal scalar identifies which candidate was present. At its completed return retain the actual advanced field

$$
\begin{array}{c|c|c}
\text{selected word}&\text{current tree}&\text{actual field for starting }q\in\{x,y\}\\ \hline
V_j&t&A^jq\\
W^+_{z,j}&g_z(t)&B_z^{\kappa_z+1}\iota_zA^jq\\
W^-_{z,j}&g_z(t)&B_z^{\kappa_z}\iota_zA^{j+1}q.
\end{array}
\tag{51.6}
$$

Keep the real binding, current rights, earned updated roster and full field at this cut. They provide complete original-menu continued service.

**Proof.** All selected Ticks and the selected successful growth have the exact ACK/Growth outputs in the original menu. Their intermediate successors are their corresponding prefix products and persistent zero lifts. The final scalar is one of two proved unequal rational numbers, so its comparison selects the correct $q$, after consuming the complete scalar frame. Formula (51.6) then initializes the exact current vector. The coordinate/term/roster invariant of §48 applies with Read$(j)$ returning the literal current terminal coordinate, range refusal also covering Read, and no root Read port. All other rows, including complete framing, guards, Zero Reset, disabledness and forwarding/return, are the original ones. Its induction gives every subsequent full output and successor, on this actual advanced specimen. $\square$

This is pair discrimination with paid candidate advice. It supplies neither exact acquisition of every unknown $q\in\mathbb Q^N$ from one scalar nor actual observations of all $(I+1)(2L-1)$ alternatives. In particular, subtracting the two scalar functions in (51.3) is a proof of separation, not a legal cloning or reset-to-the-old-field operation. Executing one selected route does not leave the other routes available at the original cut. The rank statement (51.5), the full-menu field-necessity result of §32 and the usual predictive-quotient implication are suppliers; the additional conclusion is the explicit first-terminal, one-growth, bounded-Tick family with its actual selected endpoint.

## 52. A paid passive-equality pair with a concrete active successor

**Definition 52.1 (two actual preparations and a passive window).** From the allocated zero alpha seed actually perform

$$
P_\epsilon;S_\epsilon;P_R;S_R;P_{RR}.
\tag{52.1}
$$

The resulting term is $t=\langle\beta,\langle\beta,\beta\rangle\rangle$, with eight material vertices, $L=3$, $I=5$, and first terminal $e=LL$. In one run perform Add$(2,1)$; Add$(3,-1)$; Tick. In the comparison run perform Add$(2,0)$; Add$(3,0)$; Tick. The fields at these cuts are respectively

$$
\delta=e_{RL}-e_{RR},\qquad 0.
\tag{52.2}
$$

Now actually perform Hold; Read(1), followed by eight repetitions of Tick; Hold; Read(1). This is a paid nine-scalar passive window, not just a proposed set of tests. Then actually perform

$$
S_{RL};\operatorname{Tick}^{6};\operatorname{Read}(1);\operatorname{Hold}.
\tag{52.3}
$$

**Theorem 52.2 (passive equality and explicit active distinction).** Both passive windows consist of nine literal zeros with the same declared fixed outputs and unchanged topology. At their ends the fields are again $\delta$ and zero. The active Read in (52.3) is respectively one and zero. On the nonzero run its actual final full field, in the explicitly ordered coordinates

$$
(\epsilon,L,LL,R,RL,RLL,RLLL,RLR,RR,RRL),
$$

is

$$
(8,0,1,0,22,0,9,0,7,0).
\tag{52.4}
$$

On the zero run the actual final field is zero. Both final terms are
$\langle\beta,\langle\langle\beta,\alpha\rangle,\beta\rangle\rangle$ with ten material vertices. Retaining either exact current field and its earned roster gives the complete original service, not a historical rollback.

**Proof.** Before growth, $A\delta=e_{RLL}-e_{RRL}$ and $A^2\delta=\delta$. The right-arm interchange fixes the original first terminal $LL$ and negates both alternating fields. Thus every passive first-terminal moment is zero, not merely the nine sampled ones. Eight actual Ticks return $\delta$; the comparison zero field stays zero. The initial preparation Tick gives (52.2) by the same adjacency equations.

After $S_{RL}$, let $B$ be the new adjacency and $\iota$ the old lift. Its new edges are $RLL$--$RLLL$ and $RL$--$RLR$. In the coordinates of (52.4), direct neighbor-sum recurrence gives the following sparse fields; omitted coordinates are zero:

| Epoch after the split | Nonzero coordinates of $B^r\iota\delta$ |
| --- | --- |
| $0$ | $RL:1,\ RR:-1$ |
| $1$ | $RLL:1,\ RLR:1,\ RRL:-1$ |
| $2$ | $RL:2,\ RLLL:1,\ RR:-1$ |
| $3$ | $R:1,\ RLL:3,\ RLR:2,\ RRL:-1$ |
| $4$ | $\epsilon:1,\ RL:6,\ RLLL:3$ |
| $5$ | $L:1,\ R:7,\ RLL:9,\ RLR:6$ |
| $6$ | $\epsilon:8,\ LL:1,\ RL:22,\ RLLL:9,\ RR:7$ |

Each row follows by summing the preceding row at the listed tree's neighbors; this proves all intermediate successors and (52.4). Equivalently the first unpaired length-six walk from $LL$ to the old positive $RL$ takes the new $RL,RLR,RL$ excursion. The corresponding negative endpoint and the deeper new edge require at least eight steps. Read(1) therefore returns the displayed $LL$ coordinate one. The zero-lifted zero comparison remains zero under every Tick. Growth, Tick and Hold have their original fixed outputs; Read is nondestructive. The full-field service induction then starts at the fields just computed. $\square$

**Proposition 52.3 (the complete witness bill).** Each of these two full runs, from its own known zero seed through final Hold, has exactly

$$
P=3,\quad S=3,\quad\mathrm{Add}=2,\quad\mathrm{Tick}=15,
\quad\mathrm{Read}=10,\quad\mathrm{Hold}=10,\quad\mathrm{Reset}=0.
\tag{52.5}
$$

There are six Growth replies, 27 fixed field acknowledgements and ten literal scalars: nine zeros followed by one on the nonzero run, and ten zeros on the comparison run. Each of the 43 calls has its complete framing and return. Growth creates nine vertices beyond the seed. The six growth-address depths sum to six, giving 36 growth request payload bits and 42 Growth reply payload bits in AA's address framing. The three-reference-field construction makes $3+4\cdot3+8\cdot3=39$ structural reference assignments; field initialization, Tick arithmetic, roster/navigation, grants, input preparation and I/O remain additional paid work.

**Proof.** Word (52.1) has three promotions and two splits. Preparation has two Adds and one Tick. The passive window has eight Ticks, nine Holds and nine Reads. Word (52.3) adds one split, six Ticks, one Read and one Hold. Adding these gives (52.5) and $2+15+10=27$ field acknowledgements. The event depths in order are $0,0,1,1,2,2$, so the address and structural formulas apply. No alternative passive or active run is charged as a second observation of one source. $\square$

**Proposition 52.4 (what equality does and does not identify).** At the pre-active cuts of these two runs, Space as actual geometry plus full field differs; structural Time as the native causal event order of (52.1) agrees; passive Boundary as the actual nine-scalar window agrees. Any self-contained Memory that predicts the growth experiment (52.3) must distinguish the two fields. Thus structural generation Time and passive first-terminal Boundary cannot recover full Space or growth-task Memory on this original rational-field domain.

**Proof.** The geometry, growth word and its AA causal order are common. The nonzero field $\delta$ differs from zero, while Theorem 52.2 gives equal passive windows and unequal actual active replies. A self-contained predictor with the same record and same request word could give only the same prediction, contradicting those replies. $\square$

These equalities concern the structural-generation and passive-observation projections. The two complete preparation transcripts are unequal, since their Add operands differ. No erased-advice premise or equality of all provider memories is inferred for this witness. Even granting the whole passive first-terminal stream would not distinguish these particular fields; granting the full alternative growth experiment table would be a stronger port than that passive stream. This witness does not contradict §47's four-way inverse, whose root port, prepared image and asymmetric acquisition are different.

## 53. Predictive records, field preparation and the selected experiment's bill

**Proposition 53.1 (precisely scoped predictive necessity).** For fixed earned $t$, a self-contained record sufficient to predict every experiment in (51.1) for every $x\in\mathbb Q^N$, using common source-independent code/context and without querying the source or a dependent archive during prediction, is injective as a function of $x$. If the numerical part of that record is a linear map $R:\mathbb Q^N\to\mathbb Q^m$ with common remaining context, then $m\ge N$.

**Proof.** Equal records would give equal predicted scalar outputs for every fixed word. Theorem 51.3 separates distinct fields, so record equality implies field equality. In the linear case the kernel is zero, and rank-nullity gives $m\ge N$. This is the standard predictive-quotient/rank consequence applied to the narrower explicit family, not a new generic full-menu lower bound. $\square$

There is no lower bound here on the number of unrestricted nonlinear rational registers: the countable set $\mathbb Q^N$ admits set-theoretic one-register encodings with unbounded width, and an encoding's actual arithmetic/decoding/storage would require its own account. There is no automatic bit lower bound without a finite input/precision class. In the finite owned-pair service of Proposition 51.4, a candidate tag plus the two paid vectors can suffice; this does not challenge the all-field statement or make those vectors free. A device that forwards future source calls is an actual service, but it is not a source-independent predictor of their replies before making those calls.

**Proposition 53.2 (every field has a paid original preparation).** If an actual known-zero original tree $t$ has been built with its earned roster, every $q\in\mathbb Q^N$ can be prepared using only original terminal Adds and Ticks, without Reset or an interior actuator. Choose a rational right inverse $C$ of $K$ in (51.5), partition

$$
Cq=(g_0,\ldots,g_I),\qquad g_j\in\mathbb Q^L.
$$

Add the $L$ coordinates of $g_I$ at their actual terminals. Then repeat Tick followed by all $L$ Adds of the next block, in descending block order through $g_0$. The actual endpoint is $q$, with exactly $I$ Ticks and $L(I+1)$ Adds, including zeros.

**Proof.** The successive fields are the finite Horner recurrence. At the end they equal
$Jg_0+AJg_1+\cdots+A^IJg_I=KCq=q$. All actuators are earned original terminals and every scalar operand is owned by this producer. Their ACKs, input acquisition, exact rational solves and literal widths are paid. The existence and rational construction of $C$ follow from the already supplied full row rank, by finite pivot selection/elimination. This is reachability with owned target input, not observation of an unknown current field. $\square$

If this producer is used, count its actual seed construction and input reception as well. A term with $b$ beta leaves and $L$ total logical leaves has a legal successful original preparation with $b$ promotions and $L-1$ splits, material size $2L-1+b=N$ and fresh allocation $N-1$ beyond the seed. Its particular addressed word and each full completion remain in the bill. Proposition 53.2 then adds its own $L(I+1)+I$ fixed field acknowledgements. Neither this optional owned-target producer nor the distinct concrete witness of §52 is an extra free stage of every pair experiment.

**Proposition 53.3 (one selected route, with its actual outputs).** For the selected actual experiment at starting field $q$, the exact operation and endpoint account is:

| Choice | Tick | Successful growth | Read | Complete output and endpoint |
| --- | ---: | ---: | ---: | --- |
| $V_j$ | $j$ | $0$ | $1$ | $j$ Tick ACKs; scalar $(A^jq)_e$; field $A^jq$ |
| $W^+_{z,j}$ | $j+\kappa_z+1$ | $1$ | $1$ | its Tick ACKs, one original Growth reply, scalar $w^+_{z,j}(q)$; first $W$ endpoint in (51.6) |
| $W^-_{z,j}$ | $j+\kappa_z+1$ | $1$ | $1$ | its Tick ACKs, one original Growth reply, scalar $w^-_{z,j}(q)$; second $W$ endpoint in (51.6) |

No Add, Reset, extra terminal Read or Hold occurs within these selected words. With no autonomous motion, the returned settled cut permits finite local work without an additional source call; if a separate Hold is actually used, count its ACK and backing as one additional call. A selected promotion allocates one fresh vertex, a selected split two; each has the addressed payload and lifecycle of the original dispatcher. Only the selected route's field arithmetic and output are physically executed. The alternatives' computation is finite local selector work on the owned candidates.

One explicit selector streams through the finite indexed list, propagates each candidate through that word's known matrices, compares the two predicted scalars, retains the first differing word/values and releases its scratch. With

$$
F_B=(I+1)(2L-1),\qquad D_B=2I+3,
$$

a conservative dense computation uses $O(F_B(D_B+1)(N+2)^3)$ rational operations for all trials; a sparse implementation can use less. The current source has at most $N+2$ cells. A sufficient concrete stored layout comprises two source vectors of $N+2$ rational slots each and an observer arena of

$$
C_B=12(N+2)^2+16(N+2)+16
$$

numeric slots for the owned two $N$-vectors, old/new adjacency and candidate-propagation scratch, selected predicted replies, actual decoded current vector and its update scratch. Reserve and initialize these capacities as part of this implementation. The list is generated by counters rather than stored as a physical table of source replies. Add actual term/roster/address records, code/parser, genuine references/rights, request/reply/output copies, provider inputs and every retained archive; coordinate labels are not zero-cost pointers.

Let $W_B$ be the actual maximum binary width of all integers in these rational entries, arithmetic intermediates, counters and input/output encodings. Conservative school bit work for this selector is $O(F_B(D_B+1)(N+2)^3W_B^3)$ plus actual source work, navigation, framing and copying; numerical value backing is $O((C_B+2(N+2))W_B)$ bits with the listed other records added. Every chosen scalar and operand has its literal length (50.1), and every chosen address pays its own length. During a selected route from $q$, a common denominator $D_q$ of its coordinates remains a common denominator, and if $K_q=\max(1,\max_v|D_qq_v|)$, source numerator magnitudes after $r$ Ticks are at most $3^rK_q$. Growth supplies zeros and degrees remain at most three. Selector arithmetic additionally includes the actual candidate widths; it is not bounded just by this source estimate. Any optional producer of Proposition 53.2 adds its matrix/input/intermediate widths and live buffers rather than borrowing this selected-route bound.

**Proof.** Each operation count follows directly from its word (51.1), with the original Tick ACK law. The successful edit is legal by terminal type and contributes precisely its persistent zero inclusion. The endpoint and scalar formulas are therefore its full primitive recurrence, not only input-output identifiability. The finite selector terminates by Theorem 51.3. Dense finite propagation, rational comparison and the finite matrix/scratch dimensions give the stated conservative work/layout bounds. The neighbor-sum denominator and degree estimate proves the source width envelope. Every current-predictor update in subsequent service is additional actual work on the same record/source, as in Proposition 51.4. $\square$

This account combines the selected experiment's own operations, its owned candidate selection and its actual current retention. It does not combine all alternative source runs, a regenerated minimal-memory selector and a stored-table runtime into one cost vector. No total-resource optimum, bounded-precision instrument, generic scalar acquisition of unknown rational fields or cheaper replacement for all-leaf acquisition is asserted.

## 54. Source correspondence and the limits of the two native constructions

The native meanings of terms, markers, birth restrictions, successful edits and causal order are supplied by [AA §17](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#17-birth-typed-local-growth-and-its-causal-reconstruction). The original ordered field/roster/fresh-zero implementation is [NLBA §§10–13](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md); this volume's §§17–20 describe its different raw-label attachment and full current-state consumer. Sections 45–50 instead start with an earned constructed ordered roster and replace terminal Reads by an installed original-root Read. Sections 51–53 keep the original terminal interface. The former's cleared hidden amplitudes and acquisition splits are not hypotheses or cost savings for the latter.

The exact all-leaf forcing, terminal control right inverse, full-menu field necessity and generic quotient implication are already supplied by [§§30–33](#30-a-binary-word-in-the-native-branching-field) and NLBA §3.2. Their role in (51.5) and Proposition 53.2 is direct reuse on the same unit native tree. The additional one-growth mechanism is (51.4), its parity-isolated first-terminal evaluation, the bounded alternative words, their paid candidate selector and actual advanced service. The root-read construction adds the prepared signed rational family, its asymmetric paid exposure, the triangular walk map and present-slice inverses under the stated cleared handoff. Rank-nullity, symmetry decomposition, Cayley–Hamilton, rational Gaussian elimination, Gram left inverses and tree walk counting are mature mathematics.

The relevant formal library supplies these finite-linear mechanisms within its declared domains. [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean) and its [owning Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs) concern the real finite-inner-product stacked observation map, rank and Gram criterion. Here their mathematical correspondence is to the rational matrices $U,F$ embedded in real coordinate spaces, not to a granted observation port. [FiniteTimeTomographySaturation](../../../D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation.lean) and its [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation.scribe.cs) include the general-field `all_future_kernel_eq_finrank_kernel`: its Cayley–Hamilton finite-horizon argument matches $(B,e_o^{\mathsf T},N)$ in Lemma 47.1. Its additional quantum specialization does not identify these unit-tree calls with quantum measurements. [DegenerateModeHiddenFiber](../../../D5/S3/ObserverMemory/FourierFibers/DegenerateModeHiddenFiber.lean) with its [Scribe](../../../Blueprint/D5/S3/ObserverMemory/FourierFibers/DegenerateModeHiddenFiber.scribe.cs), and [SymmetryBreakingObservabilityGain](../../../D5/S3/ObserverMemory/FourierFibers/SymmetryBreakingObservabilityGain.lean) with its [Scribe](../../../Blueprint/D5/S3/ObserverMemory/FourierFibers/SymmetryBreakingObservabilityGain.scribe.cs), already express equal-mode hidden differences and gain from broken degeneracy. They supply that structural lesson; the native edit edges, earliest walk coefficients and one-source schedules require the separate proofs above.

[NativeUniformTree](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.lean) and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.scribe.cs), together with [NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean) and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs), provide their own recursive tree traversal and actual production/read correspondence. Their literal constructor-read attachment is stronger than the scalar menus here; its private traversal helpers and public producer cannot be transported as a free constructor port. [NativeMaterialRootRecognition](../../../D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.lean) and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.scribe.cs) use reachable birth types, at least three leaves and a complete ordered material graph to obtain rooted recognition and an effective inverse. That given graph is not a root scalar observation or an unknown roster map. Here the ordered graph has already been earned by actual construction or is a declared earned input.

At the pinned [mathlib adjacency-matrix source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean), `adjMatrix_pow_apply_eq_card_walk` supplies the power/walk-count identity used in §§46 and 51. The additional walk cancellations, distances and parity are proved for the exact persistent edits here. The unique-unforced-neighbor mechanism has a primary-literature counterpart in Burgarth and Maruyama, [*Indirect Hamiltonian Identification through a small gateway*, §II](https://arxiv.org/html/0903.0612v1). That paper's infection reconstruction assumes its known graph, coupling/sign hypotheses and Hamiltonian gateway experiment; its §III tomography uses its own repeated preparation. Neither those controls nor its physical interpretation are supplied by native $P/S$, and no such bridge is used above.

The public [AAII §§68–74 and 75–83](https://github.com/the-omega-institute/trureturing/blob/7b01754c3a0711071274841dae081f111fc39796/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md) already give guard-only actual acquisition into the $J$ image with represented service, and a known-initialization maintained global history supplement. Their interfaces and retained annotations are substantive common-source results, not missing generic traversal or history theorems. The public [RGII §§77–83](https://github.com/the-omega-institute/trureturing/blob/7b01754c3a0711071274841dae081f111fc39796/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md) give the uniform rational symmetric endpoint-path compatibility/certificate under their stated hypotheses. [RGII §§84–95](https://github.com/the-omega-institute/trureturing/blob/7b01754c3a0711071274841dae081f111fc39796/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md#84-the-full-bounded-scalar-alphabet-at-every-rational-origin) give the full scalar bounded-alphabet iff and certified later-vector recognition with paid advanced prediction. Their positive-link rational path law, origin and pulse alphabet are not unit branching adjacency or the unrestricted signed amplitudes of §45. The public one-Read packed raw-binding construction of §§39–44 identifies its finite binding information under its own whole-zero preparation; it does not contradict the affine-read bound for arbitrary hidden $\mathbb Q^k$ here. Existing fixed-block/adaptive-cut results retain their own canonicality, auxiliary-alphabet and paid paired-source conditions. None of these suppliers is reproposed as a new generic result.

The attribution of §§45–53 is source-relative synthesis and application of those supplied mechanisms with the explicit native proofs and paid realization given here. This is not a claim of world priority or of absence throughout the repository or literature. For the root-read construction, numerical equivalence concerns the fixed sampled preparation/acquisition image and common access; arbitrary later history is not recoverable after Reset. For the original first-terminal construction, structural Time and passive Boundary are insufficient on arbitrary rational fields, while the active finite family is a family of alternatives and its selected one-run acquisition needs the owned pair promise. Finite exact mathematical execution does not certify physical calibration, authenticity, isolation, rights or resource supply. No universal alpha/beta minimum, total-resource optimum, unrestricted history inverse, common native/path/quantum realization or physical-law conclusion follows. The fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization and final-no-Ready obligations retain their exact original scopes; these two native constructions do not discharge the full common-process objective.

## 追加锚（本行以下为增补区）

## 55. One original-law branching criterion and its two-leaf root bridge

**Definition 55.1 (one plant and three different recovery questions).** Use the original birth-typed class $\mathcal D$ of AA §17: terms are $\alpha,\beta,\langle s,t\rangle$, and a logical alpha cannot occur at an address ending in L. Materialization retains every logical vertex, adds the unary marker $pL$ below each beta at $p$, and joins each branch to its two ordered children. Write $V(u)$ for these persistent material vertices, $A_u$ for their zero-diagonal symmetric unit adjacency, $b$ for the number of current terminals, $N=|V(u)|$ and $I=N-b$. At a branch these terminals are exactly all degree-one vertices. Canonical order means the complete left-to-right linear terminal order, not the arbitrary raw-label attachment.

The installation in this appendix has precisely the six operations of Assumption 34.1. In particular Tick returns an acknowledgement and applies $A_u$; it does not return a scalar. Read is a separate nondestructive literal rational reply. Growth retains all old vertices, edges and values, and gives fresh vertices value zero. A former Reset tag is malformed. Actual root binding, orientation, held exclusive serialization, current and fresh authority, finite exact framing and sufficient finite backing are premises, not consequences of a numerical inverse.

Three questions will be kept separate. Binary recovery asks for a prescribed word since a physically established origin on a fixed graph. Preserved-entry acquisition asks for the arbitrary old field before calibration, and physically restores its values on the retained old vertices of a larger graph. Arbitrary-current acquisition asks for a self-contained predictor of the field at the endpoint actually reached by an experiment; it may discard an entry kernel. None of these definitions gives an erased general input journal.

**Theorem 55.2 (sharp native branching criterion).** Let $u\in\mathcal D$ be earned, with its complete material/terminal correspondence. Physically establish zero at every vertex, then actually Add one at the first canonical terminal $e$ and Hold. For every finite binary word $w=d_0\cdots d_{m-1}$ execute each digit as

$$
\operatorname{Tick};\ \operatorname{Add}(e,d_i);\ \operatorname{Hold};\ \operatorname{Read}(e).
$$

Call this complete composite Next$(d_i)$: it returns all three acknowledgements and the literal Read scalar, through the earned raw binding of $e$. No growth, Reset, other Add or extra Tick belongs to this encoding phase. Its actual field is

$$
x_w=F_w(A_u)e,\qquad
F_w(z)=z^m+\sum_{i=0}^{m-1}d_i z^{m-1-i}.
\tag{55.1}
$$

The map $w\mapsto x_w$, including the empty word and every all-zero word, is injective if and only if $u$ is a branch, equivalently $b\ge2$. Four material vertices suffice and are the minimum material size in this native class. On every branching graph the two functionals $e^{\mathsf T}A_ux_w$ and $e^{\mathsf T}A_u^2x_w$ suffice to recover the word and its length by a terminating exact greedy calculation.

**Proof.** The actual recurrence is $x_{wd}=A_ux_w+de$, starting at $e$, which proves (55.1). Put $A=A_u$ and

$$
r_j=e^{\mathsf T}A^{2j}e=\|A^je\|^2,\qquad a_j=r_{j+1}\quad(j\ge0).
$$

The norm is the ordinary rational-coordinate sum of squares, viewed in $\mathbb R$ for Cauchy–Schwarz. For a leaf $e$ with neighbour $v$, $r_0=r_1=1$ and $r_2=\deg(v)$. In a connected branching material tree $\deg(v)\ge2$. Every $r_j$ is positive: bouncing on the edge incident with $e$ is a closed walk of length $2j$. Symmetry gives

$$
r_{j+1}=\langle A^je,A^{j+2}e\rangle,
\qquad r_{j+1}^2\le r_jr_{j+2}.
\tag{55.2}
$$

Thus the positive ratios $r_{j+1}/r_j$ are nondecreasing. Starting with $r_2/r_1\ge2$ yields $a_0=1$, $a_{j+1}\ge2a_j$ and

$$
a_D>\sum_{j<D}a_j\quad(D\ge1).
\tag{55.3}
$$

Indeed $a_j\le 2^{-(D-j)}a_D$ and the finite geometric sum is strictly less than one. This is a fixed-leaf argument; a theorem about the total number of closed walks alone would not establish (55.2) at this $e$.

A tree is bipartite, so its odd return moments at $e$ vanish. For any finite binary-coefficient polynomial $F(z)=\sum_k c_kz^k$ the two numbers are exactly

$$
Y_1=\sum_{j\ge0}c_{2j+1}a_j,
\qquad Y_2=\sum_{j\ge0}c_{2j}a_j.
\tag{55.4}
$$

Each sum is uniquely decoded by superincreasing greedy subtraction. Construct $a_0,a_1,\ldots$ by exact sparse powers until the next weight exceeds $\max(Y_1,Y_2)$; for zero totals no positive weight is required. Descend the constructed list, subtracting a weight exactly when the remaining total is at least it, separately for each parity. Equation (55.3) proves that this decision is the actual highest remaining digit: all lower weights together are smaller. A genuine sum is exhausted. Interleave the lists; the highest nonzero coefficient is the leading monic coefficient of $F_w$. Its degree is $m$ and the lower coefficients, in reverse order, are exactly the chronological digits. If $F=1$, this gives the empty word. All-zero words have $F=z^m$, so they are not discarded as leading-zero encodings. The weights grow at least geometrically, proving termination without an input length bound. Applying this to (55.1) proves injectivity.

The only nonbranching terms are alpha and beta. At alpha, $A=0$ and the empty word and the one-letter word $1$ both give $e$. At beta, $A^2=\mathrm{Id}$ on its two-vertex material path, and the empty word and $00$ both give $e$. No inverse of the full field can distinguish either pair. A branch in $\mathcal D$ has at least a left beta leaf and a right alpha leaf; its smallest material tree is $\langle\beta,\alpha\rangle$, with four vertices. This proves necessity and the minimum. $\square$

**Proposition 55.3 (the missing small root case).** The original root, ordered syntax and material coordinates are determined by the unrooted unit material tree with its complete ordered terminals for every branching $u\in\mathcal D$, including $b=2$.

**Proof.** For $b\ge3$ apply NLBA Theorem 11.1 with its no-left-alpha and complete-order hypotheses. Its original-domain rigidity and finite recognition are supplied by `NativeMaterialRootRecognition.original_rigidity` and `effective_inverse`; their stated lower bound of three leaves is not silently changed. If $b=2$, there is exactly one branch, its left child must be beta, and its right child is alpha or beta. The two possibilities are respectively $\langle\beta,\alpha\rangle$ and $\langle\beta,\beta\rangle$. Their material trees are paths with respectively three and four edges. In both, the original root is the vertex at distance two from the first ordered endpoint. The number of edges distinguishes the terms and the endpoint order fixes every coordinate. This proves precisely the additional two-leaf case. $\square$

Starting from an authentically known whole-zero alpha, actually execute $P_\varepsilon;S_\varepsilon$. The result is the four-vertex case with inherited label at $LL$ and appended label at $R$. Optionally execute $P_R$ for the five-vertex case, moving that label to $RL$. Then Add one at $LL$ and Hold. These are actual qualifying small origins, with no Reset or unearned label decoder. An unknown arbitrary-field attachment instead needs the separately paid entrance of §§34–36; the small construction is not an acquisition of that attachment.

## 56. Two actual late Reads, and the precise one-Read exclusion

**Definition 56.1 (Sample2).** At an encoding-image cut with actual field $x_w$, retain only the earned graph, canonical/raw correspondence, binding, rights and the phase promise as necessary input. The old word and full vector need not be retained. Actually Hold. For each $s=1,\ldots,I$, execute Tick; Add$(e,0)$; Hold, consuming all complete replies and returns. Read$(e)$ only at $s=1$ and $s=2$, and consume both complete literal replies. A branching native tree has $I\ge2$, so both calls occur. Finish every remaining round even after decoding is possible. Return the two actual scalars, the decoded pre-assay word $w$ and length, and the whole actual inner replies, which may be relayed as they complete. Install the reconstructed current vector at the completed endpoint before accepting another settled request.

**Theorem 56.2 (literal acquisition and advanced endpoint).** Sample2 terminates on every promised input, has exactly two successful scalar Reads, and satisfies simultaneously

$$
Y_1=e^{\mathsf T}Ax_w,\quad Y_2=e^{\mathsf T}A^2x_w,
\qquad x_{\rm end}=A^Ix_w=x_{w0^I}.
\tag{56.1}
$$

It recovers $w$ by Theorem 55.2 and installs $x_{w0^I}$, not $x_w$, as the present predictor. Its exact primitive counts are $I$ Tick, $I$ Add, $I+1$ Hold and two Read. The pair is historical data at offsets one and two from the start; for $I>2$ it is not a pair of final trailing readings.

**Proof.** Zero Adds, Holds and Reads are field identities. Induction gives actual field $A^sx_w$ at round $s$. This proves both sampled equations and the endpoint. Each Tick followed by the literal zero Add is exactly an encoded zero, which also proves the final equality in (56.1). Greedy inversion and then finite evaluation of (55.1) at $w0^I$ give the predictor. No inverse of $A$ or returning-scalar Tick is used. All loops have earned finite bounds and the word inverse terminates on its stated image. Counting the displayed actual calls gives the claim. $\square$

**Theorem 56.3 (two is the exact late-observer minimum on this domain).** Fix an earned branching graph and complete access correspondence. A late observer starts with source-independent records, code, tape, references and rights, and just the binary-image promise. It has no word, length, input archive, vector, field-dependent advice or dependent accessible producer state. Permit arbitrary finite local calculation, known rational Adds, Ticks, Holds, reads at any current terminal, and identity refusals/malformed/range responses. Prohibit successful growth and Reset. Every uniformly exact terminating recovery of the binary word requires at least two successful scalar Reads in the worst case. Together with Sample2 this gives a two-Read attainment on precisely this late-observer domain.

**Proof.** Suppose at most one Read is used on every input. Before that Read all complete replies are field independent, so its terminal $f$, all earlier operands and the total number $T$ of earlier Ticks are fixed on the common path. The hidden part of its scalar reply is

$$
e_f^{\mathsf T}A^TF_w(A)e;
\tag{56.2}
$$

earlier known Adds contribute the same affine offset on all inputs. Bipartiteness makes $(A^k)_{f,e}=0$ whenever $k$ has the wrong parity for the distance from $e$ to $f$. Exactly one of the exponents $T,T+1$ has that wrong parity. Compare the length-two words $00$ with $01$ if exponent $T$ is invisible, and $00$ with $10$ if exponent $T+1$ is invisible. Their polynomials differ respectively by $1$ and $z$. Equation (56.2), including its common affine offset, is equal on the selected pair. Hence the entire scalar frame is equal. Every later choice and stopping decision is the same; without another Read every later reply is field independent. The observer reports the same word on two different inputs. If it never Reads, the same contradiction is immediate. $\square$

This is a restriction on a late observer, not on an observer that watched the original digits or kept a current predictor. Successful asymmetric growth is excluded: §§51–53 already show why it can expose distinctions hidden by passive sampling, and an owned finite candidate list is additional advice. Reset erases the word image. A different interface returning field data with Tick, reference bytes, timing, guards or capacity responses does not meet the observation contract. The theorem makes no bounded-error claim and no total-resource optimum.

**Proposition 56.4 (a supporting total vector test).** On an earned branching graph, membership of any rational vector $x$ in $\{F_w(A)e:w\in\{0,1\}^*\}$ is decidable by the same two moments followed by full-coordinate verification.

**Proof.** Refuse unless both moments are nonnegative integers. Construct weights until the next one exceeds their maximum and greedily subtract in each parity. Refuse a nonzero residual. Interleave the finite digits and refuse the zero polynomial; otherwise its highest one gives a unique candidate $F_w$. Accept only after checking $F_w(A)e=x$ at every vertex. These loops are finite for every rational input. Theorem 55.2 proves completeness; the final equality proves soundness. On the four-vertex path, indexed from its first endpoint $0$, $e_2=A^2e_0-e_0$ has the same two moments as $e_0$: $r_1=1,r_2=2$ give $e_0^{\mathsf T}Ae_2=0$ and $e_0^{\mathsf T}A^2e_2=1$. But $e_2\ne e_0$; uniqueness in (55.4) forces the candidate $F=1$, which fails full-coordinate verification. Thus equality of the two moments alone is insufficient for off-image vectors. $\square$

The greedy algorithm, parity split and membership test support the single branching recovery theorem. They are not three additional independent threshold results. Acceptance of an endpoint does not certify its historical provenance: extra cancelling Adds can preserve a field while changing its full input journal.

## 57. Independent two-sample views and actual binary use

**Definition 57.1 (one joint sampled image).** Fix a physically established branching origin and the common paid callable context of §55. At a completed Sample2 cut put $v=w0^I$. Define the four returned expressions by the following different observations of this same source.

| Expression | Independent meaning |
| --- | --- |
| Space | The unrooted unit material graph, complete canonical linear terminal order and actual present field $x_v$, modulo order-preserving graph isomorphism |
| Time | AA's actual labelled successful native causal birth/lifecycle order $E(u)$, and the actual restricted binary chain $v$ since the established origin |
| Boundary | The complete ordered terminal impulse-onset metric of the actual law, with diagonal zero, and Sample2's actual historical pair $(Y_1,Y_2)$ |
| Memory | The installed finite predictor program with its retained original term, complete present vector and canonical terminal-coordinate table |

Time is causal birth order, not a chosen total serialization of incomparable old edits, elapsed time or a full call journal. Its field-input part includes the zeros actually executed by Sample2. Boundary's onset entry is the least $k$ with $(A^k)_{\ell_i,\ell_j}\ne0$: it equals graph distance by NLBA Lemma 2.1. This table is calculated from the earned graph and exported with paid local work; it is not an extra literal impulse experiment or an assumed unknown response oracle. Its two appended numbers, in contrast, are actual replies on this specimen. Memory has a current prediction, not an old word archive. The private raw table, genuine references, rights, framing, pending control and adequate backing are separately retained common context; no numerical route manufactures them.

**Theorem 57.2 (all inverse routes and their dynamics).** Every expression of Definition 57.1 recovers $(u,v)$ and all other expressions on its entire stated joint image. Every route agrees. The inverses respect an actual Next followed by an actual Sample2, and all four determine the complete canonical present service under the retained common context.

**Proof.** Space recovers the original root/code by Proposition 55.3 and recovers $v$ from its present vector by Theorem 55.2. Time recovers $u$ from $E(u)$ by AA Theorem 17.2 and already contains $v$, so (55.1) computes the field. Memory parses its term and uses its vector to recover $v$. Boundary recovers the complete unit subdivision tree from the full leaf metric by NLBA Lemma 2.3, including degree-two vertices, then applies Proposition 55.3. Its pair recovers exactly $w$ by (55.4), and appending the earned $I$ zeros gives $v$ and the genuine current field.

Conversely $(u,v)$ in this sampled image has a specified suffix of exactly $I$ zeros. Strip that many to recover $w$, even if $w$ itself ends in zeros. Compute its two moments, the actual endpoint, the complete metric, the canonical predictor and AA's uniquely determined labelled causal order. These are the original observations, not arbitrary representative histories. If $E_i(u,v)$ denotes each expression and $R_i$ its displayed inverse, $R_iE_i=\mathrm{Id}$ on this image. Therefore the route $E_jR_i$ followed by $E_kR_j$ equals $E_kR_i$, proving every round trip and agreement from the actual proved inverses.

An actual Next$(d)$ sends $v$ to $vd$; a subsequent actual Sample2 sends it to $vd0^I$, by (56.1). The same calculation applies at that new sampled cut. The full present vector and earned table initialize §64's complete service invariant. Leaving the restricted image preserves that invariant, but need not preserve a binary-history inverse. $\square$

One actual internally selected use is the following. After decoding the current chain, compute $d=|v|\bmod2$, actually submit Next$(d)$ through the earned first-terminal binding, and consume Tick/Add/Hold acknowledgements and the literal Read. Its actual successor is $x_{vd}$, and the returned scalar is $e^{\mathsf T}x_{vd}$. A following Sample2 has the just-proved new image. The digit selection, decoding, operand/reply copies and retained update are real local work. Recall and Length actually Hold before decoding the retained current vector; they need no original word advice.

## 58. Physically returning the arbitrary entry field without Reset

**Definition 58.1 (saved old values and the marked plant).** Take an arbitrary attachment of Assumption 34.1: $t\in\mathcal D$ has $a$ alpha leaves, $c$ beta leaves and $L=a+c\ge3$, arbitrary $x\in\mathbb Q^{V(t)}$, and an arbitrary exhaustive initial raw bijection. Execute exactly the arming and preorder marking of Definition 34.2, retaining every initial literal $z_j$ before its Add$(j,1-z_j)$. After the map is earned, arrange these saved numbers in the original canonical terminal order. They are old field data, not new source ports.

The supplier Theorem 34.3 earns $t,\lambda_0$ and the actual $u=\rho(t),\lambda$, where

$$
\rho(\alpha)=\beta,\qquad
\rho(\beta)=\langle\beta,\alpha\rangle,\qquad
\rho(\langle s,t\rangle)=\langle\rho(s),\rho(t)\rangle.
$$

Let $V_0=V(t)$, $T_0$ be its original terminals, and $W=V_0\setminus T_0$. The actual final sizes and marked field $m$ are

$$
b=L+c,\quad N=3L+2c-1,\quad I=N-b=2L+c-1=|V_0|,
\qquad
m_v=\begin{cases}x_v,&v\in W,\\1,&v\notin W.\end{cases}
\tag{58.1}
$$

Every old vertex is now internal and every fresh vertex is now a current terminal. These assertions include the old beta marker, which is retained as a new logical beta root when its parent is split.

**Theorem 58.2 (full-window restoration on the same specimen).** There is one finite paid no-Reset protocol returning the exact reports $(t,x,\lambda_0)$ and $(u,f,\lambda)$ and a callable synchronized current service, where its physical final field is

$$
f_v=\begin{cases}x_v,&v\in V_0,\\0,&v\in V(u)\setminus V_0.\end{cases}
\tag{58.2}
$$

The protocol works for every arbitrary entry rational field, including arbitrary internal values. It restores values on actual retained old vertices, rather than just reporting a historical vector. It does not shrink the grown geometry back to $t$.

**Proof and executed protocol.** During marking no Tick occurs. Arming overwrites only $T_0$, whose previous values were saved. The literal fresh-zero rules and rearming leave every other old value unchanged, give each old terminal value one, and give every current fresh terminal value one. At an original alpha the fresh marker is terminal; at an original beta the two fresh vertices $pLL,pR$ are terminals while its old $p,pL$ are internal. Different entry leaf cones are disjoint. This proves every coordinate statement in (58.1) and the claimed old/fresh partition.

Construct the supplier's all-leaf forcing matrices on the earned current graph:

$$
J:\mathbb Q^b\longrightarrow\mathbb Q^N,\quad
K=[J,AJ,\ldots,A^IJ],\quad
C\in\mathbb Z^{b(I+1)\times N},\quad KC=\mathrm{Id}_N.
\tag{58.3}
$$

Here $A=A_u$, and the canonical/raw translator uses the actual earned map. From the final marking Hold, Read all $b$ terminals. For each $r=1,\ldots,I$ actually Tick; Hold; Read all $b$ terminals. The complete literal block and actual endpoint are

$$
Y=K^{\mathsf T}m,\qquad m=C^{\mathsf T}Y,\qquad d=A^Im.
\tag{58.4}
$$

These are the actual calls of Definition 35.1. Symmetry and (58.3) prove the reconstruction; the real source is already at $d$ when the calculation finishes. Recover $x_v=m_v$ on $W$ and recover its remaining $T_0$ coordinates from the saved $z$ using $\lambda_0$. This recovers all of the original entry, and constructs (58.2) on the actual persistent addresses.

Compute the signed control blocks, including zeros,

$$
g=C(f-A^{I+1}d)=(g_0,\ldots,g_I).
\tag{58.5}
$$

For $s=0,\ldots,I$ actually Tick; Add at every canonical terminal the corresponding coordinate of $g_{I-s}$ in increasing order; Hold. Consume every whole reply and return. After these rounds the actual field is

$$
A^{I+1}d+\sum_{s=0}^I A^{I-s}Jg_{I-s}
=A^{I+1}d+KC(f-A^{I+1}d)=f.
\tag{58.6}
$$

Each Add follows its own round's Tick and undergoes exactly the remaining Ticks, proving the expansion by induction. Thus no internal actuator, inverse Tick, Reset, repeated preparation or hypothetical control is hidden in (58.6). Retain the complete vector $f$, graph, code and full map, then complete the requested reports and four exports of §59 through their real framed output connections. Inner replies are consumed in full and may be relayed without retaining an additional journal. Complete all retained updates, output acknowledgements and returns before the settled handoff. The loops have earned finite bounds; exact rational arithmetic and framing terminate with the stipulated backing. $\square$

**Proposition 58.3 (the distinctions that must survive calibration).** For fixed $t,\lambda_0$ and fixed $x|_W$, changing only $x|_{T_0}$ leaves the entire marked field $m$ and subsequent observation $Y$ unchanged, but changes the required restoration target. Consequently this particular marking-and-restoration schedule must retain those old-terminal distinctions in $z$ or equivalent surviving records.

**Proof.** Equation (58.1) sets every coordinate outside $W$ to one independently of its old value. Equations (58.3)–(58.4) then give the same $Y,d$. But (58.2) restricts to the original arbitrary values on $T_0$. A deterministic controller with identical surviving data cannot select two different owed targets. If each of the $L$ old terminal values is chosen independently from a fixed set of $2^h$ rationals, the surviving data must distinguish $2^{Lh}$ cases, requiring at least $Lh$ bits in any exact finite binary representation. $\square$

This necessity concerns information overwritten by this schedule. It is not a universal lower bound of $L$ unrestricted rational registers or a lower bound for every different acquisition algorithm. Here $|W|=L+c-1=b-1$; that smaller dimension alone is not an executed replacement for the full-window protocol. No sparse-row alternative or total-cost comparison is claimed.

## 59. Four independent preserved-entry views and their exact image

**Lemma 59.1 (the original predecessor is recoverable).** There is a finite inverse $\delta$ on $\rho(\mathcal D)$ with $\delta(\rho(t))=t$. Its parsing rules are: beta maps to alpha; alpha fails; the literal pattern $\langle\beta,\alpha\rangle$ maps to beta before recursive pairing; every other pair is accepted only if both children parse, and maps to their pair. Finally require the parsed term to be in $\mathcal D$ and to have $L\ge3$ for the present acquisition domain. On this domain the restored image is exactly

$$
\{(u,f):u=\rho(t),\ t\in\mathcal D,\ L(t)\ge3,
\ f\in\mathbb Q^{V(u)},\ f|_{\operatorname{Term}(u)}=0\}.
\tag{59.1}
$$

**Proof.** No $\rho(t)$ has alpha at its root. Hence a recursive image pair cannot be the literal special pattern: its right child would have to have root alpha. Induction on $t$ gives $\delta\rho=\mathrm{Id}$. Conversely induction on an accepted parse gives $\rho\delta(u)=u$, with the priority rule handling precisely the beta preimage. The subsequent birth/leaf check gives exactly the specified domain. The old/fresh partition of Theorem 58.2 says that the fresh vertices are exactly the current terminals. Any field zero there restricts to an arbitrary old vector on all current internal vertices, which are precisely $V(t)$; applying Theorem 58.2 to that vector realizes it. This proves (59.1), not merely an inclusion. $\square$

**Definition 59.2 (returned meanings).** At the restored endpoint, export the following four data through the actual output service. The common authentic binding, rights and full private raw tables remain separate paid context.

| Expression | Independent meaning on the restored image |
| --- | --- |
| Space | Unrooted unit material graph with its complete ordered terminals, and the actual present field $f$ |
| Time | Actual native causal birth/lifecycle order $E(u)$, the initial literal terminal values in original canonical order, and the actual marked-field window $Y$ in final canonical/time order |
| Boundary | Complete ordered impulse-onset metric and the finite autonomous present germ $B=(J^{\mathsf T}A^rf)_{r=0}^I$ |
| Memory | Installed present-service predictor, retaining the original current term $u$, canonical terminal table and complete present vector $f$ |

Time's value records are measurements actually taken during this acquisition; it is not structural Time alone or an arbitrary old serial journal. Boundary's germ has its own meaning as predicted current autonomous replies. It is explicitly computed and exported from the earned present state, not claimed as $b(I+1)$ additional literal Reads. Its metric is the actual-law onset metric, also computed. Exporting the arrays, causal data and vectors, including caller-retained copies, is part of the simultaneous resource account. None is identified with another expression merely by giving it a different name.

**Theorem 59.3 (complete inverses, actual agreement and limits).** On (59.1), each returned expression recovers exactly $(u,f)$, hence the original $(t,x)$ and every other expression. All routes agree and each determines the complete current canonical service. The assertion does not recover an erased earlier total history, and structural Time without its measured value records is insufficient.

**Proof.** Space recovers the ordered root/code by the original $b\ge3$ root supplier; here $b=L+c\ge4$. Its full field is already present. Memory directly gives this pair. Boundary recovers the complete unit material tree and ordered root from its metric, and (58.3) gives $f=C^{\mathsf T}B$. Time recovers $u$ from the actual causal order, then $t=\delta(u)$, reconstructs $m=C^{\mathsf T}Y$, and combines $m|_W$ with its saved initial terminal values to recover $x$. It therefore calculates precisely (58.2).

Conversely, from $(u,f)$ parse $t$. Restrict $f$ to the old vertices to obtain $x$. Its original terminal values give exactly the canonical saved $z$. Set $m=x$ on $W$ and one everywhere else, and compute $Y=K^{\mathsf T}m$, the metric and $B=K^{\mathsf T}f$. AA Theorem 17.2 gives the original labelled causal order $E(u)$. These are exactly the numerical records exported, independent of any unexported raw scan journal. Thus every route factors through the same actual pair, with both inverse identities proved as in Theorem 57.2. The full present-service invariant is §64. If $x$ is changed on an old vertex while $u$ is fixed, Space changes, so structural birth order alone cannot provide this inverse. $\square$

A subsequent arbitrary actual menu call is serviced on $(u,f)$, not on a fictitious restored small graph $(t,x)$. For example the controller can take its recovered original first-terminal value $z_1$, translate the current first canonical terminal through the earned raw table, and actually Add that value; Hold; Read that terminal. It consumes both acknowledgements and the literal scalar, and installs $f+z_1e$ as the actual successor. These are two extra field acknowledgements, one scalar, one Add, one Hold and one Read. This use can leave (59.1); full prediction continues. A new complete preserved-entry acquisition on any later admissible entry $(s,h)$ returns $(\rho(s),\operatorname{zeroextend}h)$ by the same theorem. Ordinary old-tree Tick does not commute with zero extension to the grown tree: the fresh-neighbour contributions differ. No such dynamics square, restoration of old geometry, or arbitrary-field inverse from structural birth order is asserted.

## 60. The rank that original symmetric growth cannot erase

**Lemma 60.1 (induced growth protects the previous adjacency image).** Let $A\in\mathbb Q^{n\times n}$ and $B\in\mathbb Q^{n'\times n'}$ be symmetric, and let $E$ be the coordinate inclusion of retained old vertices, with

$$
E^{\mathsf T}BE=A.
\tag{60.1}
$$

Then $BE$ is injective on $\operatorname{im}A$. Also $\operatorname{rank}(BE)\ge\operatorname{rank}A$.

**Proof.** If $z=Ay$ and $BEz=0$, compression gives $Az=0$, whence

$$
z^{\mathsf T}z=(Ay)^{\mathsf T}z=y^{\mathsf T}Az=0.
$$

A sum of rational squares vanishes only when every coordinate is zero. Thus $z=0$. For the rank inequality, (60.1) factors $A$ through $BE$, and rank cannot increase under postcomposition. $\square$

**Theorem 60.2 (source-induced surviving rank).** Fix any finite original six-operation schedule, with actual native growth and no Reset, on an entry graph with adjacency $A_0$ and $N_0$ vertices. Freeze its Add operands and all structural/control choices. Write the final field as $Px+q$, an affine function of the entry $x$. If no Tick occurs, $\operatorname{rank}P=N_0$. If at least one Tick occurs,

$$
\operatorname{rank}P\ge r_0:=\operatorname{rank}_{\mathbb Q}A_0.
\tag{60.2}
$$

**Proof.** The literal native edits add fresh vertices and edges but never change an old-old edge. Every composite growth inclusion therefore satisfies (60.1) between its old and new adjacency matrices. Before the first Tick the homogeneous map is just such an inclusion $E_0$. If $B$ is the then-current adjacency, the first Tick has map $BE_0$, of rank at least $r_0$ by compression. Its differences now lie in $\operatorname{im}B$.

Between consecutive Ticks let $E$ be the composite actual growth inclusion. Adds are common translations and cancel in differences; Holds, Reads, refusals and parser identities do not change them. The next Tick sends a difference $z\in\operatorname{im}B$ to $B' Ez$. Lemma 60.1 says this map is injective on the whole previous image, hence on the surviving difference subspace. Its new differences lie in $\operatorname{im}B'$. Induction proves that no later Tick loses any more of that rank. Final growth inclusions are injective as well. With no Tick the whole homogeneous map is the inclusion of all original coordinates, of rank $N_0$. This proves both cases on the actual schedule, without assuming a fixed final tree. $\square$

The old-old compression identity is a property of the actual $P/S$ material edits, not a generic consequence of calling an operation growth. Symmetry and the ordered rational field supply the sum-of-squares step. For example the nonsymmetric matrix $\left(\begin{smallmatrix}0&1\\0&0\end{smallmatrix}\right)$ has rank one but square zero: two Ticks erase every field without a Read. Reset also erases rank. Neither counterexample meets the theorem's original-law domain.

**Lemma 60.3 (rational forest rank and native size).** For a finite forest $G$, its zero-diagonal unit adjacency over $\mathbb Q$ has rank $2\nu(G)$, where $\nu$ is maximum matching size. For an original $t\in\mathcal D$ with $L\ge2$ logical leaves,

$$
\nu(C(t))\ge L,\qquad \operatorname{rank}_{\mathbb Q}A_t\ge2L.
\tag{60.3}
$$

**Proof.** Remove isolated vertices without changing rank or matching size. Otherwise choose a leaf $\ell$ and neighbour $v$. In the order $\ell,v,$ remaining vertices, adjacency is

$$
\begin{pmatrix}0&1&0\\1&0&c^{\mathsf T}\\0&c&D\end{pmatrix}.
$$

The leading two-by-two block $H$ is invertible with $H^{-1}=H$. Its coupling to the remainder has first row zero, so its Schur correction is $[0,c]^{\mathsf T}H^{-1}[0,c]=0$. Invertible row/column elimination therefore gives rank $2+\operatorname{rank}D$. There is a maximum matching containing $\ell v$: if $v$ is matched elsewhere, exchange that edge for $\ell v$; if neither endpoint is matched, adding the edge contradicts maximal size. Hence $\nu(G)=1+\nu(G-\{\ell,v\})$. Induction proves the formula over $\mathbb Q$.

For each beta logical leaf choose its marker edge; for each alpha logical leaf choose its edge to its parent branch. The latter parent exists because $t$ is branching. Distinct alpha leaves have distinct parents, since an alpha can only be a right child. The chosen beta edges use only the beta leaves and their markers, and cannot meet an alpha-parent edge, whose parent is a branch. Thus these $L$ edges form a matching. Apply the formula. $\square$

## 61. Adaptive scalar-Read obstruction for an arbitrary entry field

**Definition 61.1 (cleared observer and current endpoint task).** Fix an admitted native entry graph, its actual reference/rights/roster and other field-independent installation data. Permit even an earned complete initial graph/map. The hidden entry ranges over every $x\in\mathbb Q^{N_0}$. Initially all accessible observer records, local tape, reference bytes, rights, counters, selectors, provider records and advice are independent of $x$. Only successful scalar Read replies convey numerical field information; all ACKs, growth/refusal/range/framing replies have precisely the field-independent content of the original menu. There is no capacity, timing, allocation-name or other hidden numerical side channel.

A deterministic protocol may adaptively choose any original Add, Tick, Hold, Read and native growth, with all complete frames and returns; there is no Reset. It terminates exactly for every entry. At its own actual final graph/field it must either report that complete field, install a self-contained predictor of every future complete service without consulting an additional dependent archive/source during prediction, or physically null the whole field. These are current endpoint tasks, not original-entry restoration or binary recovery.

**Theorem 61.2 (transcript-wise factorization and lower bound).** On any terminating transcript with $R$ successful scalar Reads let $P$ be the frozen-path homogeneous final-field map and let $O$ stack the homogeneous entry-field rows of those Reads. Exactness of any task in Definition 61.1 requires

$$
\ker O\subseteq\ker P,
\qquad
\operatorname{rank}P\le\operatorname{rank}O\le R.
\tag{61.1}
$$

Consequently every such transcript satisfies $R\ge r_0$ if it contains a Tick. For an original branching entry with $L\ge3$, every exact transcript must contain a Tick, so every transcript satisfies

$$
R\ge\operatorname{rank}_{\mathbb Q}A_0=2\nu(C(t))\ge2L.
\tag{61.2}
$$

This remains true despite adaptive original growth and arbitrary rational Adds.

**Proof.** Fix one realized transcript at $x$. Freeze all its operands, addresses, stopping decisions and local choices. Along it every field is affine in the original $x$, because Adds are fixed translations and Tick/growth are linear. Thus its $i$th Read has the form $o_i x+c_i$. For any $\eta\in\ker O$, the alternative entry $x+\eta$ has exactly the same reply at each Read. Induction on completed calls proves it follows that very same path: previous complete replies and local state are identical, so the next command, operand, topology, guards, frame and eventual stopping rule are identical. Its actual final difference is $P\eta$ on the same final material graph.

An exact full-field report is common on this pair and therefore requires $P\eta=0$. A nuller ends at zero on both, with the same requirement. For a self-contained complete future predictor, a nonzero $P\eta$ is separated by some finite actual all-leaf window on the earned final tree: its matrices satisfy $KC=\mathrm{Id}$, hence $K^{\mathsf T}(P\eta)\ne0$. A Read at the corresponding terminal after the corresponding number of common Ticks gives a different literal scalar. The identical retained predictor could not predict both. Thus again $P\eta=0$. This proves the kernel inclusion. Equivalently, define $F$ on $\operatorname{im}O$ by $F(Oz)=Pz$; the inclusion makes this well defined, and extend a basis to obtain a linear map with $P=FO$. This gives the rank inequality with the displayed direction. It is not an assertion that $O$ has at least as much rank as the full original dimension when $P$ discards a kernel.

If a transcript has no Tick, choose a nonzero difference supported on an original internal vertex. Such a vertex exists for the specified entry. Native growth never makes an old internal vertex terminal. Without Tick this difference persists at that old coordinate, never reaches a Read terminal, and gives no other reply difference. It lies in $\ker O$ but not $\ker P$, contradicting the required inclusion. Hence a Tick is mandatory. Theorem 60.2 and Lemma 60.3 now give (61.2). $\square$

**Corollary 61.3 (zero-error random tapes).** If a randomized protocol has a field-independent random tape and, separately for every rational entry, zero error and almost-sure finite termination, the same bound holds almost surely for each entry.

**Proof.** For fixed finite graph, $\mathbb Q^{N_0}$ is countable. Intersect the probability-one correctness/termination events for all entries. On the resulting probability-one set of tapes the deterministic frozen-transcript argument applies to every entry. If backing is part of the uniform termination premise, it must cover these admitted finite runs; a field-dependent failure channel is not silently allowed. $\square$

The cleared-input condition is essential. A retained complete current predictor already contains numerical information and does not need this many new Reads to report itself. Theorem 49.1's analogous affine argument for cleared hidden cherry amplitudes is a supplier, not a second proof that the present rank survives arbitrary original growth. The latter needs (60.1) and symmetry. No lower bound for a larger returning-scalar interface, a Reset-closed task, noisy bounded-error recovery or unrestricted nonlinear register count is asserted.

## 62. Distinct attainment for an earned map and arbitrary current field

**Theorem 62.1 (exact rank-many Reads at the actual advanced field).** Let an original branching graph $u$ and exhaustive current map be earned and retained with authentic access. At a new phase entrance its entire current field is arbitrary in $\mathbb Q^N$, with no accessible field-dependent advice. Put $r=\operatorname{rank}_{\mathbb Q}A$ and use the earned $J,K,C,I$ of (58.3). There is a finite geometry-only selector and an actually executed experiment with exactly $r$ scalar Reads that installs a complete predictor at its actual endpoint

$$
w=A^{H+1}x,\qquad 0\le H\le I.
\tag{62.1}
$$

Its other primitive counts are $H+1$ Tick and $H+1$ Hold, with no Add, growth or Reset. Rank-many Reads are the exact minimum for this arbitrary-field current-predictor task, even if alternative protocols may perform adaptive original growth. The experiment does not restore $x$: its discarded entry kernel is exactly $\ker A$.

**Proof and selector.** Use exact pivot search in fixed material-coordinate order to select $r$ independent columns of $A$. Put these columns in $U\in\mathbb Q^{N\times r}$, a basis of $\operatorname{im}A$. Enumerate pairs $(k,j)$ in increasing $k=0,\ldots,I$ and then terminal order, computing the rows

$$
q_{k,j}=e_{\ell_j}^{\mathsf T}A^kU\in\mathbb Q^{1\times r}.
\tag{62.2}
$$

Keep a row exactly when it increases the row rank of those already kept, stopping at $r$ rows. This stops: if every row annihilated $c$, then $K^{\mathsf T}Uc=0$, so $Uc=0$ by (58.3), and $c=0$. Let $M$ be the square matrix of selected rows in that order and $H$ their largest $k$. Then $M$ is invertible and $H\le I$. All selections depend only on the earned graph, not on the unknown field.

Actually Tick once and Hold. Its field $z=Ax$ lies in $\operatorname{im}A$, uniquely $z=Uc$. For each selected row with $k=0$ actually Read its terminal. For levels $k=1,\ldots,H$, actually Tick; Hold, and Read exactly the selected terminals at that level. The selected literal replies obey

$$
y_{k,j}=e_{\ell_j}^{\mathsf T}A^kz=q_{k,j}c,
\qquad y=Mc.
\tag{62.3}
$$

Solve $c=M^{-1}y$ by finite rational elimination. Compute $w=A^HUc$ and install it before the settled return. All time levels were actually reached on this specimen, so (62.1) is the actual endpoint, rather than a reconstruction of the original $x$ advertised as current. The displayed calls give the exact counts and return the whole $r$ scalars and all intervening ACKs/returns.

Symmetry implies $\ker A^2=\ker A$: if $A^2v=0$, then $\|Av\|^2=v^{\mathsf T}A^2v=0$. Iterating this implication gives $\ker A^n=\ker A$ for every $n\ge1$. Thus (62.1) discards exactly that entry kernel and retains rank $r$. Theorem 61.2 applies at this cleared arbitrary-current entrance and forces at least $r$ Reads on any exact predictor protocol. The same no-Tick contradiction applies to the earned branching graph. This proves the stated minimum, with no claim about other cost coordinates. $\square$

**Construction 62.2 (actual nulling after acquisition).** At the earned field $w$ compute $g=-CA^{I+1}w$ and execute the $I+1$ reversed control rounds of (58.5)–(58.6) with target zero. This physically ends at zero, adds exactly $I+1$ Tick and Hold and $b(I+1)$ Add, and adds no Read. Its $r$-Read total attains the same lower bound for the arbitrary-current nulling task. It does not restore the entry values. A four-way zero-cut inverse then uses the already supplied zero-cut views of §36; no inverse from structural Time to an arbitrary intermediate field is inferred.

**Construction 62.3 (a paid real arbitrary-current entrance).** The arbitrary-current premise can be realized independently of the constrained marking family. From a known-zero alpha build the chosen $u$ by its legal original constructor word, retaining the earned map; if $c_u$ is its number of beta leaves, this uses $c_u$ promotions and $b-1$ splits and creates $N-1$ vertices. Receive an arbitrary owned target $x$ in a separately backed producer. Apply the supplied Proposition 53.2: compute $Cx=(h_0,\ldots,h_I)$, Add all $b$ coordinates of $h_I$, then repeat Tick followed by all Adds of the next descending block through $h_0$. Its genuine endpoint is $KCx=x$, with $I$ Tick and $b(I+1)$ Add, including zeros. Actually Hold for handoff.

Before the receiver's new phase, overwrite or isolate from it every field-dependent producer input, control block, operand packet, reply/transport copy, predictor and control register. Retain to the receiver only the earned graph/map, authentic access and field-independent code/context. For an explicit erasing implementation, overwrite all allocated dependent buffer capacities and registers after their last use, including unused suffixes of reused frames; count each overwritten bit and every retained cleared capacity. Leave no accessible numerical archive. Preparation has just produced every possible $x$, but supplies no field advice to this receiver. It can now actually run Theorem 62.1 and, if selected, Construction 62.2 on the same specimen. Provider input, preparation, clearing/isolation, source storage and receiver work are separate paid resources. A predictor retained across the handoff would violate this minimum's premise.

The marked family (58.1), by contrast, has only $b-1$ unknown coordinates after its known calibration and saved records. The rank-$r$ arbitrary-current minimum is not a minimum for that constrained family. Marking followed by a different window is not counted here as another independent acquisition result.

## 63. Separate attained call vectors on complete runs

**Proposition 63.1 (binary run including its real entrance).** For one actual arbitrary-field entry of §58 let

$$
R_{\rm mark}=L^2+\sum_{q\in\mathcal B}(L-q),
\tag{63.1}
$$

where $\mathcal B$ is the set of preorder positions of the entry beta leaves among its $L$ leaves. For a binary experiment first use exactly §§34–36's original full-window no-Reset acquisition with target zero, rather than §58's target $f$. Then actually Add one at the first earned terminal and Hold. Let $K_1$ count subsequent Next, $R_1$ count Sample2, and $Q_1$ count Recall/Length. With $m=K_1+R_1I$, the exact primitive counts on this one specimen are

$$
\begin{aligned}
P&=2L-1,&S&=c,&\mathrm{Reset}&=0,\\
\mathrm{Read}&=L+R_{\rm mark}+b(I+1)+K_1+2R_1,\\
\mathrm{Add}&=2L+c+b(I+1)+1+m,\\
\mathrm{Tick}&=2I+1+m,\\
\mathrm{Hold}&=L+2I+5+K_1+R_1(I+1)+Q_1.
\end{aligned}
\tag{63.2}
$$

Here $P$ counts all attempted promotions, including branch and wrong-type refusals; $S$ counts the actual successful splits. For the separate known-alpha small entrance of §55, putting $\eta=0$ for the four-vertex case and $\eta=1$ for the five-vertex case gives instead

$$
P=1+\eta,\quad S=1,\quad\mathrm{Reset}=0,\quad
\mathrm{Read}=K_1+2R_1,\quad\mathrm{Add}=1+m,\quad
\mathrm{Tick}=m,\quad
\mathrm{Hold}=1+K_1+R_1(I+1)+Q_1.
\tag{63.3}
$$

**Proof.** The original full-window zero entrance has Theorem 36.2's counts, including its final Hold. The origin adds one Add and Hold. Each Next adds one Tick/Add/Hold/Read; each Sample2 adds $I$ Tick/Add, $I+1$ Hold and two Read; Recall/Length add one Hold each. This proves (63.2). The two known-alpha construction words and the same origin/continuation give (63.3). Relative to replacing Sample2 by the original full-window Sample on this same acquired graph, the Read reduction is exactly $R_1[b(I+1)-2]$; the actual final graph, field and Tick/Add/Hold counts agree, but the literal returned sampling contracts differ. $\square$

**Proposition 63.2 (preserved-entry acquisition).** Theorem 58.2, from arbitrary attachment through its restored handoff and with no optional continuation, has

$$
\begin{aligned}
P&=2L-1,& S&=c,&\mathrm{Reset}&=0,\\
\mathrm{Read}&=L+R_{\rm mark}+b(I+1),\\
\mathrm{Add}&=2L+c+b(I+1),\\
\mathrm{Tick}&=2I+1,&\mathrm{Hold}&=L+2I+4.
\end{aligned}
\tag{63.4}
$$

There are $a+c=L$ successful growths, $a+2c$ new material cells, $a+2c$ binding assignments, and $4a+8c$ structural reference assignments under §21's three-reference-field convention. Field ACK payloads number $3L+c+b(I+1)+4I+5$; the Read scalars and the $2L-1+c$ complete growth/refusal replies are separate outputs.

**Proof.** Arming has $L$ Read and Add and two Holds. The $L$ leaf assays have $R_{\rm mark}$ Reads, $L+c$ rearming Adds and $L$ Holds; traversal has $2L-1$ P and $c$ S; final marking adds one Hold. Observation has $b(I+1)$ Read, $I$ Tick and Hold. Restoration has $I+1$ Tick and Hold and $b(I+1)$ Add. These sums give (63.4), and summing Add/Tick/Hold gives its ACK count. The original material templates give each fresh/reference count. Saving $z$, changing the target/control operands, constructing and returning $x,f$ and the four exports add real storage, traffic and local calculation; they do not add a hidden source call. $\square$

Equal primitive counts with the old nulling construction do not imply equal total costs: the target values, retained old values, controls, outputs, widths and calculation differ. Conversely those differences do not justify a claim that either complete total-cost vector dominates the other.

**Proposition 63.3 (arbitrary-current attainment and optional nulling).** The phase of Theorem 62.1 has exactly $(\mathrm{Read},\mathrm{Tick},\mathrm{Hold})=(r,H+1,H+1)$ and no other source calls. Include Construction 62.3's known-alpha preparation, owned arbitrary input and held handoff on that same specimen. The resulting totals are

$$
P=c_u,\quad S=b-1,\quad\mathrm{Read}=r,\quad
\mathrm{Add}=b(I+1),\quad
\mathrm{Tick}=I+H+1,\quad\mathrm{Hold}=H+2,\quad\mathrm{Reset}=0.
\tag{63.5}
$$

Actually appending Construction 62.2 changes Add to $2b(I+1)$, Tick to $2I+H+2$ and Hold to $H+I+3$, leaving Read $r$. The output is then zero, whereas without that appended stage it is (62.1). Producer reception, exact row/column selection, erasure/isolation and all returned copies remain additional paid work. These are alternatives with their own actual endpoints, not coordinates borrowed from different runs.

## 64. Complete retained service after every acquisition

**Theorem 64.1 (all original replies and successors).** At each completed handoff in §§56, 58 and 62 retain the earned current logical term, its whole material graph, the exhaustive current raw table and its canonical inverse, the complete actual current vector, the installed parser/control and the authentic reference/current and fresh grants. The vector is respectively $A^Ix_w$, $f$, $A^{H+1}x$, or zero if the stated nulling stage was actually executed. With the original serialization and backing hypotheses, one finite controller predicts and maintains every complete reply and actual successor for every finite common adaptive continuation of the entire six-operation menu.

**Proof.** Maintain equality of actual and retained term, graph, whole field and exhaustive map at each settled cut. Each claimed initialization has been proved at its actual endpoint. The full one-step correspondence is as follows.

| Acquired complete request | Predicted and actual successor | Entire source result |
| --- | --- | --- |
| Enabled $P_p$ at alpha | retain old $p$ and all other old values/edges; add zero $pL$; move the acted label to $pL$ | original Growth$(P,p)$ |
| Enabled $S_p$ at beta | retain $p,pL$ and all old values/edges; add zero $pLL,pR$; move the acted label to $pLL$ and append next integer at $pR$ | original Growth$(S,p)$ |
| Absent growth address | identity | original absent refusal |
| Growth at a branch | identity | original branch refusal |
| Growth at the wrong leaf type | identity | original wrong-type refusal |
| In-range Add$(j,q)$ | add $q$ at the earned current terminal $\lambda(j)$ | fixed Add acknowledgement |
| Tick | replace every current coordinate by its current-neighbour sum | fixed Tick acknowledgement |
| In-range Read$(j)$ | identity | literal entire rational $x_{\lambda(j)}$ |
| Hold | identity, with the held interval | fixed Hold acknowledgement |
| Integer Add/Read label outside the current roster | identity | RangeRefusal |
| Malformed complete packet, including the former Reset tag | identity | BadFrame |

Each guard is computed from the earned logical code, with a marker never treated as a logical target. A successful growth records the actual fresh coordinates and the installed label/grant lifecycle, not a fictitious internal move. Canonical Add/Read computes the actual inverse raw table and forwards that raw call through the genuine binding. An arbitrary rational operand is handled with its full sign and denominator. The retained vector has all internal coordinates needed for the Tick row. Refusals and range outcomes are distinct whole replies; none supplies an extra hidden field sample.

Acquire each actual finite input into its real backing before releasing its bit latch. A proper incomplete frame retains the real parser, bytes and pending state, makes no completed edit and has no completed reply. When a complete call is enabled, forward it, consume the entire actual output, End and local acknowledgement, return the navigation/dispatch position, and finish the matching retained successor before another settled cut. The held source allows finite local parsing, rational work, navigation, allocation reservation and output construction without unrequested dynamics. Missing rights disable the call; they are not an invented refusal. Fresh rights and adequate finite material/communication/work backing are the stated premises for completion.

Sealed reports, decoded words, arrays and inner replies use their actual output frames and complete acknowledgement/Return lifecycle. Pending requests/replies, target addresses, source and observer update buffers coexist while needed; no claim about inverses at a busy cut or crash recovery is made. Induction on completed requests proves equality of the entire outputs and successors. An adaptive next request selected from the common replies is consequently common as well. Fixing a common random tape gives the same finite induction. Hypothetical local trials use a separately paid copy and do not execute the source. $\square$

**Proposition 64.2 (exact current canonical kernel).** Within a fixed common binding/authority/framing context, two earned current states have identical complete canonical service for every common finite sufficiently backed continuation if and only if their ordered original terms and entire current fields agree. Thus the four views of §§57 and 59 have precisely this current kernel on their respective joint images.

**Proof.** Equality gives the one-step invariant and then Theorem 64.1. If terms differ, at their first differing logical constructor a P request has different success, branch or wrong-type reply. If fields differ on the same term, the supplied all-leaf forcing identity makes some $J^{\mathsf T}A^r$ Read after finitely many actual Ticks differ. These are legal common finite distinguishing continuations. The proved four-view inverses transport exactly this pair equality. The private raw table is fixed common context; absent that condition canonical equality is not a claim to recover a different raw attachment, an archive or reference bytes. $\square$

For an additional concrete acquired growth use at any of these endpoints, follow left children of the retained current code to its leftmost logical leaf. Select P if its earned type is alpha and S if beta. Submit that actual addressed request, consume its whole Growth and completed return, and update the retained graph, map and field by the first two rows. Its actual successor is the zero extension of the then-current vector on the literal new vertices. It adds one successful growth and its actual address/referral/allocation cost; it does not add a Tick or Reset. For the branching domains here the leftmost leaf is beta, so the selected S allocates two zero vertices. This is an actual internal selector using acquired data, not an external Tag/readout port. It need not preserve the sampled or restored image, and Theorem 64.1 continues to apply.

## 65. Literal widths, local work and simultaneous material

**Definition 65.1 (one literal accounting convention).** Use §17.2's finite codecs. Let $\mathsf b(n)$ be binary length for $n\ge0$, with $\mathsf b(0)=1$. A reduced rational $q=n/d$, $d>0$, has payload

$$
\ell(q)=2\mathsf b(|n|)+2\mathsf b(d)+3.
\tag{65.1}
$$

A valid nonnegative raw selector $j$ has $2\mathsf b(j)+1$ payload bits. A growth request at $p$ has $2|p|+4$ bits and its successful Growth reply $2|p|+5$; an original tagged refusal has five. Fixed field tags, reply tags, RangeRefusal/BadFrame, full packet framing, End, local acknowledgements, Print and Return retain their actual finite lengths. Invalid signed selectors and malformed packets are charged by their actual received bytes rather than the valid-selector formula.

For every one of the particular runs in §63, its exact variable payload is the sum of $\ell(q)$ over every actually sent Add operand and every actual scalar reply, plus $2\mathsf b(j)+1$ for each valid Add/Read selector, plus the stated lengths for every actual addressed growth request/reply/refusal. Add every fixed tag/framing/return occurrence and every actual report/export payload and copy. In particular all zero Adds and zero scalar replies have complete nonempty payloads. Reporting $(t,x,\lambda_0),(u,f,\lambda)$, the causal data, the germ or the decoded word transmits their literal finite encodings; this work is additional to the source-call vector. A formula symbol for an array is not a zero-cost transmission of it.

More explicitly, let $\mathcal A,\mathcal R,\mathcal G$ index the actual Add, Read and growth transactions; let $\mathcal G_+$ and $\mathcal G_-$ partition growth into successes and refusals. Let $\tau_c$ be each fixed field request-tag width, $\tau_{\rm scalar}$ the fixed scalar reply-prefix width, and $\tau_{{\rm ack},c}$ the fixed acknowledgement width for operation $c$ in this installation. Define $F_{\rm run}$ to be the sum of every remaining actual framing/End/local-acknowledgement/Return bit, including separately present inner and outward transactions. Then the exact source-channel traffic in these runs is

$$
\begin{aligned}
T_{\rm source}={}&F_{\rm run}+\sum_{\text{field calls }i}\tau_{c_i}
 +\sum_{i\in\mathcal A\cup\mathcal R}(2\mathsf b(j_i)+1)
 +\sum_{i\in\mathcal A}\ell(q_i)\\
&+\sum_{i\in\mathcal R}\bigl(\tau_{\rm scalar}+\ell(y_i)\bigr)
+\sum_{c\in\{\mathrm{Add},\mathrm{Tick},\mathrm{Hold}\}}\tau_{{\rm ack},c}\,n_c\\
&+\sum_{i\in\mathcal G}(2|p_i|+4)
 +\sum_{i\in\mathcal G_+}(2|p_i|+5)+5|\mathcal G_-|.
\end{aligned}
\tag{65.2}
$$

These are fixed literal constants and actual strings of the stipulated installation, not quantities inferred from elapsed time. Add the report/export connections' corresponding actual bit sums separately. One explicit finite report codec uses two bits per logical constructor, the same $1^{|p|}0p$ for an address, and an array count of $2\mathsf b(n)+1$ bits followed by its $n$ literal entries. Thus a vector payload is exactly $2\mathsf b(n)+1+\sum_{i=1}^n\ell(v_i)$; a list of label/address pairs has that count prefix followed by $\sum_j[2\mathsf b(j)+1+2|\lambda(j)|+1]$ bits. Causal-order records additionally encode their actual event addresses and finite relation pairs in that same integer/address codec. Selection pairs $(k,j)$ and counters have their actual integer-code widths. If $\mathcal E$ indexes the dependent buffer/register overwrite events in Construction 62.3, its specified erasing implementation performs exactly $\sum_{E\in\mathcal E}\operatorname{capacitybits}(E)$ clearing writes; repeated reuse/clearing contributes repeatedly. Reception, encoding, transmission and bit copies are additional actual work, and cleared but retained capacities still coexist in the material bill.

**Proposition 65.2 (finite algorithms with actual precision).** The row/column selection, forcing coefficients, window reconstruction, restoration/nulling controls and greedy word calculation above have finite exact implementations using only their earned finite data. Their arithmetic and storage widths must be charged at their actual values.

**Proof and one implementation.** Construct $C$ by §31's polynomial forcing recurrence. Initially a leaf has one unit coefficient; a force shifts one polynomial and subtracts at most two others. If $s$ forces have occurred, every coefficient-vector $\ell^1$ norm is at most $3^s$, by induction. There are at most $I$ forces, degree at most $I$, and at most $Nb(I+1)$ dense integer coefficient slots. Checking available forces by scanning finite adjacency and constructing the finite coefficient arrays is an actual graph/integer calculation, not an oracle. The argument that all leaves force the whole tree is supplied by the finite stalled-forest contradiction of Definition 31.1.

The products $C^{\mathsf T}Y$, $C(f-A^{I+1}d)$ and their zero-target variants take ordinary finite sums and products, with $O(Nb(I+1))$ rational arithmetic operations for each dense multiplication. A sparse application of adjacency starts a new $N$-entry zero buffer and adds along the $2(N-1)$ directed edges. Thus a source Tick has $N$ initializations and $2(N-1)$ directed additions; a separate synchronized predictor pays its own computation/buffer, and source/observer copies and cleanup are also charged. Powers applied to a vector are repeated sparse steps, with no free matrix exponentiation.

For Theorem 62.1, exact Gaussian elimination selects columns of the earned $N$-matrix in $O(N^3)$ rational operations. Starting at $U$, propagate $A^kU$ by the sparse rule through $k=I$, costing $O(INr)$ operations, inspect all $b(I+1)$ candidate rows and maintain a row echelon basis in $O(b(I+1)r^2)$ operations. Store each selected pair and its row, form $M$, and solve the augmented $r$-system in $O(r^3)$ operations. Pivot search chooses the first nonzero entry in the fixed order; a nonzero pivot exists by the proved rank, and reduction gives finite exact rationals. These are conservative attained arithmetic bounds, not a bit complexity or minimal selector theorem.

For Theorem 55.2 generate powers of $A$ through the weights needed by (55.4), storing their scalar list and reusing vector scratch. At a genuine word of length $m$, the largest parity index is at most $\lfloor m/2\rfloor$; a next weight is obtained in $O(m+1)$ sparse steps. Greedy comparison/subtraction, interleaving and output take finitely many operations linear in that list, with their actual bit widths. Evaluate the recovered polynomial by sparse Horner steps and then advance exactly $I$ times for the current endpoint, taking $O(N(m+I+1))$ further arithmetic work. The total vector recognizer has a finite bound from its supplied integer moments even for an off-image vector. No exhaustive word search is needed, but no constant-width computation is implied. $\square$

Let $W_{\rm run}$ be the largest actual numerator/denominator bit width across the plant, acquired inputs, replies, controls, reports, retained arrays and every arithmetic intermediate of the chosen finite implementation. Each admitted finite run has finite $W_{\rm run}$. For preserved-entry and arbitrary-current acquisition there is no $N$-only bound: the entry/owned input is already arbitrary rational. The integer adjacency/forcing operations on fields and controls preserve a common denominator dividing the least common multiple of the actual input denominators, but Gaussian-elimination scratch can introduce determinant denominators and is separately included in $W_{\rm run}$. For any chosen exact rational cost function $\mathsf A(W)$ including reduction, the arithmetic-operation bounds multiply by $\mathsf A(W_{\rm run})$, rather than assuming one-bit rational arithmetic.

In the restricted binary phase, if $M_j$ is the maximum absolute entry after $j$ encoded digits, $M_0=1$ and $M_{j+1}\le3M_j+1$, hence $M_j<3^{j+1}$. Its source fields and sampled entries have $O(m+I+1)$ bits through a sample starting at length $m$. Weight generation likewise has growing integer widths. The $2^m$ possible length-$m$ words are distinct, so any exact finite binary representation of their two-sample data collectively needs at least $m$ distinguishing bits in the worst case. Two scalar calls are not two fixed-precision cells.

**Definition 65.3 (stores and authority on the same run).** An explicit sufficient layout retains the plant graph, field and its separate Tick result buffer; observer code, current graph/code, complete raw and canonical tables and full predictor with its own result buffer; forcing matrix $C$; acquired windows and control blocks; reconstructed entry, marked, advanced and target vectors while live; and the required row/column bases, selected $(k,j)$ list, square solve matrix and elimination scratch. Preserved-entry acquisition additionally retains the saved $L$ original terminal rationals and original/current reports. In arbitrary-current attainment the producer's owned input and control buffers, receiver's selected rows and its new predictor coexist when used. Binary recovery uses its weight lists, both literal scalars, polynomial digits, decoded/output word and vector-evaluation scratch simultaneously when needed. None is credited as another representation's replacement unless it is actually released and its reuse work paid.

For example reserve separately $2N$ plant rational slots, $2N$ predictor/update slots, $Nb(I+1)$ integer forcing slots, $b(I+1)$ window slots, $b(I+1)$ control slots and $6N+L$ rational vector/saved-value slots. Here the extra $L$ slots are the saved old roster values in preserved-entry acquisition and are omitted when that stage is absent. The rank-based selector may additionally reserve $2Nr+2r^2+4r+N^2$ rational slots for two propagated column buffers, square/augmented row work, selected replies/coordinates and dense initial elimination. The binary decoder additionally reserves its finite weight and digit/output lists. These sufficient capacities can be allocated before their respective uses; actual simultaneous old/new/output copies require their own slots. This layout is an attained backed implementation, not a space optimum.

Structural address strings, traversal stacks, counters/selectors, the real root/dispatcher/input/output connections, reference fields and current/fresh grants, source allocations and binding assignments, parser and proper incomplete packet, acquired request, target, pending reply, End/acknowledgement/return controls and caller-retained outputs are separately backed and counted by their actual widths. Root-based navigation pays every actual descent and return. Tables expose no authority by themselves. Preparation/provider input reception, local selection, serialization, copies, initialization, overwriting and retained cleared capacities remain in the same run's bill. A copied hypothetical experiment or isolated dependent archive is an additional resource, not an omitted observer store. Uniform finite code handles every finite admitted case given sufficient finite backing; finite program size is not bounded lifetime memory.

The attained accounts assert neither a total-cost dominance among the three tasks nor a uniform optimum over traffic, source size, precision, references, local arithmetic, storage, Tick count or total physical resources. The selected Read minima apply only to their proved tasks and information domains.

## 66. Supplier subtraction and the remaining realization boundary

**Correspondence 66.1 (native and library suppliers).** [AA §17](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#17-birth-typed-local-growth-and-its-causal-reconstruction) supplies the original constructor/birth class, native causal reconstruction and literal persistent templates; its §20 supplies acquired-frame, real-reference and completed-return mechanics. [NLBA §§2–3 and 11](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md) supplies the complete unit leaf metric/subdivision inverse, all-leaf forcing and original ordered-root rigidity. This volume's §§17–20 and 34–36 supply the raw-label lifecycle, literal marking, actual full-window reconstruction, reversed nulling and synchronized service. Formula (58.5) reuses that control with a different fully reconstructed target. Neither marking nor generic observability is reproposed as a new outcome.

The source-level correspondences to the existing declarations and their owning expositions are precise:

| Supplier | What is reused and what is not transferred |
| --- | --- |
| [NativeMaterialRootRecognition](../../../D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.lean), [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.scribe.cs) | `original_rigidity` and `effective_inverse` use $\mathcal D$, complete linear terminals and at least three leaves. The private `original_root`, `coordinates_from_root`, `terminals_ordered`, `catalog_complete`, `fits_unique` and inverse helpers already supply their root/order/finite-recognition work. Proposition 55.3 supplies only the missing two-leaf application bridge; these given-graph results do not acquire an unknown raw attachment. |
| [NativePredecessorRowRecovery](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.lean), [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.scribe.cs) | Its concrete `sigma` sends true/alpha to false/beta and beta to the beta/alpha pair. Its priority `delta`, private `sigma_not_alpha` and `delta_sigma` already supply the syntactic parsing mechanism of Lemma 59.1. Its public result is predecessor-row recovery with supplied old occurrence support; it is not a physical field-restoration theorem or a grant of an inverse growth operation. |
| [FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean), [Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs) | Its real finite-inner-product stacked-kernel/rank/Gram equivalence is the ordinary observability supplier. The rational matrices here have the explicit equation $KC=\mathrm{Id}$, which remains true over the reals. Actual sample times, their advanced endpoints, geometry-only row selection and complete held acquisition still require the displayed native protocols. |
| [RegularCHS/Cubic](../../../D5/S3/Combinatorics/Graph/RegularCHS/Cubic.lean), [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/RegularCHS/Cubic.scribe.cs) | Its private `even_log_convex` concerns total rooted closed-walk moments. It does not assert the needed fixed-leaf statement. Equation (55.2) supplies that exact fixed-leaf Cauchy–Schwarz bridge directly; no new general moment inequality is claimed. |
| [NoEvenCycleRank](../../../D5/S3/Combinatorics/Graph/Walks/NoEvenCycleRank.lean), [Scribe](../../../Blueprint/D5/S3/Combinatorics/Graph/Walks/NoEvenCycleRank.scribe.cs) | The weighted no-even-cycle theorem has a characteristic-two field hypothesis. It cannot simply be instantiated over $\mathbb Q$. Lemma 60.3 supplies the needed classical rational forest specialization by leaf elimination, as an intermediate supplier calculation rather than a new generic matching theorem. |

For walk counts, use [pinned mathlib `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean), for finite decidable vertices and semiring entries, specialized here to unit natural/integer/rational adjacency. It supplies nonnegative integral moments, shortest-walk onset and the at-most-three choices per step. It supplies neither the unknown map nor source access. The proof uses the symmetric adjacency identity on this actual tree, not an arbitrary walk-total bound.

The all-leaf residual equation (58.3) is the mature infection/forcing mechanism. [Burgarth and Maruyama, *Indirect Hamiltonian Identification through a small gateway*, arXiv:0903.0612v1, §II](https://arxiv.org/html/0903.0612v1) defines infection by a marked vertex's unique unmarked neighbour and uses that residual mechanism under its known-graph Heisenberg/gateway hypotheses. Its quantum preparation, spectral data and tomography are not this scalar terminal service. Only the combinatorial mechanism transfers with the explicit polynomial recurrence of §31. Superincreasing greedy subtraction is also mature; see [Hellman, *An Overview of Public Key Cryptography*, §III, p. 27](https://ee.stanford.edu/~hellman/publications/31.pdf), where each weight exceeding the sum of its predecessors gives precisely the highest-weight decision used in (55.3)–(55.4). No cryptographic hardness claim is used. Cauchy–Schwarz, row selection, rank-nullity, affine transcript freezing and forest elimination are credited standard tools.

**Correspondence 66.2 (public native and rational results already supplied).** The source-relative increment is limited by the following existing results, with their actual original hypotheses preserved.

This volume's §§30–33 already give binary recovery for $b\ge4$, a complete literal full-window sampler at $A^Ix_w$, and independent sampled views and full continuation. NLBA's passive leaf-history results already distinguish endpoint power histories in their stated domain. Theorem 55.2 sharpens the native criterion to exactly branching, including the two-leaf root bridge, and §56 realizes the smaller two-Read contract at the same advanced endpoint with its precisely restricted late-observer converse. The old full-window contract is not silently replaced by two numbers. Greedy inversion and recognition are consumed support for this one criterion.

Sections 34–38 already acquire a marked arbitrary-field plant and null it without Reset. They do not recover arbitrary terminal values after overwriting them or physically return the old entry field. The retained old values, restored target, exact image and independently invertible measured views of §§58–59 provide that additional preserved-entry relation. This is the complete full-window route; a potentially smaller unknown-coordinate alternative is neither required nor claimed here.

The public §§39–44 already earn an arbitrary raw bijection with one Read under their known-whole-zero, growing-waveform and final-Reset conditions. Public §§45–50 already give cleared root-read cherry-amplitude recovery and its simultaneous split/Read bounds under that changed root interface. Public §§51–54 already give an original first-terminal active separating family, an actual growth witness, the owned finite-pair one-Read selector and arbitrary owned-target preparation. Their rank arguments, active visibility and producer are suppliers. An owned pair is field advice and does not solve Definition 61.1's arbitrary cleared field problem. The extra argument there is the actual induced-growth identity and symmetric-image preservation of §60, followed by the adaptive bound and separately earned arbitrary-current attainment. A generic rank inequality alone would not show that later growth/Ticks cannot erase the required rank.

[AAII §§84–92](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md#84-growing-native-fields-with-two-declared-clock-phases) already give the positive-diagonal, positive-edge, invertible-law fresh-support inverse for every successful growing serial word, its declared pre/post growth clocks, actual diagnostics and full continuation. Those laws are $a\mathrm{Id}+cA$ under their stated conditions, not the zero-diagonal unit $A$ here. Their successful serial-growth recovery is not another proposed result of this appendix. Conversely the binary theorem does not recover their changing-support serial word or an arbitrary old native journal.

[Recovery Geometry II §§84–95](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md#84-the-full-bounded-scalar-alphabet-at-every-rational-origin) already give the full scalar $D_s=\{0,\ldots,s-1\}$ iff at every reduced origin $p/q$ for $\lambda=r/s$, namely injectivity exactly when $s\nmid p$, and its legal bounded-digit collision when the condition fails. They also give certified rational positive-link contracting-vector later-origin acquisition and a total bounded-pulse recognizer, with their denominator-prime certificate and actual advanced prediction. They are complete suppliers in those domains, not unresolved scalar/vector reservations. Original unit branching adjacency is not a positive contracting endpoint path and does not meet that denominator-prime certificate: its least common entry denominator is one. No E15 scalar iff, general numeration fact or certified later-vector recognizer is counted again. Earlier statements explicitly scoped to an older source pin retain that scope; none is retroactively reinterpreted as a current absence claim.

The resulting attribution is repository-derived source-specific synthesis and application, with three distinct recovered relations: restricted binary history, physically preserved arbitrary entry, and arbitrary-current rank obstruction/attainment. It is not a claim of worldwide priority or an exhaustive absence theorem about other literature, private work or every repository file. The mathematical content here consists of ordinary quantified proofs in the declared model; no new compiled or kernel-validation claim is made.

**Boundary 66.3 (the joint source actually supplied).** In each construction the native term, persistent vertices, field law, literal Add/Tick/Read calls, current/fresh rights, selected addresses, observed records, physically reached endpoint and synchronized continued service belong to the same stipulated source. The four expressions invert only on their explicitly proved joint images, under their separately retained common callable context. Current-field prediction after discarding $\ker A$ is not restoration of that kernel, and sampled binary injectivity is not observability of arbitrary lost entry values. A computed onset table or germ is not an unperformed literal observation. A finite exact mathematical protocol does not authenticate hardware or make its backing and authority free.

No universal alpha/beta minimum, common native/original-path/quantum realization or physical-law conclusion follows. Such a realization would have to match actual initialization, legal actions and refusal/disabled domains, whole outputs, successor fields, selection/acquisition/retention, references/rights and simultaneous resources. Equality of numbers, ranks, abstract syntax or observation kernels alone supplies none of those missing bridges. The original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization and final-no-Ready obligations retain their original scopes. The full common-source programme, noisy/finite-precision acquisition and unrestricted erased-history recovery remain outside these three conditional results.

## 追加锚（本行以下为增补区）

## 67. The ternary native threshold, including the five-vertex path

**Definition 67.1 (the ternary image on a prescribed native graph).** Retain Definition 55.1's original class $\mathcal D$, symmetric zero-diagonal unit adjacency $A=A_u$, complete earned terminal map, genuine binding and six-operation installation. There is no Reset. For every finite term, including alpha and beta, the same persistent templates and finite-call semantics apply; the arbitrary-attachment lower bound $L\ge3$ in Assumption 34.1 is not imposed on this prepared known-graph task. Physically establish whole zero on the prescribed $u$, then Add one at its first canonical terminal $e$ and Hold. For $w=d_0\cdots d_{m-1}\in\{0,1,2\}^*$ execute precisely Definition 55.2's complete Next composite for each digit, now permitting Add operand two as well. In particular every digit still includes its original literal Read at $e$ and its three acknowledgements. Then

$$
x_w=F_w(A)e,\qquad
F_w(z)=z^m+\sum_{i<m}d_i z^{m-1-i}.
\tag{67.1}
$$

The empty word has polynomial one, and a length-$m$ zero word has polynomial $z^m$. A late receiver has the earned graph, map, callable context and this image promise, but no word, length, earlier Read replies, input journal, field-dependent advice or dependent accessible producer state. Graph-dependent finite calculations are paid local work. The actual entrance in §69 supplies whole zero and the map without changing the prescribed final $u$ to a marked replacement.

**Theorem 67.2 (exact ternary criterion and graph-only sample data).** For every $u\in\mathcal D$, the map $w\mapsto F_w(A_u)e$ on all finite ternary words is injective if and only if $N=|V(u)|\ge5$. Exactly those terms admit the two additional late Reads of §68, at sites and times depending only on their earned finite graph, with finite exact decoding and complete service at the actually advanced endpoint. The threshold includes $u=\langle\beta,\beta\rangle$, whose material graph is the five-vertex path; it excludes the four-vertex branch $\langle\beta,\alpha\rangle$.

**Proof.** The recurrence $x_{wd}=Ax_w+de$ proves (67.1) with the unchanged original operations. We first construct the decoding weights on the positive domain, then give whole-field collisions on every excluded term.

A branching term has $L$ logical leaves and $c\ge1$ beta leaves, hence $N=2L-1+c$. The two-leaf terms are exactly $\langle\beta,\alpha\rangle$ and $\langle\beta,\beta\rangle$, of sizes four and five. Every other branching term contains an induced five-vertex path. Indeed the first terminal is at distance at least two below the root. If the left child is a branch, that distance is at least three, while the last terminal is at least one below the root in the other child. If the right child is a branch, its last terminal is at least two below the root, while the first remains at least two below the root. If neither child is a branch and the term is not the four-vertex case, both are beta and both distances are two. In all these cases the first-to-last terminal path has at least four edges. Five consecutive vertices on this tree path induce a $P_5$.

Suppose first $N>5$. The ordinary path spectrum gives $\rho(P_5)=2\cos(\pi/6)=\sqrt3$. The induced $P_5$ is a proper principal submatrix of the connected nonnegative adjacency $A$. Strict Perron comparison therefore gives $\rho(A)>\sqrt3$. These are the classical path spectrum and Perron results of Brouwer and Haemers, *Spectra of Graphs*, [§1.4.4 and Theorem 2.2.1(i),(iii),(v)](https://www.win.tue.nl/~aeb/2WF02/spectra.pdf), applied to the actual unit material adjacency, not a positive-diagonal modification.

Use the fixed-seed return moments from (55.2),

$$
r_j=e^{\mathsf T}A^{2j}e>0.
$$

Their ratios are nondecreasing by that equation. Moreover $r_{j+1}/r_j\to\rho(A)^2$. To see this last specialization explicitly, use a real orthonormal eigenbasis $v_h$ with eigenvalues $\lambda_h$:

$$
r_j=\sum_h |\langle e,v_h\rangle|^2\lambda_h^{2j}.
$$

After division by $\rho(A)^{2j}$ the terms with $|\lambda_h|<\rho(A)$ tend to zero. The remaining coefficient sum is positive because the Perron eigenvector is strictly positive at $e$. Applying the same calculation to $r_{j+1}$ proves the limit. Finite spectral decomposition and the cited Perron assertions are the standard suppliers here.

Consequently the following exact integer search terminates using only $A$ and $e$: find the first $J\ge1$ with $r_{J+1}>3r_J$. Set

$$
f=e,\qquad K=2J,\qquad a_j=r_{J+j}\quad(j\ge0).
\tag{67.2}
$$

The search is by sparse adjacency powers and integer comparisons; it does not require computing a real eigenvalue or consulting the hidden word. Monotonicity of the ratios gives $a_{j+1}>3a_j$ for every $j\ge0$.

For the remaining positive case $N=5$, put $f$ at the other canonical terminal of $\langle\beta,\beta\rangle$. The path order is $LL,L,\varepsilon,R,RL$, so $e=LL$ and $f=RL$ are both authentically earned terminals. In the even bipartition $(LL,\varepsilon,RL)$, the restriction of $A^2$ is

$$
B=\begin{pmatrix}1&1&0\\1&2&1\\0&1&1\end{pmatrix}.
$$

It satisfies $B^3=4B^2-3B$. Thus, writing $s_n=f^{\mathsf T}A^{2n}e$, the initial values $s_1=0,s_2=1$ and recurrence $s_{n+2}=4s_{n+1}-3s_n$ for $n\ge1$ give

$$
s_n=\frac{3^{n-1}-1}{2}\quad(n\ge1).
$$

Here this identity follows also by substituting the displayed expression in that recurrence and its two initial values. Set

$$
K=4,\qquad a_j=s_{j+2}=\frac{3^{j+1}-1}{2}\quad(j\ge0).
\tag{67.3}
$$

These weights start $1,4,13,40,\ldots$ and satisfy $a_{j+1}=3a_j+1$. This is a calculation at the opposite terminal of the actual $P_5$, not a replacement of that graph or of its read interface.

In both cases $a_0>0$ and $a_{j+1}>3a_j$, so

$$
a_D>2\sum_{j<D}a_j\quad(D\ge1).
\tag{67.4}
$$

For example, bound each earlier weight by $3^{-(D-j)}a_D$ and sum the finite geometric series. Bipartiteness gives, for any finite polynomial $F(z)=\sum_k c_kz^k$ with $c_k\in\{0,1,2\}$,

$$
\begin{aligned}
f^{\mathsf T}A^{K-1}F(A)e&=\sum_{j\ge0}c_{2j+1}a_j=:Y_{\rm odd},\\
f^{\mathsf T}A^KF(A)e&=\sum_{j\ge0}c_{2j}a_j=:Y_{\rm even}.
\end{aligned}
\tag{67.5}
$$

For (67.2) these are seed return exponents $2(J+j)$. For (67.3), $K-1=3$ and an odd exponent $2j+1$ give cross exponent $2(j+2)$, while $K=4$ and an even exponent $2j$ give the same cross exponent. Wrong-parity cross moments vanish because $d(e,f)=4$ is even. This checks both whole-terminal sites and both actual offsets.

Generate the known positive integer weights through the first one exceeding $M=\max(Y_{\rm odd},Y_{\rm even})$. For each total, descend the preceding list. At weight $a_D$, take the quotient of the residual by $a_D$ rounded down, and subtract that quotient times $a_D$. On the promised sums the quotient is the actual digit in $\{0,1,2\}$: (67.4) puts the sum of all lower contributions strictly below $a_D$. Both residuals therefore end at zero. Interleave the two recovered coefficient lists. The highest nonzero coefficient of a genuine $F_w$ is one; its degree gives $m$, and the lower coefficients in descending order give $d_0,\ldots,d_{m-1}$. In particular $F=1$ decodes the empty word and $F=z^m$ decodes the length-$m$ zero word. The weights grow without bound, so generation and decoding terminate without length advice. Equality of the two functionals in (67.5) forces equality of these coefficient lists, proving field injectivity for all $N\ge5$.

The only terms with fewer than five material vertices are alpha, beta and $\langle\beta,\alpha\rangle$. At alpha the empty word and $1$ both give $e$, because $A=0$. At beta the empty word and $00$ both give $e$, because $A^2=\mathrm{Id}$. At the four-vertex path the characteristic polynomial is $q(z)=z^4-3z^2+1$, obtained by the usual path determinant recurrence. Cayley–Hamilton gives $q(A)=0$, and

$$
(z^2+1)q(z)=z^6-2z^4-2z^2+1.
\tag{67.6}
$$

The distinct monic ternary polynomials

$$
F(z)=z^7+z^6+1,\qquad G(z)=z^7+2z^4+2z^2
\tag{67.7}
$$

have this difference. They encode the length-seven words $1000001$ and $0020200$, respectively, and satisfy $F(A)e=G(A)e$. This is equality of the whole field, rather than just one selected scalar. With the same graph, map and late-receiver context, every permitted passive continuation from those equal states has identical whole replies. No passive receiver using any earned terminals, any number of Reads or any adaptive schedule can recover both words. Earlier encoding Read replies are outside this late receiver's input domain. These three collisions establish the required necessity; the actual attainment and continuation from the positive sample data are given next. $\square$

**Proposition 67.3 (the narrower seed schedule fails on $P_5$).** On the five-vertex graph, replacing the two samples in (67.5) by seed Reads at offsets one and two is not a ternary decoder, although the ternary whole-field map is injective.

**Proof.** The words $100$ and $002$ have polynomials $z^3+z^2$ and $z^3+2$. Their field difference is $A^2e-2e=-e+e_{\varepsilon}\ne0$. The seed's odd return moment is zero, while $r_1=1,r_2=2$, so both seed functionals $e^{\mathsf T}A$ and $e^{\mathsf T}A^2$ annihilate this difference. This proves failure of exactly that site/time pair. It is consistent with, and does not obstruct, the opposite-terminal acquisition of (67.3). $\square$

## 68. Two additional literal Reads and complete continued use

**Definition 68.1 (the ternary late assay).** On the positive domain of Theorem 67.2 compute $(f,K)$ and the weight rule from the earned graph by (67.2) or (67.3). At the actual encoding-image cut Hold. For $s=1,\ldots,K$ actually execute Tick; Add$(e,0)$; Hold, consuming every complete acknowledgement and return. Read at the earned raw label of $f$ exactly at $s=K-1$ and $s=K$, consuming both whole literal rational replies and their complete returns. There are no other Reads in this late assay. The two selected times are positive and distinct. No growth or field intervention other than the literal zero Adds occurs. Finish the last round and all pending returns, then perform the finite decoding of (67.5) while held. Reconstruct $x_w$ by exact Horner evaluation of (67.1), calculate $A^Kx_w$, and initialize the full current predictor before admitting another settled request. Export the decoded word, length, sample pair and requested current report through the already supplied backed output/acknowledgement/return connection. All inner replies are retained in their original roles or relayed in full; a Tick remains a fixed acknowledgement.

**Theorem 68.2 (one specimen, actual endpoint and service).** For every earned $u\in\mathcal D$ with $N\ge5$ and every finite promised ternary word, the assay terminates, recovers that exact word and length, and has simultaneously

$$
\begin{aligned}
(Y_{\rm odd},Y_{\rm even})
 &=\bigl(f^{\mathsf T}A^{K-1}x_w,\ f^{\mathsf T}A^Kx_w\bigr),\\
x_{\rm end}&=A^Kx_w=x_{w0^K}.
\end{aligned}
\tag{68.1}
$$

It uses exactly $K$ Tick, $K$ Add, $K+1$ Hold and two additional scalar Read calls. The full source graph and earned map are unchanged during the assay. From its completed handoff the existing complete six-operation controller predicts every whole reply and successor under arbitrary finite sufficiently backed common adaptive continuation, at this actual $x_{w0^K}$.

**Proof.** Holds, zero Adds and Reads preserve the field. Induction on $s$ therefore gives actual field $A^sx_w$ in round $s$, proving the two literal equations in (68.1). Each round's Tick and zero Add is also exactly the field recurrence for an appended zero digit, giving the last equality. The earlier assay round omits the Next composite's usual Read except when prescribed; this changes the returned observation contract, not that field recurrence. Theorem 67.2 supplies the finite exact inverse. Horner evaluation and $K$ further sparse steps produce the entire actual advanced vector, including internal cells. There is no inverse Tick, returning-scalar Tick, re-preparation, second specimen or assertion that the field remained $x_w$.

Retain the actual current code, full graph, exhaustive raw table and canonical inverse, reconstructed advanced vector, parser and pending-call controls, genuine connection and current/fresh grants. These establish exactly §64's one-step invariant at the new initialization $A^Kx_w$. Its complete successor correspondence applies to all six original operations: successful P/S retain old values and append the prescribed fresh zeros and bindings; guards give their distinct original refusals; Add uses the actual earned terminal; Tick updates the whole field by the current adjacency and returns only its acknowledgement; Read returns its entire current rational; Hold preserves the state. Range, malformed complete packets, the malformed former Reset tag, proper incomplete waits and disabled missing-rights cases retain §64's exact domains. Completing the actual return and the matching retained update before the next settled cut gives the same induction for every finite common adaptive continuation. The finite graph and rational backing remain charged. Later unrestricted operations can leave the ternary history image; the full-state controller remains applicable, whereas this restricted history inverse is not asserted on such states.

All graph calculations and loop bounds are finite and word independent until the two actual scalars arrive. The decoder then terminates on every promised length, including zero. Counting the actual primitive calls proves the stated assay vector. $\square$

**Corollary 68.3 (the selected late Read minimum).** On each fixed positive-domain graph, two successful additional scalar Reads are necessary in the worst case for this exact ternary history task, under the no-advice late-receiver and passive-access conditions. On each excluded graph no such decoder exists.

**Proof.** The ternary image task contains the binary image task. Theorem 56.3's one-Read indistinguishability argument already allows every earned terminal and even known nonzero rational Adds, a larger passive menu than Definition 68.1. Restricting its operands to zero and enlarging its input family to ternary cannot remove that binary obstruction. Theorem 68.2 attains two. On the excluded graphs use the whole-field collisions of Theorem 67.2. This is a scalar-call minimum for this task; the other resource coordinates are not minimized by that argument. $\square$

## 69. A paid prescribed-graph entrance and the ternary run's resource vector

**Definition 69.1 (one actual entrance to the prescribed $u$).** Start with AA §17's actually allocated known alpha seed, with its physically initialized zero cell, authentic original-root binding, its sole raw terminal and actual rights. This seed preparation, connection and zero initialization are provider resources, not a Reset call, a field measurement or an inferred property of an arbitrary attachment. For the chosen finite $u\in\mathcal D$, execute a fixed finite legal construction word supplied by AA Theorem 17.2, consuming all original Growth replies and completed returns and maintaining the exhaustive actual map by (NLBAII.4). Use no field calls during this construction. Then actually Add one at the first canonical terminal through that earned map and Hold. Receiver delivery contains the earned graph/context; its provider's later input word and past digit replies are not receiver advice. Any retained provider input, records or output copies are separately paid and are outside the late receiver's accessible state.

**Proposition 69.2 (one-run counts ending at the declared graph).** Let $L=a+c$ be the number of logical leaves of the prescribed $u$, with $c$ beta leaves. Definition 69.1 reaches exactly $u$, whole zero before the unit Add, using $c$ successful P and $L-1$ successful S calls and no refusals, Tick or Read. After that origin, one length-$m$ ternary encoding followed by one assay of Definition 68.1 has the following total primitive counts, all on that same specimen and including the origin:

$$
\begin{aligned}
P&=c,&S&=L-1,&\mathrm{Reset}&=0,\\
\mathrm{Tick}&=m+K,&\mathrm{Add}&=1+m+K,\\
\mathrm{Read}&=m+2,&\mathrm{Hold}&=m+K+2.
\end{aligned}
\tag{69.1}
$$

Its final field is $A^{m+K}e+\sum_{i<m}d_iA^{m+K-1-i}e$ on exactly that $u$, with a synchronized complete predictor. Only the last two of the $m+2$ Reads are late-acquisition samples.

**Proof.** AA Theorem 17.2 gives an enabled original construction ending at $u$. At every prefix, old zero values persist and every fresh cell is zero; no Tick or Add intervenes. Induction proves whole zero on the final prescribed graph. A P increases the number of beta logical leaves by one and leaves the logical leaf count unchanged. An S leaves the beta count unchanged and increases the logical leaf count by one. Starting at $(c,L)=(0,1)$ therefore gives exactly the stated growth counts, also $1+c+2(L-1)=N$ allocated material vertices. The authentic installed persistence rule supplies the map at every prefix and hence the actual first-terminal selector. The unit Add and Hold give precisely the origin of Definition 67.1.

Every encoded digit contributes one Tick, one Add, one Hold and one literal Read, including digits zero and two. The assay contributes the vector of Theorem 68.2, including its initial Hold and all zero Add frames. Adding the one origin Add/Hold gives (69.1). The final field follows by advancing (67.1) exactly $K$ times. No count is taken from a different preparation or endpoint. $\square$

**Proposition 69.3 (the separate arbitrary-attachment entrance).** If instead the actual starting source is Assumption 34.1's arbitrary-field attachment $t$, execute exactly §§34–36's no-Reset marking, full-window observation and zero-target control, then Add the unit at its first earned terminal and Hold. This yields the ternary origin on $u=\rho(t)$, rather than on the unchanged $t$. With entry leaf count $L_0$, beta count $c_0$, resulting $b=L_0+c_0$, $N=3L_0+2c_0-1$, $I=N-b$ and $R_{\rm mark}$ as in (63.1), one subsequent length-$m$ word and one ternary assay have

$$
\begin{aligned}
P&=2L_0-1,&S&=c_0,&\mathrm{Reset}&=0,\\
\mathrm{Read}&=L_0+R_{\rm mark}+b(I+1)+m+2,\\
\mathrm{Add}&=2L_0+c_0+b(I+1)+1+m+K,\\
\mathrm{Tick}&=2I+1+m+K,\\
\mathrm{Hold}&=L_0+2I+6+m+K.
\end{aligned}
\tag{69.2}
$$

**Proof.** Theorem 35.3 establishes whole zero on this actual $\rho(t)$ and Theorem 36.1 retains its complete map and service. Add their already supplied entrance counts, as in (63.2), to the unit Add/Hold, $m$ complete Next calls and the $K$-round assay. In particular the assay has $K+1$ Holds. These sums give (69.2). The entrance's successful marking growth has changed the graph; its counts and physical endpoint do not prepare an unchanged prescribed $t$. $\square$

**Proposition 69.4 (literal traffic, precision, work and simultaneous backing).** The runs (69.1) and (69.2) admit the following finite exact calculation and simultaneous resource account.

**Proof and accounting convention.** Apply exactly the codec and full traffic sum (65.1)–(65.2) to each actual run (69.1) or (69.2). Each of its Add operands, including every zero, has its literal signed reduced-rational payload and actual raw-label selector; each of the $m$ encoding Reads and two late Reads has its whole literal rational, reply prefix and complete frame. Every Tick/Add/Hold has its own acknowledgement and complete return. Every actual P/S pays its address request, whole Growth or original refusal and navigation/return. Add the actual caller/output report frames, acknowledgements, copies and any retained earlier digit replies. Neither the two late scalar calls nor the compact polynomial notation replaces this sum. The zero-seed allocation, physical initialization, authentic root connection and grants in Definition 69.1 are additional initial resources, not a hidden port or free preparation.

For an explicit finite calculation, generate the graph-only moment search and needed weight list by repeated sparse adjacency steps, use integer quotient/subtraction in the greedy decoder, and evaluate the decoded polynomial by sparse Horner steps followed by $K$ further steps. If $D$ is the highest coefficient parity index, $D\le\lfloor m/2\rfloor$ and (67.4) ensures that $a_{D+1}$ exceeds either genuine total. Thus $O(N(m+K+1))$ integer arithmetic operations suffice for moment generation, finite decoding and endpoint reconstruction, in addition to constructor/address processing, input/output and the actual source's work. For $N>5$ this includes searching through $r_{J+1}$; $K=2J$ already pays for its graph dependence. No uniform graph-independent bound on $K$ is asserted. A source Tick itself performs $N$ zero initializations and $2(N-1)$ directed neighbour additions using a separate result buffer; a retained predictor pays its own updates and scratch when present. Elapsed native updates are exactly the Tick counts in (69.1) and (69.2); local computation, communication and held intervals consume their own time, with no unrequested evolution.

In the ternary encoding, maximum field magnitude satisfies $M_0=1$ and $M_{j+1}\le3M_j+2$, because the material tree has maximum degree three. Hence $M_j\le2\cdot3^j-1$; after the zero-input assay every coordinate is less than $2\cdot3^{m+K}$. Source integers and sampled integers therefore have $O(m+K+1)$ bits. The moment powers and decoder intermediates also have finite growing widths, bounded by $O(m+K+1)$ for the stated sparse calculation. Exact arithmetic pays its actual width-dependent costs; it is not unit-cost bit arithmetic. The arbitrary-field entrance of (69.2), its controls and rational elimination scratch additionally retain §65's actual $W_{\rm run}$, with no $N$-only width bound. At fixed length $m$ the positive-domain image contains $3^m$ distinct fields and distinct acquired pairs, so the two literal samples cannot have uniformly bounded joint distinguishing capacity as $m$ increases.

An explicit sufficient simultaneous layout reserves separately $2N$ plant integer slots for current/update fields, $2N$ predictor slots for current/update fields after installation, and $2N$ reusable local vector slots for moment generation and endpoint evaluation. Keep the two acquired scalars, the finite weight list, two coefficient lists, decoded chronological word, length and selected-terminal/time counters while live. All lists have $O(m+1)$ entries for the decoding phase, with actual integer widths and distinct output copies charged; slot reuse requires completed last use and actual overwrite work. The graph-only search and the source assay coexist with the actual specimen. There is no accessible full-word producer archive used by the receiver. If a producer's original input or past full replies are retained elsewhere, their separate simultaneous storage remains in the run's bill. The arbitrary-attachment route additionally retains the forcing/control/window and entry/current material already specified in §65, with their actual liveness and separate reports.

The logical code, actual material graph, exhaustive raw/canonical tables, addresses, traversal and navigation records, finite instruction code, live source/predictor/output buffers, actual reference fields and root/dispatcher/input/output connections, parser and incomplete frames, pending requests/replies, End/acknowledgement/Return controls, current and fresh grants, allocation and clearing all require their actual backing. Two Reads do not establish constant precision, constant total memory, a minimal graph, minimal time or universal total-resource optimality. $\square$

## 70. Attribution and exact applicability of the ternary conclusion

**Correspondence 70.1 (suppliers and native increment).** AA §17 supplies the original reachable class, a finite enabled construction of the prescribed term and its causal account. Sections 55–56 supply the monic encoding, fixed-seed moment/log-convex bridge, passive one-Read obstruction and the binary predecessor. Sections 34–36 and 64–65 supply the separately paid arbitrary-field entrance, complete original-menu controller, literal framing and backing. Their physical restoration and arbitrary-current rank results in §§58–63 remain separate tasks. Ordinary finite spectral decomposition, path spectra, Perron strict comparison, Cayley–Hamilton and positional/superincreasing decoding are mature suppliers. Their uses are inside the proofs of the source-specific threshold, not additional generic theorem claims.

The native increment is the exact ternary criterion over this entire original class, its whole-field four-vertex collision, the opposite-earned-terminal remedy at the five-vertex boundary, and the graph-only delayed return-moment schedule for every larger branch, together with its actual advanced acquisition and service contract. It is repository-derived source-specific synthesis and application; no worldwide-priority or exhaustive literature-absence assertion is made. In particular [Akiyama, Thuswaldner and Zaïmi, *Comments on the height reducing property II*, arXiv:1403.7480v1](https://arxiv.org/html/1403.7480v1) concerns finite-digit expansions of $\mathbb Z[\alpha]$. That numeration setting does not by itself supply this prescribed native-vector family, its original earned terminal sites, actual late sampling times or source continuation. The scalar and certified contracting-vector suppliers identified in Correspondence 66.2 retain their stated rational-origin and denominator-prime hypotheses, which are not substituted for the zero-diagonal unit adjacency here.

**Boundary 70.2 (what the inverse asserts).** The history conclusion is for the complete monic ternary image on a fixed physically prepared native graph and the stipulated no-advice late receiver. It includes the empty word and all finite zero words. It does not identify an arbitrary old P/S serialization, an arbitrary Add journal or a hidden entry field. Restoring arbitrary entry values is the different §58 relation; acquiring a predictor of an arbitrary current field is the different §§60–62 rank relation. Off-image pairs are not certified by greedy subtraction alone. If desired, a total finite pair parser rejects negative/nonintegral totals, digits outside $\{0,1,2\}$, a nonzero final residual or a missing/nonunit leading coefficient, but its accepted coefficient list is only a candidate until the image promise or a full-vector equality supplies the required bridge.

The actual graph, terminal map, whole outputs, advanced state, current and fresh authority and paid resources all belong to the same specimen. Any later action outside the restricted image is handled by the initialized full-state controller, not by pretending that a ternary inverse still applies. No noisy/finite-precision theorem, hardware realization, arbitrary-attachment preparation of an unchanged graph or total-resource optimum follows.

## 追加锚（本行以下为增补区）

## 71. The original seven-vertex specimen and its quaternary image

**Definition 71.1 (native material and monic histories).** Retain the original AA §17 birth-typed source and Definition 55.1's six-operation installation. Fix

$$
u=\langle\beta,\langle\beta,\alpha\rangle\rangle.
$$

From a known zero alpha, the enabled addressed growth sequence is $P_\varepsilon,S_\varepsilon,P_R,S_R$. In the resulting materialization the logical beta vertices are $L,RL$, with their respective unary markers $LL,RLL$. In material-coordinate order

$$
(LL,L,\varepsilon,R,RL,RLL,RR),
$$

the complete undirected unit-edge set is

$$
\{LL\!\sim\!L,\ L\!\sim\!\varepsilon,\ \varepsilon\!\sim\!R,
\ R\!\sim\!RL,\ RL\!\sim\!RLL,\ R\!\sim\!RR\}.
$$

Thus the actual symmetric zero-diagonal adjacency and complete canonical terminal list are

$$
A=\begin{pmatrix}
0&1&0&0&0&0&0\\
1&0&1&0&0&0&0\\
0&1&0&1&0&0&0\\
0&0&1&0&1&0&1\\
0&0&0&1&0&1&0\\
0&0&0&0&1&0&0\\
0&0&0&1&0&0&0
\end{pmatrix},\qquad
(LL,RLL,RR),\qquad e=e_{LL}.
\tag{71.1}
$$

Assume this same specimen has physically established whole zero, its exhaustive earned raw/canonical material and terminal correspondence, genuine binding, current and fresh authority, exclusive completed-call serialization, no autonomous motion, finite exact framing and sufficient finite backing as in §§55 and 67. Original growth preserves whole zero; actually Add one at $e$ and Hold to establish $x_\emptyset=e$. For each digit of $w=d_0\cdots d_{m-1}\in\{0,1,2,3\}^*$ execute the complete original composite

$$
\operatorname{Next}(d_i)=
\operatorname{Tick};\ \operatorname{Add}(e,d_i);\
\operatorname{Hold};\ \operatorname{Read}(e).
\tag{71.2}
$$

Every composite includes its three original acknowledgements, its literal scalar Read and all completed framed returns. Tick applies $A$ and returns only its fixed acknowledgement. There is no growth, Reset, extra Tick or other Add in this encoding phase. Consequently

$$
x_w=F_w(A)e,\qquad
F_w(z)=z^m+\sum_{i=0}^{m-1}d_i z^{m-1-i}.
\tag{71.3}
$$

In particular $F_\emptyset=1$ and $F_{0^m}=z^m$; zero digits and empty histories are retained without an identification by leading zeros.

**Definition 71.2 (late passive observation).** The late receiver has the earned whole graph, exhaustive map, authentic callable context and promise (71.3), but no word, length, earlier encoding replies, input journal, field-dependent advice or dependent accessible producer state. A fixed finite passive schedule is a finite sequence chosen from that earned graph alone, independently of the word and its length. It may use Tick, Hold, identity Add$(e_\ell,0)$ and literal scalar Read$(e_\ell)$ at any earned terminal $\ell\in\{LL,RLL,RR\}$. Only Tick changes the field. All original acknowledgements, scalar frames and completed returns remain part of the transcript; there is no additional field-dependent timing, allocation or capacity channel. Framing and scalar width are fixed functions of the literal value. Every promised finite run has sufficient exact backing; this imposes no uniform bound on scalar width over all histories.

Let $K\ge0$ be the schedule's total Tick count, including Ticks after its last Read. A Read made after $t$ Ticks, $0\le t\le K$, returns $e_\ell^{\mathsf T}A^t x_w$, and the actual endpoint is $A^Kx_w$. Repeated terminal/time choices and schedules with zero or one Read are included. No earlier Next reply is among these late observations.

## 72. Injective quaternary storage in the entire native field

**Theorem 72.1 (all finite histories have distinct whole fields).** On (71.1)–(71.3), $w\mapsto x_w$ is injective on all finite quaternary histories, including the empty history and every all-zero history.

**Proof.** Put

$$
q(y)=y^3-6y^2+9y-3,\qquad
M(z)=zq(z^2)=z^7-6z^5+9z^3-3z.
\tag{72.1}
$$

Expansion of (71.1) gives $\det(zI-A)=M(z)$ and

$$
\det[e,Ae,\ldots,A^6e]=-1.
\tag{72.2}
$$

Cayley–Hamilton gives $M(A)=0$. For every $D\in\mathbb Q[z]$, division by the monic $M$ leaves a remainder of degree below seven. Equation (72.2) forces that remainder to vanish whenever $D(A)e=0$. Thus the standard cyclic linear-algebra argument, used for whole-law equality in Recovery Geometry II §44, specializes here to

$$
D(A)e=0\quad\Longleftrightarrow\quad M\mid D
\quad\text{in }\mathbb Q[z].
\tag{72.3}
$$

This is a condition on all seven actual coordinates, not on one spectral projection.

We next exclude every nonzero integer polynomial with coefficients in $[-3,3]$ from being divisible by this particular $q$, in every degree. Its three real roots lie respectively in

$$
(23/50,47/100),\qquad(33/20,83/50),\qquad(387/100,97/25).
\tag{72.4}
$$

Indeed the values of $q$ at the two endpoints of these three intervals are respectively

$$
\left(-\frac{4033}{125000},\frac{8423}{1000000}\right),\quad
\left(\frac{57}{8000},-\frac{2413}{125000}\right),\quad
\left(-\frac{70797}{1000000},\frac{73}{15625}\right).
$$

The disjoint sign changes account for all roots of the cubic. Write $s,r$ for the middle and largest roots. If $P(t)=0$ for $t>1$ and every coefficient of $P$ has magnitude at most three, each descending Horner prefix $H(t)$ satisfies

$$
|H(t)|\le\frac{3}{t-1}.
\tag{72.5}
$$

To see this, if $\ell$ digits remain, write $0=P(t)=t^\ell H(t)+\sum_{j<\ell}a_jt^j$ and divide by $t^\ell$; the finite geometric tail is bounded by $3/(t-1)$. This includes the final prefix, which is zero.

Suppose now $P\ne0$ and $q\mid P$. Both $P(r)$ and $P(s)$ vanish. At $r$, (72.5) gives a bound smaller than $300/287<2$. The leading nonzero integer coefficient must therefore be $1$ or $-1$; change the sign of $P$ so it is $1$. A constant polynomial cannot vanish. If another coefficient follows, it must be $-3$: every allowed $d\ge-2$ gives

$$
r+d>\frac{187}{100}>\frac{300}{287}.
$$

The prefix $r-3$ is positive, excluding degree one. If another coefficient follows, it too must be $-3$, since for every $d\ge-2$,

$$
r^2-3r+d>\frac{13669}{10000}>\frac{300}{287}.
$$

This forces the prefix $r^2-3r-3>3669/10000>0$. But at the other root the identical coefficient prefix obeys

$$
s^2-3s-3<-\frac{13061}{2500},\qquad
\frac{3}{s-1}<\frac{60}{13}<\frac{13061}{2500},
$$

contradicting (72.5). Every degree at least two is excluded, even when this prefix is the final one. Hence $q\mid P$ with these coefficient bounds forces $P=0$.

For two arbitrary finite histories set $D=F_w-F_v$. All its coefficients lie in $[-3,3]$, also when their lengths differ: at an unequal leading degree the coefficient is $1$ minus a digit or its negative. If $x_w=x_v$, (72.3) implies $q(z^2)\mid D(z)$. Split the polynomial and its rational quotient into even and odd powers. Writing

$$
D(z)=E(z^2)+zO(z^2)
$$

gives $q\mid E$ and $q\mid O$ in $\mathbb Q[y]$. Both $E,O$ have integer coefficients in $[-3,3]$, so the preceding argument makes both zero. Thus $F_w=F_v$. Monic degree recovers the same length and descending lower coefficients recover the same chronological word, including degree zero and all-zero cases. This proves injectivity.

The bounded-digit conjugate supplier is [Akiyama, Thuswaldner and Zaïmi, *Comments on the height reducing property II*, arXiv:1403.7480v1, Theorem 3 and its proof](https://arxiv.org/html/1403.7480v1). In their parameters take $H=3$ and their algebraic number $\alpha$ to be $r$, not the native constructor alpha. The monic cubic $q$ is irreducible over $\mathbb Q$ by the rational-root test: none of $\pm1,\pm3$ is a root. Consequently its three roots in (72.4) are precisely the conjugates, with none on the unit circle. Their theorem supplies finite recognition of bounded-digit zero representations, and its proof supplies the expanding-conjugate prefix bounds (72.5). Here the explicit forced-prefix contradiction replaces any need to construct that automaton. The cyclic whole-law and parity steps supply the additional native-vector correspondence; the literature's single algebraic evaluation alone is not whole-field equality. $\square$

## 73. Every fixed two-Read passive transcript loses a history distinction

**Theorem 73.1 (all-terminal, all-fixed-time obstruction).** For every fixed finite passive schedule of Definition 71.2 using at most two literal scalar Reads, two distinct histories have the same complete late transcript. In particular no decoder of such a transcript recovers every quaternary history. This holds for every choice of earned terminals and finite Tick offsets.

**Proof.** Use the positive vector and rational constant

$$
h=(27,52,75,96,66,34,49)^{\mathsf T},\qquad c=\frac{95}{48}<2.
$$

Direct multiplication in (71.1) gives

$$
Ah=(52,102,148,190,130,66,96)^{\mathsf T}
   =2h-2\mathbf1\le ch.
\tag{73.1}
$$

The inequality follows coordinatewise from $h_i\le96$. The standard weighted maximum norm $\|x\|_h=\max_i|x_i|/h_i$, positivity of $A$ and (73.1) give $\|Ax\|_h\le c\|x\|_h$ and $\|e\|_h=1/27$. The recurrence in (71.3) therefore gives, for every length-$m$ word,

$$
\|x_w\|_h\le\frac1{27}\left(c^m+3\sum_{j<m}c^j\right)
 <\frac{191}{1269}c^m.
\tag{73.2}
$$

Every coordinate remains a nonnegative integer. At any earned terminal after any $t\le K$ passive Ticks its literal Read $y$ consequently satisfies

$$
0\le y<96\frac{191}{1269}c^{m+K}
 =\frac{6112}{423}c^{m+K}<15c^{m+K}.
\tag{73.3}
$$

This single bound covers all terminals and all offsets, including repeated Reads and Ticks after the last Read.

Choose the common history length $m=100(K+4)$. Bernoulli's inequality gives

$$
\left(\frac{96}{95}\right)^{100}
 \ge1+\frac{100}{95}=\frac{39}{19}>2.
$$

Since $2/c=96/95$ and $c<2$, it follows that

$$
(2/c)^m>2^{K+4}\ge16c^K,\qquad
15c^{m+K}+1\le16c^{m+K}<2^m.
\tag{73.4}
$$

The number of nonnegative integer values allowed by (73.3) is less than $15c^{m+K}+1$, hence less than $2^m$. A transcript with at most two scalar replies therefore has fewer than $4^m$ possible scalar tuples; pad any absent Reads by fixed dummy values. There are exactly $4^m$ length-$m$ histories. The pigeonhole principle supplies two distinct histories with identical scalar tuples for this proposed schedule.

The graph, complete map and authentic context are common. Every other permitted reply consists of the fixed original Tick, zero-Add and Hold acknowledgements and their completed returns. A scalar's frame and literal width are determined by its already counted exact value. Thus equality of the scalar tuples gives equality of the entire permitted transcripts; no decoder of that transcript can choose the correct history on both inputs. This uses standard weighted-norm bounds, Bernoulli's inequality and integer pigeonhole counting inside the actual source observation contract.

On each input the actual endpoint is $A^KF_w(A)e$. Failure to recover the required word already rules out the joint task of history recovery and complete-service initialization. It does not assert equality of the two entire initial fields, which Theorem 72.1 excludes, or equality of their advanced fields. Nor does it establish impossibility of current-service acquisition alone: §64's controller applies when the entire actual current field and its other stated premises have separately been earned. The binary and ternary positive acquisitions of §§55–56 and 67–70 retain their own alphabets and hypotheses. $\square$

**Boundary 73.2 (stored information and acquired information).** Theorems 72.1 and 73.1 together give a separation on the single original specimen $u=\langle\beta,\langle\beta,\alpha\rangle\rangle$: the whole actual field distinguishes every monic quaternary history, while each fixed graph-dependent passive schedule with at most two scalar Reads fails to acquire all those distinctions. This source-specific combination is repository-derived synthesis of the attributed cyclic, conjugate-bound, norm and counting suppliers; no worldwide novelty claim is made. No positive quaternary acquisition, minimum Read count above two, current-service-only impossibility, unbounded adaptive-time conclusion, graph or alphabet family, physical realization, arbitrary-entry restoration, arbitrary-current acquisition, erased general journal recovery or global hierarchy/composition inverse is established here. Finite exact replies for each run do not imply a uniform precision or storage bound over all histories.

## 追加锚（本行以下为增补区）

## 74. Every fixed three-Read passive transcript loses a history distinction

**Theorem 74.1 (one parity family defeats three Reads).** Retain Definition 71.1 in full: the original AA §17 birth typing, the seven-vertex symmetric zero-diagonal unit adjacency (71.1), origin $e=e_{LL}$, exhaustive earned terminal map and actual quaternary encoding (71.2)–(71.3). Retain Definition 71.2's source-independent no-advice receiver, original operation semantics, fixed finite passive schedule, literal scalar framing and absence of extra field-dependent channels. Genuine binding, current and fresh authority, exclusive completed-call serialization, no autonomous motion and sufficient finite exact backing remain premises. For every such schedule $S$ with at most three Reads and total Tick count $K_S$, there exist distinct words

$$
w,v\in\{0,1,2,3\}^{100(K_S+4)}
\quad\text{such that}\quad
\operatorname{Transcript}_S(w)=\operatorname{Transcript}_S(v).
\tag{74.1}
$$

The transcript includes every permitted acknowledgement, literal scalar frame and completed return. Hence no such schedule recovers all finite quaternary histories, even with unrestricted exact local decoding. In particular it cannot meet the joint requirement of recovering the history and initializing complete original six-operation prediction at the actual advanced endpoint.

**Proof.** Write $K=K_S$. On the actual vertex set put

$$
\chi=0\ \text{on }\{LL,\varepsilon,RL,RR\},\qquad
\chi=1\ \text{on }\{L,R,RLL\}.
$$

Every edge of (71.1) crosses these two classes and $\chi(LL)=0$. A length-$j$ walk from $LL$ therefore ends in class $j\bmod2$, so

$$
(A^j)_{\ell,LL}=0\quad\text{unless}\quad j\equiv\chi(\ell)\pmod2.
$$

This is the bipartite support argument used in Theorem 56.3. If $F(z)=\sum_k f_kz^k$, a Read at terminal $\ell$ after $t$ actual Ticks has value

$$
e_\ell^{\mathsf T}A^tF(A)e
 =\sum_k f_k(A^{t+k})_{\ell,LL}.
\tag{74.2}
$$

It thus depends only on coefficient exponents of parity $\chi(\ell)-t\bmod2$. The terminal and Tick offset of each Read are fixed independently of the history. Among at most three Reads, some parity $p\in\{0,1\}$ occurs at most once; this also covers absent or repeated Reads.

Set $m=100(K+4)$ and $n=m/2$. For every $a=(a_0,\ldots,a_{n-1})\in\{0,1,2,3\}^n$, take

$$
F_a(z)=z^m+\sum_{i=0}^{n-1}a_i z^{2i+p}.
\tag{74.3}
$$

These are $4^n=2^m$ distinct legal monic length-$m$ histories: assign chronological digit $d_{m-1-(2i+p)}=a_i$ and every other digit zero. All displayed lower exponents lie between zero and $m-1$, so the leading monomial is fixed and untouched. Every Read associated with parity $1-p$ is constant on this family by (74.2). At most one scalar reply can vary.

Use the existing all-terminal, all-offset estimate (73.3), with $c=95/48$. For every word in (74.3), the one possibly varying scalar is a nonnegative integer $y$ satisfying

$$
0\le y<15c^{m+K},\qquad
15c^{m+K}+1<2^m.
\tag{74.4}
$$

The second inequality is exactly (73.4) at the chosen $m$: $(96/95)^{100}\ge39/19>2$ gives $(2/c)^m>2^{K+4}\ge16c^K$, while $c^{m+K}\ge1$. Thus fewer than $2^m$ integer values are available to distinguish the $2^m$ histories in (74.3). Pigeonhole counting gives two distinct members with equal possibly varying scalar. If no Read has parity $p$, every scalar is already constant on the whole family. In either case all scalar replies agree.

All remaining replies are the fixed original Tick, Hold and zero-Add acknowledgements and their completed returns. Equal literal scalar values have equal widths and frames under Definition 71.2. The same graph, map and callable context supply no further word-dependent information; no earlier encoding reply or dependent producer record is accessible. Consequently the entire late transcripts agree, proving (74.1). Arbitrary local calculation from that common transcript cannot return the correct word on both inputs. The common-length collision suffices to defeat the promise over all finite words; the promise continues to include the empty word and every all-zero word. $\square$

**Boundary 74.2 (storage, endpoints and service).** By Theorem 72.1 the two histories in (74.1) have distinct whole initial fields. Their actual advanced endpoints are respectively $A^{K_S}F_w(A)e$ and $A^{K_S}F_v(A)e$, with every scheduled Tick counted, including those after the last Read. No equality of these endpoints, inversion of Tick or restoration of the old fields is asserted or needed. The contradiction concerns the required history component of the joint task. It does not establish impossibility of current-service acquisition alone: Theorem 64.1 retains its complete actual-current-field, map, authority, framing and backing premises. Nor does it establish four-Read attainment, an exact minimum above three, an adaptive-schedule obstruction, arbitrary-entry restoration, arbitrary-current acquisition, recovery of an erased general journal, or physical realization. The binary and ternary acquisitions retain their own alphabets and hypotheses. Finite exact backing for each finite run gives no uniform history-independent bound on scalar precision, storage or time.

**Correspondence 74.3 (source-specific inference and suppliers).** The source-specific inference beyond §§56 and 73 is the family (74.3): it leaves $2^m$ distinct legal histories in one coefficient parity, on which a three-Read schedule has at most one varying scalar. Theorem 56.3 supplies the native bipartite support mechanism; (73.3)–(73.4) supply the integer capacity bound. Bipartite walk parity, positivity and the weighted maximum norm behind that bound, the finite geometric series, Bernoulli's inequality and pigeonhole counting are standard suppliers used within this proof, not additional generic theorem claims. Theorem 72.1 supplies only the separate injective-storage contrast, not a premise needed for the collision proof. This is a source-specific mathematical consequence, with no worldwide-priority assertion. The [Akiyama–Thuswaldner–Zaïmi numeration theorem cited in §72, Theorem 3](https://arxiv.org/html/1403.7480v1), concerns finite recognition of bounded-digit zero representations for an algebraic number without unit-circle conjugates; it is not needed for this obstruction and supplies neither an original native sampling schedule nor a six-operation service initialization.

## 追加锚（本行以下为增补区）

## 75. Four literal Reads acquire every quaternary history and the actual complete service

**Definition 75.1 (the original specimen, promise and passive assay).** Use the birth-typed local source of [AA Definitions 17.1 and 17.3 and Theorem 17.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#17-birth-typed-local-growth-and-its-causal-reconstruction), as in Definitions 55.1 and 71.1. Its finite ordered terms are generated by $\alpha,\beta,\langle s,t\rangle$. The actual seed is a known allocated alpha; a present logical address is born beta when it ends in L and born alpha at the root or when it ends in R. The legal changes are $P_p:\alpha\mapsto\beta$ and $S_p:\beta\mapsto\langle\beta,\alpha\rangle$ at the indicated current logical leaf. Thus the reachable class has no alpha leaf at an L-ending address. Logical descent is through branches only. Materialization keeps each logical vertex, represents beta by a vertex with a terminal left marker, and represents a branch by its two ordered child subtrees; a marker is not a logical growth target.

Fix the actual term and complete material-coordinate order

$$
u=\langle\beta,\langle\beta,\alpha\rangle\rangle,
\qquad V=(LL,L,\varepsilon,R,RL,RLL,RR).
$$

From the known whole-zero alpha, the legal word $P_\varepsilon;S_\varepsilon;P_R;S_R$ constructs exactly this term. Every old vertex and value persists and every fresh vertex is zero. The logical beta vertices are $L,RL$, with markers $LL,RLL$. The six undirected unit edges are

$$
LL\sim L,\quad L\sim\varepsilon,\quad\varepsilon\sim R,
\quad R\sim RL,\quad RL\sim RLL,\quad R\sim RR.
$$

Let $A$ be their symmetric zero-diagonal adjacency, exactly (71.1), and let $e=e_{LL}$. The complete canonical terminal list is $(LL,RLL,RR)$. Retain its exhaustive earned raw table and canonical inverse: a named terminal call below means the corresponding original raw call through this actual binding, not an additional address port.

Assume the same specimen has physically established whole zero and then actually Add$(e,1)$ and Hold, giving $x_\emptyset=e$. For every finite word $w=d_0\cdots d_{m-1}\in\{0,1,2,3\}^*$, execute the original complete composite

$$
\operatorname{Next}(d_i)=\operatorname{Tick};\operatorname{Add}(e,d_i);
\operatorname{Hold};\operatorname{Read}(e).
$$

Each composite includes the three original acknowledgements, the entire literal scalar and every framed completed return. There is no growth, Reset, other Add or extra Tick in this encoding. Its actual field is

$$
x_w=F_w(A)e,\qquad
F_w(z)=z^m+\sum_{i=0}^{m-1}d_i z^{m-1-i},\qquad
F_\emptyset=1,\quad F_{0^m}=z^m.
\tag{75.1}
$$

Retain all of Definitions 71.1–71.2's service and receiver premises. The installation is precisely the original $P,S,\mathrm{Add},\mathrm{Tick},\mathrm{Read},\mathrm{Hold}$ menu of Assumption 34.1. Tick applies the current adjacency and returns only its fixed acknowledgement; Read is a separate nondestructive entire rational reply. Genuine original-root reference and binding, orientation, current and fresh grants, exclusive completed-call serialization, no autonomous motion, complete finite exact framing and sufficient finite backing are assumed. The late receiver has the earned graph, exhaustive map, callable context and promise (75.1), but no word, length, earlier encoding replies, journal, field-dependent advice or dependent accessible producer state. No extra field-dependent timing, allocation or capacity channel is supplied; scalar framing and width are fixed functions of its literal value.

On that same specimen execute the fixed graph-dependent passive schedule

$$
\underbrace{\operatorname{Tick};\operatorname{Tick};
\operatorname{Tick};\operatorname{Tick}}_{4\ \mathrm{Ticks}};
\operatorname{Hold};\operatorname{Read}(LL);\operatorname{Read}(RR);
\operatorname{Tick};\operatorname{Hold};
\operatorname{Read}(LL);\operatorname{Read}(RR);\operatorname{Hold}.
\tag{75.2}
$$

All calls consume their original full replies and completed returns. This schedule has five Tick, three Hold and four additional literal scalar Read calls, and no Add, growth, Reset or other intervention. It is independent of $w$ and $m$. Write its four scalars, in order, as

$$
Y(w)=\bigl(e_{LL}^{\mathsf T}A^4F_w(A)e,
 e_{RR}^{\mathsf T}A^4F_w(A)e,
 e_{LL}^{\mathsf T}A^5F_w(A)e,
 e_{RR}^{\mathsf T}A^5F_w(A)e\bigr).
\tag{75.3}
$$

The source remains held without autonomous motion or revocation during the receiver's finite local calculation.

**Theorem 75.2 (four-Read acquisition and complete true-endpoint continuation).** Under Definition 75.1's entire original-source, receiver, framing, authority, serialization and backing hypotheses, $Y$ is injective on all finite quaternary words, including empty words, all-zero words and pairs of different lengths. There is one exact decoder using only the stated context and four literal scalars that terminates on every promised image input and recovers the exact word and length. With sufficient finite backing for that decoding, full-state calculation and subsequent calls, it initializes complete original six-operation prediction at the actual advanced endpoint

$$
x_{\rm end}=A^5F_w(A)e.
\tag{75.4}
$$

From this completed handoff it predicts and maintains every entire reply and actual successor for every finite sufficiently backed common adaptive continuation of the original six-operation service, including subsequent growth. Termination is asserted only on the promised image; no uniform history-independent time, precision, storage or physical-realization bound is assumed or concluded.

**Proof.** First relate the literal samples to integer polynomial remainders. Put

$$
B=A^2,\qquad q(y)=y^3-6y^2+9y-3.
$$

The identity $Aq(A^2)=0$ is supplied by §72, (72.1)–(72.2) and Cayley–Hamilton. Therefore $Bq(B)=0$, although

$$
q(B)e=(-1,0,1,0,0,0,-1)^{\mathsf T}\ne0
\tag{75.5}
$$

in the displayed material order. In particular no reduction using $q(B)=0$ is made. For any $P\in\mathbb Z[y]$, division by the monic $q$ gives

$$
P=qQ+(a+by+cy^2),\qquad Q\in\mathbb Z[y],\quad a,b,c\in\mathbb Z.
$$

For every $h\ge1$, the factor $Bq(B)=0$ legitimately gives

$$
B^hP(B)e=B^h(aI+bB+cB^2)e.
\tag{75.6}
$$

Define $L_h(P)=((B^hP(B)e)_{LL},(B^hP(B)e)_{RR})^{\mathsf T}$. Multiplication in the particular adjacency (71.1) gives

$$
L_2(P)=
\begin{pmatrix}2&5&15\\1&5&21\end{pmatrix}
\begin{pmatrix}a\\b\\c\end{pmatrix},\qquad
L_3(P)=
\begin{pmatrix}5&15&51\\5&21&84\end{pmatrix}
\begin{pmatrix}a\\b\\c\end{pmatrix}.
\tag{75.7}
$$

Their entire integer kernels, not just rational kernel directions, are respectively

$$
\mathbb Z(30,-27,5),\qquad \mathbb Z(63,-55,10).
\tag{75.8}
$$

Indeed the first pair of zero equations gives $a=6c$ and $5b=-27c$, hence $c=5n$, $b=-27n$, $a=30n$. The second pair gives $2b+11c=0$, so $c=2t$, $b=-11t$, and then $5a=63t$; hence $t=5n$ and $(a,b,c)=n(63,-55,10)$. Conversely these vectors annihilate the two displayed matrices, so no integer solutions have been lost.

Let $\eta$ be the small root of $q$ in $(23/50,47/100)$ from (72.4). For any finite integer polynomial $P$ whose coefficients have magnitude at most three,

$$
|P(\eta)|\le 3\sum_{j=0}^{\deg P}\eta^j
\le\frac3{1-\eta}<\frac{300}{53}<6;
\tag{75.9}
$$

the zero polynomial satisfies the same bound directly. If $L_2(P)=0$, (75.8) and $q(\eta)=0$ imply

$$
P(\eta)=n(30-27\eta+5\eta^2),\qquad
30-27\eta+5\eta^2>30-27\frac{47}{100}
=\frac{1731}{100}>6.
$$

Thus the integer $n$ is zero by (75.9), and the entire remainder is zero. If $L_3(P)=0$, the corresponding calculation is

$$
P(\eta)=n(63-55\eta+10\eta^2),\qquad
63-55\eta+10\eta^2>63-55\frac{47}{100}
=\frac{743}{20}>6,
$$

again forcing $n=0$. Either zero sample pair therefore implies $q\mid P$ in $\mathbb Z[y]$. Now apply the already established all-degree bounded-coefficient lemma inside the proof of Theorem 72.1: no nonzero integer polynomial with every coefficient in $[-3,3]$ is divisible by $q$. Its proof uses the middle and largest roots in (72.4) and the Horner-prefix bound (72.5); it is reused here, not a new lemma. Consequently

$$
\bigl(L_2(P)=0\ \text{or}\ L_3(P)=0\bigr)
\quad\Longrightarrow\quad P=0
\quad\text{whenever all coefficients of }P\text{ lie in }[-3,3].
\tag{75.10}
$$

For arbitrary finite $w,v$ with $Y(w)=Y(v)$, set

$$
D(z)=F_w(z)-F_v(z)=E(z^2)+zO(z^2).
$$

Every coefficient of $D$, and therefore of $E,O\in\mathbb Z[y]$, lies in $[-3,3]$. For equal lengths the monic terms cancel. For unequal lengths the higher leading coefficient is $1$ or $-1$; at the smaller leading degree it is a digit minus $1$, or its negative; all other differences are differences of digits or a digit and zero. This proves the same bound without assuming equal lengths or dropping zero digits.

The actual bipartition, as used in Theorem 56.3 and §74, is

$$
\{LL,\varepsilon,RL,RR\}\ \sqcup\ \{L,R,RLL\}.
$$

Since $e,LL,RR$ lie in the first class, their odd-walk entries vanish. The two sample differences at time four are exactly $L_2(E)$. At time five the even component vanishes at these two terminals and the odd component is

$$
A^5 A O(B)e=A^6O(B)e=B^3O(B)e,
$$

so the two remaining differences are exactly $L_3(O)$. Equal samples and (75.10) give $E=O=0$, hence $F_w=F_v$. Monic degree gives the true length, and descending lower coefficients give the true chronological word. This includes $F_\emptyset=1$ and every $F_{0^m}=z^m$, without taking a quotient by leading zeros. The argument proves injectivity in every finite degree, rather than up to a length cutoff.

For decoding enumerate lengths $m=0,1,2,\ldots$ and, within each length, all quaternary words in fixed lexicographic order. Compute (75.3) by exact integer arithmetic on the known finite graph and compare with the four received scalars. Each level is finite and each candidate calculation terminates. Every promised finite input word therefore appears after finitely many candidates; injectivity makes its match unique. This is one terminating decoder on the promised image, requiring no supplied word length, previous encoding replies, journal, field-dependent advice or accessible producer state. Outside that image the enumeration may not terminate. Finite enumeration and arithmetic for each image input do not give a uniform time or bit-width bound.

Only the five actual Ticks in (75.2) change the source field, so its true endpoint is (75.4). While that source remains held, exact Horner evaluation of (75.1), followed by five applications of the known $A$, computes all seven coordinates of $x_{\rm end}$, including internal coordinates. Retain this vector together with the actual logical term, whole graph, exhaustive raw table and canonical inverse, authentic original-root reference/binding, installed parser/control and actual current/fresh grants. At this completed held cut, these data establish equality of the complete retained and actual current states. This supplies the new initialization for the proof invariant of Theorem 64.1, just as §68.2 initializes that same invariant at its own advanced endpoint; the earlier initializations listed in §64.1 are not substituted for (75.4).

For completeness the one-step correspondence preserves the entire original service. An enabled $P_p$ at alpha retains every old vertex, edge and value, attaches zero $pL$, and moves the acted raw label to that new terminal. An enabled $S_p$ at beta retains old $p,pL$ and every old value and edge, adds zero $pLL,pR$, moves the acted label to $pLL$ and appends the next raw integer at $pR$. These successes return the original complete Growth$(P,p)$ and Growth$(S,p)$ packets, respectively. Record the genuine fresh bindings and grants and update the term, graph, both map directions and whole field. An absent address, a branch target and a wrong leaf type produce their distinct original identity-successor refusals; a material marker is never a logical target. An in-range Add adds its entire rational, with its full sign and denominator, at the actually bound terminal and returns the fixed Add acknowledgement. Tick replaces every coordinate by its current-neighbour sum and returns only its fixed acknowledgement. An in-range Read preserves the state and returns the entire current rational; Hold preserves it through its held interval and returns its fixed acknowledgement. Integer Add/Read labels outside the current roster return RangeRefusal with identity successor. A complete malformed packet, including the former Reset tag, returns BadFrame with identity successor. Missing rights disable a call and are not represented as a refusal.

A proper incomplete frame retains the actual parser, received bytes and pending state, has no completed edit and produces no completed reply. Acquire every finite input into real backing before releasing its input latch. For each enabled complete call, forward through the authentic binding, consume the full output, End, local acknowledgement and completed return, restore navigation/dispatch position, and complete the matching retained update before admitting the next settled request. The actual parser/control, reference and current/fresh-grant lifecycle are maintained along with the mathematical state. Whole rational operands and outputs, pending requests and replies, target addresses, graph/field copies and work buffers all have their actual simultaneous finite backing. Any decoded-word or current-state export also uses its complete backed output frame, acknowledgement and return; an inner reply is not an extra uncharged communication port. Held serialization supplies time for finite local work without unrequested motion.

Thus equality of entire actual and retained states is preserved at every completed cut, with the same whole reply. Induction proves the claimed full service for every finite common adaptive continuation; a next request chosen from common replies is common, and a fixed common random tape gives the same induction. Successful later growth may leave the seven-vertex history image, and arbitrary later rational Adds may leave (75.1). Prediction then relies on the maintained complete state and current adjacency, not on applying the history inverse to an out-of-image field. No inverse Tick, Reset, restoration of the old field, second specimen or hidden field channel is used. Rights, framing, sufficient finite backing and absence of other writers, revocation and crashes are service premises, not products of digit decoding; no inverse at a busy cut or backing-exhaustion behavior is included.

The source-specific correspondence is (75.7)–(75.10): the two actual terminal sampling kernels at $h=2,3$ are excluded by evaluation at the contracting root, and parity then connects these literal samples to the complete history and true current service. Definitions 71.1–71.2 supply the native graph, seed, encoding and observation contract; §72 supplies the annihilator, root intervals and all-degree lemma; §§64.1 and 68.2 supply the full-state continuation invariant and its advanced-endpoint initialization method. The attributed literature supplier remains [Akiyama–Thuswaldner–Zaïmi, *Comments on the height reducing property II*, arXiv:1403.7480v1, Theorem 3 and its proof](https://arxiv.org/html/1403.7480v1): with digit bound $H=3$ and algebraic number the largest root of $q$, its bounded-digit zero-recognition and expanding-conjugate prefix bounds underlie §72. No automaton construction is needed here. That literature result supplies neither this native sampling schedule nor its service bridge; the kernel/contraction correspondence above is the source-specific synthesis. The theorem is confined to this original unit graph, specified seed, full monic quaternary image and stated service premises, rather than arbitrary fields, arbitrary graphs or recovery of an erased general journal. $\square$

**Corollary 75.3 (the same-class minimum is four Reads).** Under exactly Definitions 71.1–71.2 and 75.1's fixed graph-dependent passive, no-advice and full quaternary joint history/true-endpoint service task, the minimum number of additional literal scalar Reads is four. The attained schedule has total Tick count five; no minimum Tick count is asserted.

**Proof.** Theorem 74.1 rules out every such fixed finite passive schedule with at most three Reads, allowing all earned terminals and every finite Tick offset, including Ticks after the last Read. Theorem 75.2 attains four under the same original-source and resource hypotheses. These bounds compare the same joint task and do not assert a lower bound for current-service acquisition alone. $\square$

## 追加锚（本行以下为增补区）

## 76. 同一原生历史任务的四 Tick 获取

**定义 76.1（原有编码之后的固定被动获取）。** 完整沿用定义 71.1–71.2、75.1 的全部假设及 [AA 定义 17.1、17.3 和定理 17.2](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md#17-birth-typed-local-growth-and-its-causal-reconstruction) 的原 birth-typed 局部源。固定同一个实际项 $u=\langle\beta,\langle\beta,\alpha\rangle\rangle$、(71.1) 的对称零对角单位邻接矩阵 $A$、坐标序 $(LL,L,\varepsilon,R,RL,RLL,RR)$ 及首个 canonical terminal 种子 $e=e_{LL}$。完整 earned terminal 表为 $(LL,RLL,RR)$，保留其穷尽 raw 对应及 canonical 逆表；下述命名终端调用均经真实绑定转成原 raw 调用，不增加地址端口。原出生类型、合法 $P/S$ 守卫和 material marker 非逻辑生长目标的约束均保留。

在同一源上实际建立 whole zero，再实际执行 Add$(e,1)$ 和 Hold。对每个有限字 $w=d_0\cdots d_{m-1}\in\{0,1,2,3\}^*$，执行 (71.2) 的每个完整原 Next，即 Tick、Add$(e,d_i)$、Hold、Read$(e)$，包括三个原确认、整个 literal scalar、全部 framing 和完成返回。于是获取开始时

$$
x_w=F_w(A)e,\qquad
F_w(z)=z^m+\sum_{i=0}^{m-1}d_i z^{m-1-i},
\qquad F_\emptyset=1,\quad F_{0^m}=z^m.
$$

接收者只有 earned 图、完整映射、真实可调用上下文及此历史像承诺，没有字、长度、旧编码回复、journal、依赖于场的 advice 或可访问的相关 producer 状态。保留 genuine original-root reference/binding、方向、current/fresh authority、排他的完成调用串行化、无自主运动、按 literal 值决定宽度的完整精确 framing 及每个有限承诺运行所需的充足有限精确 backing；没有额外依赖于场的 timing、allocation 或 capacity 通道。解码期间源保持 held，且无其他写入者、撤权或崩溃；这些权利与资源是前提，不由解码产生。

在完整编码结束之后，选取如下一个固定获取 schedule；它只依赖已知图，不依赖 $w$ 或 $m$：

$$
\operatorname{Tick};\operatorname{Tick};\operatorname{Tick};
\operatorname{Hold};\operatorname{Read}(LL);\operatorname{Read}(RR);
\operatorname{Tick};\operatorname{Hold};
\operatorname{Read}(LL);\operatorname{Read}(RR);\operatorname{Hold}.
\tag{76.1}
$$

每次调用先消费原有完整回复及完成返回，才进行下一次。此 schedule 属于定义 71.2 原有的 Tick、Hold、identity Add$(0)$、earned-terminal literal Read 被动菜单，实际用了四 Tick、三 Hold、四个额外 scalar Read，零 Add、零 growth、零 Reset，亦无其他干预。按定义 71.2，$K$ 计入获取 schedule 中所有实际 Tick，包括最后一次 Read 之后的 Tick；(76.1) 的 $K=4$，最后一次 Read 之后有零 Tick。原长度 $m$ 编码的 $m$ 个 Tick 及全部 Next 调用仍须实际执行并支付：从已建立的单位种子到此端点共有 $m+4$ 个 Tick，$K=4$ 不是整段编码与获取的总成本。

按返回顺序记四个 literal scalars 为

$$
Y_4(w)=\bigl(
e_{LL}^{\mathsf T}A^3F_w(A)e,\,
e_{RR}^{\mathsf T}A^3F_w(A)e,\,
e_{LL}^{\mathsf T}A^4F_w(A)e,\,
e_{RR}^{\mathsf T}A^4F_w(A)e
\bigr).
\tag{76.2}
$$

**推论 76.2（四 Read、四获取 Tick 的完整同任务入口）。** 在定义 76.1 的全部原有假设下，一个固定 schedule (76.1) 和一个精确 decoder 适用于所有有限 quaternary words，包括空字、所有全零字及任意不等长比较。decoder 仅用既定上下文及四个 literal scalars，在整个承诺像上终止，恢复确切字与长度，并在同一源的真实 advanced endpoint

$$
x_{\mathrm{end}}=A^4F_w(A)e
\tag{76.3}
$$

初始化完整原六操作预测。从该完成且 held 的交接 cut 起，对每个充足有限 backing 的有限共同 adaptive continuation，预测和维护每个完整回复及实际 successor，包括之后的合法生长与任意 rational Add。

**证明。** 对任意有限 $w,v$，置

$$
D(z)=F_w(z)-F_v(z)=E(z^2)+zO(z^2),
\qquad E,O\in\mathbb Z[y],\qquad B=A^2.
$$

$D,E,O$ 的系数都在 $[-3,3]$。等长时 monic 最高项抵消；不等长时较高最高项为 $\pm1$，在较低 monic 次数处为 digit 减一或其负数，其余处为两 digit 之差或 digit 与零之差。因此该界不限制长度，也不舍去零 digit。

直接使用 (75.7)–(75.10) 的同一个全次数结果：对这个 $A,e,B$，令

$$
L_2(P)=
\begin{pmatrix}
(B^2P(B)e)_{LL}\\
(B^2P(B)e)_{RR}
\end{pmatrix}.
$$

则每个有限整数系数多项式 $P$ 只要全部系数在 $[-3,3]$，便有 $L_2(P)=0\Longrightarrow P=0$。这里参数正是 §75 的 $h=2$、$q(y)=y^3-6y^2+9y-3$，其全次数排除来自定理 72.1 证明中的 bounded-coefficient 结论；不另作代数证明，也不使用 $q(B)=0$ 或 $h=1$ 的结论。

由 §§74–75 的实际二分
$\{LL,\varepsilon,RL,RR\}\sqcup\{L,R,RLL\}$，$e,LL,RR$ 同在第一类，故对应的奇数 walk entries 为零。因此 (76.2) 的时间三差读数及时间四差读数分别为

$$
\begin{aligned}
\begin{pmatrix}
(A^3D(A)e)_{LL}\\
(A^3D(A)e)_{RR}
\end{pmatrix}
&=
\begin{pmatrix}
(A^4O(B)e)_{LL}\\
(A^4O(B)e)_{RR}
\end{pmatrix}
=L_2(O),\\
\begin{pmatrix}
(A^4D(A)e)_{LL}\\
(A^4D(A)e)_{RR}
\end{pmatrix}
&=
\begin{pmatrix}
(B^2E(B)e)_{LL}\\
(B^2E(B)e)_{RR}
\end{pmatrix}
=L_2(E).
\end{aligned}
\tag{76.4}
$$

这两次均是既有 $L_2$ 的应用。若 $Y_4(w)=Y_4(v)$，则 $O=E=0$，从而 $F_w=F_v$；monic degree 恢复确切长度，按降幂读取较低系数恢复 chronological word。这包括 $F_\emptyset=1$ 与每个 $F_{0^m}=z^m$，不对 leading zeros 作商。

取 §75 的精确枚举 decoder，将其候选样本公式 (75.3) 换为 (76.2)：依次枚举 $m=0,1,2,\ldots$，每个长度内按固定字典序枚举全部 quaternary words，在已知有限图上精确计算候选的 $Y_4$ 并比较四个完整标量。每层和每个候选计算均有限，每个承诺输入的字都在有限步骤后出现，单射性保证唯一匹配。因此一个 decoder 在整个承诺像上终止，无需长度、旧回复或额外 advice；不推断 off-image 终止。

(76.1) 中只有四个实际 Tick 改变场，故完整返回后的实际场是 (76.3)。源保持 held 时，用恢复的字在本地作 Horner 计算得到 $F_w(A)e$，再作四次本地矩阵应用，得到 (76.3) 的全部七个坐标，包括 internal cells。这些本地计算不给实际源增加 Tick，也不逆转 Tick、恢复旧场或执行 Reset。

现在直接初始化定理 64.1 证明中的完整实际态等于保留态的不变量。其本端点参数对应为：逻辑项取上述实际 $u$，全图取 $C(u)$，当前邻接取 (71.1) 的 $A$，全向量取 (76.3)，raw 表及 canonical 逆表取原来完整 earned 表，parser/control、original-root reference/binding 及 current/fresh grants 均取实际当前数据。该对应逐项给出完成且 held 的 cut 上全状态相等；§64.1 原列举的其他入口向量不代替这里的 $A^4F_w(A)e$。

从此 cut 起，复用定理 64.1 的完整逐调用对应及归纳，连同 §75 的真实 advanced-endpoint 入口用法：$P/S$ 的旧值保留、fresh 零值及 raw-label/grant 更新，absent、branch、wrong-type 三种不同守卫拒绝，完整 rational Add、全场 Tick、整个 rational Read 和 Hold，RangeRefusal、BadFrame、incomplete-frame pending state 及 missing-right disabled calls，全部保留原有语义。每个有限输入先取得真实 backing；完整输出、End、local acknowledgement、完成返回和匹配的保留态更新全部先于下一个 settled call。完整 decoded-word 或当前态导出同样使用其实际 backed 输出帧与完整确认/返回，不增加隐含通信端口；pending 请求、回复、地址、图场副本及工作缓冲按需同时有有限 backing。故所述有限共同 adaptive continuation 上，整个回复和实际 successor 逐步相同；以固定共同 random tape 选择后继请求亦然。后续生长和任意 rational Add 可以离开七顶点历史像，此后依靠维护中的完整当前态与当前图，不在 off-image 场上重用历史 inverse。

所得结论是定理 75.2 的同一原生 joint history/真实端点服务任务，将获取 Tick 从五减至四；额外 scalar Read 仍为四，其最小性已由定理 74.1 及推论 75.3 给出，不新增 Read 下界，也不主张 Tick 最小性。此应用直接复用 (75.10) 的全次数 $L_2$ 结果及定理 64.1 的完整服务不变量，不建立新的通用代数定理，也不主张文献优先权。§72 中 Akiyama–Thuswaldner–Zaïmi 的数学归属仍按该节引用；此处所需的有界系数排除已由该节的完整初等论证给出，不另依赖外部定理。

每个有限承诺运行的充足精确 backing 不给出统一时间、存储、precision 或整段总成本界。结论限于上述固定源、指定种子、完整 monic quaternary 历史像及原权利、framing、串行化和 held 前提，不推出任意场或任意图恢复、adaptive 获取 schedule 定理、已擦除一般 journal 的恢复、busy cut 的 inverse、backing 耗尽或崩溃恢复行为，亦不提供物理实现。$\square$

## 追加锚（本行以下为增补区）

## 77. WLAB-ord: acquiring an unknown law on one ordered native source

**Definition 77.1 (the WLAB-ord installation).** Fix one reachable original term
$u\in\mathcal D$ with $b\ge3$ logical leaves, its complete ordered terminal roster
$\ell_1<\cdots<\ell_b$, and its $N=2b+c-1$ material vertices, where $c$ is the
number of beta leaves.  The ordering is an authentic source binding and is not a
coordinate oracle supplied to a decoder.  Let $J:\mathbb Q^b\to\mathbb Q^N$ be the
terminal inclusion in this earned order and $C=J^{\mathsf T}$.

The source law is an unknown matrix

$$
T=T^{\mathsf T}\in\mathbb Q^{N\times N},
\qquad
T_{vw}>0\ \Longleftrightarrow\ v\sim w\quad(v\ne w),
\qquad
T_{vw}=0\ \text{for distinct non-neighbours},
\tag{77.1}
$$

with arbitrary rational diagonal.  Here $v\sim w$ is the actual material-tree
incidence of $u$.  The initial field $x_0\in\mathbb Q^N$ is arbitrary, including
zero and fields invisible to a chosen terminal at a short time.  The installed
commands on this same source are

$$
\operatorname{Tick}(x)=Tx,\qquad
\operatorname{Add}(j,q)(x)=x+q e_{\ell_j},\qquad
\operatorname{Read}(j)(x)=x_{\ell_j},
\tag{77.2}
$$

and Hold.  Tick, Add and Hold return their fixed acknowledgements; Read returns
the complete literal rational.  There is no Reset, clone, coefficient port,
interior Read, free response table, or field-dependent timing or capacity channel.
The provider has actually commissioned the old coefficients and retained the
ordered roster.  This is a premise of this named installation.  Future successful
$P/S$ calls preserve old coefficients and old fields, add zero cells, and use unit
weights on new edges with zero new diagonal; this future rule does not claim that
the old commissioned coefficients were generated by those later unit edges.

All framing, source and observer backing, current and fresh rights, endpoint
binding, serial completion, and Hold control are the literal resources of the
same source.  A complete input is acquired before its input latch is released,
and the complete output, acknowledgement, End and Return are consumed before the
next settled call.  Physical conformance to these premises is not inferred from
the numerical construction.

Put

$$
R=3b-1,
\qquad H=2R-1,
\qquad \tau_j=jH\ (1\le j\le b),
\qquad L=(b+1)H.
\tag{77.3}
$$

The inequality $N=2b+c-1\le3b-1=R$ uses $c\le b$.  First scan all terminals at
epochs $0,1,\ldots,H$ from the unmodified source.  At epoch $\tau_j$ perform the
literal $\operatorname{Add}(j,1)$, then scan all terminals at relative epochs
$0,1,\ldots,H$, retaining every earlier pulse in the same field.  A Hold is
performed at each sampled epoch, including the initial and final held cuts.

**Lemma 77.2 (a rational recurrence earned from $2R$ vector returns).** For any
$v\in\mathbb Q^N$, the vector sequence

$$
s_k(v)=CT^kv\in\mathbb Q^b
\tag{77.4}
$$

is determined by its first $2R$ values and can be continued by one monic rational
recurrence of order $R$.  The assertion includes singular $T$, zero $v$, repeated
eigenvalues and signed transients.

**Proof.** Cayley--Hamilton gives a monic annihilator of degree $N$. Multiplying it
by $z^{R-N}$ gives a monic $q(z)$ of degree $R$ annihilating every sequence
$s_k(v)$.  Solve over $\mathbb Q$ for coefficients $\gamma_0,\ldots,\gamma_{R-1}$
in the $bR$ equations

$$
s_{k+R}(v)+\sum_{i=0}^{R-1}\gamma_i s_{k+i}(v)=0,
\qquad 0\le k<R.
\tag{77.5}
$$

The system has a solution because the coefficients of $q$ are one.  Let $p$ be
the resulting monic polynomial and let $\widetilde s$ be the sequence generated
by $p$ from the first $R$ values of $s$.  The first $R$ values of
$d=s-\widetilde s$ vanish, and (77.5) gives the next $R$ values as zero.  The
operator product $pq$ annihilates both $s$ and $\widetilde s$, hence annihilates
$d$.  A monic recurrence of order $2R$ with $2R$ initial zero vectors has every
later vector zero by forward induction.  Thus $s=\widetilde s$.  This proves both
finite determination and exact rational continuation. $\square$

The recurrence is a local calculation on the returned scalars.  It is not a
preinstalled response oracle and it does not identify the order $N$ with the
visible rank of the initial field.

**Lemma 77.3 (sequential pulses expose the complete terminal law).** Let

$$
f_k=CT^kx_0,
\qquad h_j(k)=CT^ke_{\ell_j}.
\tag{77.6}
$$

The actual free scan and the $j$th pulse scan determine $f_k$ and the complete
vector sequence $h_j(k)$ for every $j$, first for $0\le k\le H$ and then for all
$k$ by Lemma 77.2.  In particular they determine every terminal moment matrix

$$
M_k=C T^kJ=[h_1(k)\ \cdots\ h_b(k)]\in\mathbb Q^{b\times b}.
\tag{77.7}
$$

**Proof.** The first scan literally returns $f_0,\ldots,f_H$.  The $j$th pulse
block returns, for $0\le k\le H$,

$$
y_{j,k}=f_{\tau_j+k}
 +\sum_{i<j}h_i\bigl((j-i)H+k\bigr)+h_j(k).
\tag{77.8}
$$

The free recurrence from the first scan gives every required $f$ value.  By
induction on $j$, all earlier $h_i$ values in the sum are already known and can
be evaluated by their earned recurrences.  Subtracting those actual, already
paid responses from the literal $y_{j,k}$ leaves $h_j(k)$ for $0\le k\le H$.
Lemma 77.2 then continues the sequence.  No second source, Reset, or hypothetical
response run is used. $\square$

**Theorem 77.4 (U4: WLAB-ord unknown-law acquisition and callable use).** Under
Definition 77.1, the schedule (77.3) terminates with the exact $u$, material
incidence, $T$, $x_0$, and the actual endpoint

$$
x_* = T^Lx_0+\sum_{j=1}^{b}T^{L-\tau_j}e_{\ell_j}.
\tag{77.9}
$$

It installs a predictor for every sufficiently backed finite adaptive continuation
of the complete menu and for the declared future $P/S$ extensions.  The attained
startup costs are

$$
(b+1)(2R-1)\ \text{Ticks},\quad b\ \text{Adds},\quad
2Rb(b+1)\ \text{scalar Reads},\quad 2R(b+1)\ \text{Holds},
\tag{77.10}
$$

before any optional later use.  These counts include all literal zero or signed
rational payloads, acknowledgements, framing, End/Return traffic and local
copies; (77.10) is the operation count, not a bit-width or total-resource bound.

**Proof.** Lemma 77.3 supplies the whole terminal moment sequence.  For two
terminals $i,j$, the first $k$ with $(M_k)_{ij}\ne0$ is their tree distance:
before the distance there is no walk, and at the distance the unique simple path
has the positive product of its edge weights; a diagonal stay or a backtrack
would make the walk longer.  The positive weighted terminal metric therefore
earns the complete rooted material tree and its subdivision vertices by the
existing terminal-metric/root-recognition supplier, with the authentic ordered
roster retained.  This use is source-specific; it does not infer a graph from a
name or a finite response table.

Run the infection calculation on the earned tree.  Start with terminal coordinate
vectors.  When a marked vertex $v$ has one unmarked neighbour $w$, the exact
incidence equation is

$$
Te_v=a_v e_v+T_{wv}e_w+\sum_{z\sim v,\ z\ne w}T_{zv}e_z.
\tag{77.11}
$$

All terms except $a_v$ and the positive $T_{wv}$ are already represented by
terminal polynomials.  Moment pairings from (77.7) determine $a_v$ and
$T_{wv}^2$; the promised rational positive coefficient determines the positive
rational square root.  Induction over at most $I=N-b$ infection steps constructs
polynomials $p_{v,r}$ of degree at most $I$ with

$$
e_v=\sum_{r=1}^{b}p_{v,r}(T)e_{\ell_r}.
\tag{77.12}
$$

The pairings in (77.12) require moments only through $2I+1\le2R-1$; these are
already earned.  Thus the full rational matrix $T$, including arbitrary diagonal,
is reconstructed.  This is the existing positive-tree infection argument applied
to the actual pulse matrix, not a new generic observability theorem.

Equation (77.12) gives the initial field from the actual free responses:

$$
(x_0)_v=\sum_{r=1}^{b}\sum_{k=0}^{I}p_{v,r,k}\,(f_k)_r,
\qquad
p_{v,r}(z)=\sum_{k=0}^{I}p_{v,r,k}z^k.
\tag{77.13}
$$

Indeed, transpose (77.12) and pair with $x_0$. Symmetry gives
$e_{\ell_r}^{\mathsf T}p_{v,r}(T)x_0
=\sum_k p_{v,r,k}e_{\ell_r}^{\mathsf T}T^kx_0
=\sum_k p_{v,r,k}(f_k)_r$. Thus each term in (77.13) is scalar and
uses the actual $r$th terminal component of the free scan. This is the
Time-to-entry route used below; it adds no Read.

The pulse schedule itself gives (77.9), since every pulse remains in the same
source and is advanced by the remaining number of actual Ticks.  During the final
Hold retain the exact term, current roster, $T$, $x_*$, all genuine bindings and
rights, the parser state and a complete predictor.  For a valid terminal Add the
predictor adds $qe_{\ell_j}$; for Tick it applies the current $T$; for Read it
returns the corresponding coordinate; for Hold it preserves the state.  A future
growth updates the material incidence by the declared zero-cell/unit-edge rule,
updates the roster and retains all old coefficients and values.  Distinct absent,
branch and wrong-type growth replies, out-of-roster refusals, malformed frames,
proper incomplete frames and disabled calls retain their original service
semantics.  The actual input, full output and successor are consumed before each
next settled call.  Induction on complete calls proves predictor equality and
complete adaptive service.  It does not require the continuation to stay on the
startup trajectory.

The first scan has $b(H+1)=2Rb$ Reads; each of the $b$ pulse blocks has the same
count.  There are $(b+1)H$ Ticks and $(b+1)(H+1)$ Holds, giving (77.10), and one
literal Add for each pulse.  All exact arithmetic, elimination, root recognition,
record retention and simultaneous backing remain charged. $\square$

**Construction 77.4a (one acquired callable successor).** After the final held
cut, choose the earned last terminal $\ell_b$, compute its current rational
$q=(x_*)_{\ell_b}$ from the retained predictor, and actually execute
$\operatorname{Add}(b,q)$, Hold, and $\operatorname{Read}(b)$.  The returned scalar
is $(x_*)_{\ell_b}+q$, and the retained predictor updates to
$x_*+q e_{\ell_b}$.  The terminal choice and the whole rational operand are
earned data and are paid through the real selector, frame, acknowledgement and
Return.  This is a concrete same-source callable use; it is not a free selector,
an extra coefficient port, or a claim that the post-use field remains a startup
image.

**Proposition 77.5 (U4 views and exact recovery limits).** On the fixed WLAB-ord
installation define the four expressions at the startup/endpoint cut as follows:

| View | Independent meaning |
| --- | --- |
| Space | the actual ordered material tree, its commissioned $T$, and the current field $x_*$ |
| Time | the actually executed free scan, ordered pulse epochs $(\tau_j,j)$, literal terminal returns, and completed Tick/Add/Hold chronology |
| Boundary | the terminal transfer function $\Phi_T(z)=C(zI-T)^{-1}J$ together with a declared current readout $Cx_*$ |
| Memory | the retained full predictor, current field, law, roster, parser and callable rights |

Time is the paid startup chronology, not an unrestricted old journal.  Boundary's
transfer function is computed from the acquired law; it is not a claim that every
coefficient was separately read.  Memory contains a callable predictor and its
actual backing, not a free copy of Time.

The complete startup transcript has exact kernel $(u,T,x_0)$: the free and pulse
blocks determine that triple, and the triple determines every return of the fixed
schedule.  At a settled cut, complete future service has kernel $(u,T,x_*)$:
equality of this triple gives the same guarded menu and successor induction, while
a difference in the current field is separated by a finite terminal Krylov Read.
These are task kernels for the named installation, not a statement that a bare
Boundary value or an erased command journal is sufficient.

For fixed $T$ and fixed pulse schedule put

$$
r=\sum_{j=1}^{b}T^{L-\tau_j}e_{\ell_j},
\qquad x_*=T^Lx_0+r.
\tag{77.14}
$$

Then the following are exact on their stated domains.

1. Time recovers Space by (77.13) and (77.9), and the actual source run realizes
   that endpoint. Space recovers Time's mathematical scalar sequence by replaying
   the fixed schedule with recovered $T$ and $x_0$ only under the condition in
   item 3; this replay is a calculation and does not replace the provenance of
   the literal returns.
2. Space and Memory recover one another by the retained predictor equality.  The
   route remains valid after a future growth because the predictor is updated with
   the actual new incidence and old coefficients.
3. Space recovers the performed Time, including the original field, exactly when
   $T$ is invertible.  If $T$ is singular, an archive $D x_0$ restores this route
   exactly when

   $$
   \ker T\cap\ker D=\{0\};
   \tag{77.15}
   $$

   any linear archive satisfying (77.15) has rank at least $\dim\ker T$.
4. On the attained endpoint affine space $r+\operatorname{im}T$, Boundary recovers
   the current field exactly when

   $$
   \ker C\cap\operatorname{im}T=\{0\}.
   \tag{77.16}
   $$

   Under (77.15) and (77.16), all displayed routes agree through the same
   $(T,x_0,x_*)$; when either condition fails, the corresponding inverse is not
   claimed.

**Proof.** Since $T$ is symmetric, $\ker T^L=\ker T$ for $L\ge1$.  Thus two
startup fields have the same endpoint exactly when their difference lies in
$\ker T$.  Adding the archive $D$ distinguishes every such difference exactly
when (77.15) holds, proving the third assertion and its rank lower bound.  For
Boundary, two attained endpoints differ by an element of $\operatorname{im}T^L=
\operatorname{im}T$; equality of $Cx_*$ is therefore equivalent to a difference
in $\ker C\cap\operatorname{im}T$, proving (77.16).  The first two assertions
follow from Theorem 77.4.  Every route computes the same affine formula (77.14),
so compositions commute wherever the displayed injectivity conditions hold. $\square$

The limits are real on the named domain.  In the seven-vertex source of (71.1),
with unit $T=A$, put

$$
\eta_\varepsilon=1,\qquad
\eta_{LL}=\eta_{RR}=-1,
\qquad \eta_v=0\ \text{otherwise}.
\tag{77.17}
$$

The explicit edge list in (71.1) gives $A\eta=0$, while the earned terminal
values are $(-1,0,-1)$.  Hence $x_0$ and $x_0+\eta$ have different startup Time
and identical endpoint and complete future service.  This is a counterexample to
unqualified Time-from-Space recovery.  Conversely, if $T$ is invertible then
$\operatorname{im}T=\mathbb Q^N$; since $b<N$, terminal Boundary with
$C=J^{\mathsf T}$ has a nonzero kernel and cannot recover an arbitrary current
interior coordinate.  No unrestricted four-view inverse, unknown-coefficient
oracle, arbitrary raw permutation, or physical installation theorem follows.

[Unknown Field Native Startup](RECURSIVE_RELATIONAL_OBSERVATION_UNKNOWN_FIELD_NATIVE_STARTUP.md)
§§1–5 already supplies paid free/forced subtraction,
unknown-law acquisition, installation at the true advanced field, complete
retained adaptive prediction and subsequent actual terminal control. Its source
is a rooted rational Jacobi path with a supplied order cap, $0<T<I$, one scalar
port, and Tick returning the updated root value. Here the authentic complete
ordered roster earns $R=3b-1$ on an unknown branching native tree; $T$ may be
singular or indefinite with arbitrary diagonal, Tick returns only ACK, and each
vector scan costs $b$ separate Reads. Lemmas 77.2–77.3 provide the rational
vector recurrence and successive pulse columns under precisely these changed
hypotheses. The generic subtraction, predictor and control methods are reused;
neither the Jacobi reconstruction nor its returning-Tick counts are transferred.

The WLAB-ord result uses the finite-dimensional saturation supplier
`D5.S3.ObserverMemory.Dynamics.FiniteTimeTomographySaturation.all_future_kernel_eq_finrank_kernel`
only to justify a finite moment horizon after a full ambient law is known; the
actual rational recurrence and the pulse subtraction above are source-specific.
The terminal linear algebra uses the finite observability/Gram supplier over
$\mathbb R$ after extension of scalars, with rational rank certified by nonzero
minors.  Native material/root recognition is the exact ordered $D$, $b\ge3$
supplier in
`D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition`; it supplies
syntax and incidence recognition, not coefficients, rights or an unknown-law
port.  The infection mechanism is the established positive-tree argument and the
primary zero-forcing/infection literature cited in §§1–3.  The added content is
the one-source WLAB-ord pulse schedule, its arbitrary-diagonal recurrence proof,
the actual endpoint, and the exact kernels (77.15)–(77.16).

## 78. U5: the exact fresh-Read price of a same-material polynomial law

**Definition 78.1 (the law-transfer task and complete entrance information).**
Retain the original integral, symmetric, zero-diagonal native adjacency
$A\in\mathbb Z^{N\times N}$ on one fixed material tree $u\in\mathcal D$ with
$b\ge3$ terminals, its earned complete roster, genuine terminal Add/Read rights,
ACK-only Tick and Hold, and no Reset or deletion. Let $f\in\mathbb Q[z]$ and

$$
F=f(A),\qquad F\text{ invertible},\qquad \|F\|_2<1.
\tag{78.1}
$$

Fix a known matrix $M\in\mathbb Q^{m\times N}$, independent of the entry field,
and put $d=\operatorname{rank}M$, allowing $0\le d\le N$ and redundant rows.
The actual source field at entrance ranges over every $x\in\mathbb Q^N$.
The values $Mx$ have actually been acquired and retained before this task;
that acquisition, its source preparation and its surviving stores remain paid
premises. They are the **complete initially accessible field-dependent
information**, not a subrecord selected from a more informative predictor.
Precisely, in a fixed field-independent context $\kappa$, the entire accessible
initialized receiver state is $\rho_\kappa(Mx)$ for a fixed effective map
$\rho_\kappa$, and it includes the literal values $Mx$. Equal $Mx$ therefore
means equal initialized receiver states. This contract includes every accessible
provider record, advice, program, selector, counter, parser/control state,
reference byte and random tape: any dependence on $x$ must factor through $Mx$.
All remaining data, including $M$, graph, law, genuine bindings/rights, fixed
program and any fixed random tape, are independent of $x$. An inaccessible
producer archive is not advice and its isolation/backing is still charged.

Only fresh successful scalar Read replies add field-dependent information.
All ACKs, guards, refusal/range/framing replies and enabledness have their
original field-independent semantics. There is no field-dependent timing,
capacity, allocation-name or other numerical channel. Every actual input,
complete output, End, acknowledgement, Return and matching controller update is
finished before the next settled call; proper incomplete frames retain their
real pending state. Exact rational work and sufficient simultaneous backing are
installation premises, not observations about $x$.

The task is to end on this same material with physical field $Fx$, for every
entry; a field report is not required. Any successful growth strictly enlarges
the persistent material and cannot be undone, so it cannot occur on a successful
same-material path. Refused growth probes leave the material and field unchanged.
The principal instance is $F=(4I+A)/8$. Every native vertex has degree at most
three, so the symmetric spectrum of $A$ lies in $[-3,3]$ and this $F$ has spectrum
in $[1/8,7/8]$, satisfying (78.1). The target is a compound operation; the
primitive native Tick remains $A$.

**Lemma 78.2 (integral-spectrum separation).** For every $k\ge0$,

$$
F-A^k\ \text{is invertible over }\mathbb Q.
\tag{78.2}
$$

**Proof.** Orthogonal diagonalization of the real symmetric $A$ also diagonalizes
$F-A^k$. If the latter were singular, an eigenvalue $\lambda$ of $A$ would
satisfy $f(\lambda)=\lambda^k$. For $k=0$, this contradicts
$\lvert f(\lambda)\rvert<1$. For $k\ge1$, $\lambda=0$
would make $f(0)=0$ and hence make $F$ singular. If $\lambda\ne0$, it is an
algebraic integer because $A$ is integral. Its minimal polynomial divides both
$\chi_A$ and the rational polynomial $f(z)-z^k$. Every conjugate $\mu$ is
therefore another eigenvalue of $A$ and satisfies

$$
|\mu|^k=|f(\mu)|<1.
$$

The norm of the nonzero algebraic integer $\lambda$ is a nonzero integer, but the
product of its conjugates has absolute value below one, a contradiction. Thus
$f(\lambda)\ne\lambda^k$ for every eigenvalue of $A$, proving (78.2).
The integrality of $A$ and strict contraction of $F$ are both essential to this
argument. $\square$

**Theorem 78.3 (U5 lower bound: every exact transfer pays the missing rank).**
Under the complete entrance-information contract of Definition 78.1, any exact
pointwise-finite adaptive protocol on the same material uses at least

$$
N-d
\tag{78.3}
$$

fresh scalar Reads on every terminating input path. No field report is required.
Here an exact deterministic protocol, or a protocol with a fixed field-independent
random tape, must be correct and terminate on every rational entry.

**Proof.** Fix one actual terminating path at $x$, with $r$ fresh successful
Reads and $k$ Ticks. Freeze its complete actual command/operand sequence, replies,
local choices and stop. Along this sequence the source field after $t$ Ticks is
$A^t x+q_t$, where $q_t$ is the offset from the Adds already performed. A fresh
Read at terminal $\ell$ then has row $e_\ell^{\mathsf T}A^t$ and offset
$e_\ell^{\mathsf T}q_t$. Stack its $r$ rows into $O$.

For every $\eta\in\ker M\cap\ker O$ compare the actual executions at $x$ and
$x+\eta$. Initially their **whole receiver states** agree by
$\rho_\kappa(M(x+\eta))=\rho_\kappa(Mx)$, their material/bindings/rights and
control phases agree, and their source fields differ by $\eta$. Induct on the
completed calls, retaining equality of the whole receiver state and pending
input/output control, and source-field difference $A^t\eta$. Equal receiver
state and the common fixed program/tape select the same next entire input,
address, rational operand and local work. An Add translates both fields equally;
a Tick multiplies the difference by $A$; Read and Hold preserve it. Every Read
has equal literal rational values because its row in $O$ annihilates $\eta$.
Consequently its entire encoding, framing and return agree too. ACKs, guards,
refusals, range and malformed-frame replies are identical by the installed
semantics and common material/authority. A proper incomplete frame leaves the
same real pending bytes/state in both executions; completion introduces only the
same call and declared reply. All receiver updates, including retained records,
selectors, counters, parser and stopping control, are deterministic from these
identical inputs and complete outputs. No hidden resource channel supplies a
further distinction. Thus the induction preserves all its assertions, including
the same termination decision and the same final Add offset $q$.

Both entries lie in the all-$\mathbb Q^N$ task domain, so correctness gives
$F\eta=A^k\eta$. Lemma 78.2 forces $\eta=0$. Hence $[M;O]$ has rank $N$;
its first block has rank $d$ and its second has at most $r$ rows, yielding
$r\ge N-d$. The proof freezes a realized path only to prove that every point of
this affine fibre realizes the same complete path; it does not assume that
adaptivity or its control state is initially field-independent beyond $Mx$.

For a field-independent random tape with zero error and almost-sure termination
separately for every rational entry, intersect those probability-one events over
the countable set $\mathbb Q^N$. On the resulting probability-one set of tapes
the same deterministic proof applies simultaneously to every entry. Thus the
bound also holds almost surely for each entry under that contract. $\square$

**Theorem 78.4 (U5 attainment by a paid terminal control).** The bound (78.3) is
attained for every $0\le d\le N$. Use a fixed rational pivot order to select $d$
independent actual rows $M_B$ of $M$, retaining their acquired values $M_Bx$.
Select $N-d$ rows from the finite terminal Krylov family

$$
\{e_{\ell}^{\mathsf T}A^j:\ell\text{ a terminal},\ 0\le j\le I=N-b\}
\tag{78.4}
$$

that complete $M_B$ to an invertible $N\times N$ matrix $Q=[M_B;O_S]$.
All selections depend only on the known matrices and fixed orders, never on
unknown values of $x$. Order selected sample pairs $(j,\ell)$ by increasing
epoch and then terminal, and define
$H=\max(\{0\}\cup\{j:(j,\ell)\text{ selected}\})$. At each epoch
$t=0,\ldots,H$, actually Hold and perform exactly the selected Reads at $t$,
consuming their full returns. Release the Hold before each intervening Tick.
The actual fresh values $y=O_Sx$, together with $M_Bx$, reconstruct
$x=Q^{-1}\binom{M_Bx}{y}$, with the two value blocks stacked as a column,
while the real source is at $d_0=A^Hx$.
The final sampling Hold covers this solve and the control solve below.

Select $N$ independent allowed control columns from the same family, written

$$
K=[A^{j_1}e_{\ell_{i_1}}\ \cdots\ A^{j_N}e_{\ell_{i_N}}],
\qquad L=\max_r j_r.
\tag{78.5}
$$

Solve the exact rational system

$$
Kc=Fx-A^Ld_0.
\tag{78.6}
$$

Release the sampling Hold. At each relative control epoch $s=0,\ldots,L$,
execute every selected $\operatorname{Add}(i_r,c_r)$ with $L-j_r=s$, in a fixed
tie order, then actually Hold. End that Hold before the next Tick to $s+1$.
Thus injections occur at $L-j_r$ in decreasing $j_r$ order, including at epochs
zero and $L$ when selected. The final source field is exactly $Fx$. The account is

$$
(N-d)\ \text{fresh Reads},\quad N\ \text{Adds},\quad
H+L\ \text{Ticks},\quad H+L+2\ \text{Holds},
\tag{78.7}
$$

with $H,L\le I$, no growth and no Reset. Zero Add operands remain literal calls.
The $H+1$ sampling Holds and $L+1$ control Holds are separate real calls, including
the two phase Holds at their common absolute epoch $H$.

In particular, if $d=N$, no fresh row is selected, $O_S,y$ are empty, $H=0$,
$Q=M_B$ is invertible and $d_0=x$ is reconstructed solely from the actually
retained full-rank values. Execute the initial Hold and the same control phase.
This branch has zero fresh Reads and zero sampling Ticks, but still $N$ Adds,
$L$ Ticks and $L+2$ Holds. It applies equally when $M$ has more than $N$ rows.
When $d=0$, $M_B$ is empty and all $N$ reconstruction values are fresh Reads.

**Proof.** The existing all-terminal forcing identity in §31.1 makes (78.4)
span the native row space. Fixed exact pivoting therefore extends any basis
$M_B$ by exactly $N-d$ rows; redundant retained rows are not counted twice.
Symmetry gives the same spanning assertion for the control columns, so $K$ is
invertible. The source has no Adds in the sample phase, proving its actual
values and endpoint. This also proves reconstruction and the empty-selection
branch, without a maximum of an empty set.

During the control phase, at epoch $s$, after that epoch's Adds, induction on
actual Tick and Add calls gives the entire source field
$A^s d_0+\sum_{L-j_r\le s}c_r A^{s-(L-j_r)}e_{\ell_{i_r}}$.
An Add at epoch $L-j_r$ has exactly $j_r$ remaining Ticks before epoch $L$.
Its endpoint contribution is therefore $c_rA^{j_r}e_{\ell_{i_r}}$.
At $L$ the sum is $A^Ld_0+Kc=Fx$, by (78.6).

After reconstructing $x$, initialize the full predictor at the true $d_0$;
then update it on every actual Add/Tick/Hold and consume every complete inner
reply/Return before exposing the endpoint. The schedule counts give (78.7),
including the full-rank branch and literal zeros. Matrix selection/solves,
rational widths, source and predictor update buffers, retained $Mx$, samples,
control record, phase/schedule, genuine references/rights, parser, input/output
backing, ACKs, framing, End/Return traffic and any exports coexist when live and
are separately charged under §65. No scalar-count formula makes them free.

Retain the synchronized current vector $z=Fx$. For another transfer use its
actually acquired full record, namely $M=I$ and values $z$, at the new entrance.
The $d=N,H=0$ branch physically produces $Fz$ with no fresh Reads, paying all
$N$ Adds, $L$ Ticks, $L+2$ Holds and the same work/backing/traffic. This is warm
use of acquired information, not an exemption from Definition 78.1. $\square$

**Proposition 78.5 (U5 completed-endpoint views, transport and failure boundary).**
Fix the context of Definition 78.1, the deterministic selectors and tie orders of
Theorem 78.4, and a declared rational input subspace $X\subseteq\mathbb Q^N$.
The lower bound remains an all-$\mathbb Q^N$ theorem; $X$ specifies only the
view-recovery domain. The common cut here is **after all sampling, solving,
control, full outputs/Returns and predictor updates of that transfer**, in its
final Hold with no pending packet and a retained completed-transfer phase marker.
It is not an arbitrary settled acquisition/control cut.

The receiver actually retains the chosen sample/column lists, $H,L$, phase and
counter records, $Mx$, fresh sample triples, performed Add operands and complete
transaction chronology, and the synchronized predictor at $z=Fx$. Lists and
counters are obtained by the paid selections and actual calls just specified;
$Mx$ comes from the paid entrance acquisition, $y$ from the new actual Reads,
and $c$ from the paid solve and performed Adds. Their distinct live copies and
retained backing are charged. Fixed contextual data $\kappa$ includes the
material/law, $f,M$, program, selectors, schedule/phase convention, installed
references and rights. It includes **no values $Mx,y,c,x$ or $Fx$**. Actual
bindings/authority and the fact that these transactions occurred are common
installation/run premises; numerical recovery does not manufacture them.

On completed runs starting at $x\in X$ define these views by their independent
exposures, relative to that retained context and phase:

| View | Independent meaning |
| --- | --- |
| Space $\mathsf S(x)$ | the actual fixed native material, $A$, and current field $z=Fx$ at the completed transfer endpoint |
| Time $\mathsf T(x)$ | this transfer's actual ordered selected Read triples $(j,\ell,y_{j,\ell})$, all performed control Add inputs $(L-j_r,i_r,c_r)$, and completed Tick/Hold/ACK/framing/Return chronology |
| Boundary $\mathsf B(x)$ | the declared target $f$, actual terminal control interface, and a specified rational linear endpoint readout $w=C_Fz$ |
| Memory $\mathsf M(x)$ | the retained synchronized predictor at $z$, acquired literal record $Mx$, solved control vector $c$, and completed phase/schedule/callable control state |

Time is the finite actual transaction window of this transfer, not an unrestricted
pre-entry history. Its input values, including zero Adds, are exposed as well as
its Read outputs. Memory retains a current prediction and the specified acquired
and control records, not the entire Time journal. Boundary's
$C_F\in\mathbb Q^{s\times N}$ is fixed and known. Its value can be a paid
computed export from the acquired predictor; that interpretation installs no
new source port and claims no extra physical
measurement. If instead an allowed endpoint Read is actually performed to supply
it, that additional call and its complete traffic are charged separately from
(78.7). Neither interpretation creates an unperformed measurement's provenance.

The common joint image consists exactly of
$(\mathsf S(x),\mathsf T(x),\mathsf B(x),\mathsf M(x))$ from these completed
actual runs with $x\in X$, in this fixed context and phase. Every such input has
the acquisition/transfer execution of Theorem 78.4; no separate marginal optima
are being joined. On this image Space, Time and Memory recover each other's
exposed mathematical content. Boundary recovers them exactly when

$$
\ker(C_FF)\cap X=\{0\}.
\tag{78.8}
$$

All existing recovery routes agree. These statements concern content in the
common actual run, not numerical certification that an absent run took place.

**Proof.** Write $h=H+L$. The direct decoders of Space and Memory are
$x=F^{-1}z$, using the actually current field or its synchronized predictor.
In particular Space-to-Memory first recovers $x$, then computes the retained
values $Mx$, samples $O_Sx$, and unique control
$c=K^{-1}(F-A^h)x$ with the fixed selectors/schedule. It reproduces the defined
completed control state; it does not infer archived values from predictor
synchronization at an earlier cut.

Time has a decoder requiring no import of Memory or of an unlisted $Mx$:
its complete performed Add operands give $c$, and (78.6) gives

$$
Kc=(F-A^{H+L})x,\qquad x=(F-A^{H+L})^{-1}Kc.
\tag{78.9}
$$

The inverse exists by Lemma 78.2, including $H=0$. This route uses the actual
input chronology and the known $K,H,L$, not matrix $M$ as if it were the values
$Mx$. Alternatively, when the acquired values are explicitly supplied alongside
Time, $Q^{-1}\binom{M_Bx}{y}$ gives the same $x$ by the acquisition equations.
With either direct decoder, forward evaluation computes $Fx$, $Mx$, $O_Sx$ and
$c$; the fixed schedule then computes exactly the scalar/frame content of the
already performed Time. Actual provenance is supplied by the joint-image
premise, not by this calculation. The authentic reference and grants are retained
context throughout, not reconstructed from rationals.

For Boundary, two inputs in $X$ have equal readout exactly when their difference
lies in $\ker(C_FF)\cap X$. Under (78.8), rational elimination on a basis of
$X$ supplies a left inverse on the attained readout image, recovering $x$ and
hence all three other views. If (78.8) fails, $0$ and a nonzero rational vector
in that intersection have equal Boundary values but distinct endpoints because
$F$ is invertible. Thus that inverse is impossible on this declared domain.
Forward evaluation always supplies Boundary from each of the other views.

Each decoder followed by its encoder is the identity on its attained image,
and each encoder followed by its decoder recovers the same $x$. Consequently
all routes with the same endpoints agree; where (78.8) fails this statement
includes only the three invertible views and their forward Boundary maps.
Different $x$ also give different complete future native field service at these
endpoints: $F(x-x')\ne0$ is separated by an all-terminal Krylov Read. Equal
endpoints have equal complete service by §64 with fixed material and callable
context. Thus the invertible views have exactly the same kernel as the declared
continuation task. Boundary has that kernel precisely under (78.8).

For dynamics, start at this completed endpoint $z=Fx$ and actually execute the
warm branch of Theorem 78.4. It ends at $Fz=F^2x$; its intermediate native law
is still $A$. Apply the same view definitions to that new transfer with context
$\kappa^{\rm w}$, acquired record $M^{\rm w}=I$, and input domain $FX$.
The old transaction archive is separately retained with its own backing or
released; it is not silently part of the newly defined window. If $E_i^\kappa$
and $D_i^\kappa$ denote the encoders and proved decoders for view $i$, the
transport is $E_i^{\kappa^{\rm w}}\circ F\circ D_i^\kappa$. For every $x\in X$
it returns $E_i^{\kappa^{\rm w}}(Fx)$, the content supplied by this same warm
execution. Composing any two recovery routes and this transport therefore gives
the same result, by substitution of $x$ and then $Fx$. Boundary participates
in an inverse transport square only when (78.8) holds on $X$ and its counterpart
holds on $FX$ for the new readout. Actual calls and complete outputs, not local
reencoding alone, establish the new run's provenance. Growth changes the material
or adjacency and ends this fixed-$F=f(A)$ correspondence. $\square$

The completed-endpoint restriction is essential. On the seven-vertex unit law
(71.1), let $\eta$ be (77.17), so $A\eta=0$ but
$C\eta=(-1,0,-1)$. Take the actually acquired complete entrance information to
be $Mx=Cx$, with $d=b<N$. A completing sample set must contain a positive epoch,
since its epoch-zero rows already lie in the row span of $C$; hence $H\ge1$.
At the held cut after acquisition and the solve but before control, entries $x$
and $x+\eta$ have identical actual fields $A^Hx$, while their retained $Mx$
and control records differ: $K(c'-c)=F\eta\ne0$. Both predictors are correctly
synchronized with that same intermediate field. Thus synchronization alone
cannot invert the archive projection there. Nor does the completed-endpoint
inverse extend through arbitrary subsequent singular native Ticks with archives
retained. Complete prediction continues with those archives, but the old
Space-to-archive claim has left its domain.

The theorem is deliberately narrower than a physical equivalence of primitive
laws. If the target is itself $F=A^k$, native Ticks attain it with zero fresh
Reads and the separation hypothesis (78.2) is false. For an arbitrary rational
weighted or nonsymmetric law, the algebraic-integer proof does not apply.
Unrestricted nonlinear entrance information, noisy or finite-precision calls,
growth during the transfer, and total-resource optimality are outside the theorem.
The effective initialization $\rho_\kappa(Mx)$ may process its acquired values
nonlinearly; what is restricted is the complete information supplied at entrance.
The exact source-relative addition is the same-material, no-report lower bound
and paid attainment for the contracting polynomial family. Generic Krylov
spanning, finite saturation, complete adaptive transcript induction and terminal
control are reused suppliers. Unknown Field Native Startup §§3–5 already gives
paid control from an acquired advanced predictor on its different Jacobi source
with scalar-returning Tick; it does not assert this original-integral-$A$
no-report price. No new Lean certification, primitive-law replacement or
original-$Q$ result follows.

## 79. Scope of the two law units

Sections 77 and 78 are separate installations and separate tasks. WLAB-ord pays
to acquire an unknown commissioned law and its current field from one actual
ordered specimen; U5 assumes a known integral unit law and pays to execute a
different polynomial target on that same material. Their favorable counts cannot
be added, exchanged, or compared as a scalar optimum. Neither unit supplies the
fixed-$G_{\rm gc}$/original-$Q$ result, the parked-consumer or unchanged-
initialization obligations, a universal alpha/beta generator, or the joint
native/path/quantum/continuous apparatus. All earlier scoped settlements stand
unchanged. The full common-process objective and the named original obligations
remain open outside these declared domains.

## 追加锚（本行以下为增补区）

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

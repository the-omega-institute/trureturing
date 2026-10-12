# Intrinsic root depth after a retained literal history

> This `generic-v1` reference volume gives ordinary mathematical proofs. It makes no claim of Lean kernel verification. Its existing text is append-only after integration; subsequent mathematical additions follow the final append anchor.

## 1. Source, actual producer and complete retained boundary

**Definition 1.1 (static native source and supplied depth algebra).** All sources are nonempty finite free ordered trees

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

There is no sharing quotient, associativity or commutativity. A repeated subtree has repeated native occurrences. For every finite absolute word $q$ over $\{L,R\}$, including $\varepsilon$, the only source operation is $\mathsf{Read}(q)$, returning $r_u(q)\in\{\alpha,\beta,\mathsf{br},\mathsf{abs}\}$. A strict descendant of a leaf is absent. The source remains $u$ throughout; neither the mathematical operation $\rho$ nor its inverse is an available source action.

Use the primitive-ray and pairing results of [JM, §§36, 49][JM]. Put

$$
T_j=\rho^j\alpha,\qquad
\nu(t)=\max\{n:t\in\rho^n[\mathcal T]\},\qquad
Q(t)=(\nu(t),e(t)),\quad e(t)=\mathbf1_{\{T_j:j\ge0\}}(t).
$$

Every $t$ has a unique primitive endpoint $p(t)$ with $t=\rho^{\nu(t)}p(t)$. In particular $\nu(\rho^n t)=n+\nu(t)$, $\rho$ is injective, and $e(t)=1$ precisely when $t=T_{\nu(t)}$. With $Q(s)=(a,e)$ and $Q(t)=(b,f)$ the supplied ordinary pairing law is

$$
Q(\langle s,t\rangle)=
\begin{cases}
(b+2,1),&e=f=1\text{ and }a=b+1,\\
(\min(a,b),0),&\text{otherwise}.
\end{cases}
\tag{LRD.1}
$$

Thus $T_0=\alpha$, $T_1=\beta$, and $T_{j+2}=\langle T_{j+1},T_j\rangle$. Both $\nu$ and the atomic flag are intrinsic coordinates of a finite tree, not physical time, an actual entrance count, a size oracle or a reply supplied by $\mathsf{Read}$.

**Assumption 1.2 (the canonical acquired row).** Fix a common finite prefix-free cut $P$ and the whole-source producer of [SLH, Definitions 59.1–59.3 and Theorem 59.4][SLH]. It starts from common source-independent installed data, actually traverses one source, computes its complete concrete exterior $C$, and computes the entire equality partition $\pi$ of the reached cut subtrees. Its row is $R=(C,\pi)$. Unreached cut addresses remain blocked by concrete strict-prefix leaves of $C$. The cut and all common task data are declared; they cannot themselves select a source.

At the complete row handoff every accessible source-bearing field factors through $R$, and $R$ is recoverable from the accessible boundary. Handles, program selection, schedules, lengths, outputs, control positions, caches, permissions, timing distinctions and archives convey no additional source information. This is a condition on accessible information; it does not require physical destruction of inaccessible material. The earlier acquisition transcript is not available for free.

Write $B$ for the finite set of old equality classes. Every class has at least one reached occurrence; choose its representative address $p_b$ by a common order. The supplied exact row fiber is

$$
U_R=\{C[(z_{[i]})_i]:z_b\in\mathcal T,\ z_b\ne z_c\ (b\ne c)\}.
\tag{LRD.2}
$$

The filling is a bijection from these jointly legal class tuples to sources of this same producer. Equal occurrences share one $z_b$; every different-class disequality is retained, including classes outside a later queried cone. Zero classes give the single empty tuple and the concrete source $C$. An arbitrary source-selective procedure returning a tuple called $(C,\pi)$ is outside this assumption.

**Assumption 1.3 (actually acquired finite history and entry).** From the row handoff a common deterministic effective controller starts with $R$ and common installed data. It chooses every query from these fields and preceding replies only; every local calculation between actions terminates. Let $h$ be an actually attained finite event prefix, or an attained terminal record including the stop decision. It contains every complete query word, reply, repetition, order and accessible source-bearing control or termination distinction. Derived control is allowed precisely when recoverable from $R,h$. There is no source-dependent hidden schedule, program or old archive.

The next complete cut exposes exactly $(R,h)$, in the same information sense as Assumption 1.2. A controller that has halted is absorbing. A subsequent service or continuation has a separately declared common entry, installation and invocation, on this same stationary source. No theorem below grants a free post-halt invocation. The entry's initial accessible source-bearing fields are exactly the declared boundary. It has only the four-reply port, with no equality, image-membership, clock, update, source-label, spatial-coordinate, reroot or stream oracle.

**Definition 1.4 (exact attained fiber).** For a fixed attained $R,h$, let

$$
D(R,h)=\{u:\text{the canonical producer outputs }R\text{ and its common controller attains }h\}.
$$

Specializing [SLH, Theorem 62.2][SLH] to stationary epoch zero gives

$$
D(R,h)=\{u\in U_R:r_u(q)=c\text{ for every read }(q,c)\text{ in }h\}.
\tag{LRD.3}
$$

The non-read events must also pass the common replay condition. Here that condition holds because $h$ is attained. The forward direction records actual replies. Conversely, membership on the right first runs the same actual row producer by (LRD.2); induction over the events of $h$ then gives the same next query, reply, local result and stop decision. This converse neither decides controller termination on unrelated records nor equates arbitrary literal lists with actual runs. All later witnesses below use this converse on the declared common entry.

## 2. Shared history cells and simultaneous deep finite realizations

**Definition 2.1 (the reused exact cell representation).** Set

$$
d=1+\max(\{0\}\cup\{|q|:(q,c)\text{ is a read in }h\}).
$$

A native depth-$d$ pattern exposes pairs and literal leaves above depth $d$, stops at early leaves, and places one residual at each reached depth-$d$ position. Enumerate such patterns $\eta_b$ for every old class. A residual name is the pair $(b,w)$ of old class and frontier position; every occurrence of that old class uses the same names. Different names are not required to have different values.

Let $E_{\eta,b}$ be its free pair term over $\alpha,\beta$ and these names, and let

$$
W_\eta=C[(E_{\eta,[i]})_i],\qquad
\Delta_\eta=\bigwedge_{b\ne c}E_{\eta,b}\ne E_{\eta,c}.
\tag{LRD.4}
$$

These are whole-term negatives, not childwise negatives. Fixed native ground pieces are expanded into the literal free signature. Keep patterns for which $W_\eta$ gives every recorded reply and every displayed negative has syntactically different sides. Every query is strictly above every frontier in absolute coordinates, so its branch, leaf or absence reply is constant over the fillings of a fixed pattern. Absence is justified by an actual earlier terminating leaf, never by an empty residual. Contradictory literals eliminate the pattern.

The existing `NativeHistoryCells.oldTerm`, `wholeTerm`, `cell_feasibility_exact` and `historyCellEquiv`, with stationary history and empty recutting cut, give the disjoint exact representation

$$
D(R,h)\ \cong\
\coprod_{\eta\ \mathrm{kept}}
\{v:X_\eta\longrightarrow\mathcal T:\Delta_\eta[v]\}.
\tag{LRD.5}
$$

The map is $v\mapsto W_\eta[v]$; its inverse extracts each class value at $p_b$ and takes its unique depth-$d$ decomposition. It retains every repetition, unused-cut guard and old-class disequality. Syntactic feasibility here is supplied by finite free-term ground separation, already proved in `NativeGroundSeparation`. `NativeGroundSolutionSpace.constrainedEquiv` similarly transports the entire pulled-back constraint rather than an unrestricted product. These cell, feasibility, unification and generic recutting results are reused, not new claims of this volume. The next theorem supplies the additional simultaneous rank-and-prefix property needed for depth recovery.

**Theorem 2.2 (prescribed non-atomic ranks, deep leaves and all negatives together).** Let $X=\{x_1,\ldots,x_s\}$ be finite. After any chosen variables have been replaced by fixed finite ground trees and those trees have been literally expanded, let $\mathcal L$ be a finite list of syntactically unequal pairs of free $\alpha/\beta$ pair terms over $X$. For arbitrary prescribed $r_i\in\mathbb N_0$ and $L\in\mathbb N_0$, there is one tuple of finite non-atomic trees $z_i$ such that

$$
\nu(z_i)=r_i,\qquad
\mu(z_i)>L,\qquad
A[z]\ne B[z]\quad((A,B)\in\mathcal L),
\tag{LRD.6}
$$

where $\mu$ is minimum native leaf depth. The tuple can moreover be chosen pairwise distinct. Repeated names use one value throughout. Pairwise distinctness is a permitted construction, not an extra assumption on distinct names in (LRD.5).

**Proof.** We use the equal-native-leaf-count reflection mechanism of the existing private `compound_mass_ne` and `bounded_eval_injective`, not a new general disunification theorem. The additional choice of their equal-mass representatives is explicit.

For $s=0$, every side is already ground and the empty tuple works. Otherwise let $t$ bound the syntactic leaf counts of all listed sides, with each variable occurrence counted as one leaf. Choose $h_0>L$ with $h_0\ge1$ and $2^{h_0}\ge s$. Let $\ell_i$ be the native leaf count of $T_{r_i}$. Choose a positive common multiple $M$ of all $\ell_i$, sufficiently large that

$$
M>\max(t,1),\qquad M/\ell_i>2^{h_0}\quad(1\le i\le s).
$$

Start from a complete height-$h_0$ all-$\alpha$ tree. For the $i$th seed replace its $i$th bottom leaf by an all-$\alpha$ comb with $M/\ell_i-2^{h_0}+1$ leaves. This number is at least two. The resulting $p_i$ has exactly $M/\ell_i$ leaves and no leaf above depth $h_0$. Set $z_i=\rho^{r_i}p_i$.

Every nonempty all-$\alpha$ tree is primitive: every $\rho$ image has a $\beta$ leaf. Thus $\nu(z_i)=r_i$ by primitive-ray uniqueness. No $p_i$ is the one-leaf atomic endpoint $\alpha$, so $z_i$ is non-atomic. Substitution never moves an old leaf upward and therefore $\mu(z_i)\ge h_0>L$. Since $\rho^{r_i}$ replaces each $\alpha$ leaf by $T_{r_i}$, each $z_i$ has exactly $M$ native leaves. Unequal prescribed ranks distinguish values; at equal ranks the seed leaf counts agree, the extended bottom positions distinguish the seeds, and injectivity of $\rho^{r_i}$ distinguishes the values.

For completeness, the reused reflection argument applies simultaneously to this tuple. A term with $a$ variable occurrences and $b$ constant occurrences has evaluated leaf count $Ma+b$. A ground term in the list or one of its subterms has fewer than $M$ leaves. A compound term containing variables has evaluated count greater than $M$: if $a\ge2$ it has at least $2M$, and if $a=1$ its other syntactic leaf contributes $b\ge1$. Hence a variable image of count $M$ cannot equal a constant or a compound side. Distinct variable names have distinct images. A constant cannot equal a pair; two pairs can be equal only if their ordered children are equal. Induction on the two bounded terms consequently makes evaluated equality imply syntactic equality. Every listed negative has unequal syntax and is preserved by this same assignment. This includes repeated occurrences and negatives involving expanded fixed ground pieces. The finite construction is effective, and proves all of (LRD.6) at once. $\square$

## 3. An exact finite chart for the root target

**Definition 3.1 (anchors, cutoff and observable charts).** A retained leaf anchor is a concrete exterior leaf, a recorded $\alpha$ or $\beta$ reply, or a recorded absent reply. An attained absent word is nonempty and witnesses a leaf at some strict prefix. If there is an anchor, every kept $W_\eta$ contains a concrete leaf.

Let $H_\eta$ be the pair-height of $W_\eta$, counting residual variables as leaves. For a kept cell containing a literal leaf choose

$$
B_\eta=2H_\eta+1,\qquad A_\eta=B_\eta+2H_\eta=4H_\eta+1.
\tag{LRD.7}
$$

The pairing law gives $\nu(\langle s,t\rangle)\le\nu(s)+2$ and $\nu(\langle s,t\rangle)\le\nu(t)+2$. Following the concrete leaf, whose intrinsic depth is zero or one, bounds every whole-cell root by $B_\eta$. This cutoff is deliberately sufficient rather than sharp.

An observable chart $\theta$ assigns each residual either $j\in\{0,\ldots,A_\eta\}$, meaning exactly $T_j$, or $\star$, meaning the complement of this finite atomic list. Substitute the fixed $T_j$ into $W_\eta$ and every side of $\Delta_\eta$, expanding them literally; call the resulting terms $W_{\eta,\theta}$ and $\Delta_{\eta,\theta}$. Discard a chart if a negative has identical syntactic sides. In a chart with no $\star$, the whole source is ground. Otherwise let $G_{\eta,\theta}$ be the finite nonempty list of maximal ground subterms of $W_{\eta,\theta}$ and put

$$
c_{\eta,\theta}=\min_{g\in G_{\eta,\theta}}\nu(g).
\tag{LRD.8}
$$

The list is nonempty because an original concrete leaf remains. Every remaining residual occurs in the whole-source term. Define

$$
V_{\eta,\theta}=
\begin{cases}
\{\nu(W_{\eta,\theta})\},&\text{no }\star,\\
\{0,1,\ldots,c_{\eta,\theta}\},&\text{some }\star.
\end{cases}
\tag{LRD.9}
$$

The finite chart is internal mathematics, not an extra observation alphabet or an assumed read oracle.

**Theorem 3.2 (justified finite cutoff, including high atomic residuals).** In a cell containing a concrete leaf, replace any residual value $T_j$ with $j>A_\eta$ by any non-atomic value of the same intrinsic depth. Keep every other residual's $Q$ coordinate fixed. This replacement preserves the root $Q$ of $W_\eta$, including its exact intrinsic depth. It is a statement about evaluation; the intermediate replacement need not satisfy old disequalities.

**Proof.** For $b\ge0$ write $q\sim_b q'$ if the two $Q$ coordinates agree exactly or both depth coordinates exceed $b$. The supplied pairing operation takes two child relations $\sim_{b+2}$ to a parent relation $\sim_b$. If both child coordinates agree, their outputs agree. Otherwise each changed child has depth greater than $b+2$. If the other child has depth at most $b$, an atomic exceptional pair would require adjacent child ranks, which is impossible; both outputs are that low minimum with flag zero. If the other child has depth greater than $b$, both output depths are greater than $b$, regardless of atomic flags. These cases also cover two changed children. The strict inequalities keep the ranks at the cutoff and both adjacent boundary ranks in the exact part.

The altered variable coordinates satisfy $\sim_{A_\eta}$. Induction through a pair term of height $H_\eta$ loses at most two cutoff units per edge and gives root relation $\sim_{B_\eta}$. Both roots have depth at most $B_\eta$, by the original literal leaf bound independent of fillings. Therefore their root coordinates agree exactly. An atomic residual of arbitrarily high rank has not been deleted: its root contribution has been proved replaceable for this bounded target. $\square$

**Theorem 3.3 (exact feasible chart spectra).** A chart of Definition 3.1 is attained by a source in its exact cell if and only if none of its substituted negatives has identical sides. For every retained chart its exact attainable root-depth set is $V_{\eta,\theta}$. In particular the interval endpoint in (LRD.9) satisfies $c_{\eta,\theta}\le B_\eta$. This assertion includes every actual high atomic value in $\star$, not just chosen non-atomic representatives.

**Proof.** Identical negative sides are impossible under any filling. If no residual remains, all negatives are concrete unequal trees, so the ground source is legal and gives the singleton in (LRD.9). If residuals remain and all negatives are nontrivial, Theorem 2.2 realizes them simultaneously by non-atomic trees at any independently prescribed ranks. Such trees avoid every $T_0,\ldots,T_{A_\eta}$ and therefore satisfy the entire chart.

For non-atomic residual values, every ancestor containing a residual has atomic flag zero by (LRD.1). Induction gives

$$
\nu(W_{\eta,\theta}[z])
=\min\bigl(\{\nu(z_i):i\text{ a remaining name}\}
             \cup\{\nu(g):g\in G_{\eta,\theta}\}\bigr).
\tag{LRD.10}
$$

Thus all these values lie in $\{0,\ldots,c_{\eta,\theta}\}$. Conversely for any $k$ in that interval prescribe rank $k$ to every remaining name and use Theorem 2.2 on the entire negative list. The result is a legal same-source realization of root depth $k$. Prescribing all ranks greater than $c_{\eta,\theta}$ also realizes the endpoint, whose leaf bound proves $c_{\eta,\theta}\le B_\eta$.

Now take an arbitrary actual filling of the chart. A $\star$ value is either non-atomic or an atomic $T_j$ with $j>A_\eta$. Use Theorem 3.2 to replace every such high atomic value by a non-atomic value of the same rank. The resulting evaluation has the same root depth and is governed by (LRD.10). If replacement broke a negative, apply Theorem 2.2 again, with precisely these residual ranks and the fixed ground substitutions, to restore all negatives simultaneously. The new tuple remains in this chart and preserves (LRD.10). Hence no actual filling contributes a further root value, and every enumerated value has a genuinely legal source. Repeated residuals were never assigned separate values. Finally (LRD.3) turns these legal ground fillings into actual producer/controller realizations of the same $R,h$. $\square$

**Theorem 3.4 (all-attained spectrum dichotomy).** For every attained finite $(R,h)$ the exact spectrum

$$
\Sigma(R,h)=\{\nu(u):u\in D(R,h)\}
$$

has an effective description. If there is no leaf anchor, it is exactly $\mathbb N_0$. If there is an anchor, it is the nonempty finite union

$$
\Sigma(R,h)=\bigcup_{\eta,\theta\ \mathrm{retained}}V_{\eta,\theta}.
\tag{LRD.11}
$$

Each summand is a singleton or an initial interval; the union itself need not be an interval.

**Proof.** With an anchor every kept cell contains a concrete leaf, so Definitions 3.1 and Theorem 3.3 give a finite exact enumeration. Pattern enumeration, literal evaluation, finite atomic expansion, syntactic comparison and finite inverse parsing all terminate on these finite inputs.

Without an anchor the exterior contains only pair constructors and holes, and every history reply is branch. There is at least one old class. Give every class the complete branch pattern of relative depth $d$. Its residual names remain indexed by class and position, so different old-class terms have unequal syntax. Every recorded query has length less than $d$ and gives branch in this leafless whole term. This is a kept leafless cell. Apply Theorem 2.2 to its entire negative list, assigning every residual rank $n$. Every ancestor is non-atomic and its rank is the minimum, so the whole root has rank $n$. These are actual finite sources by (LRD.3) for every $n\ge0$. No larger set of natural-number targets exists, proving the first alternative. Other cells in this boundary may have unqueried concrete leaves; their existence does not remove the leafless cell's witnesses. $\square$

## 4. Native recovery and the minimum further complete code range

**Definition 4.1 (three different recovery requirements).** A fresh common service entry as in Assumption 1.3 receives $(R,h)$ and common installed data. Zero-read identification makes no further source call. Sourcewise finite recovery halts correctly for each $u\in D(R,h)$, with a bound allowed to depend on $u$. Uniform finite-call recovery uses one deterministic effective service with a finite bound $K_{R,h}$ for every source in this same fiber. Bounds may depend on the finite boundary; no constant across all $R,h$ is required. Literal word length, local work, installation and invocation remain separate resources.

**Theorem 4.2 (zero reads, sourcewise termination and uniform service).** Zero-read identification is possible exactly when $\Sigma(R,h)$ is a singleton. Sourcewise finite exact recovery is possible for every attained boundary. In the anchored case uniform finite-call recovery without an additional retained field is possible exactly when

$$
|V_{\eta,\theta}|=1\quad\text{for every retained chart}.
\tag{LRD.12}
$$

There is no uniform finite-call service without an additional field in the no-anchor case.

**Proof.** A zero-read deterministic entry has the same output on the entire complete boundary fiber, proving necessity. If the spectrum is a singleton, the finite classification computes its value without reading the source, proving sufficiency.

For sourcewise recovery use the actual traversal of [SLH, Proposition 53.2][SLH] or `ActualTreeReadoutAcquisition.acquisition_foundation`: query the root, recurse to ordered children on branch, and close the node on a leaf. It terminates on each finite source and reconstructs that actual tree. The supplied finite inverse parser computes $\nu$. This reacquisition is paid anew, even if the producer once queried the same nodes. Its source-dependent call count is not a uniform bound.

For the constructive uniform service first acquire $\eta$ by reading, at each representative $p_b$, every suffix of length less than $d$. Early leaf and absence replies determine its unique pattern. Then for every reached frontier at representative absolute address $a_i$, test the finite templates $T_j$, $0\le j\le A_\eta$. A template's literal leaf-address certificate suffices: matching every template leaf label forces equality with that finite ordered tree by induction on its pair structure. Alternatively query every suffix through the maximum template height and compare complete prefix tables. Both use only actual four-reply calls. They determine the actual $\theta$, with no equality or image oracle. When (LRD.12) holds, return its singleton value.

For necessity consider a proposed uniform service with bound $K$. At a fixed complete boundary its reachable reply tree has at most four successors per read and bounded read depth. It contains finitely many actual query words; terminating local computation introduces no additional source distinctions. Let $L$ bound all their literal lengths. If a chart with a residual has $c\ge1$, realize each of two different values in $\{0,\ldots,c\}$ by Theorem 2.2 with all residual leaves below depth $L$. Their ground pieces are the same and every residual returns branch at every relative address of length at most $L$. The two whole sources agree at all absolute words of length at most $L$, including words through ground leaves that are absent. They are legal actual sources of this same $R,h$ but have different targets. The service therefore executes identically and cannot be correct on both. Ground charts are singletons, so this proves (LRD.12). Without an anchor, a bounded four-branching reply tree has finitely many outputs while Theorem 3.4 supplies all natural-number targets. $\square$

**Definition 4.3 (paid additional code and complete refined handoff).** A separate augmented preparation starts on the same stationary source at the attained base boundary, pays for a full native traversal, and computes an additional complete field $E(u)$. It then makes a fresh complete handoff exposing exactly $(R,h,E(u))$. The acquired tree, preparation transcript, acquisition lengths, temporary workspace, source-dependent control, handles, schedules and every other source-bearing accessible field factor through this tuple; inaccessible material need not be physically erased. None of the first producer's archive is an undeclared input. The original history $h$ remains retained.

Conditional on this fixed $R,h$, the acquired code range is the set of complete values

$$
\mathcal E_{R,h}=\{E(u):u\in D(R,h)\}.
$$

A finite code of size $m$ has $m$ complete distinguishable values. An unbounded finite binary string, including its accessible length, has countably many possible complete values, not two. A code-assisted uniform service receives this complete refined boundary at one common deterministic entry and has one finite call bound on the entire base fiber. Its queries may adapt to its code and prior replies; the lower bound does not prescribe the template consumer.

**Theorem 4.4 (minimum complete additional alphabet, with attained upper bound).** In the anchored case put

$$
m(R,h)=\max_{\eta,\theta\ \mathrm{retained}}|V_{\eta,\theta}|.
\tag{LRD.13}
$$

The least finite cardinality $|\mathcal E_{R,h}|$ enabling some uniform finite-call exact service is precisely $m(R,h)$. It is effectively computable. A one-value field conveys no additional distinction, so Theorem 4.2 is the case $m=1$. Without an anchor no finite range suffices; the minimum attainable cardinality is countably infinite.

**Proof.** For the finite upper construction the augmented producer computes the actual pattern, chart and target from its paid full acquisition. If that chart is ground, set $E(u)=1$. Otherwise set

$$
E(u)=\nu(u)+1.
\tag{LRD.14}
$$

The latter is the one-based position of the target in its initial interval (LRD.9), so $1\le E(u)\le m(R,h)$. If $m>1$, a chart attaining the maximum realizes every value $0,\ldots,m-1$ by Theorem 3.3; hence this code actually has every complete value $1,\ldots,m$. If $m=1$ its range is exactly $\{1\}$. After the refined cut, the service uses the paid finite native menu of Theorem 4.2 to determine its actual chart. It returns the ground target on a ground chart and $E-1$ otherwise. This proves sufficiency with the declared actual producer and port.

For the lower bound allow any acquired encoding into a range of $s<m$ complete values and any code-assisted deterministic service with bound $K$. Across the $s$ entry values and all reachable four-reply histories its query words form a finite set; let $L$ bound their lengths. Choose a chart with $m$ targets. For each target, fix its exact atomic substitutions and apply Theorem 2.2 to all its negatives, with residual ranks attaining that target and every residual leaf below depth $L$. These $m$ sources are jointly legal separately, all lie in the actual base fiber, and have the same whole-source replies through $L$. They do not require independent marginal fillings to be jointly realizable. Two sources receive the same complete encoded value by pigeonhole. Their identical replies and identical code force the same adaptive execution and output, contradicting their different target depths. This proves $s\ge m$ for arbitrary encodings, arbitrarily long finite words and adaptive services, not just for (LRD.14).

Without an anchor, $s$ finite entry values and a depth-$K$ four-reply tree give finitely many terminal outputs, at most $s4^K$. Terminal reply words are prefix-free because stopping is deterministic. They cannot cover the infinite target image. A paid traversal can retain $E(u)=\nu(u)+1\in\mathbb N_{>0}$ and the later service returns $E-1$ without new reads. The complete range is all positive integers by Theorem 3.4. This proves the countable upper bound and excludes every smaller finite cardinality. Its finite binary serialization has unbounded length. $\square$

## 5. Exact next-read refinement and retained-code continuation

**Assumption 5.1 (the common continuation contract).** A declared continuation of the attained base boundary chooses its next query from $R,h$ and common data, obtains its actual reply on the same source, and retains the full event and resulting control in $h'$. Its choice of this retained-history query does not consult the optional code $E$. This preserves the original common-controller contract of Assumption 1.3. If the old controller has halted, this is a newly invoked common entry with its own cost, not an event after an absorbing halt. The extended record retains the old stop and the common invocation marker; $D(R,h')$ then refers to the declared composition of the original controller and this entry, whose replay is still determined by the retained data. A code-assisted service may also use a fixed code-independent menu and append those actual events under this contract. More general source-bearing controllers require their additional fields in the base boundary and are not silently treated as $(R,h)$.

**Theorem 5.2 (simultaneous substitution gives the exact actual next boundary).** For an actual next query $q$ and reply $a$, the shared cells can be effectively refined by one finite operation so that their legal fillings represent exactly $D(R,h')$. Every old equality, whole-class disequality and literal or absence guard remains imposed. Theorems 3.4, 4.2 and 4.4 consequently reclassify the exact new spectrum, uniform-service criterion and minimum extra range.

**Proof.** Follow $q$ in the fixed syntax of each $W_\eta$. A reached constructor root has its fixed reply; a literal leaf has its fixed label at its root and absent reply at every strict extension. Keep or discard that case according to $a$. If the path first enters a residual name $x$ with remaining suffix $w$, enumerate its native patterns to depth $|w|+1$, including all early leaf patterns. Retain precisely those producing $a$ at $w$. For an absent response, these are precisely the patterns with a terminating leaf at a strict prefix of $w$; at $w=\varepsilon$ absence has no pattern. Branch, $\alpha$ and $\beta$ are likewise tested at the actual reached endpoint.

Substitute each retained pattern for $x$ simultaneously in $W_\eta$, every $E_{\eta,b}$ and both sides of every old negative. The replacement is global at every occurrence of this name, including other repeated-class cones. New names are indexed by the old name and new frontier position. Names not on the query path remain, and no off-path negative is removed. Discard cases with syntactically identical negative sides; existing free-term separation decides the remaining pure negative feasibility. If a common normal form is wanted, refine every old class to

$$
d'=\max(d,|q|+1),
$$

using the same simultaneous substitution. This only subdivides the cases and preserves their reconstruction.

An old ground solution with the actual new reply has its unique native decomposition for the queried residual and therefore lies in one kept refinement. Conversely every legal filling of a kept refinement evaluates to an old legal solution with exactly the new reply; all original negatives and guards were transported by substitution. The inverse correspondence follows by extracting the actual old and new frontiers. Existing `NativeSymbolicRecutting.symbolic_recut_exact` and `NativeHistoryCells` supply this source-level refinement mechanism. The common next-step replay of Assumption 5.1 supplies its operational converse, giving

$$
D(R,h')=D(R,h)\cap\{u:r_u(q)=a\}.
\tag{LRD.15}
$$

This equality is accompanied by the explicit finite shared substitution, not used as a substitute for it. The actual source remains, so the new fiber is nonempty. Applying the proved root chart and service construction to these exact new cells gives the stated depth and code consequences. $\square$

**Definition 5.3 (normal-form code invariant and monotone cutoffs).** Use the encoding (LRD.14), with value $1$ initially on a ground chart. After a local continuation allow any in-range code value on a ground chart; on every chart with an unresolved $\star$ require exactly $E=\nu(u)+1$. In the no-anchor case use the complete countable field $E=\nu(u)+1$ on every source.

Use canonical relative depths $d$ that never decrease. Along each actual cell refinement, $W_{\eta'}$ is obtained by replacing old frontier names by finite patterns, so

$$
H_{\eta'}\ge H_\eta,\qquad
A_{\eta'}=4H_{\eta'}+1\ge A_\eta
\tag{LRD.16}
$$

whenever the old boundary is anchored. There is no demand that cutoffs in different unrelated cells coincide. Once an anchor is retained it stays retained. After the local update a complete cut exposes exactly $(R,h',E')$: obsolete code values, old code-buffer lengths, temporary tables, workspace and source-bearing control outside this tuple are inaccessible or factor through it. This is the same accessible-information condition as the preparation cut, without another traversal or a requirement of physical erasure.

**Theorem 5.4 (locally maintained sufficient code with optimal new range).** Under Assumption 5.1 and Definition 5.3, after the actual new response the optimal code can be updated without another full-source preparation or any additional source read. When the new boundary is anchored, compute $m'=m(R,h')$ from its complete retained history and set

$$
E'=\begin{cases}E,&E\le m',\\1,&E>m'.\end{cases}
\tag{LRD.17}
$$

The refined boundary $(R,h',E')$ satisfies the normal-form invariant and has exactly the optimal complete code range $\{1,\ldots,m'\}$ conditional on $R,h'$. If both boundaries are unanchored, retain $E'=E$ and its complete countable range. This covers a countable-to-finite transition. For two anchored boundaries, $m'\le m(R,h)$. These conclusions concern the specified normal-form encoder and monotone cutoffs, not arbitrary optimal encoders or unproved shrinking cutoffs.

**Proof.** First a ground old chart cannot become a new unresolved-star chart. In a ground old chart each old residual equals some $T_j$ with $j\le A_\eta$. Every reached native subtree of $T_j$ is $T_\ell$ with $\ell\le j$: this follows by descent using the atomic recurrence, with its two leaf bases. Refinement either exposes concrete syntax of that tree or puts one of these reached atomic subtrees at a new frontier. By (LRD.16) its index is still within the new exact atomic list. Thus the actual new chart is ground. This also handles zero old variables and early leaves. It is the reason for retaining the specified cell-dependent monotone cutoff.

On a new unresolved-star chart, an anchored old boundary therefore also had an unresolved star. Its retained code is $\nu(u)+1$ by the invariant. The new interval theorem gives

$$
1\le\nu(u)+1\le c_{\eta',\theta'}+1\le m',
$$

so (LRD.17) leaves this necessary code unchanged. If the old boundary was unanchored, the countable code already equals $\nu(u)+1$, and the same argument applies. On a new ground chart the depth is independently known from the chart, and any value in $\{1,\ldots,m'\}$ suffices; (LRD.17) always produces one. Hence the invariant and the bounded native decoding service persist without another acquisition.

If $m'>1$, some new unresolved-star chart attains $m'$ and realizes every root value $0,\ldots,m'-1$ with its actual source. Each such source retains $E'=\nu+1$ by the preceding argument, so the entire range $1,\ldots,m'$ is attained. If $m'=1$, every updated code is $1$. The lower bound of Theorem 4.4 proves optimality of these exact ranges. If the new boundary is unanchored, its target spectrum is still all naturals and the unchanged countable code realizes every positive integer.

For finite monotonicity restrict the old encoder and old bounded service to the new actual subfiber. The old history prefix and old boundary are recoverable from $R,h'$; common installed data records its prefix endpoint. This restriction has no more than $m(R,h)$ complete values and the same old call bound, so the arbitrary-code lower bound at the new boundary gives $m'\le m(R,h)$. The local update itself uses only $E$ and the effectively recomputed $m'$, not an undisclosed actual chart or source tree. Repeated finite continuation follows by induction. The growing original history remains retained and charged; reducing this extra field does not prove that total observer memory decreases. $\square$

## 6. Actual finite examples of joint constraints and changed service

**Theorem 6.1 (marginal root summaries lose the shared realization).** Use $P=\{L,R\}$ and the single-class row $C=\langle X,X\rangle$. A common controller reads $LL$ and then $RR$. The attained replies $\beta,\alpha$ give exactly

$$
D(R,h)=\{\langle T_2,T_2\rangle\},\qquad \Sigma(R,h)=\{2\}.
\tag{LRD.18}
$$

Nevertheless each literal separately permits class summary $Q(X)=(0,0)$. Intersecting these marginal summary sets falsely preserves that summary for the joint history.

**Proof.** The actual source $\langle\langle\beta,\alpha\rangle,\langle\beta,\alpha\rangle\rangle$ produces this same single-class row and the prescribed replies. Both old occurrences share one $X$. Reply $LL=\beta$ makes its left child exactly $\beta$; reply $RR=\alpha$ makes its right child exactly $\alpha$. Therefore $X=T_2$, and (LRD.1) gives root depth two. For the first literal alone take $X=\langle\beta,\langle\alpha,\alpha\rangle\rangle$, of non-atomic depth zero. For the second alone take $X=\langle\alpha,\alpha\rangle$, again of non-atomic depth zero. Each gives an actual finite same-row source by using that same value at both holes. These are separate witnesses to the marginals and not a single witness to both. Shared constructor refinement excludes them jointly, whereas independent summary filtering does not. $\square$

**Theorem 6.2 (one retained actual reply lowers the extra range from two to one).** Use $P=\{R\}$ and $C=\langle\beta,X\rangle$ with one class. For empty history the spectrum is $\{0,1,2\}$ and the minimum extra complete range is two. A common controller first reads $R$ and, on its branch reply, obtains an attained prefix $h_0=((R,\mathsf{br}))$ with spectrum $\{0,1\}$ and minimum extra range still two. It next reads $RR$ once. In its attained $\alpha$ branch,

$$
D(R,h')=\{\langle\beta,\langle s,\alpha\rangle\rangle:s\in\mathcal T\},
\qquad
\Sigma(R,h')=\{0,1\},\qquad m(R,h')=1.
\tag{LRD.19}
$$

The spectra immediately before and after this last event are both $\{0,1\}$. Zero further reads still do not identify the target, but one paid $\mathsf{Read}(RL)$ does. Thus a genuinely acquired history changes later acquisition ability while preserving exactly the same nonsingleton root spectrum.

**Proof.** Before refinement (LRD.1) gives depth two for $X=\alpha$ and otherwise depth $\min(1,\nu(X))$. All three values occur. Non-atomic rank-zero and rank-one class values with arbitrarily deep common branch prefixes exist by Theorem 2.2; therefore no uniform finite-call no-code consumer can separate the latter two targets. A two-value acquired field suffices: the producer retains $\mathbf1_{\{\nu(X)\ge1\}}$, and the consumer reads $R$, returns two for reply $\alpha$, and otherwise returns the retained bit. These are actually attained values of that field and give a correct one-call service. Theorem 4.4's lower bound, or its two-target separator directly, proves that two is minimal. On the attained $R/\mathsf{br}$ prefix $X$ is a pair, so the exceptional $X=\alpha$ is excluded and the spectrum is exactly $\{0,1\}$. The same deep rank-zero and rank-one witnesses are pairs and satisfy this additional guard, preserving the two-value lower bound. The same acquired bit supplies the upper bound, now by returning it directly.

The new response $RR=\alpha$ says precisely $X=\langle s,\alpha\rangle$. Every such source is finite and the same canonical producer outputs the old row. The declared controller actually obtains $R/\mathsf{br}$ followed by $RR/\alpha$ on each such source. The inner pair has depth two when $s=\beta$, and depth zero otherwise; its atomic flag is one only in the former case. Pairing it with the fixed $\beta$ then gives root depth one when $s=\beta$ and zero otherwise. Both occur, for $s=\beta$ and $s=\alpha$. Reading $RL$, the root of $s$, returns $\beta$ precisely when $s$ is that literal leaf; every other reply gives target zero. Hence the extra range is one although the target spectrum remains nonsingleton. The old optimal normal-form field can be updated to this one-value field by (LRD.17). Both the original $R$ event and the new $RR$ event stay in the retained history and are charged. $\square$

## 7. Separate resource coordinates and applicability limits

**Definition 7.1 (sufficient native menus and their literal cost).** Let $k=|B|$, $P_*=\max_b|p_b|$, and $N_*=\max_\eta|X_\eta|$ over kept cells. Empty maxima are zero. In the anchored case put $A_*=\max_\eta A_\eta$ and $H_*=\max_{0\le j\le A_*}\operatorname{height}(T_j)\le A_*$. One sufficient menu first reads all $k$ representative suffixes of length less than $d$, then reads every suffix of length at most $H_*$ at each actual frontier. It has at most

$$
Q_*=k(2^d-1)+N_*(2^{H_*+1}-1)
\tag{LRD.20}
$$

new calls and maximum literal word length at most $P_*+d+H_*$. Its total submitted literal length is at most $Q_*(P_*+d+H_*)$. This bound counts repeated submissions; caching may improve it. There are exactly $2^j$ binary suffixes of length $j$, so an inclusive suffix menu through $K$ has $2^{K+1}-1$ words, and their suffix lengths sum to

$$
\sum_{j=0}^{K}j2^j=(K-1)2^{K+1}+2\qquad(K\ge0).
\tag{LRD.21}
$$

All three coordinates are finite for a fixed boundary. They are sufficient bounds, not a sharp call count or a word-cost optimum. No call is made when $k=0$.

**Definition 7.2 (charged preparation, computation and retained information).** A full root traversal on an actual source $u$ uses $|\operatorname{Pos}(u)|$ calls, maximum literal length $\operatorname{height}(u)$, and total literal length $\sum_{p\in\operatorname{Pos}(u)}|p|$. The canonical first producer and any later augmented preparation each pay their own actual acquisition. Their sourcewise finite costs have no uniform bound on all finite sources. Computing the row and equality partition, parsing $\nu$, enumerating patterns and charts, expanding atomic templates, comparing syntax and maintaining the code are finite local computations charged separately from the read counts. Common installation, continuation invocation, address construction and transmission, temporary workspace and handoff also remain separate.

The boundary stores the full exterior and partition, every literal word and reply in $h$, repetitions and accessible control. Its retained word contribution includes $\sum_{(q,c)\in h}|q|$ and its maximum retained word length; event count and reply storage are separate coordinates. Extra code size is the cardinality of the complete field conditional on this boundary, not the cost of the whole boundary. A fixed-width serialization of a finite range of size $m$ needs $\lceil\log_2m\rceil$ conditional bits; physical storage or an optimal overall memory layout is not asserted. Countable codes use unbounded finite strings. A smaller $E$ after continuation can accompany a longer $h$ and larger finite tables.

**Definition 7.3 (precise non-transfers).** The domain includes every attained finite literal history under Assumptions 1.2–1.3, with no bound on source shape, source rank or query length. It does not include retained positive mixed-epoch subtree equations, newly acquired equality partitions beyond the old row, an interpreted $\rho$ relation oracle, or source-bearing fields outside the complete boundary. Such positive relations can couple the residuals after literal expansion; Theorem 2.2 is then not a license to replace that constrained domain by a Cartesian product. Rational or infinite trees are not source witnesses here.

Exact root depth does not recover physical time, forgotten entrance history, the full source, all future replies, arbitrary action languages or spatial coordinates. The statements separate a mathematical target coordinate, actual finite acquisition history and the information crossing a complete boundary. The finite construction does not assert practical solver performance, a minimum read-call number, a sharp word-length tradeoff or a Pareto optimum over all resource coordinates.

## 8. Exact correspondence, prior coverage and remaining questions

**Definition 8.1 (supplier correspondence and proof status).** Unless a different object is named, repository suppliers below refer to the immutable snapshot `825e04a631a09ecbd5264880115cccd1977f771a`. This volume's claims are ordinary deductions. Lean source statements are exact correspondences used for reuse, not a fresh kernel verification of this manuscript. In that correspondence $\mathcal T$ is `FreeMagma Bool`, $\alpha$ is `.of true`, $\beta$ is `.of false`, pairing is `FreeMagma.mul`, and $L,R$ are address booleans `false,true`. Every literal history event has epoch zero; the new recutting cut used in `historyCellEquiv` is empty.

| Supplier | Exact mathematical use and boundary |
| --- | --- |
| [JM §§36 and 49][JM] | Primitive-ray uniqueness, interpreted inverse parsing, injectivity and (LRD.1). The displayed pairing statement carries its existing ordinary-proof status; it is not newly certified here. |
| [SLH §§53, 59–62 and 74][SLH] | Actual whole-source row producer, full partition, absent-cut guards, exact source/controller replay, native acquisition and finite shared refinement. The new result specializes the static literal case and adds its root-depth/service consequences. |
| [NativeCutFibers][NCF] | `legal_values_row`, `rowFiberEquiv`; private `filled_exterior`, `classValue_distinct`, `recover_fill`, `fill_injective`. Their actual row-filling bijection is (LRD.2), not a free combination of source labels. |
| [NativeDepthPatterns][NDP] | `Pattern`, `Frontier`, `frontierAddress`, `depthEquiv`, `original_prefix_locality`. Reached depth-$d$ frontiers and early leaves are distinguished. |
| [NativeHistoryCells][NHC] | `oldTerm`, `wholeTerm`, `cell_feasibility_exact`, `historyCellEquiv`; private `pattern_evaluate`, `whole_evaluate`, `whole_deep`, `syntax_iff_ground`, `feasible_history`. One variable per old class/frontier and the entire negative list supply (LRD.5). |
| [NativeGroundSeparation][NGS] | Public `simultaneous_ground_separation`; private `count_length`, `evaluated_length`, `compound_mass_ne`, `bounded_eval_injective`. Theorem 2.2 reuses their native leaf-count reflection and adds an explicit prescribed-rank arbitrarily-deep representative tuple. |
| [NativeSymbolicRecutting][NSR] and [NativeGroundSolutionSpace][NGSS] | `symbolic_history_constant`, `symbolic_recut_exact`, `constrainedEquiv`. Full pulled-back constraints and simultaneous occurrence substitution remain imposed. Generic unification and recutting are not new contributions. |
| [ABC §§2–3][ABC], [URR §§1–3 and 7][URR], [NSF][NSF], [NPL][NPL] | Native atomic blocks, mixed-template rank projections and signed feasibility are existing results. URR's unrestricted residual premise is used here only after exact literal expansion; no positive mixed-epoch equality is imported into the free frontiers. Feasibility alone is not uniform recovery. |
| [Native discovery and retained context][NDR] and [intrinsic-depth certificates][IDC] | Paid native full acquisition and exact finite certificates remain suppliers. Sourcewise acquisition alone does not settle (LRD.12) or (LRD.13). |

The immutable published [retained-row candidate][RDR] at `a726b0cd1b89bf4d7615983e83fd5a0225a693d4` supplies ordinary prior bare-row projection, spectrum, native-service and code arguments. Its algebraic correspondence is precisely the same $(\nu,e)$ and the same pairing law; its class variables correspond to unrefined old class values, whereas here the variables are class/frontier names after the literal guards have been expanded. Its bare-row results are prior coverage, not new content credited to this volume. Only its stated ordinary-proof content is attributed; it is not asserted to be a kernel-verified supplier. The proofs above use the displayed JM algebra and provide the necessary joint separation directly.

The published [signed productive-contact source][SPC] at `efcd2d9e7c82b2d6f2172dc27917d753f9b0a992` concerns complete signed acquired input, positive mixed-epoch relations and a prescribed pair of complete recut-row labels. It supplies sufficient finite productive counterfamilies and a non-rational common completion contact, while leaving arbitrary signed stopping open. Its target is a complete recut row rather than root $\nu$. Its completion points are not finite sources, and its positive interpreted equations are not constraints licensed for elimination in (LRD.5). The literal-only common-controller classification here neither settles that signed stopping problem nor depends on its completion construction.

**Definition 8.2 (literature status and the ordinary increment).** Finite free-term negative separation is mature background. [Comon–Lescanne][CL], *Equational Problems and Disunification*, §3.2 Lemma 1 and Appendix B.3, treats nontrivial syntactic disequations with infinite ground sort carriers; the appendix proceeds by finite avoidance of one-variable solutions. Section 6.2 explicitly restricts transfer to nontrivial equational theories. The current signature has two nullary labels and one free ordered binary constructor after exact literal expansion. No rational-tree solution is admitted, and interpreted $\rho$ is never made a free unary symbol. That literature statement supplies neither independently prescribed intrinsic ranks nor the required arbitrary common branch prefix; Theorem 2.2 proves those together with all negatives.

[Roughgarden][RG], *Communication Complexity (for Algorithm Designers)*, Lemma 4.2 and Theorem 4.3, supplies the mature identical-deterministic-transcript/identical-output and finite protocol-tree counting method. Only that method is used in the native lower bound. Its two-party rectangle property is not imported into the nonproduct cell fiber; the actual common-prefix families are supplied by Theorem 2.2.

These passages are `literature-attested` within the stated conditions. The new composition is `repo-derived`: exact retained literals are expanded jointly, prescribed-rank deep witnesses retain all old negatives, observable singleton/interval charts classify the entire actual fiber, and their matching arbitrary-code lower bound and paid consumer support the explicit normal-form code continuation. Bare-row finite projection, primitive rays, $Q$ composition, acquisition, signed feasibility and generic unification are attributed to their existing suppliers. There is no external originality, broad exhaustive-absence or implemented-solver claim.

**Definition 8.3 (open scope).** It remains open here to determine the exact minimum calls at a prescribed complete-code size together with a prescribed literal-word budget, or to normalize every bounded adaptive service to an effectively bounded address support without changing those coordinates. The menu (LRD.20) is only a sufficient construction. Maintaining optimal sufficiency for an arbitrary optimal encoder, or after a cutoff shrinks so that an old ground chart can become unresolved, also remains unproved here; Theorem 5.4 requires its explicit normal form and monotonicity. General signed relational histories and nonstationary or spatial/physical recovery require their own joint realization and operation bridges. These are extensions of the persistent relation/space/time/boundary/memory recovery objective, not a claim that the objective is complete.

[JM]: RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DISCOVERY_AND_RETAINED_CONTEXT.md
[IDC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_INTRINSIC_DEPTH_CERTIFICATES.md
[NCF]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[NDP]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[NHC]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.lean
[NGS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.lean
[NSR]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean
[NGSS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace.lean
[RDR]: https://github.com/the-omega-institute/trureturing/blob/a726b0cd1b89bf4d7615983e83fd5a0225a693d4/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_ROW_DEPTH_RECOVERY.md
[SPC]: https://github.com/the-omega-institute/trureturing/blob/efcd2d9e7c82b2d6f2172dc27917d753f9b0a992/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf
[RG]: https://arxiv.org/pdf/1509.06257v1

## 追加锚（本行以下为增补区）

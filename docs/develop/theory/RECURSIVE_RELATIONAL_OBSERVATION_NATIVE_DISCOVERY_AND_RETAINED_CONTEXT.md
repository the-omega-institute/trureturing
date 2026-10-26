# Recursive Relational Observation: Native Discovery and Retained Context

## 1. Native sources, independent holes and common acquisition

**Definition 1.1 (the original source and observation).** Let $\mathcal T$ be the nonempty finite ordered full binary trees with leaf labels $\alpha,\beta$:

$$
T ::= \alpha\mid\beta\mid\langle T,T\rangle.
$$

An address is a finite word $q\in\{L,R\}^*$; the empty word $\varepsilon$ addresses the root. Every address is a legal request, including addresses not present in the tree. The truthful reply $r_T(q)$ is $\alpha$ or $\beta$ at a leaf, $\mathsf{branch}$ at a branch, and $\mathsf{absent}$ when navigation leaves the tree. Thus a nonempty suffix below a leaf always gives $\mathsf{absent}$. Write $\operatorname{Leaf}(T)$ and $\operatorname{Pos}(T)$ for its actual leaf and node addresses, and $m(T)=|\operatorname{Leaf}(T)|$.

The source is fixed throughout a run. A request neither changes it nor supplies a coordinate, subtree, leaf count, shape, identity tag or event time. These are the native definitions `Source = FreeMagma Bool` in [GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean) and `Address`, `Reply`, `readout`, `leaves`, `nodes` in [ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean); `true` labels $\alpha$ and `false` labels $\beta$.

**Definition 1.2 (independent completion family).** A context $C$ is a finite ordered full binary expression whose leaves are fixed labels or distinguished holes $\square_1,\ldots,\square_k$, with $k\ge1$. Every hole occurs exactly once. Its root-relative addresses $p_1,\ldots,p_k$ are therefore pairwise prefix-incomparable. The entire finite $C$, including those addresses, is known. Set

$$
\begin{aligned}
\mathcal U_C
  &=\{C[U_1,\ldots,U_k]:U_i\in\mathcal T\text{ for every }i\},\\
M_C(C[U_1,\ldots,U_k])
  &=\sum_{i=1}^k m(U_i).
\end{aligned}
\tag{NDR.1}
$$

There are no equality or disequality restrictions between the $U_i$. Independence here means this Cartesian completion domain, without a probability law. The filling map is injective because each $U_i$ can be retrieved at the known occurrence $p_i$. The special context $C=\square_1$ has $k=1$, $\mathcal U_C=\mathcal T$ and $M_C(T)=m(T)$; knowing this context supplies no source-dependent information.

**Assumption 1.3 (one policy and an exact source-total target).** For a fixed $C$, a deterministic acquisition policy receives $C$, common installed parameters, and its own finite chronological history

$$
h=((q_1,y_1),\ldots,(q_j,y_j)).
$$

Its next action is either to request a finite address or to halt with an ordered labelled tree. Every request receives $y=r_T(q)$ from the same $T\in\mathcal U_C$. The same policy and the same source-independent initialization, conditional on $C$, are used on every completion. On every $T\in\mathcal U_C$ it halts after finitely many requests and returns exactly $T$. Denote the class of these policies by $\mathcal A_C$. Arbitrary deep probes, arbitrary query order and repeated requests are allowed. Neither $M_C(T)$ nor the hidden hole values are initial inputs.

A policy is a history selector; source-dependent response timing or service state is not another selector input. An effective policy may keep growing finite working state, provided that state is generated from these inputs. Local computation and storage are separate resources. The lower bound below applies to all such deterministic selectors; the matching policy is effective.

The original `ActualTreeReadoutAcquisition.Policy` and `Strategy` have a Boolean return target, namely membership in the third substitution image. Assumption 1.3 specifies a different, full-tree return target. Only their native reply contract, reconstruction supplies and history pricing are reused; their Boolean correctness hypothesis is not interpreted as full-tree correctness.

**Definition 1.4 (phase costs and determining evidence).** For the finite terminal history of $A\in\mathcal A_C$ on $T$, put

$$
\begin{aligned}
d_A(T)&=|\{q:(q,y)\text{ occurs in that history for some }y\}|,\\
n_A(T)&=\text{the length of that history}.
\end{aligned}
\tag{NDR.2}
$$

Both start at this acquisition entry; $d_A(T)\le n_A(T)$. A repeated raw call increases $n_A$, even when it adds no new phase address. For an empty original history, $d_A$ agrees with the cardinality of `ActualTreeReadoutAcquisition.paid`.

A determining certificate at $T\in\mathcal U_C$ is a finite address set $J$ with truthful replies satisfying

$$
\forall V\in\mathcal U_C,\qquad
\bigl(\forall q\in J,\ r_V(q)=r_T(q)\bigr)\Longrightarrow V=T.
\tag{NDR.3}
$$

Write $\operatorname{cert}_C(T)$ for its minimum cardinality. A certificate is a mathematical benchmark indexed by the actual source. Its addresses, its replies and its cardinality are not supplied to the common acquisition policy. Suprema and infima of nonnegative costs or ratios are taken in $[0,+\infty]$; individual terminal costs are finite by Assumption 1.3.

## 2. Suppliers for evidence, traversal and leaf necessity

**Definition 2.1 (the reused evidence baseline).** The two full-tree clauses of `ActualTreeReadoutAcquisition.source_foundation` supply the following facts on the entire $\mathcal T$: matching every actual labelled leaf reply of a reference tree forces equality with that tree; changing one actual leaf label changes no reply at any other address. These clauses concern all trees, independently of the theorem's additional third-image and Boolean-strategy clauses.

Their exact application to (NDR.3) gives

$$
\operatorname{cert}_C(T)=M_C(T).
\tag{NDR.4}
$$

Indeed the union of the hidden labelled leaf records suffices. Replies at all fixed outside leaves are already determined by $C$, so the supplied full-leaf uniqueness criterion applies to the full tree. Conversely, if $J$ omits a hidden leaf address $a$, flip just that leaf. Its hole value remains a member of $\mathcal T$ and the modified whole source remains in $\mathcal U_C$. The supplied locality clause leaves every reply on $J$ unchanged, while the tree differs. Every one of the $M_C(T)$ hidden leaves is necessary. This is a reuse of leaf-address rigidity, rather than an additional rigidity theorem.

The same locality also forces every successful acquisition run to request every hidden leaf address. If a run halts without requesting $a$, replay the same policy on the flipped source. Induction on the finite chronological history gives the same requests and replies: at each step the histories agree, hence the next action agrees, and the requested address is not $a$. The same terminal tree would then be returned for two different sources. This contradicts Assumption 1.3. This replay uses full-tree correctness in the specified family, not the original Boolean `Strategy.correct` condition.

**Definition 2.2 (the reused attaining traversal).** Start a pending list at the $k$ known hole roots. Query a pending root; at a reported branch insert its ordered children, and at a reported leaf close that pending item. Reconstruct the $U_i$ from these actual reports and fill the retained $C$.

The mechanism is the prefix-translated `acquisitionStep`, `acquisitionTrace` and `restore` of [ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean). Its `acquisition_foundation` supplies the actual root traversal; [Sparse Literal History Transport](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md), Proposition 53.2, already states its full-tree consumer. The exact actual-node fee for the supplied bounded pure observer is `ActualPureAcquisitionCompiler.pure_node_fee`; it is an attainment statement, not an optimum over Assumption 1.3.

For this policy $A_{\rm tr}$,

$$
d_{A_{\rm tr}}(T)=n_{A_{\rm tr}}(T)=2M_C(T)-k.
\tag{NDR.5}
$$

Each finite $U_i$ is completely traversed, with no absent request and no repetition. Its $m(U_i)$ leaves and $m(U_i)-1$ branches give $2m(U_i)-1$ nodes. Different hole cones are disjoint, so summing gives (NDR.5). The full-binary node identity and traversal are also supplied by [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §44.9. They require no beforehand knowledge of $m(U_i)$.

The unknown part in the comparison below is whether another single source-total policy can uniformly discover determining evidence with a smaller multiplier. Equations (NDR.4) and (NDR.5) separately give a certificate and a traversal; neither is that discovery lower bound.

## 3. A finite static-source completion witness

**Theorem 3.1 (native finite-witness alternative).** Fix any context $C$ with $k\ge1$ independent holes, any $A\in\mathcal A_C$, and any integer $B\ge1$. There is a single finite immutable $T\in\mathcal U_C$ satisfying at least one of the following alternatives:

$$
\begin{array}{ll}
\mathrm{I}:&M_C(T)=B+k,\qquad d_A(T)\ge2M_C(T)-k;\\[2mm]
\mathrm{II}:&k\le M_C(T)\le B+k-1,\qquad d_A(T)\ge3M_C(T)-k.
\end{array}
\tag{NDR.6}
$$

The same inequalities hold with $n_A$ in place of $d_A$. In particular, for cold acquisition on all native trees, $k=1$: either $m(T)=B+1$ and $d_A(T)\ge2m(T)-1$, or $1\le m(T)\le B$ and $d_A(T)\ge3m(T)-1$.

**Proof.** Construct replies while following this one policy, maintaining a finite partial completion of $C$. Its unknown terminal positions are called placeholders; they form a changing frontier inside the original holes, rather than the fixed retained-hole list. Initially their addresses are exactly the $p_i$; splitting an original hole replaces its frontier root by descendant placeholders. Every concrete leaf committed during the construction has label $\alpha$. Let $s$ be the number of branch commitments and $z$ the number of leaf commitments. The number of current placeholders is $k+s-z$.

Maintain the following invariant: every earlier reply is correct for every finite filling of all current placeholders, and no previously requested address lies in the cone of a current placeholder. The cone includes its root. Initially there is no history. The placeholder cones are pairwise disjoint. A requested address $q$ has exactly one of these possibilities.

If $q$ is exactly a placeholder root and $s<B$, commit that root to a branch, replace it by two child placeholders, reply $\mathsf{branch}$ and increase $s$ by one. The old cone had no queried address. The new child cones contain neither an earlier query nor the current root query, so the invariant survives.

If $q$ is a strict descendant of a placeholder root $a$, commit $a$ to the leaf $\alpha$, reply $\mathsf{absent}$ and increase $z$ by one. The reply is correct for every remaining filling because the queried nonempty suffix lies below this now fixed leaf. The old cone had no earlier query, so this commitment changes no earlier reply. Record $q$ as the absent witness $w(a)$ for that final leaf.

In the remaining case $q$ is outside all placeholder cones. Its reply is fixed by the partial expression. In particular, an ancestor of a placeholder is an already concrete branch, and a suffix below a concrete leaf is absent. Reply with that fixed value. No placeholder is changed. Repeated requests necessarily fall in this case and reproduce their old replies.

Stop making commitments as soon as $s=B$ or no placeholder remains. In the first case fill every remaining placeholder with $\alpha$; in the second the partial completion already is concrete. Denote the resulting tree by $T$. It is finite, fills every original hole with a nonempty finite tree, and reproduces all replies already given. Thereafter answer only from this fixed $T$. Source-totality of $A$ makes the rest of its run finite and correct.

It remains to show that this stopping condition is reached. A finite halt before it is reached would leave a placeholder. Fill all placeholders with $\alpha$ for one source and change the label at one such root to $\beta$ for a second source. The invariant says that both completions give the whole terminal history. Determinism makes the terminal output the same on both, contradicting exactness.

An infinite run without reaching the stopping condition has at most $B-1$ branch commitments. It also has at most $k+B-1$ leaf commitments: $z\le k+s$. Thus only finitely many changes of the partial expression occur. After the last change, fill any remaining placeholders with $\alpha$ to obtain a finite tree $T_0$. The invariant verifies every previous reply on $T_0$. Every subsequent reply also agrees with $T_0$: a request in a remaining placeholder cone would cause a further commitment, contrary to the choice of the last change. The same selector on $T_0$ therefore has this entire infinite request stream, contradicting its pointwise finite termination. No uniform termination bound is used.

Now count distinct addresses in the terminal run on the resulting $T$. The forest occupying the original $k$ holes has $s$ branch nodes and $M=s+k$ leaves, whether or not some leaves were filled only at the stopping condition. Each of those $s$ branches was committed by a query at its root. These are $s$ different actual branch addresses. Definition 2.1 forces all $M$ actual hidden leaf addresses to be requested as well, and these cannot coincide with branch addresses.

If $s=B$, this gives $M=B+k$ and

$$
d_A(T)\ge s+M=2M-k,
$$

which is Alternative I.

If the placeholders disappeared with $s<B$, every final hidden leaf was committed by a strict-descendant absent query, rather than by the final filling rule. There are $M=s+k$ such witnesses $w(a)$. They are distinct because final leaf cones are pairwise disjoint. They are absent addresses of $T$, so none is any actual leaf or branch address. Consequently the three sets of counted requests are disjoint and

$$
d_A(T)\ge s+M+M=3M-k,
\qquad k\le M=s+k\le B+k-1.
$$

This is Alternative II, including the possibility $s=0$. Finally $n_A(T)\ge d_A(T)$ gives its version of both alternatives. The completed tree realizes the replies from the start of the run. The construction selects an input witness; it does not give an acquisition policy permission to mutate a live source. $\square$

The classical distinction between a certificate and a common adaptive query procedure is `literature-attested` background from Harry Buhrman and Ronald de Wolf, *Complexity measures and decision tree complexity: a survey*, Theoretical Computer Science 288 (2002), 21–43, [DOI](https://doi.org/10.1016/S0304-3975(01)00144-X), [author manuscript](https://homepages.cwi.nl/~rdewolf/publ/qc/dectree.pdf), §3.1 and §4.2, manuscript pp. 5 and 9. There the source is a fixed finite Boolean coordinate cube. Its certificate/sensitive-block relation does not supply the arbitrary-address invariant, static finite completion or source-total termination argument above. Theorem 3.1 is a `repo-derived` ordinary deduction on the native source family, with those mature query methods credited; Theorem 4.1 is its matching ratio consequence. This attribution makes no claim of external originality.

## 4. The sharp strict uniform discovery ratio

**Theorem 4.1 (strict multiplicative factor two).** For every fixed finite independent-hole context $C$ with $k\ge1$,

$$
\inf_{A\in\mathcal A_C}\ \sup_{T\in\mathcal U_C}
       \frac{d_A(T)}{\operatorname{cert}_C(T)}
=
\inf_{A\in\mathcal A_C}\ \sup_{T\in\mathcal U_C}
       \frac{n_A(T)}{\operatorname{cert}_C(T)}
=2.
\tag{NDR.7}
$$

These equalities also hold when the infima are restricted to effective policies. In particular they hold on the unchanged all-tree family $\mathcal T$ with a source-independent empty initial history. Equivalently, for every deterministic exact source-total $A$ and every real $c<2$, some finite completion satisfies $d_A(T)>cM_C(T)$ and therefore $n_A(T)>cM_C(T)$.

**Proof.** The reused certificate equality (NDR.4) identifies the denominators as $M=M_C(T)\ge k>0$. For any $c<2$, choose $B\ge1$ large enough that

$$
2-\frac{k}{B+k}>c.
$$

Apply Theorem 3.1. In Alternative I,

$$
\frac{d_A(T)}M\ge2-\frac{k}{B+k}>c.
$$

In Alternative II, $M\ge k$ and hence

$$
\frac{d_A(T)}M\ge3-\frac{k}M\ge2>c.
$$

Thus every eligible policy has supremum at least two, for distinct requests and actual calls alike. This includes each effective policy.

For the matching upper bound, the common effective traversal of Definition 2.2 gives

$$
\frac{d_{A_{\rm tr}}(T)}M
=\frac{n_{A_{\rm tr}}(T)}M
=2-\frac{k}M<2.
$$

Completions with arbitrarily many leaves exist: enlarge one hole to a finite comb of increasing leaf count and fill the other holes with $\alpha$. Their $M$ is unbounded, so the traversal's supremum is exactly two. It belongs to both policy classes in the statement. This proves all equalities. $\square$

The benchmark comparison is strictly multiplicative: (NDR.7) concerns $d/M$ and $n/M$ with no additive allowance. Daniel D. Sleator and Robert E. Tarjan, *Amortized Efficiency of List Update and Paging Rules*, Communications of the ACM 28 (1985), 202–208, [DOI](https://doi.org/10.1145/2786.2793), [author PDF](https://www.cs.cmu.edu/~sleator/papers/amortized-efficiency.pdf), pp. 202 and 205, supplies the `literature-attested` mature comparison between common online behavior and an informed benchmark. Its request-sequence, list and paging models, amortization and constants are not instantiated here. In particular, (NDR.7) does not assert a lower bound excluding $d_A(T)\le cM_C(T)+b$ for a fixed additive $b$. The early-closing alternative of Theorem 3.1 need not give witnesses of arbitrarily large size.

**Theorem 4.2 (the pointwise traversal lower bound is false).** There exists a common effective exact policy on all $\mathcal T$ that reconstructs every two-leaf source with exactly two calls and two distinct requests. Hence the stronger assertion

$$
\forall A\in\mathcal A_{\square_1}\ \forall T\in\mathcal T,
\qquad d_A(T)\ge2m(T)-1
\tag{NDR.8}
$$

is false, even for a policy whose strict uniform ratio is two.

**Proof.** First request $L$. If it is a labelled leaf, request $R$. If both are labelled leaves, return the pair of those labels. Such replies force a branch at the root and leaves at both children, so the returned tree is the source. In every other case use the supplied root traversal, retaining these initial reports and substituting a cached truthful reply when its address becomes pending. This skips a source call at a previously queried address, but otherwise follows the same finite reconstruction. It halts correctly on every finite tree.

On each two-leaf source the first two replies are labels and the cost is two, below $2m-1=3$. On a one-leaf source the first $L$ reply is absent, and the fallback queries the root: the cost is two. On any other branch-rooted source, every preliminary address queried is an actual node; the fallback with cache reuse results in exactly one call at each actual node. Its cost is $2m-1$. Thus both ratios have supremum two. This is a counterexample to (NDR.8), not an exact size-dependent optimum for every leaf count. $\square$

## 5. An actually acquired context and paid reacquisition

**Assumption 5.1 (complete access cut after actual acquisition).** Fix a common finite prefix-free public cut menu $P\subseteq\{L,R\}^*$. On an arbitrary unknown $T\in\mathcal T$, the producer performs the actual full root traversal of Definition 2.2 with $C=\square_1$. It reconstructs $T$ solely from its truthful replies. Let

$$
I_P(T)=P\cap\operatorname{Pos}(T)=\{p_1,\ldots,p_k\},
$$

listed in address order, and let $C_P(T)$ replace the subtree at each $p_i$ by the once-occurring hole $\square_i$. It retains all outside brackets and labels. Unused menu addresses are guarded by fixed outside leaves: for each $p\in P\setminus I_P(T)$, a strict prefix of $p$ is a concrete leaf of $C_P(T)$.

This is the actual producer of [Sparse Literal History Transport](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md), Definitions 59.1–59.2. That producer computes $(C_P(T),\pi_P(T))$, where $\pi_P(T)$ is the complete equality partition of hole values. Here apply its projection to $C_P(T)$: deliberately retain neither any hole value nor that partition.

The new entry has only an accessible finite decodable encoding of $C=C_P(T)$, common code and $P$, a common initial epoch zero and entry position, and source-independent empty new work and query history. All other accessible source-dependent information must factor through $C$. Old full trees, subtree copies, raw caches, output, archives, comparison tables, counters, timings, allocation lengths, pointers and control locations are inaccessible unless they are functions of this retained $C$. Source authentication preserves the same immutable register and original root; it supplies no distinguishing source identity. The source remains this same $T$ from the producer's first request through completion of reacquisition, including the interval between phases. No substitution, reset, copy, move of the root or hidden service field is allowed.

This is the complete access condition of SLH Assumption 59.3 applied to the projected row, not a deletion operation added to the original observer. The permission boundary and the new common entry are explicit supplied resources, with their implementation and charges separate. If the producer has reached an absorbing halt, the entry is a distinct authorized task invocation, not a transition out of that halt. The cut is a mathematical information/access contract, not a physical erasure assertion.

For every admissible reached $C$, the exact remaining source fiber is

$$
\{T:C_P(T)=C\}=\mathcal U_C.
\tag{NDR.9}
$$

This follows by forgetting the partition in SLH Theorem 59.4. More explicitly, a filling $C[U_1,\ldots,U_k]$ preserves every hole root and every unused-menu leaf guard. Its re-extracted context is $C$, regardless of which $U_i$ happen to be equal. Conversely, every source producing $C$ fills exactly those holes. The union over all actual equality partitions removes both equality and disequality restrictions. Since all accessible fields factor through $C$, neither a source's distinct old run length nor its old acquired history further filters (NDR.9).

**Theorem 5.2 (retained-context phase ratio and lifetime distinction).** Under Assumption 5.1, fix a reached context $C$ with $k\ge1$ holes. Compare common deterministic exact policies from that same new entry on all sources in its complete fiber. Their strict optimal phase ratios for distinct addresses and actual calls, relative to the minimum new determining evidence, are both two. The evidence benchmark is $M=\sum_i m(U_i)$; the common hole traversal uses exactly $2M-k$ phase addresses and calls.

Let $m_{\rm out}(C)$ be the number of concrete labelled leaves retained outside the holes. For this specified producer followed by this specified reacquisition traversal,

$$
\begin{aligned}
n_0(T)&=d_0(T)=2\bigl(m_{\rm out}(C)+M\bigr)-1,\\
n_1(T)&=d_1(T)=2M-k,\\
n_{\rm lifetime}(T)&=n_0(T)+n_1(T),\\
|Q_0\cup Q_1|-|Q_0|&=0.
\end{aligned}
\tag{NDR.10}
$$

Here $Q_j$ is the set of addresses actually requested in phase $j$. The lifetime-distinct expression is not the phase price $d_1$.

**Proof.** This is the `repo-derived` retained-context application of the native discovery bound. The actual producer and complete cut give the full independent completion domain (NDR.9) and exactly the common initial information in Assumption 1.3. Thus the certificate application in Definition 2.1 and Theorems 3.1 and 4.1 apply to the new task entry. Their phase lower bounds hold against arbitrary deep requests and repeats, not just against the traversal. The retained $C$ is not treated as a hidden shape oracle for any $U_i$.

The producer reads every original node once; the hidden subtrees and fixed outside leaves give $m(T)=m_{\rm out}(C)+M$. The hole traversal reads only original actual nodes in the union of the $k$ hole cones, each once. The supplied counts yield the first two lines of (NDR.10). Every phase-one call is a genuinely new call after entry, so calls add. But $Q_0=\operatorname{Pos}(T)$ and $Q_1\subseteq\operatorname{Pos}(T)$, so there are zero new lifetime-distinct addresses in this continuation. The phase-one lower bound on $d_1$ cannot become a positive lower bound on $|Q_1\setminus Q_0|$.

The last equality is for the specified traversal. Another policy may probe absent addresses not present in $Q_0$; the theorem makes no equality assertion for its lifetime-distinct count. If $k=0$, the retained context already is the whole tree and a full-tree value task needs no new source calls; the positive-denominator ratios of Theorem 4.1 are then inapplicable. $\square$

**Definition 5.3 (other resource coordinates).** Phase address transmission is

$$
\ell_A(T)=\sum_{j=1}^{n_A(T)}|q_j|.
$$

It counts repeated transmissions if raw calls transmit literal addresses. For the hole traversal this is $\sum_i\sum_{q\in\operatorname{Pos}(U_i)}(|p_i|+|q|)$. Encoding each four-valued reply by two bits gives reply payload $2n_A(T)$, without specifying framing. Retained context bytes, temporary evidence, complete tree or parser-code storage, installed parameters, internal computation, output, entry, isolation and source-service charges are separate coordinates. A lifetime-first-address tariff would charge the last line of (NDR.10), whereas a raw-call tariff charges $n_1$ and a phase-distinct-address tariff charges $d_1$. They describe different contracts.

SLH Proposition 53.2 supplies this address/reply separation. Process Geometry §44.9 supplies the possibility of quadratic literal-address sums on combs and distinguishes node work from the actual `restore` history scans and `finiteDecision` candidate enumeration. Neither source-call count nor the factor in (NDR.7) is an executable runtime, physical memory, energy or total-price bound.

## 6. Full recovery consumers and the chronology boundary

**Definition 6.1 (an injective geometry target).** For $T\in\mathcal T$, let $w(T)$ be its complete ordered leaf-label word and define the complete inorder ancestor-coordinate list by the existing recursion

$$
\begin{aligned}
g(\alpha)&=g(\beta)=(),\\
g(\langle U,V\rangle)&=g(U)\mathbin{+\!+}[m(U)m(V)]\mathbin{+\!+}g(V),\\
\tau(T)&=(w(T),g(T)).
\end{aligned}
\tag{NDR.11}
$$

These are `wd` and `AncestorAreaInterval.coordinates`. [NativeAncestorUniqueness](../../../D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness.lean), `native_ancestor_uniqueness`, supplies injectivity of this full pair on all native labelled trees. This is a downstream supplier, not another native uniqueness claim.

The conversion from a recovered tree to $\tau$ is internal finite recursion. Conversely, for a tuple in the actual image, its finite word fixes the number and ordered labels of leaves. Enumerate the finitely many full binary bracketings of that word, compute each coordinate list, and compare with the supplied list. The actual source is among them and the supplier's injectivity makes the match unique. This gives a finite inverse on the actual image, without any additional source requests or any time bound for the computation. An empty word or a tuple with no matching bracketing can be assigned a fixed default tree; this makes the conversion total without changing it on any correct terminal output.

Consequently Theorem 4.1 prices exact acquisition of this target as well: compose a full-tree policy with its forward map for one inequality, and an exact $\tau$ policy with this inverse for the other. Both compositions preserve the actual request histories and both phase costs. Determining evidence for $\tau$ is likewise exactly determining evidence for the tree. No unknown-source coordinate port is supplied by this conversion.

A recovered tree also gives $r_T(q)$ for every later supplied finite address $q$. Retaining an accessible tree description or the lossless `AtomicPrefixParser.code` suffices for these later value requests with zero further source calls. Its exact decoding and injectivity are supplied by [AtomicPrefixParser](../../../D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.lean), `result`; storage, decoding, computation and output remain charged separately. The determining leaf records of Definition 2.1 are another sufficient retained representation, not a new coordinate-acquisition obligation.

**Definition 6.2 (intrinsic depth and subtree boundaries as consumers).** From the recovered source, the complete addressed-subtree intervals are supplied by [AncestorAreaInterval](../../../D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.lean), `ancestor_area_interval`. In its notation, for $1\le a\le b\le m(T)$,

$$
\operatorname{area}_T(a,b)=\binom{b-a+1}{2}
\quad\Longleftrightarrow\quad
[a,b]\text{ is the complete leaf interval of an actual subtree occurrence}.
$$

Here the area is evaluated from the acquired coordinate list, and the occurrence includes its ambient address. This gives the existing relational boundary consumer of the paid acquisition; it is not a total-area identity or an extra oracle.

For the substitution $\rho$ with $\rho(\alpha)=\beta$, $\rho(\beta)=\langle\beta,\alpha\rangle$ and preservation of ordered pairing, the existing inverse-image parsing and primitive-ray decomposition define

$$
\nu(T)=\max\{n\ge0:T\in\rho^n[\mathcal T]\}.
$$

Their finite computation from the complete tree is supplied by [Joint Moment Fibers](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md), §§36.2–36.3 and the evidence consumers of Theorem 57.2. Thus exact retained tree memory supplies this intrinsic inverse-generation depth without new raw reads. This is not the depth of a queried address, elapsed source-query duration, physical age or the unknown true entry history.

The same current tree $\beta$ can have actual entry $\beta$ with zero substitutions or entry $\alpha$ with one substitution. Both histories produce the identical current four-reply function and the identical $\tau(\beta)$ and $\nu(\beta)=1$. Deterministic queries to that unchanged current source therefore cannot tell which entry occurred. This is the existing entry ambiguity of JM §37.3, and it survives complete acquisition. An authenticated entry record or actual event archive is another supplied input.

Likewise, the tree $\langle\alpha,\beta\rangle$ admits the read orders $(\varepsilon,L,R)$ and $(L,R,\varepsilon)$, and arbitrary repeated requests, all with the same semantic source and final full description. That description alone cannot recover which past order occurred. If a particular deterministic acquisition program and its entire initial inputs are supplied, its abstract trace can be replayed from the tree, but replay does not recover actual timestamps, durations or unrecorded executions. The cut of Assumption 5.1 specifically prevents old chronology from becoming an unlisted input.

## 7. Changed fibers and limits of the ratio

**Theorem 7.1 (known shape and retained equality change the benchmark).** The independent-hole ratio in Theorem 4.1 cannot be transported unchanged to either of the following information contracts.

First, if the exact shape of every $U_i$ is supplied and only its leaf labels remain unknown, exact reconstruction uses $M$ label requests. Second, for $C=\langle\square_1,\square_2\rangle$, if the retained partition supplies $U_1=U_2$, reconstruction uses $2m(U_1)-1$ calls by traversing just one occurrence and filling both holes, although the independent-completion denominator would be $M=2m(U_1)$.

**Proof.** In the first contract, the leaf-address set is already known. Read those addresses once and insert their labels into the supplied shapes. Leaf flips are still legal in this changed family, so $M$ is its exact label-evidence price; discovery of the shape has been separately supplied. In the second contract, the actual equality relation makes the one acquired value sufficient for both occurrences. The supplied traversal gives $2m(U_1)-1$ calls and disjoint-occurrence leaf flips are no longer legal counterexamples in the equality fiber. Hence (NDR.4) with $M=2m(U_1)$ is not that fiber's certificate benchmark. These contracts fail precisely the independent completion or initial-information hypotheses. $\square$

**Theorem 7.2 (a leaf word is not a full recovery target).** The sources

$$
S=\langle\langle\alpha,\beta\rangle,\alpha\rangle,
\qquad
T=\langle\alpha,\langle\beta,\alpha\rangle\rangle
$$

have the same complete leaf word $\alpha\beta\alpha$, but different shapes and different original reply functions. Therefore retaining only that word neither supplies the exact full-tree description nor preserves the independent labelled-leaf-flip domain used in Theorem 3.1.

**Proof.** Their words agree by the ordered leaf recursion. At address $L$, $r_S(L)=\mathsf{branch}$ and $r_T(L)=\alpha$. Thus neither the tree nor the response function factors through the word. Flipping a leaf changes the complete word, so the necessity argument of Definition 2.1 does not remain inside a fixed-word fiber. This does not compute the discovery optimum on that different fiber. JM §55 and its later fixed-word theorems retain their own source promises and targets. $\square$

**Assumption 7.3 (scope of the deterministic comparison).** The benchmark remains the original immutable all-tree source, or a reached context with all independent hole completions, and the target is full reconstruction or the explicitly invertible target in Definition 6.1. A shape-only, membership-only or finite specified response task has a different determining relation. In particular SLH §69 optimizes a finite prescribed future response row under its retained-partition and history contract; it does not supply a whole unknown-tree discovery optimum relative to (NDR.4).

The quantifier in Theorem 3.1 is $\forall A\,\forall B\,\exists T$. It is not a fixed-size minimax formula or a pointwise lower bound. Applying it after fixing a random tape would let the bad source depend on that tape; this does not prove a fixed-source expected-cost or bounded-error randomized lower bound. No source-independent full-recovery call bound follows, since the compulsory leaf count is unbounded. The separate word-only, randomized, additive-constant and complete digital-storage optimizations are not determined by (NDR.7).

The recovery arrows established here connect the actually acquired labelled native tree, its complete relational geometry, its addressed subtree boundaries and its retained finite description under the stated access contract. Intrinsic inverse-generation depth is a supplied consequence of that description. The example in Definition 6.2 blocks an inverse from current geometry to arbitrary actual chronology. Mutual recovery including physical time, actual entry history, physical boundaries and physical memory requires additional represented relations and certified source/operation contracts.

## 追加锚（本行以下为增补区）

## 8. Randomized full reconstruction with only terminal measurability

**Definition 8.1 (the selected randomized contract).** Fix exactly the context $C$, independent completion family $\mathcal U_C$, original-root reply interface and full labelled-tree target of Definitions 1.1–1.2 and Assumption 1.3. In particular $k\ge1$, $M=M_C(T)$ is not supplied, and every finite address remains legal, including deep, absent, repeated and outside-hole requests. The immutable source is fixed before and throughout execution.

Choose one tariff $\gamma\in\{d,n\}$. A randomized policy $A$ has a probability space $(\Omega,\mathcal F,\mathbb P)$ and a history selector $A_\omega$ for each seed. Conditional on the known $C$, the seed law and all other initial inputs are source independent. The same seed and finite chronological history give the same next request or returned full tree on every source. For each fixed $T\in\mathcal U_C$ separately, require that

$$
\begin{aligned}
W_T&=\{\omega:A_\omega\text{ returns a finite tree different from }T\},\\
D_T&=\{\omega:A_\omega\text{ has no finite terminal return on }T\}
\end{aligned}
\tag{NDR.12}
$$

are measurable null sets. A finite return, including a wrong return, pays the selected terminal history cost of Definition 1.4. Nontermination pays $+\infty$. Require only that this chosen extended tariff

$$
\omega\longmapsto\gamma_A(T,\omega)\in[0,+\infty]
\tag{NDR.13}
$$

is measurable for each fixed $T$. Write $\mathcal R_C^\gamma$ for this class. Its effective subclass consists of policies implemented by a common effective randomized procedure satisfying the same contract. The upper bound below uses no randomness.

The $d$ and $n$ contracts are separate. Membership in $\mathcal R_C^d$ does not assume measurable raw-call count; membership in $\mathcal R_C^n$ does not assume measurable distinct-address count. Neither contract assumes measurable intermediate seed histories, a complete seed probability space, a source-size cap, a source distribution supplied at runtime, or access to a source-dependent identifier. This is the per-source null-exception form of `ActualTreeReadoutAcquisition.RandomContract`, with the explicitly different full-tree target and, for $n$, the explicitly different tariff. Its Boolean `Strategy` is unchanged.

**Lemma 8.2 (a common measurable exactness set).** Every $A\in\mathcal R_C^\gamma$ has a measurable set $G\subseteq\Omega$ of probability one on which $A_\omega$ is a deterministic, finitely terminating, correct full-tree policy on every $T\in\mathcal U_C$ simultaneously.

**Proof.** Finite labelled binary trees form a countable set, for example by their finite constructor descriptions. The finite product of the $k$ hole-value sets, and hence its image $\mathcal U_C$, is countable. Therefore

$$
G=\Omega\setminus\bigcup_{T\in\mathcal U_C}(W_T\cup D_T)
\tag{NDR.14}
$$

is measurable and has probability one. At every seed in $G$, every source has a finite correct return. Fixing that seed leaves the same history selector and source-independent initialization on the whole family. No event concerning an intermediate seed transcript was used. $\square$

This lemma supplies a common good set; it does not by itself permit choosing a different bad tree for each seed. The source-law argument below keeps the final bad input outside the seed expectation.

## 9. A subcritical finite-source law and the charge for indirect discovery

**Definition 9.1 (an analyst's law on the original sources).** Fix $0<p<1/2$. Independently in each of the $k$ hidden holes, use the ordered $0/2$ offspring law: a present node is a branch with probability $p$ and otherwise a leaf; conditional on being a leaf, its label is independently fair between $\alpha$ and $\beta$. The two children of a branch have independent copies of this law. The fixed context is not randomized. Denote the resulting law on $\mathcal U_C$ by $\mu_{C,p}$.

One mathematical realization assigns independent variables $X_{i,q}$ to every potential slot $(i,q)$, where $1\le i\le k$ and $q\in\{L,R\}^*$. Each variable has probabilities

$$
\Pr(X_{i,q}=\mathsf{branch})=p,
\qquad
\Pr(X_{i,q}=\alpha)=\Pr(X_{i,q}=\beta)=\frac{1-p}{2}.
\tag{NDR.15}
$$

The slot is an actual node precisely when all its strict ancestors in that hole are branches. Descendants of a leaf are not part of the source, irrespective of their latent variables. This realization defines a distribution on already fixed sources. No latent variable, offspring sampler, label port or provisional source is given to the observer, and no source changes in response to a request.

**Lemma 9.2 (finite support points, full support and first moments).** The law in Definition 9.1 is concentrated on finite sources and gives positive probability to every member of $\mathcal U_C$. Put

$$
V(T)=\sum_{i=1}^k|\operatorname{Pos}(U_i)|=2M_C(T)-k.
$$

Then

$$
\begin{aligned}
\mathbb E_{\mu_{C,p}}V&=\frac{k}{1-2p},\\
\mathbb E_{\mu_{C,p}}M_C&=\frac{k(1-p)}{1-2p},\\
\mu_{C,p}(\{T\})&=p^{M_C(T)-k}\left(\frac{1-p}{2}\right)^{M_C(T)}.
\end{aligned}
\tag{NDR.16}
$$

The support consists of countably many finite trees; it is not a finite set.

**Proof.** At relative depth $j$, each of the $k2^j$ potential slots is present with probability $p^j$. The expected number $Z_j$ of actual nodes there is $k(2p)^j$. If the forest is infinite, it has a node at every depth, because every bounded-depth binary forest is finite. Hence

$$
\Pr(\text{forest infinite})\le\Pr(Z_j\ge1)\le k(2p)^j
$$

for every $j$, and this tends to zero. Nonnegative summation gives

$$
\mathbb E V=\sum_{j\ge0}k(2p)^j=\frac{k}{1-2p}.
$$

A finite full binary forest with $k$ roots and $M$ leaves has $M-k$ branches and $V=2M-k$ nodes. Thus $M=(V+k)/2$, proving its displayed mean. For a particular labelled forest, independence requires exactly its $M-k$ actual branch variables and its $M$ actual labelled-leaf variables. All latent variables below leaves are unrestricted. Multiplying their probabilities gives the last line of (NDR.16), which is positive. The filling map into the fixed context is injective, so no multiplicity factor is needed. $\square$

**Lemma 9.3 (arbitrary-address source-law charge).** Let $a$ be any deterministic history policy that halts correctly on every member of $\mathcal U_C$, from the initialization of Assumption 1.3. Its requests may have arbitrary depths, repetitions, absences and positions outside the holes. For $\gamma=d$ and for $\gamma=n$,

$$
\mathbb E_{T\sim\mu_{C,p}}\gamma_a(T)\ge\mathbb E_{T\sim\mu_{C,p}}V(T)
=\frac{k}{1-2p}.
\tag{NDR.17}
$$

**Proof.** All random quantities in this proof depend on the source, with the deterministic selector fixed. Since the source set is countable, no seed-transcript measurability is involved.

Use the latent realization of Definition 9.1 only to analyze the actual run. In addition to the observer's genuine history, keep an analyst's revealed set, initially empty in every hole. To evaluate a query in a hidden cone, follow its path from that hole root. Inspect a slot variable only if it has not previously been inspected, and stop at the query endpoint or at the first leaf before it. Replies outside the hidden cones are determined by $C$ and require no such inspection. Previously inspected variables are reused. The observer receives exactly its one original four-valued reply, not this auxiliary revealed path or its labels. Thus this analysis leaves both its policy and its request history unchanged.

Call a first inspection *strict* if its actual node address is a proper prefix of the current requested address. A first inspection at the requested address is not strict. Let $B_s$ and $L_s$ be the numbers of strictly first-inspected branches and leaves during the run, and let $S=B_s+L_s$.

Before a new slot is inspected, whether it is strict and which as-yet uninspected slot is next are determined by the past revealed variables, $C$ and the policy. The next query is determined by its earlier genuine replies, all of which are functions of those revealed variables. Navigation to a new slot uses only previously inspected ancestors. It therefore does not inspect the new variable in order to choose that variable or decide strictness. Independence in (NDR.15) consequently gives

$$
\mathbb E B_s=p\,\mathbb E S,
\qquad
\mathbb E L_s=(1-p)\,\mathbb E S,
\qquad
\mathbb E B_s=\frac{p}{1-p}\mathbb E L_s.
\tag{NDR.18}
$$

Here is a non-stopping-time way to justify the sums. List first inspections in their order, padding with no inspection after termination. For each index, condition on a preceding finite revealed record. If another inspection occurs, its selected coordinate has not appeared in that record and has the original independent law (NDR.15); the strictness decision precedes its value. Sum the branch and leaf conditional probabilities over the countably many such records and then over inspection indices. Nonnegative summation proves the first two identities. Each inspected actual node is inspected only once, so $S\le V$; Lemma 9.2 makes every expectation in (NDR.18) finite. This argument charges a chain of previously unqueried ancestors one node at a time; it does not replace an arbitrarily deep request by a paid sequence of prefix requests.

Next compare these inspections with the policy's actual distinct requests. Definition 2.1 forces the policy to request every hidden labelled leaf. Indeed, omitting such a leaf would give the same terminal history and output on its legal label-flipped competitor, contradicting full-tree correctness. Consequently every hidden actual node is eventually inspected by the analyst: every such node is on a path to some leaf that is requested.

Let $H$ be the number of actual hidden branches whose own addresses are never requested. Every one of these branches is first inspected strictly along a request for a descendant, so $H\le B_s$. Let $R$ count distinct requested addresses with absent replies, and let $O$ count distinct requested actual nodes outside all hidden cones. Every strict first inspection of a leaf ends a query with an absent reply. Two such first inspections cannot be assigned the same requested address: its first evaluation has already inspected its entire traversed path and the blocking leaf, and a repeat inspects no new slot. Hence $L_s\le R$.

All hidden leaves are requested, and the only missed hidden actual nodes are the $H$ branches. Partitioning distinct requests into hidden actual nodes, absent addresses and outside actual nodes therefore gives

$$
\begin{aligned}
d_a&=V-H+R+O,\\
d_a+B_s&\ge V+L_s.
\end{aligned}
\tag{NDR.19}
$$

If $\mathbb E d_a=+\infty$, the desired bound is immediate. Otherwise take expectations in (NDR.19), use the finite identities (NDR.18), and rearrange:

$$
\mathbb E d_a
\ge\mathbb E V+\frac{1-2p}{1-p}\mathbb E L_s
\ge\mathbb E V.
\tag{NDR.20}
$$

All terms being subtracted are finite. This proves the distinct-address case without restricting query order or depth. Pointwise $n_a\ge d_a$ proves the raw-call case, with no seed integration in either argument. $\square$

The absent replies are essential to this charge. A deep request can avoid querying several branch roots, and Theorem 4.2 already refutes a pointwise traversal lower bound. Formula (NDR.18) balances these possible savings against strict first inspections of leaves under one common source law; it asserts no pointwise inequality $d_a(T)\ge V(T)$.

## 10. Exact Bayes value, fixed-source additive obstruction and factor two

**Theorem 10.1 (exact analyst-law value for each selected tariff).** Fix $C$, $0<p<1/2$ and $\gamma\in\{d,n\}$. Every $A\in\mathcal R_C^\gamma$ satisfies

$$
\sum_{T\in\mathcal U_C}\mu_{C,p}(\{T\})
      \mathbb E_{\omega}\gamma_A(T,\omega)
\ge\frac{k}{1-2p}.
\tag{NDR.21}
$$

The traversal of Definition 2.2 attains equality, with the pathwise identity

$$
\gamma_{A_{\rm tr}}(T)=2M_C(T)-k
\quad\text{for every }T\in\mathcal U_C.
\tag{NDR.22}
$$

Thus the exact Bayes infimum in (NDR.21) is $k/(1-2p)$, both over all eligible policies and over effective eligible policies.

**Proof.** For each $\omega\in G$ from Lemma 8.2, the fixed selector $A_\omega$ meets every hypothesis of Lemma 9.3. Therefore

$$
F_\gamma(\omega):=
\sum_{T\in\mathcal U_C}\mu_{C,p}(\{T\})\gamma_A(T,\omega)
\ge\frac{k}{1-2p}
\quad(\omega\in G).
$$

Only the selected terminal tariff enters this sum. Each of its source-indexed functions is measurable by Definition 8.1, so the countable nonnegative sum $F_\gamma$ is measurable. Nonnegative integration and countable sum interchange give

$$
\begin{aligned}
\sum_T\mu_{C,p}(\{T\})\mathbb E_\omega\gamma_A(T,\omega)
&=\int_\Omega F_\gamma(\omega)\,d\mathbb P(\omega)\\
&\ge\int_G\frac{k}{1-2p}\,d\mathbb P(\omega)
=\frac{k}{1-2p}.
\end{aligned}
$$

For $\gamma=n$, this integrates only $n$; the deterministic use of $n\ge d$ in Lemma 9.3 introduced no measurability requirement on the seed-dependent $d$. For $\gamma=d$, no raw-call measurability was used. The measurable set $G$ and this terminal sum are sufficient even on a noncomplete seed space.

The deterministic supplied traversal is effective, terminates correctly on every source, has no exceptional seeds and satisfies (NDR.5). Its expected selected cost is $\mathbb E V=k/(1-2p)$ by Lemma 9.2. This gives both attainments. $\square$

In (NDR.21) the source average is a proof device. It is independent of the observer seed, never a service or extra input, and is supported on the same finite immutable sources for which the policy was already required to succeed individually. No actual source is selected after a tape is inspected.

**Theorem 10.2 (no smaller leading factor with any finite additive allowance).** For each $\gamma=d$ separately and $\gamma=n$ separately, every $A\in\mathcal R_C^\gamma$, every real $c<2$ and every finite $B\ge0$ admit a fixed finite $T\in\mathcal U_C$ such that

$$
\mathbb E_\omega\gamma_A(T,\omega)>cM_C(T)+B.
\tag{NDR.23}
$$

This includes effective randomized policies. The chosen $T$ is outside the seed expectation.

**Proof.** Choose $p\in(0,1/2)$ sufficiently close to $1/2$ that

$$
\frac{k\bigl(1-c(1-p)\bigr)}{1-2p}>B.
\tag{NDR.24}
$$

Such a choice exists because the numerator tends to $k(1-c/2)>0$ and the positive denominator tends to zero. Suppose no fixed source satisfied (NDR.23). Then every source would satisfy the opposite weak inequality, and averaging these fixed-source expectations under $\mu_{C,p}$ would give

$$
\begin{aligned}
\sum_T\mu_{C,p}(\{T\})\mathbb E_\omega\gamma_A(T,\omega)
&\le c\,\frac{k(1-p)}{1-2p}+B\\
&<\frac{k}{1-2p},
\end{aligned}
$$

contrary to Theorem 10.1. The affine source average is finite, since $c,B$ are finite and Lemma 9.2 gives a finite mean for $M_C$. This is an averaging contradiction over fixed atoms $T$; no map from a tape to a bad source is constructed or used. The lower bound applies to the larger class and hence also to its effective subclass. $\square$

**Corollary 10.3 (sharp fixed-source expected discovery factor).** For every finite context $C$ with $k\ge1$, and for $\gamma=d$ and $\gamma=n$ with their respective measurability contracts,

$$
\inf_{A\in\mathcal R_C^\gamma}\ \sup_{T\in\mathcal U_C}
\frac{\mathbb E_\omega\gamma_A(T,\omega)}{M_C(T)}=2.
\tag{NDR.25}
$$

The same equality holds when the infimum is restricted to effective randomized policies.

**Proof.** Apply Theorem 10.2 with $B=0$ for every $c<2$. Since $M_C(T)\ge k>0$, each policy's supremum in (NDR.25) is at least two. The effective traversal has pointwise ratio $2-k/M_C(T)<2$, whose supremum is two because the completion family has unbounded leaf counts. It supplies the matching upper bound in both classes. $\square$

The order in (NDR.25) is a worst fixed-source expectation, not the expectation of a tape-wise worst source. This settles the randomized and finite-additive questions left separate in Assumption 7.3 for this full-reconstruction interface. It supplies no bounded-error theorem, fixed-size optimum, word-only reconstruction optimum or full digital-storage optimum.

## 11. The same acquisition cut, continued values and simultaneous costs

**Proposition 11.1 (the genuinely reached retained-context entry).** Use exactly the actual producer, projected retained context and complete access cut of Assumption 5.1. Fix a reached $C$ with $k\ge1$. Allow a fresh source-independent seed law conditional on this $C$, and impose Definition 8.1 on the new phase's selected tariff. Then Theorems 10.1–10.2 and Corollary 10.3 apply to that phase, on the entire actual fiber $\mathcal U_C$.

For the already specified producer followed by the already specified attaining traversal, let $m_{\rm out}$ be the concrete outside leaf count, $M=M_C(T)$, and $Q_j$ the actual address sets in the two phases. Their same-run account remains

$$
\begin{aligned}
n_0=d_0&=2(m_{\rm out}+M)-1,\\
n_1=d_1&=2M-k,\\
n_{\rm lifetime}&=n_0+n_1,\\
Q_1&\subseteq Q_0,\qquad |Q_0\cup Q_1|-|Q_0|=0.
\end{aligned}
\tag{NDR.26}
$$

**Proof.** Assumption 5.1 and (NDR.9) identify the actual remaining source family with all independent fillings of the retained $C$. Every accessible source-dependent field factors through $C$; in particular the old length, chronology, acquired subtree values and equality partition do not further restrict this family. The new common entry and seed law therefore instantiate Definition 8.1. Apply the preceding theorems conditional on this fixed $C$.

The producer's actual full root traversal is paid before the cut. The new traversal reads only actual nodes in the holes, each of which it already visited in the producer phase. These are exactly the facts used in Theorem 5.2 and (NDR.10), yielding (NDR.26). Their prices concern these two actual runs, not a claim that an arbitrary competitor visits no new lifetime addresses. Access isolation and lawful new entry remain supplied, charged services, including when the producer has reached an absorbing halt. $\square$

The new lower bound prices phase-distinct addresses or new raw calls. It gives no positive lower bound on new lifetime-distinct addresses in (NDR.26). Its $B$ is a fixed additive allowance for the selected phase tariff, not an erased producer bill or a charge that can absorb all other resource coordinates.

**Proposition 11.2 (literal traffic, including its analyst-law mean).** On the same attaining phase, its literal address-letter traffic and two-bit reply payload are

$$
\begin{aligned}
\ell_1(T)&=\sum_{i=1}^k\sum_{q\in\operatorname{Pos}(U_i)}(|p_i|+|q|),\\
\operatorname{replybits}_1(T)&=2(2M-k).
\end{aligned}
\tag{NDR.27}
$$

Under Definition 9.1,

$$
\begin{aligned}
\mathbb E\ell_1
&=\frac{\sum_i|p_i|}{1-2p}+\frac{2pk}{(1-2p)^2},\\
\mathbb E\operatorname{replybits}_1
&=\frac{2k}{1-2p}.
\end{aligned}
\tag{NDR.28}
$$

**Proof.** The traversal sends the literal original-root address of each actual hidden node once; the translation is $q\mapsto p_iq$. This is precisely the traffic convention of Definition 5.3 and SLH Proposition 53.2. At relative depth $j$ in hole $i$, expected actual node count is $(2p)^j$. Nonnegative summation therefore gives

$$
\mathbb E\ell_1
=\sum_i\sum_{j\ge0}(|p_i|+j)(2p)^j.
$$

The identities $\sum_{j\ge0}x^j=(1-x)^{-1}$ and $\sum_{j\ge0}jx^j=x(1-x)^{-2}$ for $0<x<1$ give (NDR.28); the second follows from the mean of $V$. $\square$

In particular the exact source-call factor does not bound literal traffic by the same constant. The producer's traffic is separately $\ell_0=\sum_{q\in\operatorname{Pos}(T)}|q|$, with its $2n_0$ reply bits. Lifetime traffic adds $\ell_0+\ell_1$, even though lifetime-distinct address increments vanish. At fixed sources the comb behavior of Process Geometry §44.9 still permits quadratic address sums.

**Definition 11.3 (one simultaneous observer layout and the resources it uses).** The upper bound uses the existing root-frontier traversal, with the $k$ known hole-root prefixes, and no source update. The following is an account for one implementation of that supplied mechanism, not a new traversal or a claim of minimum total storage.

Let $N=2(m_{\rm out}+M)-1$ be the full source node count, $V=2M-k$ the phase node count, $h$ the maximum hidden-subtree height, $H=\max_i(|p_i|+h(U_i))$, and $D$ the full source height. These are after-the-fact bounds, not installed caps. Let $E_C$ count all actually retained context encodings, decoded copies and hole-root address lists, including lengths and indices. Let $K$ count installed generic traversal, reconstruction, parser and consumer code together with its fixed tables. No table indexed by an unknown source size is supplied.

For concreteness, a chronological report may store an address with a unary length prefix followed by its letters, and then a two-bit reply. These fields have $2|q|+3$ bits per record. Thus a retained full phase history has payload $2\ell_1+3V$, in addition to actual aggregate framing and length/index fields. Sending this particular address framing would likewise add $\ell_1+V$ bits to the raw $\ell_1$ address letters; no framing cost is hidden in (NDR.27).

| Coexisting store or service on this run | Representation and charge |
| --- | --- |
| The same original source | All $N$ actual ordered nodes and labels, its source representation, preparation, continuity and readout backing; it is not replaced by the observer's earned copy. |
| Public context and installed observer | $E_C+K$ bits for the representations actually kept, plus their installation work. The complete cut excludes other old accessible source advice. |
| Actual chronological phase reports | Payload $2\ell_1+3V$, plus the chosen framing, count and indexing fields. If the old producer archive physically survives behind the cut, its backing still exists and is counted although it is inaccessible. |
| Pending work and live address | At most $k+h$ pending addresses, of length at most $H$, plus lengths, stack positions and allocation metadata; one additional live transmitted address and its framing are included. |
| Earned full description and code | The reconstructed tree and `AtomicPrefixParser.code(T)` may both be retained. The code has $3(m_{\rm out}+M)-1$ bits: two per leaf and one per branch. A pointer-tree copy uses $O(N\log(N+2))$ bits with bounded-width node tags and indices. Separate output copies are added. |
| Reconstruction, parser and consumer workspace | The allocated recursion stack, current indices and counters, history-search workspace, temporary decoded copies, integer operands and output buffers. A tree recursion can have depth $D$; its indices need $O(\log(N+2))$ bits each. |
| Root references, call rights and lawful entry | Their actual retained representation, binding and service backing, including access isolation, new invocation and continuity assurance. A binding reference authenticates the same source without exposing its identity as advice. |
| Seed, control and additional records | The attaining traversal needs no random tape. Its growing control stack and counters remain charged; any general competitor's seed access/storage and any retained command or output journal are separate resources. |

The pending-list bound follows directly from this traversal's depth-first order: unstarted holes contribute at most $k$, and the current descent contributes at most one postponed sibling per hidden level. With explicit literal addresses, its address payload is at most $(k+h)H$, and the lengths and actual integer fields must also be stored. If a length or count is held in binary, its own width is charged; finite program size is not a bound on these growing fields.

One admissible installation retains the reports while reconstructing the full tree, writing its code and allocating the later decoder. It therefore counts these stores together. In symbols, its actual storage is the sum of source backing, any still existing isolated producer backing, $E_C$, $K$, report storage, allocated pending/stack storage, tree and code copies, scratch/output storage, and reference/rights/entry backing. A backing is counted once only if it is actually shared. This sum does not take the smallest store from mutually incompatible implementations. Releasing an archive or stack later changes later storage, and requires its real access/allocation operations; it cannot remove earlier acquisition work from the run.

Literal serialization, navigation and comparison are work as well as traffic. In an ordinary root-following implementation of the immutable service, each attained phase query traverses its $|q|$ original edges, so the phase uses $\ell_1$ such edge traversals and $V$ endpoint tag reads; an implementation checking each traversed constructor also performs $\ell_1$ departure-tag inspections. Observer address generation, history scans, finite reconstruction, allocation, code creation, decoding and output have their own costs at their actual word widths. The original `restore` repeatedly searches a chronological history; the original Boolean `finiteDecision` also enumerates candidates. As already separated in Process Geometry §44.9, neither is assigned a linear CPU bound merely from $V$ source requests. Full-tree output does not require that Boolean decision.

A conservative account for the supplied history-scanning mechanism can be made explicit. If the pending list is recomputed by folding the phase history at each action, the histories of lengths $0,1,\ldots,V$ cause $V(V+1)/2$ frontier-fold steps, including the final stopping action. A terminal `restore` at each hidden root visits $V$ hidden nodes altogether; each visit searches at most the $V$ reports, so it uses at most $V^2$ address comparisons. Comparing literal addresses and creating their child extensions costs $O(H+1)$ bit steps per such operation. With $u=\lceil\log_2(N+H+2)\rceil$, binary loop indices, fuel and allocated-node references have $O(u)$ bits. Consequently these frontier/reconstruction operations admit the conservative bit-work allowance $O(V^2(H+u))$, with report framing, context copying, full-tree/code allocation and consumer work added. This counts the actual supplied traversal with a report-scanning realization; it is neither a new source-query method nor a CPU claim about the additional Boolean candidate enumeration. A different list or pointer implementation pays its own copying and allocation costs.

Geometry and intrinsic-depth consumers also use actual-width arithmetic and their stated finite searches. A coordinate product of leaf counts is not a unit-cost scalar when those counts grow. No physical time, energy, fixed memory bound or price for an unimplemented authentication/isolation mechanism follows from the query tariff.

**Proposition 11.4 (continued exact values on the existing acquired cut).** After this attainment has acquired and retained the full tree, keep precisely the complete value-access contract of §6: an accessible earned tree description or its lossless code, installed decoding/consumer rules, original-root interpretation, and the appropriate lawful task entry. Then its geometry, addressed subtree-boundary and intrinsic-depth consumers are those already supplied by Definitions 6.1–6.2. Any finite common adaptive continuation asking for values $r_T(q)$ can be answered from that earned description with zero further source calls, while charging task input, decoding, local work, output and retained records.

**Proof.** The traversal's reconstruction is exactly $T$ on every source. Definition 6.1 supplies the existing finite conversion to the complete word/ancestor-coordinate pair and its inverse on the actual image; Definition 6.2 supplies the complete addressed-subtree criterion and intrinsic inverse-generation depth. Their original hypotheses hold for this same acquired $T$. No geometry or parser inverse is added here.

The retained description computes the original four-valued reply for every subsequently supplied finite address, including absent addresses. Induct over a finite adaptive continuation: identical public inputs and already produced values give the common rule the same next request, and evaluation from the retained exact tree gives the same value as the unchanged source. The source stays $T$ and the retained tree stays its exact description throughout. The required access and entry are explicit premises, and the actual computation and serialization remain paid. $\square$

This is a value task, not an obligation to manufacture a fresh raw event; such an obligation would require its actual source call. A stored description does not create a right to copy, reset or mutate the source, nor does it recover an erased actual chronology. The entry ambiguity and distinct read orders of Definition 6.2 persist under complete randomized acquisition. The new result prices how the already useful exact description is acquired; it does not give a new universal time coordinate or a physical boundary/memory realization.

## 12. Mathematical suppliers and the exact source-relative advance

**Convention 12.1 (immutable repository correspondence).** The repository suppliers in this section are fixed at public revision `39687802cb999fa97ebdbf17f226a541563cc351`; each cited source keeps its own stated source versions and hypotheses. The newly used native source is exactly `GenealogicalFiberTransport.Source = FreeMagma Bool`, with true meaning $\alpha$, false meaning $\beta$, ordered free pairing and no empty tree. These correspondences include the original owning Scribes, not a new compiled check.

| Supplied result and owning source | Actual correspondence and limit |
| --- | --- |
| [ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean), `source_foundation`, `acquisition_foundation`, `readout`, `paid`, `RandomContract`; its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.scribe.cs) | Addresses are `List Bool`, false $=L$, true $=R$; the four replies are exactly Definition 8.1's interface. The full-leaf uniqueness and one-leaf locality conjuncts yield Definition 2.1's $M$ certificate and compulsory leaves for the different full-tree target. The actual reconstruction/traversal conjunct supplies attainment. The Boolean third-image correctness clause is not this target; its measurable distinct-cost contract is only the model for the selected terminal contract. |
| [ActualPureAcquisitionCompiler](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.lean), `pure_node_fee`, public `nodes_nodup` and internal `paid_nodes`; its [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.scribe.cs) | For an installed positive budget $N$ and `Allowed N U`, arbitrary address price `tau` is summed on actual nodes. This is a bounded pure-observer attainment supplier, not an all-size randomized optimum or a free finite controller for the present unbounded family. The internal paid-set identity and its public consequence are credited rather than recreated as declarations. |
| Native Discovery §§1–7; [SLH](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md), Proposition 53.2 and §§59.1–59.4 | The same original literal family, paid actual traversal, $M$ evidence benchmark, projected context cut and complete independent fiber are retained. Equality/disequality partitions and old source-dependent run lengths are not additional inputs. §7's deterministic tape-wise warning does not supply the fixed-source expected result. |
| [NativeAncestorUniqueness](../../../D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness.lean), `native_ancestor_uniqueness`; its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness.scribe.cs) | Equality of both complete ordered leaf words and exact inorder ancestor-coordinate lists implies equality of native trees, with repeated labels and repeated subtrees allowed. §6 already supplies the finite image inverse; no coordinate port is installed. |
| [AncestorAreaInterval](../../../D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.lean), `ancestor_area_interval`, and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval.scribe.cs); [AtomicPrefixParser](../../../D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.lean), `code`, `parse`, `decode`, `result`, and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.scribe.cs) | The interval theorem requires $1\le a\le b\le m(T)$ and identifies an actual ambient subtree occurrence. The parser's private `parseFuel` and public exact suffix/decoding theorem supply the already retained code consumer, with fuel derived from input length. None supplies source acquisition or zero decoding work. |
| [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §44.9; [Recovery Geometry II](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md), §§36–42 | Process Geometry supplies the actual-node/literal-address/CPU separation used in §11. The other owner concerns an authentically prepared unknown rational positive Jacobi path with Read/Tick/Hold and optional Add; its earned native/record synchronization and simultaneous-width account are a distinct conditional model. Its pulse, Hold, order certificate and $2N$ tick horizon are not supplied to the immutable tree interface. |
| [Native Constructor Boundary Networks](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md), Assumption 1.2 and §§6–9; [NativeRelativePrefixBoxes](../../../D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeRelativePrefixBoxes.lean), `canonical_factor_levels`, and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeRelativePrefixBoxes.scribe.cs) | CBN's all-accessible-field retained alphabet and paid isolation are kept explicit. Its height-bounded canonical carriers, late-target one-Read task and complete temporal factors have different fibers and goals. Prefix-box classification assumes `q.length < d` in the canonical carrier and classifies genuine blocking leaves; it is not all-source shape advice, a full-tree decoder or an alternative to the arbitrary-depth charge. |
| [Compatible Predictive Waves](AURIC_COMPATIBLE_PREDICTIVE_WAVES_AND_RELATIONAL_SPECTRA.md), §§2, 11–12 | The owner distinguishes full common relations from diagonal/marginal lists, and keeps actual references, controls and growing records in its conditional joint model. Here the common object is a classical fixed source and actual history; no complex phase, coherent-control, independent tensor resource or physical-time port is inferred from the analyst's probability law. |

**Convention 12.2 (mature probability and query methods).** The $0/2$ offspring construction is classical Galton–Watson theory; see Theodore E. Harris, *The Theory of Branching Processes*, [Springer monograph](https://doi.org/10.1007/978-3-642-51866-9). Its specialization here has offspring generating function $1-p+pz^2$, mean $2p<1$, $k$ independent ancestors, and independent fair labels on terminating leaves. Lemma 9.2 proves the finite-source concentration and exact moments actually needed; these classical facts are not claimed as new branching theory.

The use of a source distribution to lower-bound randomized worst-input performance is mature query-complexity methodology; compare Andrew C.-C. Yao, *Probabilistic computations: Toward a unified measure of complexity*, FOCS, pp. 222–227, [DOI](https://doi.org/10.1109/SFCS.1977.24), and the decision-tree survey already cited after Theorem 3.1. The finite Boolean-cube models and finite minimax formulations are not applied as black boxes to this countably infinite arbitrary-address family. Lemma 9.3 proves its own source-law charge, and Theorems 10.1–10.2 prove the needed averaging passage directly, including the measurable per-source null exceptions.

The nonnegative countable-sum interchange is the ordinary monotone-convergence/Tonelli principle. At the upstream revision `56a005855ea17e0b0958f73ec801ae140b0a1679` pinned by this repository's `lake-manifest.json`, [Mathlib, Lebesgue/Add.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean), `MeasureTheory.lintegral_tsum`, assumes a countable index and an almost-everywhere measurable nonnegative extended-valued function at each index. In Theorem 10.1 the index is the countable fixed-source family and that function is $\mu_{C,p}(\{T\})\gamma_A(T,\cdot)$, measurable by the selected contract. No measurable intermediate transcript or assumption on the unselected tariff is needed. This is a source correspondence, not a new Lean application or verification claim.

**Scope 12.3 (the advanced cut and its remaining boundary).** Relative to these suppliers, the additional conclusions are the arbitrary-address source-law charge, its exact Bayes value for full reconstruction, the sharp worst fixed-source expected factor two, and exclusion of every $c<2$ even with an arbitrary fixed finite additive allowance. They hold on the original independent completion domain with the selected terminal measurability contract, including effective randomized policies. Attainment, full-tree evidence, geometry inversion, subtree boundaries, parser inversion and the actual retained-context producer are credited suppliers.

These are conditional source-relative deductions, without a worldwide-originality claim. The complete current tree, native relational geometry and retained description have their existing independently meaningful consumers on the same paid run. Actual past query order, authentic entry chronology, physical elapsed time, a universal alpha/beta generator, minimum simultaneous memory, bounded-error randomized recovery, physical installation and mutual recovery for every source/operation model remain separate obligations. This finite-source theorem does not complete the continuing space–time–boundary–memory programme.

## 追加锚（本行以下为增补区）

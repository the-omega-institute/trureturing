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

# Recursive relational observation: rooted boundary, literal history and memory recovery

This volume is ordinary finite-history and algebraic theory prose. It supplies no new Lean verification and no derivation of physical spacetime. Its subject is a typed relational process: which distinctions its spatial incidence, ordered time, boundary response and memory retain, and which local conditions make those expressions mutually recoverable. Existing mathematical suppliers retain their own hypotheses; their presence does not make this synthesis kernel-verified.

## 1. A common actual history fiber

**Definition 1.1 (actual typed process).** Fix a source identity $\xi$, an epoch $\nu$, an observation and operation contract $\Gamma$, and an initial type $i_0$. Let $I$ be the type set and $X_i$ the actual joint configurations of type $i$. A configuration includes every source relation, permission, controller input and retained record required by $\Gamma$. An actual joint configuration set need not be a Cartesian product of its coordinate images.

For each named operation $a:i\to j$, including its parameters in its name, specify a legal domain $D_a\subseteq X_i$, a deterministic successor $F_a:D_a\to X_j$, and an event label $\ell_a:D_a\to E_a$. Also specify the current declared readout $q_i:X_i\to O_i$. All legal successors remain in this same source/epoch contract. An executed failure is a legal step whose label records failure and its declared reason; an unavailable step is outside $D_a$ and has no successor. A terminal result has its declared type and legal menu.

Choose a root set $R$ and configurations $x_r\in X_{i_0}$ for $r\in R$. The set $H=H_{\xi,\nu,\Gamma,i_0}$ consists of all finite legal executions from those roots, including empty executions. A history records its root identifier and its ordered named operations and event labels. Its prefixes are histories, and $h\cdot a$ is a history exactly when $a$ is legal at its endpoint $\eta(h)$. Determinism determines the intervening configurations and labels from the root and word. Distinct root identifiers remain distinct histories even if a proposed observation identifies their starting configurations.

Here “actual” means allowed by this one joint source model. It does not mean that every member of $H$, or every continuation of one member, has been physically executed. An epoch-changing action requires an explicitly enlarged, consistently tagged model; it is not silently compared inside the fixed fiber.

**Definition 1.2 (four views and their actual joint image).** A choice of expressions is four functions on this same $H$:

$$
S:H\to Y_S,\qquad T:H\to Y_T,\qquad
B:H\to Y_B,\qquad M:H\to Y_M.
$$

$S$ records specified spatial incidence; $T$ records specified temporal data; $B$ records the chosen boundary response; $M$ records retained memory. These names impose no injectivity. In particular, a scalar duration, a literal event word and an ordered prefix archive are different possible functions. Their actual joint image is

$$
\mathcal J=(S,T,B,M)(H)\subseteq
Y_S\times Y_T\times Y_B\times Y_M.
$$

All comparisons below use this common carrier. Replacing $\mathcal J$ by the product of the four separate images would admit combinations not supplied by a common history. Current type tags belong to the expressions whenever operations are to be transported through them.

## 2. Exact recovery on actual images

**Definition 2.1 (view kernel and recovery).** For $u:H\to U$, write

$$
\ker u=\{(h,k)\in H^2:u(h)=u(k)\},\qquad
u^\#:H\to u(H),\quad u^\#(h)=u(h).
$$

Recovery of $v$ from $u$ means a function $\bar v:u(H)\to v(H)$ with $v^\#=\bar v\circ u^\#$. It refers only to realized values, including when $H$ is empty. It asserts neither an effective algorithm nor a total decoder on arbitrary ambient encodings.

**Theorem 2.2 (actual-image recovery criterion, reused).** For any $u:H\to U$ and $v:H\to V$,

$$
\left(\exists!\,\bar v:u(H)\to v(H),\quad
v^\#=\bar v\circ u^\#\right)
\quad\Longleftrightarrow\quad \ker u\subseteq\ker v.
$$

Consequently $u$ and $v$ recover each other exactly when $\ker u=\ker v$; the resulting functions between their images are inverse bijections.

Proof. A factor sends equal $u$ values to equal $v$ values, giving necessity. Conversely define $\bar v(u(h))=v(h)$. Kernel inclusion makes this independent of the history representing the input, and its output belongs to $v(H)$. Every input in $u(H)$ has a representative, which also proves uniqueness. With both inclusions, each composite fixes every realized value. This is precisely the actual-image criterion of [Process Geometry §34, PG.3403](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), recalled as a supporting result rather than a new general factorization theorem. $\square$

**Definition 2.3 (the recovery obligation for four expressions).** Put $J=(S,T,M)$. Theorem 2.2 gives the exact obligations

$$
\begin{aligned}
B\text{ determines }J
&\Longleftrightarrow \ker B\subseteq\ker S\cap\ker T\cap\ker M,\\
J\text{ determines }B
&\Longleftrightarrow \ker S\cap\ker T\cap\ker M\subseteq\ker B.
\end{aligned}
$$

Thus $B$ and $J$ recover each other iff these two kernels are equal. This does not imply that each component of $J$ separately recovers $B$. All four expressions recover each other pairwise iff

$$
\ker S=\ker T=\ker B=\ker M.
$$

The joint quotient $H/(\ker S\cap\ker T\cap\ker B\cap\ker M)$ retains exactly their collective distinctions, as in PG.3404. “Minimal” here concerns distinctions required by the chosen targets: identifying any more histories loses one of those targets. It is not a universal minimum of alphabet size, physical dimension, bit length, description length or acquisition cost. A common kernel need not be the diagonal $\Delta_H$; recovering the views is weaker than recovering literal history.

## 3. Forward congruence is an additional condition

**Definition 3.1 (executable view).** For a view $u$ with type tags, let $c(h)$ denote the entire declared input available to strategy selection and record updating. Require that $u(h)=u(k)$ imply:

1. Equal current declared readouts and equal $c(h),c(k)$.
2. For every named operation at the common type, equal enabledness.
3. If that operation is legal, equal complete event labels, including any executed failure, and $u(h\cdot a)=u(k\cdot a)$.

The comparison is for the same operation with the same parameters. A strategy using additional acquired information must expose that information in $c$ or refine the view. A private input cannot be replaced by an unrecorded oracle.

**Theorem 3.2 (descent of the declared process, reused).** Definition 3.1 is necessary and sufficient for unique readout, input, legal-domain, event and successor functions on $u(H)$ that intertwine the original ones. The descended legal domain is $u(\{h:h\cdot a\in H\})$. A fixed strategy that uses only the descended input produces matching named operations and labels from equal view values for as long as it executes.

Proof. Equal enabledness makes the legal domain a union of fibers. Define each descended quantity by a representative; the other equalities make every definition independent of that representative. Surjectivity of $u^\#$ gives uniqueness. Conversely an intertwining function on an image has only one value at an equal pair of inputs. Induction on the executed word proves the strategy statement. This is the typed partial-process application of [Process Geometry §3 and §34](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md); it adds no assumption that an illegal attempt is a successful successor. $\square$

In particular, a static map from memory to boundary says nothing by itself about a memory update. Updating memory through the declared tuple $(M(h),a,\ell_a(\eta(h)),c(h))$ requires that this tuple determine $M(h\cdot a)$ on its actual legal image. If two histories with that same tuple have different updated records, no such update function exists. If two views have equal kernels and either gives the entire executable interface above, their inverse image transports conjugate the descended processes. There is no transport claim about undeclared operations.

## 4. Recursive context-response profiles

**Definition 4.1 (independent contexts).** Let $C_n(i)$ contain every syntactically type-compatible named word of length at most $n$ starting at $i$, including the empty word. It is indexed independently of the state being tested. The response $\operatorname{Resp}(x,w)$ records the current readout, the ordered encountered event labels and cut readouts, and either completion or the first unavailable operation. An executed failure label and an unavailable operation remain distinct. A word that becomes unavailable does not acquire a fictitious successor.

Define $R_n(x)$ to be the response function on $C_n(i)$, retaining $i$. Define the equivalent recursive presentation $p_n$ by

$$
\begin{aligned}
p_0(x)&=(i,q_i(x)),\\
p_{n+1}(x)&=\left(i,q_i(x),\bigl(t_{a,n}(x)\bigr)_{a:i\to j}\right),\\
t_{a,n}(x)&=
\begin{cases}
\operatorname{absent},&x\notin D_a,\\
\operatorname{present}\bigl(\ell_a(x),p_n(F_a x)\bigr),&x\in D_a.
\end{cases}
\end{aligned}
$$

The sum tags are disjoint. The next level exposes both the legality and event of the first operation and the complete previous-level profile of its successor. It does not merely name an unexplained “response to responses.” On histories these maps mean $p_n\circ\eta$ and $R_n\circ\eta$.

**Theorem 4.2 (tower refinement and depth-relative recovery).** The profiles $p_n$ and $R_n$ determine each other on their actual images. Truncation gives

$$
\ker(p_{n+1}\circ\eta)\subseteq\ker(p_n\circ\eta),\qquad
\ker(R_\infty\circ\eta)=\bigcap_{n\ge0}\ker(p_n\circ\eta),
$$

where $R_\infty$ contains all finite-word responses. For any target $V:H\to Y$, exact depth-$n$ recovery is equivalent to

$$
\ker(p_n\circ\eta)\subseteq\ker V.
$$

Proof. At depth zero only type and current readout occur. Split a nonempty word at its first operation. Absence determines its unavailable response; presence supplies the event and the recursively required suffix response. Conversely the one-step responses give legality and labels, and responses to all prefixed suffixes give the successor profile. Induction proves the equivalence. Forgetting deepest suffixes gives truncation. Every finite word has some finite length, proving the intersection formula. The last assertion is Theorem 2.2 applied to this actual history fiber. The recurrence and kernel identification reuse the mathematical content supplied by `typed_finite_view_kernel` in [TypedFiniteViewKernel](../../../D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean); source inspection is not a fresh compilation of this presentation. $\square$

**Proposition 4.3 (compatible finite views need not have a source realization).** Take as actual states the eventually-zero infinite binary streams, with current readout the first bit and one total action that deletes it. For every $n$, the stream consisting of $n+1$ ones followed by zeros has an all-one depth-$n$ profile. These profiles form a compatible tower with no actual source realizing the entire tower. Also no fixed finite depth recovers the entire actual stream.

Proof. Any finite truncation of the all-one tower is realized by the stated eventually-zero stream. A realization of the entire tower would have a one in every coordinate, contradicting eventual zero. For any fixed $n$, the streams with respectively $n+1$ and $n+2$ initial ones have equal depth-$n$ profiles and different full streams. $\square$

Thus finite-stage consistency does not establish realization inside the declared source image, and the ability to separate each pair at some depth does not establish a uniform separating depth. The tower is a semantic family of possible tests; acquiring all its branches on one unknown source additionally needs the relevant continuation, copying, reset and permission contracts. [Context Geometry §§1–2 and 7](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) separates those operations and finite-budget acquisition from the full test family.

## 5. The local condition for literal history recovery

**Definition 5.1 (reachable boundary machine).** Suppose the boundary of a history depends on its endpoint, $B=b\circ\eta$, and satisfies the process descent conditions of §3. Write $\mathcal B_i$ for its reachable image of type $i$. Each legal named action then has a domain $\mathcal D_a\subseteq\mathcal B_i$, a successor $U_a:\mathcal D_a\to\mathcal B_j$, and a descended event label. Let $\rho:R\to\coprod_i\mathcal B_i$ be the boundary values at the roots. All sets and maps are restricted to these reachable images.

If $B$ is a complete response quotient, completeness means the entire declared continuation family, legality and ordered event labels, including the empty-context readout. A finite selected response list is not substituted for that quotient. Completeness for this future family does not itself say anything about the past.

Let $P$ be the map from the disjoint union of all reachable legal named-action domains:

$$
P:\coprod_{a:i\to j}\mathcal D_a\longrightarrow\coprod_j\mathcal B_j,
\qquad P(a,z)=U_a(z).
$$

Its input retains the operation name, parameters, source type and predecessor boundary. Define the following three conditions:

$$
\begin{aligned}
\mathrm{ROOT}:&\quad \rho\text{ is injective},\qquad
\rho(R)\cap P\left(\coprod_a\mathcal D_a\right)=\varnothing;\\
\mathrm{PREDECESSOR}:&\quad P\text{ is injective};\\
\mathrm{RECORD}:&\quad \exists d:M(H)\to B(H),\qquad
B^\#=d\circ M^\#.
\end{aligned}
$$

PREDECESSOR requires both injectivity within each action and disjointness of the images of distinct named actions. By Theorem 2.2, RECORD is exactly $\ker M\subseteq\ker B$. It is a statement about actual records, not about arbitrary candidate memory strings.

**Theorem 5.2 (rooted boundary-history and record criterion).** Under Definition 5.1, let $T_{\mathrm{lit}}$ retain the root and complete ordered named-action/event word, so that $T_{\mathrm{lit}}$ is injective on $H$. Let $M$ be any specified deterministic function of the same history. The following are equivalent:

1. ROOT, PREDECESSOR and RECORD.
2. $B$ is injective on $H$, and $B$ is recoverable from $M$ on the actual images.
3. $B$, $T_{\mathrm{lit}}$ and $M$ are pairwise mutually recoverable on the actual images.

Under these conditions there is a unique history decoder $D_B:B(H)\to H$. It has the equations

$$
\begin{aligned}
D_B(\rho(r))&=\varepsilon_r,\\
D_B(U_a(z))&=D_B(z)\cdot a,\\
D_B(B(h))&=h,\qquad B(D_B(z))=z.
\end{aligned}
$$

Event labels in the second equation are the declared deterministic labels of the recovered predecessor and action. This theorem concerns finite legal history. It does not assume a preassigned numerical clock or a uniform bound on history length.

Proof. First suppose ROOT and PREDECESSOR. If two histories have the same boundary and one is empty, ROOT forces the other to be empty, and root injectivity identifies the roots. If both are nonempty, write them $h'\cdot a$ and $k'\cdot b$. PREDECESSOR forces $a=b$ with all its typed parameters and $B(h')=B(k')$. Induction on the length of the first history, using the empty case to handle the other history's length, identifies both prefixes and hence the histories. Labels agree because the boundary machine retains their deterministic values. Thus $B$ is injective. RECORD supplies the second part of assertion 2.

Conversely suppose $B$ is injective on $H$. Equality of two root values identifies their empty histories, so $\rho$ is injective. A root value in a successor image would identify an empty history with a nonempty one, since that predecessor has a finite reaching history. This proves ROOT. If $U_a(z)=U_b(z')$, choose finite histories reaching $z$ and $z'$. Their extensions have equal boundaries and hence are the same literal history. Its last named action and its prefix are unique, giving $a=b$ and $z=z'$. This proves PREDECESSOR. The other part of assertion 2 is RECORD.

For assertion 3, $T_{\mathrm{lit}}$ already has diagonal kernel. Under assertion 2, $B$ does also; RECORD forces $M$ to have diagonal kernel. Theorem 2.2 gives all three inverse image transports. Conversely mutual recovery of $B$ and $T_{\mathrm{lit}}$ makes $B$ injective, and recovery of $B$ from $M$ is included in assertion 3.

Finally each reachable boundary has a finite reaching history. ROOT recognizes mathematically which values are roots, and PREDECESSOR gives a unique incoming pair for every other reachable value. Backward peeling follows any one finite reaching history in reverse and therefore terminates. In particular no infinite predecessor chain can begin at a reachable value under these conditions. Reversing the peeled operations gives $D_B$, and the equations follow from uniqueness. Decidability of root membership and effective computation of the predecessor have not been assumed. $\square$

**Definition 5.3 (coherent earlier records).** Under Theorem 5.2 put

$$
D_M=D_B\circ d:M(H)\to H,
\qquad \rho_k(M(h))=M(h|_k)\quad(k\le |h|),
$$

where $h|_k$ is the length-$k$ prefix. These are well-defined partial restriction maps on the actual memory image. They obey

$$
\rho_{|h|}(M(h))=M(h),\qquad
\rho_j(\rho_k(M(h)))=\rho_j(M(h))\quad(j\le k\le |h|).
$$

Indeed $D_M(M(h))=h$, so an actual memory value determines its unique length and all prefixes. Restricting a prefix twice gives the shorter prefix. The canonical prefix-table record

$$
M_*(h)=\bigl((0,B(h|_0)),\ldots,(|h|,B(h))\bigr)
$$

is an explicit persistent record satisfying RECORD by its last row, with restrictions given by table truncation. More compressed records satisfying RECORD have the same semantic recall through decoding; actual callable recall still needs an allowed reading and computation interface. No physical storage, access or retention guarantee follows from a set-theoretic restriction map.

**Definition 5.4 (a spatial expression with the same information).** Let $S_{\mathrm{path}}(h)$ be the oriented rooted incidence path of its successive cuts, with distinguished root identifier, endpoint, typed named edges and their event labels. Vertices are successive occurrences, even when a raw configuration repeats. An isomorphism must preserve all these data. Reading the unique oriented path recovers $T_{\mathrm{lit}}$; constructing that path from the word is inverse. Therefore its kernel is diagonal, and under Theorem 5.2 all four expressions $S_{\mathrm{path}},T_{\mathrm{lit}},B,M$ recover each other. This is spatial incidence carrying a path, not a derivation of a Euclidean metric. Removing edge names or root identity changes the expression and can destroy this conclusion.

The theorem gives a local criterion on a reachable boundary process for the diagonal historical kernel required by [MPC.25](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_MINIMAL_PREDICTIVE_CORE_BRIDGE.md). A forward congruence transports future executions; a unique predecessor and excluded roots recover past executions. Neither direction substitutes for the other. The underlying rooted-forest argument is elementary; the content here is its explicit application to the same typed boundary, chronology and record fiber, with an iff rather than an unconditional identification.

## 6. A rational realization and the Stern–Brocot convention

**Definition 6.1 (positive coprime boundary process).** Use one type, one root $(1,1)$, and

$$
\mathcal B=\{(p,q)\in\mathbb N_{>0}^2:\gcd(p,q)=1\}.
$$

Both named actions are total:

$$
L(p,q)=(p,p+q),\qquad R(p,q)=(p+q,q).
$$

Their event labels are their names. The current exact response is $r(p,q)=p/q\in\mathbb Q_{>0}$. Equality of these rational responses identifies the pairs: if $pq'=p'q$ and both fractions are positive and reduced, coprimality gives $p\mid p'$ and $p'\mid p$, so $p=p'$ and then $q=q'$. Thus this scalar rational readout retains the entire declared boundary state.

These two child formulas are the classical **Calkin–Wilf** convention, not the usual Stern–Brocot mediant-child order. The rational construction is literature-attested in Calkin and Wilf, *Recounting the Rationals*, [DOI:10.1080/00029890.2000.12005205](https://doi.org/10.1080/00029890.2000.12005205). Both conventions use the same two positive unimodular matrix generators. Definition 6.4 gives the explicit correspondence to the Stern–Brocot chart and to the repository's convention; their ordered histories are not silently identified.

**Theorem 6.2 (exact rational history and four-view reconstruction).** Every positive coprime pair is reached by a unique finite chronological $L/R$ word. Its reduced rational response determines that word, the oriented rooted named-incidence path and its indexed prefix table; each of these expressions determines the other three. No scalar step count replaces the word in this assertion.

Proof. The identities $\gcd(p,p+q)=\gcd(p,q)=\gcd(p+q,q)$ preserve $\mathcal B$. An $L$ image has first coordinate smaller than its second and has unique inverse $(p,q)\mapsto(p,q-p)$. An $R$ image has first coordinate larger and has unique inverse $(p,q)\mapsto(p-q,q)$. Each inverse stays positive and coprime on its stated domain. The images are disjoint; neither contains $(1,1)$. Equality $p=q$ in $\mathcal B$ forces $p=q=1$.

Starting at any pair, the appropriate subtraction decreases $p+q$ strictly and keeps it a positive integer. It therefore terminates at $(1,1)$. Reversing the subtractions gives a reaching word, while the strict inequalities make every inverse step unique. ROOT and PREDECESSOR hold on all $\mathcal B$, and the prefix table satisfies RECORD. Theorem 5.2 and Definition 5.4 give the four reconstructions. The rational readout can replace the pair because it is injective as proved above. This uses the classical subtractive Euclidean argument as supporting arithmetic, without claiming a new enumeration of the rationals. $\square$

**Definition 6.3 (decoder and matrix orientation).** For a positive rational first take its unique reduced positive pair. Define the word decoder by

$$
\begin{aligned}
\operatorname{dec}(1,1)&=\varepsilon,\\
\operatorname{dec}(p,q)&=\operatorname{dec}(p,q-p)L&& (p<q),\\
\operatorname{dec}(p,q)&=\operatorname{dec}(p-q,q)R&& (p>q).
\end{aligned}
$$

Appending, rather than prepending, the peeled last action gives chronological order. If $\operatorname{enc}$ executes a word from $(1,1)$, then

$$
\operatorname{dec}(\operatorname{enc}(w))=w,\qquad
\operatorname{enc}(\operatorname{dec}(p,q))=(p,q).
$$

With column vectors the matrices are

$$
G_L=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
G_R=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

For chronological $w=a_1\cdots a_k$,

$$
\operatorname{enc}(w)=G_{a_k}\cdots G_{a_1}\binom11.
$$

In [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean), `false` denotes $L$, `true` denotes $R$, and `wordMatrix` obeys $W(aw)=G_aW(w)$. Therefore the chronological pair formula is $W(\operatorname{reverse}w)(1,1)^{\mathsf t}$, not $W(w)(1,1)^{\mathsf t}$. For example executing $LR$ gives $(3,2)$, whereas $G_LG_R(1,1)^{\mathsf t}=(2,3)$. Both generators have determinant one.

**Definition 6.4 (literal Stern–Brocot chart).** For a chronological path word $w$, let

$$
W(w)=\begin{pmatrix}a&b\\c&d\end{pmatrix},\qquad
r_{\mathrm{SB}}(w)=\frac{a+b}{c+d}.
$$

The bounding fractions are $b/d$ and $a/c$, with $1/0$ allowed as the upper bound at the root. Their mediant is the displayed response. Right multiplication by $G_L$ replaces the upper bounding column by the column sum, so it selects the left mediant child; right multiplication by $G_R$ replaces the lower bounding column by the sum, selecting the right child. Thus this is the usual Stern–Brocot path order. It satisfies

$$
r_{\mathrm{SB}}(w)=r(\operatorname{enc}(\operatorname{reverse}w)),
\qquad
D_{\mathrm{SB}}(r)=\operatorname{reverse}(\operatorname{dec}(r)).
$$

Here $\operatorname{dec}(r)$ means decoding its reduced pair. The equations follow from the product convention and Theorem 6.2. Word reversal is bijective on all finite words, so this chart also recovers the literal word and all its prefixes. Reversal is a correspondence of encodings; it is not a prefix-preserving reversal of the actually executed process. To update the Stern–Brocot rational using this chart, recover its path or bounding matrix and append the chosen operation. Its child rule is not automatically the pair rule $r\mapsto r/(1+r)$ or $r+1$ at that same rational.

For the pair process choose $T(w)=w$, $B(w)=r(\operatorname{enc}(w))$, $M(w)$ the indexed table of prefix pairs, and $S(w)$ its root-oriented named-incidence path. For the Stern–Brocot chart replace each prefix pair by its mediant and bounding incidence. The above decoders give, in either convention, functions $D_V:V(H)\to H$ and transports

$$
\mathcal R_{VW}=W^\#\circ D_V,
\qquad
\mathcal R_{WV}\mathcal R_{VW}=\operatorname{id}_{V(H)}.
$$

All inverses are on the corresponding actual images. The repository's `unimodular_wordMatrix`, `word_node_is_reduced` and `unimodular_iff_wordMatrix` supply matrix facts with their stated scopes. In particular, the first module's reduced lower row is a different readout from the positive column-sum response here; the matrix-generation theorem alone does not assert the present four-view recovery or uniqueness of the positive-rational decoder.

## 7. Sharp failures of the recovery conditions

**Proposition 7.1 (actionwise injectivity does not recover order).** Let configurations be subsets of $\{a,b\}$, rooted at the empty set. The operation named $a$ adds $a$ only when it is absent; $b$ is defined similarly. Each successor map is injective on its own legal domain, the root is outside both images, and the endpoint is an exact current readout. Nevertheless $ab$ and $ba$ have the same endpoint $\{a,b\}$.

Proof. Removing the named element inverts each individual operation. But the two incoming pairs $(b,\{a\})$ and $(a,\{b\})$ have the same successor. Thus PREDECESSOR fails at precisely the overlap between action images. Every declared future response from that common endpoint is the same, including its exhausted legal menu, while the literal past words differ. Taking memory to be the endpoint satisfies RECORD and still cannot repair this collision. $\square$

**Proposition 7.2 (root exclusion is independent of unique predecessor).** On $\mathbb N$ let $U_L(n)=2n$ and $U_R(n)=2n+1$, with root $0$ and current readout $n$. The disjoint-union predecessor map is injective, but the empty word and $L$ have the same endpoint.

Proof. Parity determines the last action and integer division determines its predecessor, so PREDECESSOR holds. However $U_L(0)=0$, placing the root in a successor image and violating ROOT. Its repeated root returns identify arbitrarily many different lengths. $\square$

**Proposition 7.3 (a complete future boundary can erase endpoint and time).** Consider the actual archive-lifted process

$$
(n\bmod3,a^n)\longmapsto((n+1)\bmod3,a^{n+1})
$$

from $(0,\varepsilon)$. Let its only action always be legal, with constant event label and constant declared readout, and exclude the archive and work-state from the boundary tests. Then its entire response profile $B$ is constant. With $M=B$, boundary and memory recover each other but recover neither the work-state $n\bmod3$ nor the scalar count $n$, let alone the literal word.

Proof. Every finite continuation has the same label word and constant cut readouts, independently of the starting $n$. In particular $\varepsilon$ and $a$ have equal boundary and memory but different work-states and counts. Even retaining the work-state does not recover chronology: $\varepsilon$ and $a^3$ have the same work-state and different counts. The full configurations remain distinct because their archives differ. This is the $C_3$ separation of [Process Geometry §34](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), with the projections specified explicitly. A fuller declared readout changes the boundary and requires a new kernel comparison. $\square$

**Proposition 7.4 (exact rational recovery has no uniform noise margin).** Equip positive rational responses with ordinary absolute error and literal histories with the discrete distinction between unequal words. The rational decoder of §6 has no uniform positive response tolerance that determines every literal word.

Proof. The root response is $1$. For $n\ge1$, the distinct word $R^{n-1}L$ has response $n/(n+1)$, whose distance from $1$ is $1/(n+1)$. For any error radius $\epsilon>0$, choose $n$ with $1/(n+1)<2\epsilon$. The two closed error intervals then overlap, so a common corrupted measurement is compatible with two different histories. No decoder using only that measurement can always return both correct words. Thus exact set-theoretic inversion supplies neither a uniform noise margin nor a uniformly continuous inverse into the discrete history space. $\square$

These failures separate four obligations: avoiding action-image mergers, excluding rooted returns, retaining the requested distinctions in the response contract, and obtaining sufficient precision. They do not refute the conditional theorem, and solving one obligation does not discharge the others.

## 8. Repository and literature correspondences

**Definition 8.1 (scope of reused suppliers).** The following correspondences fix the meaning of the source citations. They are source-level mathematical dependencies and analogues with explicit hypotheses, not a claim that the prose above has been compiled.

| Source | Exact correspondence and retained boundary |
| --- | --- |
| [Process Geometry §34, PG.3403–3404](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md) | Common actual histories, kernel factorization, joint image and forward congruence supply §§1–3; its archive-lifted $C_3$ example supplies Proposition 7.3. Their static conditions do not themselves give unique pasts. |
| [Joint Kernel Minimal Predictive Core Bridge, MPC.25](RECURSIVE_RELATIONAL_OBSERVATION_JOINT_KERNEL_MINIMAL_PREDICTIVE_CORE_BRIDGE.md) | The intersection of endpoint/time and memory kernels must be diagonal to recover a path. Theorem 5.2 gives an explicit local rooted-boundary criterion in the stronger case where boundary alone separates literal histories. |
| [Typed Residual Cocycle Reconstruction §§1–4](RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md) | Ordered legal words in an actual residual graph, and the loss of return-block order under commutative accumulated time. Its finite recurrent positive-duration criterion has different hypotheses from the rooted forest here. |
| [Native Clocked Recovery and Order §§5–8](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md) | A concrete acquired-source four-view construction, with retained primitive chronology and a separate acquired order relation. This volume does not import its access, installation or clock convention into the rational process. |
| [Context Geometry §§1–2 and 7](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) | Typed contexts, explicit failure distinctions and the difference between a full context geometry and its finite-budget acquired portion. |
| [TaskIdentityGlobalIdentityCriterion](../../../D5/S3/ConceptDynamics/SufficiencyQuotient/TaskIdentityGlobalIdentityCriterion.lean), `task_identity_global_identity_criterion` | Joint target-profile injectivity is equivalent to diagonal kernel and injective task identity. It does not assert that a chosen boundary family is jointly faithful. |
| [MinimalPredictionBeliefState](../../../D5/S3/ConceptDynamics/SufficiencyQuotient/MinimalPredictionBeliefState.lean), `minimal_prediction_belief_state` | Given a predictor factoring the full specified profile through a summary, the actual summary image maps uniquely and surjectively to the predictive quotient. Prediction sufficiency is not literal-history recovery. |
| [FiniteObservationQuotientRange](../../../D5/S3/ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange.lean), `finiteObservationQuotientEquivRange` | The finite joint-readout quotient is equivalent to its realized range. The volume's arbitrary-view actual-image reasoning is not an assertion that all target families are finite. |
| [LinearProjectionDescentCriterion](../../../D5/S3/Observer/Dynamics/LinearProjectionDescentCriterion.lean), `linear_projection_descent_criterion` | For its finite complex matrix projection, interface descent is equivalent to vanishing hidden-to-visible flow; the commutator equivalence additionally assumes Hermitian dynamics. It is a linear instance of forward descent, not a physical origin theorem. |
| [ProjectedExactDescent](../../../D5/S3/Observer/Hankel/ProjectedExactDescent.lean), `projectedState_eq_of_descent`, `outputs_eq_of_descent` | Fixed global intertwining and the stated output factorization propagate through the same driven input sequence. Separately chosen inputs are not substituted for that common sequence. |
| [WordNodesAreReduced](../../../D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.lean), `wordMatrix`, `unimodular_wordMatrix`, `word_node_is_reduced` | The exact two generators, recursive multiplication order, determinant-one invariant and lower-row coprimality. The lower-row fraction is not the column-sum chart of Definition 6.4. |
| [UnimodularGeneration](../../../D5/S3/PrimeForms/SternBrocot/UnimodularGeneration.lean), `unimodular_iff_wordMatrix` | Natural determinant-one matrices are generated by finite words. Its adapted arithmetic source and license attribution remain those of the original file; no source code is reproduced here. |
| [TypedFiniteViewKernel](../../../D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean), `typed_finite_view_kernel` | Typed partial labelled finite views equal their recursive refinement relations, whose intersection is full behavior; a plateau on the full declared domain persists. An observed plateau on a sample is not that hypothesis. |
| [ArchiveClockRecovery](../../../D5/S3/ObserverMemory/Algorithms/ArchiveClockRecovery.lean), `archive_clock_recovery_and_finite_ambiguity` | Under its finite configuration/action/output assumptions, visible archive clock recovery has a synchronized-path and reachable-edge criterion, with ambiguity length at most the square of the configuration count. It is not a theorem that a final boundary or a scalar count reconstructs the action word. |

**Definition 8.2 (literature status and the synthesis).** Exact response equivalence, deterministic quotient processes and coalgebraic behavior are classical background, `literature-attested`, with the repository's [Rutten literature note](../../../Library/ConceptDynamics/rutten1996universal.md) pointing to *Universal coalgebra: a theory of systems*, CWI report CS-R9652, and the published article [DOI:10.1016/S0304-3975(00)00056-6](https://doi.org/10.1016/S0304-3975(00)00056-6). The positive-rational child construction and Euclidean decoding in §6 are `literature-attested` arithmetic, attributed to Calkin and Wilf above; the shared generator formulas are also explicitly present in the cited Lean suppliers.

The source-specific assembly in §§5–6 is `repo-derived`: the boundary-image ROOT/PREDECESSOR criterion, the RECORD equivalence, coherent prefix restriction maps, four-view transports, and the explicit separation of chronological column action from the repository word product are derived here for the declared common fiber. This label records the location of the derivation and makes no claim of literature novelty. The factorization lemma, recursive observation principle and rational enumeration are supporting known mathematics, not claimed as new general results. No assertion of whole-repository absence or of an original physical theory is made.

## 9. Limits and open obligations

**Definition 9.1 (what the minimal relational structure specifies).** The structure used here consists of types, roots, legal named edges, successor and event functions, and declared readouts on one actual joint carrier. The four expressions add no independent ontology: they are incidence, ordered execution, response and retained-record maps of that carrier. Equal kernels certify equal retained distinctions; forward congruence certifies the declared operations; ROOT and PREDECESSOR certify unique finite ancestral words. These are separate mathematical properties of a specified model.

**Proposition 9.2 (unbounded histories require unbounded distinguishable records).** At depth $n$ in the binary rational process there are $2^n$ different literal histories and therefore $2^n$ different values of any record satisfying Theorem 5.2. An encoding into fixed-length binary records requires at least $n$ bits at that depth. The subtractive decoder need not use a number of steps bounded by a constant multiple of the bit length of its rational input.

Proof. Every binary word of length $n$ is legal and Theorem 6.2 separates them. An injective encoding of these words needs at least $2^n$ code values, whereas $b$ bits have only $2^b$ values, giving $b\ge n$. The pair $(1,N)$ has an input of $O(\log N)$ bits but the stated subtractive decoder performs $N-1$ subtractions and outputs the word $L^{N-1}$. This does not exclude an efficient compressed decoder with a different output contract. $\square$

**Obligation 9.3 (metric and physical time).** The spatial path has an incidence relation and orientation, but no supplied Euclidean or Lorentzian metric, dimension, locality law or dynamics of physical matter. Literal time is an ordered finite word. A duration requires a separately specified edge weight or clock law; recovering a word from a scalar duration requires its own fiber-separation proof. A spatial metric or physical duration is not obtained by renaming the incidence or word.

**Obligation 9.4 (precision, access and source identity).** A physical realization needs a measurement channel with explicit errors, allowed actions, preparation and source-identity guarantees, resource accounting, and an accessible persistent record. Proposition 7.4 rules out a uniform noise tolerance over all rational histories in the stated metric. Finite denominator or depth bounds can change that question but are additional restrictions. A set-theoretic inverse neither grants permission to inspect its input nor certifies which source/epoch produced it. Backward mathematical decoding also does not grant an inverse physical transition or a reset.

**Obligation 9.5 (quantum and nondeterministic realization).** No quantum instrument, channel, probability law, coherent branch realization or nondeterministic successor has been specified. The deterministic partial-function theorem does not automatically apply to their marginal response laws. Any such extension must specify a common joint realization, the retained classical or quantum information, and the admissible operations; equality of separately attainable marginals does not supply these data.

**Obligation 9.6 (uniform bounds and formalization).** No uniform finite context depth for arbitrary actual sources follows from §4, and no effective predecessor algorithm follows from §5 without decidable domains and effective maps. A Lean formalization of the rooted boundary-history/record synthesis, its exact supplier instantiations and the convention bridge is not supplied by this prose. Existing declarations remain authoritative only for their own compiled statements and hypotheses. These boundaries leave the finite deterministic mathematical conclusions intact and specify the additional obligations needed to use them for a concrete implementation or a physical model.

## 追加锚（本行以下为增补区）
